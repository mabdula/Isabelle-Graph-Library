# Style guide for algorithm theories in the Isabelle Graph Library

Version 2, 2026-10-11. Version 1 is kept as `Library_Style_Guide.v1.md`.

**Precedence (user decision, 2026-10-11).** The depth-first and breadth-first
search theories are the ground truth:

- `Set_Graphs/Graph_Algorithms/DFS.thy`
- `Set_Graphs/Graph_Algorithms/DFS_Example.thy`
- `Set_Graphs/Graph_Algorithms/BFS_2.thy`
- `Set_Graphs/Graph_Algorithms/BFS_Subprocedures.thy`
- `Set_Graphs/Graph_Algorithms/BFS_Example.thy`

Other library theories are used only where they do not contradict these
five. Where they do, the DFS/BFS form is used, and this guide says so. Where
DFS/BFS do not decide a question, the guide says that too.

Every rule states the measurement or the source text it rests on. Where the
Hopcroft–Karp (HK) theories deviate, the HK figure is given next to it.

Code templates use the ASCII form of Isabelle symbols (`\<Longrightarrow>`, ...),
as the theories on disk must. The templates show the **intended shape only**;
none of them has been checked by Isabelle.

---

## 0. Corpus and method

| Group | Theories | Lines | Lemmas | Role |
|---|---|---|---|---|
| DFS | `DFS.thy` (+ `DFS_Example.thy`) | 878 | 81 | ground truth |
| BFS | `BFS_2.thy` (+ `BFS_Subprocedures.thy`, `BFS_Example.thy`) | 1806 | 103 | ground truth |
| Library (same template) | `DFS_Cycles.thy`, `DFS_Cycles_Aux.thy`, `Dinic/DFS_Collect_Backtrack.thy`, `Matroids_Greedy/Best_In_Greedy.thy`, `Hungarian_Method/Hungarian_Method_Top_Loop.thy` | 6638 | 371 | context only |
| HK | `Hopcroft_Karp.thy`, `HK_Top_Loop.thy`, `HK_Search.thy`, `HK_Phase.thy`, `HK_Example.thy` | 2086 | 108 | measured against the ground truth |
| Read-only spec (interim; replaced by the Graph ADT split, step R0-0) | `Hopcroft_Karp/Pair_Graph_Specs_Read_Only.thy` | 167 | 18 | measured against the ground truth |

The proof-style statistics (§1) are taken over `DFS.thy` and `BFS_2.thy`; the
example and subprocedure theories are used for §3.6. The locale and
interpretation counts in §2.2 and §3.6 cover all tracked library theories
outside `Micali_Vazirani/`.

Scripts, next to this file:

- `style_stats.py`: proof and naming statistics. It removes comments, masks
  the strings and cartouches, splits each theory into top-level commands,
  splits each lemma into statement and proof, and counts.
  ```
  python3 style_stats.py out.json DFS=<lib>/Set_Graphs/Graph_Algorithms/DFS.thy BFS=<lib>/Set_Graphs/Graph_Algorithms/BFS_2.thy NEW=<thy>,<thy>
  ```
- `locale_struct.py`: imports, locales with their parents, and the
  `sublocale` / `interpretation` / `global_interpretation` commands with their
  enclosing context.
  ```
  python3 locale_struct.py <dir-or-theory> ...
  ```

The output quoted here is `stats.txt`.

---

## 1. Summary of the measurements

The DFS and BFS columns are the targets. The library column is context.

| Metric | DFS | BFS | Library (5) | HK |
|---|---|---|---|---|
| Lemmas closed by a single `by` (possibly after `using`) | 76.5% | 63.1% | 66.8% | **38.0%** |
| Lemmas with a structured (`proof … qed`) proof | 21.0% | 27.2% | 27.5% | **61.1%** |
| Median proof length (non-blank lines) | 1 | 2 | 2 | **8** |
| Proof lines per statement line | 1.50 | 3.15 | 2.94 | **4.43** |
| `auto` among all method calls | 61% | 51% | 43% | **11%** |
| `simp` among all method calls | 2% | 4% | 9% | **29%** |
| `rule` among all method calls | 10% | 8% | 5% | **24%** |
| `elim!:` / `intro!:` per lemma | 0.38 / 0.46 | 0.50 / 0.49 | 0.75 / 0.40 | **0.00 / 0.00** |
| Labelled `have`/`show`/`obtain` per lemma | 0.01 | 0.21 | 0.43 | **2.29** |
| `[OF …]` per lemma | 0.26 | 0.61 | 0.68 | **2.10** |
| Facts quoted as cartouches `\<open>…\<close>` per lemma | 0.07 | 1.64 | 1.69 | **0.02** |
| Named assumptions (`assumes h: …`) per lemma | 0.00 | 0.00 | 0.01 | **0.51** |
| Statements in plain `"\<lbrakk>…\<rbrakk> \<Longrightarrow> …"` form | 79% | 78% | 78% | **57%** |
| `\<lbrakk>` per statement | 0.69 | 0.79 | 0.55 | **0.00** |
| Lemmas carrying an attribute (`[invar_holds_intros]`, `[simp]`, …) | 80% | 67% | 61% | **6.5%** |
| `by` starting its own line | 100% | 95% | 71% | **17%** |
| `using` starting its own line | 100% | 99% | 95% | **35%** |
| `by (rule …)` among the closing calls of structured proofs | 2.6% | 1.0% | 0.7% | **25.9%** |
| `named_theorems` declared | 9 | 9 | 25 | **0** |
| State `record`s | 1 | 1 | 5 | **0** |
| Recursive definitions that are `function (domintros)` over one state record | 1/1 (+ `_impl`) | 1/1 (+ `_impl`) | 6/6 (+ 5 `_impl`) | **0** (one over a bare matching, one 6-argument `fun`) |
| Invariant families (`invar_*` definitions) | 5 | 13 | 20 | **0** |

---

## 2. Naming

### 2.1 Theories

Ground truth: `DFS`, `DFS_Example`, `BFS_2`, `BFS_Subprocedures`,
`BFS_Example`. An algorithm has:

- one theory named after the algorithm;
- if it has sub-procedures, a theory `<Algorithm>_Subprocedures` that
  implements them;
- a theory `<Algorithm>_Example` with the executable instance and the
  demonstrations.

Abbreviations are used where the abbreviation is the algorithm's established
name (`DFS`, `BFS`). Multi-word names are spelled out with capitalised words
(`Bellman_Ford_Example` elsewhere in the library; this does not contradict
DFS/BFS).

The `_Instantiation` theories of the Hungarian method and Dinic are not part
of the DFS/BFS layout. What they contain goes into the `_Example` theory
(§3.6).

*HK:* `HK_Top_Loop`, `HK_Search`, `HK_Phase`, `HK_Example` use an abbreviation
that is not the algorithm's established name. Use `Hopcroft_Karp_Top_Loop`,
`Hopcroft_Karp_Phase` (plus `…_Subprocedures` where §3.6 calls for one), and
`Hopcroft_Karp_Example`.

### 2.2 Locales

Ground truth:

| Role | DFS | BFS |
|---|---|---|
| Definitions locale | `DFS` | `BFS` |
| Proofs | `locale DFS_thms = DFS + assumes DFS_axioms: DFS_axioms` | `context includes … assumes BFS_axiom begin … end` inside `BFS` |
| Further proofs locale for a special case | `locale DFS_immediate_termination = DFS + assumes graph_invar_G: "Graph.graph_inv G"` | — |
| Sub-procedure implementation | — | `BFS_subprocedures` |
| Shared bundle of data-structure parents | — | `Pair_Graph_Sepcs_Set2` (sic) |
| Data-structure parents and their qualifiers | `Graph: Pair_Graph_Specs`, `set_ops: Set2` | the same |

Rules:

1. **The definitions locale has the algorithm's name.** The proofs are in
   `<name>_thms = <name> + assumes <name>_axioms`, or in a `context …
   assumes <name>_axiom` inside the definitions locale.
2. **The `_spec` convention is not used.** Twenty-three locales elsewhere in
   the library are named `<name>_spec` and paired with a proofs locale
   `<name>` (`hungarian_loop_spec`/`hungarian_loop`, `dinic_spec`/`dinic`,
   `orlins_spec`/`orlins`: 19 pairs). That gives the bare name to the
   *proofs* locale, the opposite of DFS (`DFS`/`DFS_thms`), so it contradicts
   the ground truth.
3. **Data-structure specifications** have capitalised names ending in
   `_Specs` (`Pair_Graph_Specs`), and enter as qualified parents: `Graph:`
   for the graph, `set_ops:` for the vertex sets.
4. **Algorithm names are capitalised** (user decision, 2026-10-11), as `DFS`
   and `DFS_Cycles` are. The capitals carry over to everything prefixed by
   the name: the locale, the loop constant, the record type and the branch
   constants (`Hopcroft_Karp_Loop`, `Hopcroft_Karp_Loop_state`,
   `Hopcroft_Karp_Loop_impl`, `Hopcroft_Karp_Loop_call_1_conds`, as in
   `DFS_state`, `DFS_impl`, `DFS_call_1_conds`). Role suffixes stay lower
   case (`Hopcroft_Karp_Loop_thms`, as `DFS_thms`). Interpretation names and
   the executable constants of the example theory stay lower case, as in
   `DFS_Example` (`dfs`, `dfs_impl`; here `hopcroft_karp_loop`,
   `hopcroft_karp_loop_impl`). The lower-case names of other library parts
   (`hungarian_loop`, `dinic`) are not followed.

*Read-only spec:* `pair_graph_specs_read_only` is a data-structure
specification, so by rule 3 it is `Pair_Graph_Specs_Read_Only` (user
ruling, 2026-10-11: "It should be capitalised as
Pair_Graph_Specs_Read_Only"). In the algorithm locales it enters as the
`Graph:` parent.

Status (2026-10-11, R0-0 done in the HK copy): the Graph ADT split is
applied, with both base locales capitalised by the user's choice:
`Pair_Graph_Specs_Read_Only` in `Directed_Set_Graphs.Pair_Graph_Specs` and
`Pair_Graph_U_Specs_Read_Only` for undirected graphs. The full library build
passes (exit 0). The renamed patch is
`Hopcroft_Karp/backups/integration/Graph_ADT_Split_capitalised.patch` (md5
`fed53843…`). The interim theory is deleted, and `RO.*` is now `G.*`:
`G` in `Pair_Graph_RBT` has exactly the read-only operations, so
interpretation subsumption holds and no bridges are needed.

Facts established in R0, for writing interpretations:
- The parameter order of `Pair_Graph_Specs_Read_Only` is `insert isin t_set
  sel vset_empty vset_delete vset_inv lookup adjmap_inv`.
- `global_interpretation … for x y defines c = t` abstracts `c` only over
  the `for` variables that occur in `t`.

*HK:* `hk_loop_defs` (definitions) and `hk_loop_spec` (assumptions and proofs)
become `Hopcroft_Karp_Loop` and `Hopcroft_Karp_Loop_thms`. Version 1 of this
guide proposed `hopcroft_karp_loop_spec`/`hopcroft_karp_loop`, which follows
the Hungarian convention and is withdrawn.

### 2.3 Constants

Measured over all constants of DFS, BFS and their example theories:

| Role | Name pattern | Examples |
|---|---|---|
| The loop | algorithm name | `DFS`, `BFS` |
| Executable twin | `<loop>_impl` | `DFS_impl`, `BFS_impl` |
| Branch condition | `<loop>_call_<i>_conds`, `<loop>_ret_<i>_conds` | `DFS_call_1_conds`, `BFS_ret_1_conds` |
| Branch update / result | `<loop>_upd<i>`, `<loop>_ret<i>` | `DFS_upd2`, `DFS_ret1` |
| Input conditions bundled | `<loop>_axioms` / `<loop>_axiom` | `DFS_axioms`, `BFS_axiom` |
| Initial state | `initial_state` (no prefix) | |
| Invariants | `invar_<i>` for representation invariants, `invar_<what it says>` otherwise | `invar_1`, `invar_seen_stack`, `invar_visited_through_seen`, `invar_dist'` |
| Termination measures | `call_<i>_measure`, `call_<i>_measure_<j>`, `<loop>_term_rel'` | `call_1_measure`, `call_1_measure_2`, `DFS_term_rel'` |
| Relations between states | `state_rel_<i>` | `state_rel_1` |
| Running the loop | `<loop>_run`, `<loop>_run_impl` | `DFS_run = DFS initial_state` |
| Sub-procedure parameters | their own names, no prefix | `expand_tree`, `next_frontier` |
| Executable constants (example theory) | lower-case algorithm name + role | `dfs_impl`, `dfs_initial_state`, `bfs_impl`, `bfs_initial_state`; graph operations `neighbourhood`, `add_edge`, `from_list` |

Where another library locale already plays the same role, reuse its parameter
names; this does not contradict DFS/BFS. For a matching interface those are
the Hungarian method's `empty_matching`, `matching_invar`, `augment` and
`matching_abstract` (HK: `matching_abs`, and no `empty_matching`).

Global abbreviations are rare. DFS has one (`neighbourhood'`, with notation
`\<N>\<^sub>G`) and BFS two (`neighbourhood'`, `BFS_ret1`).

*HK:*
- The prefix `hk_` (`hk_loop`, `hk_phase`, `hk_srcs`, `hk_blk`, `hk_idfs`) is
  not the algorithm's name.
- The phase context of `HK_Phase.thy` declares nine abbreviations with names
  of one to three letters (`es`, `Mt`, `Ut`, `S`, `st`, `T`, `cl`, `CG`, `lv`).
  Spell them out, or better, make them parameters or definitions of the phase
  locale (§6.2).
- A name must not collide with an existing constant. `matching`
  (Basic_Matching) and `sources` (Pair_Graph) are taken, so the record field is
  `current_matching` and the phase uses `bfs_sources`.

### 2.4 Lemmas

DFS/BFS lemma names average 18–22 characters and 4.0–4.5
underscore-separated parts; HK names average 14 characters and 3.0 parts. The
names say which object a lemma is about and what it says about it. They follow
fixed schemes for the loop machinery:

| Lemma | Name | Attribute |
|---|---|---|
| Branch condition, elimination form | `<loop>_call_<i>_conds`, `<loop>_ret_<i>_conds` | `[call_cond_elims]` |
| Branch condition, introduction form | `<loop>_call_<i>_condsI`, `<loop>_ret_<i>_condsI` | `[call_cond_intros]` |
| Case split over the branches | `<loop>_cases` | — |
| Unfolding per branch | `<loop>_simps` | — |
| Induction per branch | `<loop>_induct` | — |
| Domain per branch | `<loop>_domintros` | — |
| Invariant, elimination form | `invar_<x>_props` | `[invar_props_elims]` |
| Invariant, introduction form | `invar_<x>_intro` | `[invar_props_intros]` |
| Invariant preserved by branch *i* | `invar_<x>_holds_<i>` (DFS) or `invar_<x>_holds_upd<i>` / `_ret_<i>` (BFS) | `[invar_holds_intros]` |
| Invariant preserved by the loop | `invar_<x>_holds` | `[invar_holds_intros]` |
| Return condition reached | `ret<i>_holds`, `<loop>_ret_<i>` | `[ret_holds_intros]` |
| Correctness at a return branch | `<loop>_correct_ret_<i>` (DFS), `<loop>_correct_<k>_ret_<i>` (BFS) | — |
| Termination | `call_<i>_terminates`, `in_<loop>_term_rel'`, `<loop>_terminates` | `[termination_intros]` |
| Initial state | `initial_state_props` | `[invar_holds_intros, termination_intros]` |
| Final results | `<loop>_correct_<k>`, `<loop>_correct_<k>_strong` | — |
| Executable twin | `<loop>_impl_same` (BFS), `<loop>_impl_to_<loop>` (DFS) | — |
| Sub-procedure contract, as proved by the implementation | the name of the contract assumption (`next_frontier`, `expand_tree`) | — |

*HK* names such as `G_char`, `M_sub`, `S_free`, `st_eq`, `st_valid'`, `cl_mem`,
`CG_abs`, `DS_facts`, `inp_parts`, `C`, `A` refer to the one-letter
abbreviations above and say little about the content. Rename them together
with the abbreviations: e.g. `matching_subset_graph`, `sources_are_free`,
`bfs_state_valid`.

### 2.5 Variables, cases, labels

- The state variable has the name of the record, in lower case: `dfs_state`,
  `bfs_state`. *(HK: `m`.)*
- In loop inductions the case is named `IH`:
  `case IH: (1 dfs_state)`. It is then used positionally (`IH(1)`, `IH(2-)`).
- Assumptions are not named in the statement (0.00 named assumptions per
  lemma in DFS and BFS). They are referred to as `assms(2)` or as cartouches
  `\<open>invar_2 bfs_state\<close>`. *(HK: 0.51 per lemma.)*
- Facts inside a proof are rarely labelled (0.01 per lemma in DFS, 0.21 in
  BFS). They are passed on with `hence`/`thus`/`moreover`/`ultimately` or
  quoted as cartouches. *(HK: 2.29 labels per lemma.)*

---

## 3. Definitions, program state, locales and theories

### 3.1 State record and result datatype

The loop takes **one** argument, a `record` holding the whole program state.
That is 4 of 4 recursive definitions in DFS/BFS, and 15 of 15 in the wider
corpus. Field names are nouns for what the field holds. Results that the
caller must inspect are a field, typed by a small `datatype`:

```
datatype return = Reachable | NotReachable
record ('ver, 'vset) DFS_state = stack:: "'ver list" seen:: "'vset"  return:: return

record ('parents, 'vset) BFS_state = parents:: "'parents" current:: "'vset" visited:: "'vset"
```

Updates use record syntax:
`dfs_state \<lparr>stack := stack', seen := seen'\<rparr>`.

*HK:* there is no record. `hk_loop` recurses on the bare matching.
`disjoint_search_gen` is a `fun` with six arguments
(`un blk step avoid vis rs`), and the phase state is threaded through a
`case … of (Some p, vis') \<Rightarrow> …` on a pair.

### 3.2 The loop

- `function (domintros)` with an explicit type signature over the state
  record. Body: `case`/`if` on the state, with each branch either recursing on
  an updated record or returning one. Closed by `by pat_completeness auto`.
- A twin `partial_function (tailrec) <loop>_impl` with the same body.
  - BFS places it directly after the loop, in the definitions locale, with
    `BFS_impl_same: "BFS_dom state \<Longrightarrow> BFS_impl state = BFS state"`.
  - DFS places it in a later `context DFS` and proves
    `DFS_impl_to_DFS: "DFS_impl initial_state = DFS initial_state"` in
    `context DFS_thms`.
  - Both use `lemmas [code] = <loop>_impl.simps initial_state_def`.
- No `fun`, `primrec` or `function (sequential)` is used for algorithm loops.
  Structural recursion over a list of roots is written as a loop whose state
  contains the remaining list (§6.2).

### 3.3 Branch decomposition and the four standard lemmas

For every branch *i* of the loop body there is a definition of its condition
and of its update (recursive branch) or result (returning branch). These are
followed by exactly four lemmas, whose proofs are the same in DFS and BFS:

```
definition "DFS_call_1_conds dfs_state = (case stack dfs_state of ... )"
lemma DFS_call_1_conds[call_cond_elims]:
  "DFS_call_1_conds dfs_state \<Longrightarrow>
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl; hd (stack dfs_state) \<noteq> t; ...\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp: DFS_call_1_conds_def split: list.splits option.splits if_splits)
definition "DFS_upd1 dfs_state = (let ... in dfs_state \<lparr>stack := stack', seen := seen'\<rparr>)"
...
lemma DFS_cases:   (one premise "DFS_<branch>_conds dfs_state \<Longrightarrow> P" per branch) shows "P"
lemma DFS_simps:   assumes "DFS_dom dfs_state" shows "DFS_call_1_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS (DFS_upd1 dfs_state)" ...
lemma DFS_induct:  assumes "DFS_dom dfs_state" and "\<And>dfs_state. \<lbrakk>DFS_dom dfs_state; DFS_call_1_conds dfs_state \<Longrightarrow> P (DFS_upd1 dfs_state); ...\<rbrakk> \<Longrightarrow> P dfs_state" shows "P dfs_state"
lemma DFS_domintros: assumes "DFS_call_1_conds dfs_state \<Longrightarrow> DFS_dom (DFS_upd1 dfs_state)" ... shows "DFS_dom dfs_state"
```

After these four lemmas, `<loop>.psimps` and `<loop>.pinduct` are not used
in invariant or correctness proofs. DFS uses `psimps` only in `DFS_simps`, in
the twin lemma `DFS_impl_to_DFS`, and in the special-case lemmas of
`DFS_immediate_termination`. No invariant or correctness proof does a `cases`
on the loop condition by hand.

*HK:* `hk_loop_invar`, `hk_loop_final` and `hk_loop_impl_same` each do
`induction rule: hk_loop.pinduct`, then `cases "phase m = []"`, then unfold
`hk_loop.psimps`.

### 3.4 Other definitions

- Definitions are untyped equations: `definition "invar_1 dfs_state = vset_inv
  (seen dfs_state)"`. All 45 definitions in DFS/BFS take this form; HK has 24
  of 26 (`augment_all` and `augment_list` are typed). Types are given only to
  the loop function. BFS_Subprocedures types its sub-procedure definitions
  (`definition next_frontier::"'vset \<Rightarrow> 'vset \<Rightarrow> 'vset" where`), which
  is acceptable for definitions that implement a parameter.
- The conditions on the input are bundled in a single definition
  (`DFS_axioms`, `BFS_axiom`). It is unpacked once into `[simp]`/`[intro]`
  facts (`graph_inv`, `s_in_G`, `srcs_invar`). HK's `hk_input` already does
  this.

### 3.5 Layout inside an algorithm theory

1. **Named theorems at the top:** `named_theorems call_cond_elims
   call_cond_intros ret_holds_intros invar_props_intros invar_props_elims
   invar_holds_intros state_rel_intros state_rel_holds_intros`, plus
   `termination_intros` before the termination subsection. DFS and BFS
   declare the same nine. *(HK: none.)*
2. **The definitions locale.**
   - Data-structure parents with qualifiers and `where`-instantiations:
     `Graph: Pair_Graph_Specs where lookup = lookup + set_ops: Set2 vset_empty
     vset_delete _ t_set vset_inv insert for lookup :: …`.
   - `fixes` for the inputs (DFS: `G s t`; BFS: `srcs G`) and for the
     sub-procedures (BFS: `expand_tree next_frontier`).
   - `assumes` for the sub-procedures' contracts (BFS; §3.6). DFS has no
     sub-procedures and hence no assumptions.
   - It holds the input-condition definition (`DFS_axioms`), the loop, its
     twin, the branch definitions, the invariants, the measures and
     `initial_state`.
3. **The proofs:** `locale <name>_thms = <name> + assumes <name>_axioms:
   <name>_axioms` (DFS), or `context includes … assumes <name>_axiom begin`
   inside the definitions locale (BFS). Special cases get their own small
   proofs locale (`DFS_immediate_termination`).
4. **Automation:** inside the proofs, `context includes set_ops.automation2
   and Graph.adjmap.automation and Graph.vset.set.automation begin`, so that
   `auto` sees the data-structure facts and proofs need not list them.
   *(HK: one `includes`, in `Hopcroft_Karp.thy`; none in the top loop, search
   or phase theories, where `Graph.vset.set.invar_empty` and similar facts are
   passed by hand.)*
5. **Subsections:** DFS has *The program state*, *Setup for automation*,
   *locale for fixing data structures and their implementations*, *Using the
   function package to model while-loops*, *Termination*; BFS has
   *Termination* and one topical subsection. The library uses `subsection`
   under one `section`; HK uses 13 `section`s and 1 `subsection`.

### 3.6 Layering: algorithms, sub-procedures, theories and imports

DFS has no sub-procedure. BFS has two, `expand_tree` and `next_frontier`, and
its three theories are the ground truth for layering:

| Theory | Imports | Contains |
|---|---|---|
| `DFS.thy` | `Directed_Set_Graphs.Pair_Graph_Specs`, `Data_Structures.Set2_Addons` | locales `DFS`, `DFS_thms`, `DFS_immediate_termination` |
| `DFS_Example.thy` | `DFS`, `Directed_Set_Graphs.Pair_Graph_RBT` | one `global_interpretation dfs: DFS where … for F t s defines …`, example data, `value` |
| `BFS_2.thy` | `Directed_Set_Graphs.Pair_Graph_Specs`, `HOL-Eisbach.Eisbach_Tools`, `Directed_Set_Graphs.Dist`, `Data_Structures.Set2_Addons`, `Directed_Set_Graphs.More_Lists` | locale `BFS`: sub-procedures as parameters, their contracts as assumptions |
| `BFS_Subprocedures.thy` | `BFS_2`, `HOL-Data_Structures.RBT_Map`, `Data_Structures.Set_Addons` | locales `Pair_Graph_Sepcs_Set2` and `BFS_subprocedures`, which implement the sub-procedures and prove the contract |
| `BFS_Example.thy` | `BFS_Subprocedures`, `HOL-Data_Structures.RBT_Map`, `Directed_Set_Graphs.Pair_Graph_RBT` | `global_interpretation bfs_subprocedures: …`, then `global_interpretation bfs: BFS where expand_tree = "expand_tree G" …`, example data, `value` |

All five theories are in the same session (`Graph_Algorithms_Dev`).

Rules:

1. **An algorithm theory imports specifications and mathematics only.**
   `DFS.thy` and `BFS_2.thy` import specification theories (`Pair_Graph_Specs`,
   `Set2_Addons`) and mathematics (`Dist`, `More_Lists`), never a concrete
   data structure. `Pair_Graph_RBT` and `RBT_Map` are imported by the example
   theory. (`BFS_Subprocedures` imports `RBT_Map`, but its locales are stated
   over the abstract operations.)
2. **A sub-procedure is a parameter with a contract.** The calling algorithm's
   definitions locale fixes it (`expand_tree`, `next_frontier`). It states the
   sub-procedure's contract as `assumes` of that same locale, over the
   abstraction (`Graph.digraph_abs`, `t_set`), with the representation
   invariants it needs as premises of each clause:
   ```
   assumes
      next_frontier[simp]:
       "\<lbrakk>vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>  vset_inv (next_frontier frontier vis)"
       "\<lbrakk>vset_inv frontier; vset_inv vis; Graph.graph_inv G\<rbrakk> \<Longrightarrow>
          t_set (next_frontier frontier vis) =
            (\<Union> {Pair_Graph.neighbourhood (Graph.digraph_abs G) u | u . u \<in> t_set frontier}) - t_set vis"
   ```
   The contract is therefore not a premise of the proofs locale (the Hungarian
   method puts it there; that contradicts BFS).
3. **Dependencies point from the implementation to the caller.** `BFS_2.thy`
   does not import the sub-procedures' theory. `BFS_Subprocedures.thy`
   imports `BFS_2`.
4. **The implementation is its own locale.** `BFS_subprocedures` has the
   same data-structure parents (through the bundle `Pair_Graph_Sepcs_Set2`),
   its own parameters and assumptions (`fold_vset`, `fold_adjmap`), and its
   own definitions (`next_frontier`, `expand_tree`). It proves lemmas whose
   names and statements are exactly the contract clauses.
5. **Composition happens only in the example theory**, by global
   interpretations in order:
   - First the implementation:
     `global_interpretation bfs_subprocedures: BFS_subprocedures where … for G
     defines next_frontier = bfs_subprocedures.next_frontier and expand_tree =
     bfs_subprocedures.expand_tree …`
   - Then the algorithm, with the defined constants in place of the
     parameters:
     `global_interpretation bfs: BFS where … and expand_tree = "expand_tree G"
     and next_frontier = "next_frontier G" and G = G and srcs = srcs for G
     srcs defines bfs_initial_state = "bfs.initial_state" and bfs_impl =
     bfs.BFS_impl`
   - The contract is discharged by
     `apply unfold_locales by (auto simp add: bfs_subprocedures.expand_tree
     bfs_subprocedures.next_frontier)`.
   - The interpreted locale is the *definitions* locale, unconditionally, with
     the inputs as `for` variables. Because each contract clause carries its
     own premises, the interpretation holds for all inputs, and the defined
     constants are premise-free code equations. No wrapper constants are
     needed.
6. **No `sublocale`, no `interpretation`, no type-class `instantiation`** in
   the five theories.
   - Library-wide there are 14 `sublocale`s, none between an algorithm and a
     sub-procedure. They are used for imperative refinements
     (`Pair_Graph_Imperative`, `DFS_Imperative`, `Imperative_DS`), adaptors
     between graph representations (`Pair_Graph_Library_Adaptor`,
     `Pair_Graph_Berge_Adaptor`), and probability spaces and problem settings
     in the linear-programming and RANKING analyses.
   - Library-wide there are 18 type-class `instantiation`s, all in executable
     or imperative theories. The graph-algorithm ones only give `linorder` to
     the types of RBT keys (vertex and edge wrapper types, and pairs in
     `Bellman_Ford_Example`). If an example needs one, it goes in the example
     theory.
7. **Correctness of the concrete instance is not part of DFS/BFS.** The
   examples stop at executability. When a concrete correctness statement is
   wanted, the form used elsewhere does not contradict DFS/BFS
   (`Hungarian_Method_Instantiation`, `Dinic_Instantiation`). Put it in the
   example theory, after the global interpretations:
   - a `context` or locale whose assumptions are the input conditions;
   - inside it, `interpretation <name>_proofs: <name>_thms …` of the proofs
     locale;
   - then `lemmas … = <name>_proofs.<lemma>[folded …]`, with no new proof.
8. **Interpretation names** are the lower-case algorithm name (`dfs`, `bfs`,
   `bfs_subprocedures`). Defined constants are `<name>_impl`,
   `<name>_initial_state` and the graph operations.
9. **Data structures go through ADTs.** Anything that is, or could be,
   implemented by a data structure is used through an ADT: a locale that
   fixes the operations, a representation invariant and an abstraction
   function, and assumes each operation's specification over the
   abstraction, with the invariant as a premise. Use an existing ADT when one
   fits: `Set`, `Set2` and `Map` from HOL-Data_Structures, `Pair_Graph_Specs`,
   `Set_Choose`. A new ADT follows the style of the existing ones:
   - its name ends in `_Specs` (§2.2, rule 3);
   - the operations, the invariant and the abstraction are locale parameters;
   - its axioms have the form of those of `Set` and `Map` in `Set_Specs` and
     `Map_Specs`;
   - it has abstraction lemmas and an `automation` bundle, as in `Set_Addons`;
   - it enters the algorithm locales as a qualified parent (§2.2, rule 3);
   - it is instantiated only in the `_Example` theory (rule 5).

Where HK and the Micali–Vazirani theories stand against these rules:

- `HK_Top_Loop.thy` fixes `phase` and `augment` as parameters, which is
  rule 2. Their contracts, however, sit in the second locale (`hk_loop_spec`)
  rather than in the definitions locale.
- `HK_Phase.thy` fixes no sub-procedure. It calls the RBT instances
  `alt_bfs_impl` and `hk_idfs` directly, and itself contains
  `global_interpretation hkbfs: Alt_BFS.BFS`, `global_interpretation mate:
  Matching_Augmentation_Specs`, `interpretation mate_thms`, the RBT
  interpretation `RO` of the read-only spec (removed by the split, R0-0), and
  `interpretation W: IDFS_witness`. Under rules 1, 2 and 5:
  - the phase's definitions locale fixes the alternating BFS and the
    disjoint-paths search as parameters, with their contracts as assumptions;
  - the alternating BFS and the incremental DFS prove those contracts in their
    own theories;
  - all global interpretations move to `Hopcroft_Karp_Example.thy`.
- Each contract clause must carry the input conditions it needs as premises,
  as BFS's clauses carry `Graph.graph_inv G`. That is what lets the example's
  global interpretation hold for all inputs. Where an input condition
  involves data that the algorithm does not compute (the bipartition `X`,
  `Y`), it has to be a premise of the clause. The restyle plan must decide its
  form.
- `HK_Example.thy` already interprets the definitions locale with `for Gin
  vs … defines …` (rule 5), and the proofs locale inside a `context … assumes
  inp` (rule 7). Only the re-export by `[folded …]` is missing.
- `Micali_Vazirani/IDFS.thy` connects the witness locale to the abstract
  double search by `sublocale DDFS_layered ⊆ DDFS`. That is not the DFS/BFS
  form (rule 6). It is recorded here, and no change is proposed for the
  Micali–Vazirani session.

---

## 4. Invariants, termination and final correctness

Each invariant is a separate definition with a fixed family of lemmas. In DFS
all five invariants have the complete family: elimination, introduction, one
lemma per branch (4 branches), and the loop lemma. That is 7 lemmas each, 35 in
all. BFS has 13 invariants, all with per-branch lemmas; its four `invar_3_*`
invariants have no separate loop lemma.

```
definition "invar_seen_stack dfs_state \<longleftrightarrow>
    distinct (stack dfs_state) \<and> set (stack dfs_state) \<subseteq> t_set (seen dfs_state) \<and> ..."

lemma invar_seen_stack_props[invar_props_elims]:
  "invar_seen_stack dfs_state \<Longrightarrow>
     (\<lbrakk>distinct (stack dfs_state); set (stack dfs_state) \<subseteq> t_set (seen dfs_state); ...\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_seen_stack_def)

lemma invar_seen_stack_intro[invar_props_intros]:
  "\<lbrakk>distinct (stack dfs_state); ...\<rbrakk> \<Longrightarrow> invar_seen_stack dfs_state"
  by (auto simp: invar_seen_stack_def)

lemma invar_seen_stack_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk>
     \<Longrightarrow> invar_seen_stack (DFS_upd1 dfs_state)"
  by (force simp: Let_def DFS_upd1_def elim!: call_cond_elims invar_props_elims intro!: invar_props_intros)

(* ... one lemma for each further branch ... *)

lemma invar_seen_stack_holds[invar_holds_intros]:
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_seen_stack dfs_state"
   shows "invar_seen_stack (DFS dfs_state)"
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed
```

Rules:

- **One invariant, one definition.** Conjunctions are split by topic:
  representation invariants (`invar_1`: `vset_inv`, `graph_inv`, finiteness)
  apart from mathematical ones (`invar_visited_through_seen`).
- **Elimination and introduction forms have flat premises** (no nested
  `\<And>thesis`), so that `elim!: invar_props_elims` stays well behaved.
- **One preservation lemma per branch**, stated as
  `\<lbrakk><branch>_conds s; <invariants it needs> s; invar_x s\<rbrakk> \<Longrightarrow> invar_x (<branch update> s)`,
  even when the proof is trivial (returning branches usually are).
- **The loop lemma is always the same three-line induction** shown above, so
  it never needs thought. Its premises are the union of the branch lemmas'
  premises. On its `apply`, see §5.6.
- **Termination** and **final correctness** use the same machinery
  (§4.1, §4.2).

*HK:* there is no `invar_*` definition. The matching invariant is a locale
parameter. Preservation is proved once for the whole loop, inside each
correctness lemma.

### 4.1 Termination

Termination uses the same machinery as the invariants: one lemma per
recursive branch, and one loop lemma whose proof is the same in DFS and BFS.

```
definition "call_1_measure dfs_state = card (dVs (Graph.digraph_abs G) - t_set (seen dfs_state))"
definition "call_2_measure dfs_state = card (set (stack dfs_state))"
definition "DFS_term_rel' = call_1_measure <*mlex*> call_2_measure <*mlex*> {}"

lemma call_1_terminates[termination_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     (DFS_upd1 dfs_state, dfs_state) \<in> call_1_measure <*mlex*> r"
lemma call_2_measure_1[termination_intros]:
  "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow>
    call_1_measure dfs_state = call_1_measure (DFS_upd2 dfs_state)"
lemma call_2_terminates[termination_intros]:
  "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state\<rbrakk> \<Longrightarrow>
     (DFS_upd2 dfs_state, dfs_state) \<in> call_2_measure <*mlex*> r"
lemma wf_term_rel: "wf DFS_term_rel'"
  by(auto simp: wf_mlex DFS_term_rel'_def)
lemma in_DFS_term_rel'[termination_intros]:
  (one clause "\<lbrakk>DFS_call_<i>_conds dfs_state; <invariants>\<rbrakk> \<Longrightarrow> (DFS_upd<i> dfs_state, dfs_state) \<in> DFS_term_rel'" per recursive branch)
  by (simp add: DFS_term_rel'_def termination_intros)+

lemma DFS_terminates[termination_intros]:
  assumes "invar_1 dfs_state" "invar_seen_stack dfs_state"
  shows "DFS_dom dfs_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_domintros) (auto intro!: invar_holds_intros less in_DFS_term_rel')
qed
```

BFS has one recursive branch. Its relation is `BFS_term_rel' =
call_1_measure_1 <*mlex*> call_1_measure_2 <*mlex*> {}`, with
`in_BFS_term_rel'` and `BFS_terminates` of the same shape.

Rules:

- **Measures are definitions** (`call_<i>_measure`, or `call_<i>_measure_<j>`
  for the components of a lexicographic measure). They are combined into
  `<loop>_term_rel'` with `<*mlex*>`. One component suffices for one
  recursive branch with one decreasing quantity: `<loop>_term_rel' =
  call_1_measure <*mlex*> {}`.
- **One decrease lemma per recursive branch**, `call_<i>_terminates`, as its
  own lemma. Its premises are the branch condition and invariants only. A
  branch that decreases a later component also needs a lemma saying that it
  leaves the earlier components unchanged (`call_2_measure_1`).
- **The shared helpers are copied unchanged**: `in_prod_relI`, `less_rel` and
  `wf_less_rel` are identical in DFS and BFS. `wf_term_rel` is the same
  one-line proof in each.
- **`<loop>_terminates` has invariants as its only premises.** It has no
  branch condition and no domain premise, concludes `<loop>_dom s`, and is
  proved by `wf_induct_rule` in the three lines above.
- **The domain of the initial state is part of `initial_state_props`.** That
  lemma lists every invariant of the initial state and also
  `<loop>_dom initial_state` (DFS item 6; BFS `BFS_dom initial_state`), and is
  tagged `[invar_holds_intros, termination_intros]`. After it, no lemma about
  the initial state has a domain premise.
- **Not used:** the Hungarian method's `less_induct` on a natural number, with
  the decrease as a second conclusion of the one-step lemma and an export
  `[OF _ refl]`. It contradicts the DFS/BFS form; version 1 of this guide
  allowed it, and that is withdrawn.

*HK:* `hk_loop_dom_aux` (28 lines) uses `less_induct` and does the
cardinality arithmetic inside the termination proof (`card ?m' = card m +
length (phase m)`, then `presburger`). In DFS/BFS form it becomes:
- `call_1_measure state = card G - card (matching_abstract (current_matching
  state))` and `Hopcroft_Karp_Loop_term_rel' = call_1_measure <*mlex*> {}`;
- `call_1_terminates`, with the arithmetic proved there;
- `Hopcroft_Karp_Loop_terminates` by `wf_induct_rule`.

### 4.2 Final correctness

Correctness is proved in three layers and then carried over to the
executable loop, each time by a short proof.

1. **At each returning branch:** `<loop>_correct_ret_<i>` (DFS), or
   `<loop>_correct_<k>_ret_<i>` with one lemma per property *k* (BFS). The
   invariants and the return condition give the property of the state. This
   is where the mathematical argument goes. Statements use the
   `\<lbrakk>…\<rbrakk> \<Longrightarrow> …` form:
   ```
   lemma DFS_correct_ret_1:
     "\<lbrakk>invar_visited_through_seen dfs_state; DFS_ret_1_conds dfs_state; u \<in> t_set (seen dfs_state)\<rbrakk>
            \<Longrightarrow> \<nexists>p. distinct p \<and> vwalk_bet (Graph.digraph_abs G) u p t"
     by (auto elim!: call_cond_elims invar_props_elims)
   ```
2. **The final state lies in a returning branch:**
   - `ret<i>_holds[ret_holds_intros]`, e.g. `assumes "DFS_dom s" "return (DFS
     s) = NotReachable" shows "DFS_ret_1_conds (DFS s)"`. It is proved by the
     three-line induction with `DFS_cases`, together with
     `DFS_ret_<i>[ret_holds_intros]`, which says that returning preserves the
     condition.
   - With several returning branches, the result field selects the branch
     (`return (DFS initial_state) = NotReachable`).
   - With one returning branch (BFS) there is no result field, and the lemma
     concludes `BFS_ret_1_conds (BFS s)`.
   - When the property relates the final state to the initial one (DFS:
     `s \<in> t_set (seen (DFS initial_state))`), a relation `state_rel_<i>` with
     its own family (`_holds_<branch>`, `_holds`, `_trans`, bundle
     `state_rel_holds_intros`) carries it through the loop.
3. **About the initial state:** `<loop>_correct_<k>`, one `lemma` per
   property. Each is stated for `<loop> initial_state`, with no domain or
   invariant premise and only the hypothesis on the outcome. It is proved by
   two lines:
   ```
   lemma BFS_correct_2:
     "\<lbrakk>t \<in> t_set (visited (BFS initial_state)) - t_set srcs\<rbrakk>
            \<Longrightarrow> distance_set (Graph.digraph_abs G) (t_set srcs) t =
            distance_set (Graph.digraph_abs (parents (BFS initial_state))) (t_set srcs) t"
     apply(intro BFS_correct_2_ret_1[where bfs_state = "BFS initial_state"])
     by(auto intro: invar_holds_intros ret_holds_intros)
   ```
   Strengthenings are separate lemmas (`DFS_correct_1_strong`). DFS and BFS
   use `lemma` throughout; `theorem` does not occur.
4. **The executable loop and the run:** `DFS_impl_to_DFS: "DFS_impl
   initial_state = DFS initial_state"` (from the twin lemma and the domain of
   the initial state), together with `definition "DFS_run = DFS
   initial_state"` and `definition "DFS_run_impl = DFS_impl initial_state"`.
   An algorithm whose answer is one field of the final state reads it off
   that field in its final lemmas.

   The Hungarian method uses a wrapper definition with an `option` result and
   a `theorem` with one conclusion per outcome. That is not the DFS/BFS form
   and is not used.
5. **The concrete instance**, when wanted: §3.6 rule 7 (in the example
   theory, `interpretation` of the proofs locale under the input conditions,
   then `[folded …]` re-exports).

*HK:*
- `hk_loop_correct` (32 lines) is stated for an arbitrary matching `m` with
  the premise `matching_invar m`, and contains the Berge argument.
- `hk_loop_final` is the link to the returning branch.
- `hopcroft_karp_correct` in `HK_Example.thy` proves its conclusions again
  from `hk.hk_loop_impl_correct`, through labelled `have`s.

The DFS/BFS form is:

- `Hopcroft_Karp_Loop_correct_ret_1`:
  `\<lbrakk>invar_matching state; Hopcroft_Karp_Loop_ret_1_conds state\<rbrakk> \<Longrightarrow>
  max_card_matching G (matching_abstract (current_matching state))`. The
  Berge argument goes here; a structured proof in the form of §5.2 is
  appropriate.
- `ret1_holds`: `Hopcroft_Karp_Loop_dom state \<Longrightarrow>
  Hopcroft_Karp_Loop_ret_1_conds (Hopcroft_Karp_Loop state)`. There is one
  returning branch and no result field.
- `initial_state_props`: `invar_matching initial_state` and
  `Hopcroft_Karp_Loop_dom initial_state`.
- `Hopcroft_Karp_Loop_correct_1`:
  `max_card_matching G (matching_abstract (current_matching
  (Hopcroft_Karp_Loop initial_state)))`, and `Hopcroft_Karp_Loop_correct_2`:
  `matching_invar (current_matching (Hopcroft_Karp_Loop initial_state))`.
  Each is proved in two lines.
- `Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop`, plus
  `Hopcroft_Karp_Loop_run` and `Hopcroft_Karp_Loop_run_impl`.
- In `Hopcroft_Karp_Example.thy`: the `[folded …]` re-export under the input
  conditions, with no new proof.
- The later bound on the number of phases (HK-M5) is another final lemma,
  about `phases (Hopcroft_Karp_Loop initial_state)`. It will need its own
  invariant family relating the phase count to the length of the shortest
  augmenting path.

---

## 5. Proof style

### 5.1 Default: one automatic call configured by the bundles

Three quarters of DFS lemmas and two thirds of BFS lemmas are a single `by`.
The typical call is `auto`, `force` or `fastforce`, configured by the
named-theorem bundles, the branch definitions and `Let_def`:

```
  by (auto elim!: call_cond_elims invar_props_elims intro!: invar_props_intros
           simp: DFS_upd1_def Let_def)
```

The DFS/BFS method mix is 51–61% `auto`, 9–12% `force`/`fastforce` and 2–4%
`simp`. `elim!:` and `intro!:` each appear in 0.4–0.5 calls per lemma. HK's
mix is 11% `auto`, 29% `simp`, 24% `rule`, and HK never uses `elim!:` or
`intro!:`.

The proof's job is to say which definitions to open and which bundles to use.
It does not list the individual facts that `auto` can find for itself.

### 5.2 When a structured proof is needed

About a fifth (DFS) to a quarter (BFS) of the lemmas have a structured proof,
with a median of 8 lines in DFS and 17 in BFS. They share the following shape:

- They open with a method that does the routine part:
  `proof(rule invar_props_intros, elim invar_visited_through_seen_props
  call_cond_elims exE, goal_cases)`, or `proof(induction rule: …)`, or
  `proof(cases …)`.
- The cases are named by `case (1 v1 p v2 stack_tl)` or `case IH: (1 …)`.
- They argue in a forward chain: `hence`, `thus`, `moreover … ultimately`,
  `then obtain`, `show ?thesis`. Previous facts are quoted as cartouches
  (`using \<open>u \<in> set p \<inter> set (stack dfs_state)\<close>`; 1.64 per lemma in BFS), not
  by labels.
- Each step is a mathematical step of the argument. Book-keeping (that a list
  is non-empty, that a set inclusion follows from an invariant) is left to the
  closing `auto`/`force` of the step that needs it.
- Non-obvious case distinctions are explained in `text \<open>…\<close>` blocks
  inside the proof (DFS `invar_visited_through_seen_holds_2`: Case 1, Case 2,
  Case a, Case b).

### 5.3 What to avoid (each seen in HK)

| Pattern | HK example | DFS/BFS form |
|---|---|---|
| A labelled `have` for every small fact | `have pne: "p \<noteq> []" using plen by auto`, `have hq: "hd q \<in> set q" by (rule hd_in_set[OF qne])` (25 labelled steps in `aug_path_disjoint_preserved`) | Leave it to the closing `auto`, or one `have` per mathematical step |
| Forward application by `rule` | `by (rule augment_abs[OF Cons.prems(1) p])` (26% of closing calls) | `by (auto intro!: augment_abs)` or `using … by auto` |
| Named assumptions | `assumes M: "matching M" and p: … and q: … and disj: …` | Unnamed, or a plain `"\<lbrakk>…\<rbrakk> \<Longrightarrow> …"` statement; `assms(i)` |
| Unfolding the loop by hand | `cases "phase m = []"` + `hk_loop.psimps[OF 1(1)]` | `<loop>_cases` + `<loop>_simps` in the 3-line induction |
| Data-structure facts by hand | `simp add: … Graph.vset.set.invar_empty Graph.vset.set.set_empty` | `context includes … automation` |
| `using` and `by` at the end of the stated line | `have finG: "finite G" by (rule finite_Vs_then_finite) (use G in simp)` | `using`/`by` on their own lines, indented (§5.5) |

### 5.4 Statements

- About 78% of DFS/BFS lemmas are stated as one string:
  `"\<lbrakk>A; B\<rbrakk> \<Longrightarrow> C"` (0.69–0.79 `\<lbrakk>` per statement; HK 0.00).
- `assumes … shows …` (about 22%) is used for the loop lemmas
  (`assumes "DFS_dom dfs_state" …`), for lemmas with several conclusions, and
  for some final lemmas.
- Final lemmas state the result for `<loop> initial_state`, not for an
  arbitrary state with a domain premise (§4.2).

### 5.5 Layout

- `using` and `by` start their own lines, indented two spaces beyond the
  statement or the `have`. That is 100% in DFS, 95–99% in BFS; HK 17% / 35%.
  ```
    have "set p \<inter> set (stack dfs_state) \<noteq> {}"
      by (auto simp: DFS_upd2_def)
  ```
- `proof-`, `proof(…)`, `apply(…)` are written with no space. DFS/BFS have 19
  `proof-` and 58 `proof(`, and none with a space; HK has 41 `proof -` and 52
  `proof (`. `by (` and `by(` both occur; `by (` is the majority.
- Long method calls are split with one modifier per line (DFS
  `call_1_terminates`):
  ```
    by(fastforce elim!: invar_props_elims call_cond_elims
            simp add: DFS_upd1_def call_1_measure_def Let_def
            intro!: mlex_less psubset_card_mono
            dest!: Graph.vset.choose')
  ```
- Line length: in DFS/BFS, 95% of lines are at most 117–119 characters.

### 5.6 Project rules, and one conflict with the ground truth

The project rules are unchanged: no `sorry`, `smt`, `metis` or `meson`; no
`{ … }` blocks; ASCII-only theory files. BFS itself has `metis` (3.8% of its
method calls) and one `smt` call. Those are exactly what the project rules forbid;
the rest of the DFS/BFS style is reached with `auto`, `force`, `fastforce` and
`blast` and the bundles.

**`apply` in the boilerplate (user decision, 2026-10-11: use `apply`, as long
as it is used as in DFS/BFS).** DFS and BFS use `apply` in exactly these
fixed templates, which are therefore written as in DFS/BFS:
- the loop lemma: `apply(rule DFS_cases[where dfs_state = dfs_state])`, then
  `by (auto …)`;
- the final lemmas: `apply(intro BFS_correct_2_ret_1[where bfs_state = "BFS
  initial_state"])`, then `by(auto …)`.

- the discharge of locale assumptions in the example theory's global
  interpretations: `apply unfold_locales`, then `by (auto …)` (BFS_Example);
- the boilerplate lemmas `<loop>_induct` and the twin lemmas, where DFS/BFS
  write `apply(rule <loop>.pinduct …)` etc.

That is 2.5% of DFS lemmas and 9.7% of BFS lemmas. The coder's general rule
"No `apply` scripts" (`.claude/agents/coder.md:176`) yields for these
templates; it still holds everywhere else. An `apply` sequence that does not
occur in DFS/BFS is not allowed.

Elsewhere, where automation fails, use a short structured proof of the form in
§5.2, not an `apply` script.

---

## 6. Application to Hopcroft–Karp

### 6.1 Top loop (`Hopcroft_Karp_Top_Loop.thy`)

Shape, following DFS/BFS (names per §2.2 rule 4; contract per §3.6 rule 2):

```
record 'matching Hopcroft_Karp_Loop_state = current_matching :: 'matching  phases :: nat

locale Hopcroft_Karp_Loop =
  fixes G :: "'v set set"
    and empty_matching :: 'matching
    and augment :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
    and matching_invar :: "'matching \<Rightarrow> bool"
    and matching_abstract :: "'matching \<Rightarrow> 'v set set"
    and phase :: "'matching \<Rightarrow> 'v list list"
  assumes matching_invar_empty: "matching_invar empty_matching"
                                "matching_abstract empty_matching = {}"
      and augment: (the two clauses for augment, each with its premises)
      and phase: (the three clauses for phase, each with the input conditions it needs as premises)
begin

definition "Hopcroft_Karp_Loop_axiom = graph_invar G"   (* plus any further input condition *)

function (domintros) Hopcroft_Karp_Loop::
  "'matching Hopcroft_Karp_Loop_state \<Rightarrow> 'matching Hopcroft_Karp_Loop_state" where
  "Hopcroft_Karp_Loop state =
     (if phase (current_matching state) \<noteq> [] then
        let ps = phase (current_matching state) in
        Hopcroft_Karp_Loop (state \<lparr>current_matching := foldl augment (current_matching state) ps,
                                   phases := Suc (phases state)\<rparr>)
      else state)"
  by pat_completeness auto

partial_function (tailrec) Hopcroft_Karp_Loop_impl:: ...   (same body)
lemma Hopcroft_Karp_Loop_impl_same: ...                       (as BFS_impl_same)

definition "initial_state = \<lparr>current_matching = empty_matching, phases = 0\<rparr>"
definition "Hopcroft_Karp_Loop_call_1_conds state = (phase (current_matching state) \<noteq> [])"
definition "Hopcroft_Karp_Loop_upd1 state = (let ps = phase (current_matching state) in ...)"
definition "Hopcroft_Karp_Loop_ret_1_conds state = (phase (current_matching state) = [])"
abbreviation "Hopcroft_Karp_Loop_ret1 state \<equiv> state"
definition "invar_matching state = matching_invar (current_matching state)"
definition "call_1_measure state = card G - card (matching_abstract (current_matching state))"
definition "Hopcroft_Karp_Loop_term_rel' = call_1_measure <*mlex*> {}"
lemmas [code] = Hopcroft_Karp_Loop_impl.simps initial_state_def
(* conds lemmas, _cases, _simps, _induct, _domintros: §3.3 *)
end

locale Hopcroft_Karp_Loop_thms = Hopcroft_Karp_Loop +
  assumes Hopcroft_Karp_Loop_axiom: Hopcroft_Karp_Loop_axiom
begin
(* invar_matching_props / _intro / _holds_upd1 / _holds_ret_1 / _holds: §4 *)
(* call_1_terminates, in_Hopcroft_Karp_Loop_term_rel', Hopcroft_Karp_Loop_terminates: §4.1 *)
(* Hopcroft_Karp_Loop_correct_ret_1, ret1_holds, initial_state_props,
   Hopcroft_Karp_Loop_correct_<k>, Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop: §4.2 *)
end
```

The `phases` field is optional for correctness. It is the natural place for
the later bound on the number of phases (HK-M5).

The input bundle is named in the singular, `Hopcroft_Karp_Loop_axiom` (BFS:
`BFS_axiom`). Isabelle itself generates `<locale>_axioms` for a locale with
parents and assumptions, so the plural would clash. The restyle plan (user
decision RD5) moves the input conditions into a shared parent locale,
because the contract clauses of the definitions locale need them as
premises, and a locale assumption cannot refer to a definition made inside
the same locale.

The matching operations are a data structure, so by §3.6 rule 9 they come
through an ADT, not as plain parameters as in the locale above: as a
qualified data-structure parent, the mate-function specification
`Matching_Augmentation_Specs` (Basic_Matching), whose operations are then
`augment_impl` and the invariant and abstraction it defines.

### 6.2 Phase (`Hopcroft_Karp_Phase.thy`)

Replace the six-argument `fun disjoint_search_gen` by a loop over a record. A
possible state:

```
record ('v, 'vset) Disjoint_Paths_Search_state =
  roots :: "'v list"  avoided :: 'vset  explored :: 'vset  paths :: "'v list list"
```

It has three branches:

- `call_1`: `roots ≠ []` and the search from `hd roots` finds a walk. Add it
  to `paths`, add its vertices to `avoided`, drop the root.
- `call_2`: `roots ≠ []` and the search finds no walk. Update `explored`, drop
  the root.
- `ret_1`: `roots = []`.

Layering (§3.6):

- The search step is a parameter of the search loop's definitions locale,
  with its contract as `assumes`.
- The incremental DFS proves the contract in its own theory, or in a
  `…_Subprocedures` theory that imports the search loop.
- The phase's definitions locale fixes the alternating BFS and the search as
  parameters, with their contracts as `assumes`.
- The executable composition (global interpretations of the alternating BFS,
  the incremental DFS, the search loop, the phase and the top loop) happens
  only in `Hopcroft_Karp_Example.thy`.

The invariants become families in the sense of §4:

| Invariant | Content |
|---|---|
| `invar_1` | `vset_inv` of `avoided` and `explored` (today `search_pre`) |
| `invar_paths_disjoint` | today `phase_disjoint` |
| `invar_paths_augmenting` | today `phase_sound` |
| `invar_explored_closed` | the closure fact behind `phase_complete` (today `none_closed_reach`) |

The current `context fixes m assumes …` block with nine one-letter
abbreviations becomes the definitions locale of the phase. Its inputs (edge
list, alternating BFS result, copies graph, levels) become parameters or
definitions with spelled-out names.

### 6.3 Renaming list (first pass)

| Now | DFS/BFS style |
|---|---|
| `pair_graph_specs_read_only` (interim theory) | `Pair_Graph_Specs_Read_Only`, in `Pair_Graph_Specs` (done, R0-0) |
| undirected read-only base locale | `Pair_Graph_U_Specs_Read_Only` (done, R0-0) |
| `RO.c` (interim interpretation) | `G.c` (done, R0-0; subsumption confirmed) |
| `hk_loop_defs` / `hk_loop_spec` | `Hopcroft_Karp_Loop` / `Hopcroft_Karp_Loop_thms` |
| `hk_loop`, `hk_loop_impl` | `Hopcroft_Karp_Loop`, `Hopcroft_Karp_Loop_impl` |
| `matching_abs` | `matching_abstract` |
| `hk_phase`, `hk_idfs`, `hk_srcs`, `hk_roots`, `hk_blk`, `hk_level`, `hk_stack0` | `Hopcroft_Karp_Phase`, … (no `hk_`), or parameters/definitions of the phase locale |
| `es`, `Mt`, `Ut`, `S`, `st`, `T`, `cl`, `CG`, `lv` | `edge_list`, `matching_graph`, `non_matching_graph`, `bfs_sources`, `bfs_state`, `bfs_dag`, `copies_edge_list`, `copies_graph`, `copy_level` |
| `hk_loop_invar`, `hk_loop_final`, `hk_loop_dom_aux` | `invar_matching_holds`, `ret1_holds`, `Hopcroft_Karp_Loop_terminates` (DFS form, §4.1) |
| `hk_loop_correct` (arbitrary `m`), `hk_loop_impl_correct` | `Hopcroft_Karp_Loop_correct_ret_1` + `Hopcroft_Karp_Loop_correct_<k>` about `initial_state`; `Hopcroft_Karp_Loop_impl_to_Hopcroft_Karp_Loop` |
| `hopcroft_karp_correct` (proved again in `HK_Example`) | `[folded …]` re-export in `Hopcroft_Karp_Example.thy` (§3.6 rule 7) |
| `M_sub`, `S_free`, `st_eq`, `cl_mem`, `CG_abs`, `DS_facts`, `inp_parts`, `G_char` | names stating the content, e.g. `matching_subset_graph`, `sources_are_free` |

### 6.4 What already conforms

- The read-only spec's proofs: 89% single `by`, median one line, with
  `[simp]`/`[intro]`/`[elim]` attributes on most lemmas (measured on the
  interim theory, whose content the split moves into `Pair_Graph_Specs`).
  Only its locale name deviates.
- Glue definitions (`match_list`, `free_list`, `UG_of`, `hk_input`) are
  untyped equations.
- `hk_input` bundles the input conditions the way `DFS_axioms` does.
- `HK_Example.thy` interprets the definitions locale globally with `for Gin
  vs … defines …`, as `DFS_Example`/`BFS_Example` do.
- The Micali–Vazirani theories `DDFS.thy` and `Alt_BFS.thy` follow §§3.1–4
  (state record, branch definitions, `invar_*` families, with 97 and 61 uses
  of `invar_holds_intros`). They are the nearest templates for the phase.
  Their layering is not checked here.

---

## 7. Checklist for a new or restyled theory

Re-run `style_stats.py` and `locale_struct.py`, and compare with the DFS/BFS
columns:

1. Every algorithm loop is `function (domintros)` over one state record, with
   a `partial_function (tailrec)` twin and `<loop>_impl_same` (or
   `<loop>_impl_to_<loop>`).
2. Every branch has `_conds` (with `[call_cond_elims]`) and `_upd<i>`/`_ret<i>`
   definitions, and the four lemmas `_cases`, `_simps`, `_induct`,
   `_domintros` exist. No `.psimps`/`.pinduct` outside them and the twin
   lemma.
3. Every invariant is an `invar_*` definition with `_props`, `_intro`, one
   `_holds_<branch>` per branch, and `_holds`, each with its bundle attribute.
4. The named theorems of §3.5 are declared, and the proofs use them.
5. At least 63% of the lemmas close with a single `by` (BFS: 63%, DFS: 77%).
   The median proof length is at most 2 lines.
6. At most 0.25 labelled facts and 0.6 `[OF …]` per lemma (BFS: 0.21 and
   0.61; DFS: 0.01 and 0.26), and no named assumptions.
7. `using`/`by` start their own lines; `proof-` and `proof(` have no space.
8. Locale and constant names follow §2.2–§2.3: the definitions locale has the
   algorithm's name and the proofs locale ends in `_thms`; no `_spec`/bare
   pairs, no one- or two-letter global abbreviations, no `hk_`-style
   prefixes, no clashes with existing constants.
9. The project rules of §5.6 hold: no `sorry`/`smt`/`metis`/`meson`, ASCII on
   disk; `apply` only as the user decides in §5.6.
10. Termination (§4.1): measures as definitions, `<loop>_term_rel'` with
    `<*mlex*>`, one `call_<i>_terminates` per recursive branch,
    `<loop>_terminates` by `wf_induct_rule` with invariant premises only, and
    `<loop>_dom initial_state` in `initial_state_props`.
11. Final correctness (§4.2) has three layers: returning branch, link from
    the final state to a returning branch, and premise-free `lemma`s about
    `<loop> initial_state`. The executable twin is related on the initial
    state; there is no wrapper `theorem`.
12. Layering (§3.6):
    - algorithm theories import no concrete data structure;
    - anything that is, or could be, implemented by a data structure is used
      through an ADT, existing or new, in the style of the existing ADTs
      (§3.6, rule 9);
    - sub-procedures are parameters whose contracts are `assumes` of the
      definitions locale;
    - implementations import the caller, not the other way round;
    - every `global_interpretation` is in the `_Example` theory, interpreting
      the definitions locale for all inputs;
    - no `sublocale` connects algorithms;
    - a concrete correctness statement, if any, is an `interpretation` of the
      proofs locale plus a `[folded …]` re-export in the `_Example` theory.
