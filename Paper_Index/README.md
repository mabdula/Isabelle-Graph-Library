# Paper_Index: a machine-checked index of the paper's listings

This directory maps every listing in the appendix of the paper, that is Section D
"Formal Listings", Listings 1 to 115, to its formal counterpart in the library.
Each mapping is checked when the session is built: the listing is referenced with
an Isabelle antiquotation, one of `@{thm ...}`, `@{const ...}`, `@{type ...}` or
`@{locale ...}`, so that the build fails if the named theorem, definition, locale
or type has been renamed or removed. Every entry also records the file and the
line at which the entity occurs, through a `\<^file>` link that is itself checked
to exist.

## Layout

The index is split into one theory per section of the paper, each in its own
subdirectory and its own session, with all of the sessions in the session group
`paper_index`.

| Theory | Part of the paper | Listings |
|---|---|---|
| `Index_00_Introduction_Main_Theorems` | Introduction, Section 2 opening | 1–4 |
| `Index_21_Graph_Models_And_Reasoning` | Section 2.1, mathematical models and reasoning principles | 5–27 |
| `Index_22_Implementing_Graphs` | Section 2.2, implementing graphs | 28–47 |
| `Index_23_Modelling_Algorithms` | Section 2.3, modelling algorithms | 48–52 |
| `Index_Algorithms_Main_Theorems` | Main theorems of the verified algorithms (Table 1) | 53–82 |
| `Index_24_Proofs_About_Algorithms` | Section 2.4, proofs about algorithms | 83–100 |
| `Index_25_Imperative_Implementations` | Section 2.5, imperative implementations | 101–106 |
| `Index_26_Other_Methodological_Points` | Section 2.6, other methodological points | 107–115 |

## Building and checking

Each section is its own session, and all eight sessions share the group
`paper_index`. Run the commands from the repository root, so that the library
sessions are on the session path. To check one section without building the rest
of the library, build its session, for example:

```
isabelle build -d . -d Paper_Index Paper_Index_21_Graph_Models_And_Reasoning
```

To check all eight sections, which builds the whole library on which they depend,
build the group:

```
isabelle build -d . -d Paper_Index -g paper_index
```

A green build is the verification: if any listed theorem, definition or locale no
longer exists under the referenced name, the corresponding antiquotation makes the
build fail and names the stale entry. To include the index in the top-level build
of the artefact, add `Paper_Index` to the repository `ROOTS` file.

## Coverage

Of the 115 listings, 113 are checked by an antiquotation in this snapshot. Two
listings are documented but not checked by an antiquotation, because they are not
present in this snapshot: 1. Listing 44, the locale `Multi_Graph_Specs`, which
exists only on the development branch `bfs_refinement`, and 2. Listing 91,
"collections of theorems", which refers to the methodology's use of
`named_theorems` rather than to one named entity. Listing 28, `wf_digraph`, is an
entry of the Archive of Formal Proofs, and it is checked through the
`Graph_Theory` session. The interpretations, that is Listings 36, 37, 41, 42, 103,
104, and 107, have no antiquotation of their own, so each of these entries checks
the interpreted locale and records the name and the source location of the
interpretation.

## Differences between the paper and this snapshot

Some listings cite theory files or names as they appear on development branches,
for example `Acyclic_Flow.thy` for the edge iterators, `Blossom_Algo_Main_Loop.thy`
for the blossom main loop, and `Kruskal_Functional.thy` for the Kruskal
interpretation. Where the location or the name in this snapshot differs, the entry
points at the actual location in the snapshot and records the difference in a
`Note` line.
