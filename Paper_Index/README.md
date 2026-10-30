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

The index is split into one session per section of the paper, each in its own
subdirectory, with all of the sessions in the session group `paper_index`. Each
session has one theory, except two sessions that refer to theories which cannot be
imported together: the session of Section 2.6 has a second theory for Listing 111,
and the session of Table 1 has a second theory for Listings 61 and 63.

| Theory | Part of the paper | Listings |
|---|---|---|
| `Index_00_Introduction_Main_Theorems` | Introduction, Section 2 opening | 1–4 |
| `Index_21_Graph_Models_And_Reasoning` | Section 2.1, mathematical models and reasoning principles | 5–27 |
| `Index_22_Implementing_Graphs` | Section 2.2, implementing graphs | 28–47 |
| `Index_23_Modelling_Algorithms` | Section 2.3, modelling algorithms | 48–52 |
| `Index_Algorithms_Main_Theorems`, `Index_Algorithms_Main_Theorems_Spanning_Trees` | Main theorems of the verified algorithms (Table 1) | 53–82 |
| `Index_24_Proofs_About_Algorithms` | Section 2.4, proofs about algorithms | 83–100 |
| `Index_25_Imperative_Implementations` | Section 2.5, imperative implementations | 101–106 |
| `Index_26_Other_Methodological_Points`, `Index_26_Usage_Capacitated` | Section 2.6, other methodological points | 107–115 |
| `Index_C_AI_Assisted_Development` | Appendix C, the theories named in the style statistics | none |

## Building and checking

The commands that build the index are in `ARTEFACT_README.md` at the repository
root.

## Coverage

Of the 115 listings, 114 are checked by an antiquotation in this snapshot. Listing
44, the locale `Multi_Graph_Specs`, is documented but not checked, because it
exists only on the development branch `bfs_refinement`. A listing that shows
several theorems, e.g. Listing 53, checks each of them, and Listing 91 checks each
of the eight collections of theorems that it declares. Listing 28, `wf_digraph`,
is an entry of the Archive of Formal Proofs, and it is checked through the
`Graph_Theory` session. The interpretations, that is Listings 36, 37, 41, 42, 103,
104, and 107, have no antiquotation of their own, so each of these entries checks
the interpreted locale and records the name and the source location of the
interpretation.

The index also checks what the paper names outside the listings: the locale
`nomulti_digraph` and the abstractions `ugraph_abs` and `graph_assn` of Table 4,
in the entries of Listings 28, 34 and 38, and the theories named in Appendix C,
in the session of that appendix.

## Differences between the paper and this snapshot

Some listings cite theory files or names as they appear on development branches,
for example `Acyclic_Flow.thy` for the edge iterators and `Kruskal_Greedy.thy` for
the correctness of Kruskal's algorithm. Where the location or the name in this snapshot
differs, the entry points at the actual location in the snapshot and records the
difference in a `Note` line.

Listings 2 and 51 are taken from the session `Edmonds_Blossom_Algorithm`, which is
not part of this artefact. Their entries point at the corresponding theorem and
locale of the executable version in `Edmonds_Blossom_Executable`, which are stated
for the implementations of the graph and of the matching.

In the following listings, the entity of this snapshot is stated differently from
the listing, and the `Note` line of the entry says how: 1. Listings 33 and 34,
whose locales have the read-only graph operations as a parent, 2. Listing 35,
whose locale asks the entries of each range, not the whole list of edges, to be
distinct, 3. Listing 45, whose assumptions are those of two parent locales, 4.
Listing 57, whose last two conclusions are about a relation of parents, 5. Listing
73, which is stated for the implementation, 6. Listing 86, which has one more
conclusion, 7. Listings 60 and 93, in which the loop `BestInGreedy` is called
`BestInGreedy_base`, and 8. Listings 80 and 108, in which a field of the state is
called `solution` instead of `sol`.
