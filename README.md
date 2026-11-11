# Isabelle-Graph-Library

A formal mathematical library covering results in graph theory, with a focus on graph algorithms and results from combinatorial optimisation.
Results include:

 - A set-based simple representation of graphs (both directed and undirected). In this representation, we tried to port as many results from other graph libraries in Isabelle as possible, using representation adaptors, i.e. lemmas that connect different representations.

 - Simple graph algorithms, like Depth-First-Search, Breadth-First-Search, cycle detection, and Bellman-Ford. 

 - Berge's lemma, which is a fundamental result from the theory of matching.

 - Edmonds' blossom shrinking algorithm.

 - The RANKING algorithm for online bi-partite matching, by Karp, Vazirani, and Vazirani.

 - An algorithm for vertex-weighted online matching.

 - The AdWords algorithm for online auction allocation, by Mehta, Saberi, Vazirani, and Vazirani.
 
 - Background theory on independence systems/matroids and the Best-In-Greedy algorithms for matroids and greedoids.
 
 - The matroid intersection algorithm for unweighted matroids.

 - Kruskal's algorithm for finding minimum spanning trees, implemented as an instance of the Best-In-Greedy algorithm for Matroids.
 
 - Prim's algorithm for finding minimum spanning trees, implemented as an instance of the Best-In-Greedy algorithm for Greedoids.
 
 - An $O(n·m·(log n + log m))$ algorithm for bi-partite maximum cardinality matching based on the matroid intersection algorithm.
 
 - Fundamental theory for maximum flows and and related algorithms, including Dinic's Algorithm, which is one of the most efficient methods for max-flow.
 
 - Some fundamental theory for minimum cost flows and related algorithms, including Orlin's Algorithm, which is one of the most efficient methods for min-cost-flow.

For the more practically usable algorithms, we include an implementation. For others, we only focus on the mathematical analysis.

# Publications
 - M. Abdulaziz. 'Graph Algorithms'. In Functional Data Structures and Algorithms: A Proof Assistant Approach. Editor: Tobias Nipkow. ACM Books, 2025. [url](https://fdsa-book.net/functional_data_structures_algorithms.pdf#chapter.24)


 - M. Abdulaziz, T. Ammer, S. Meenakshisundaram, and A. Rimpapa. 'A Formal Analysis of Algorithms for Matroids and Greedoids', Accepted in The 16th International Conference on Interactive Theorem Proving (ITP), 2025. doi: [10.48550/arXiv.2505.19816](https://doi.org/10.48550/arXiv.2505.19816).

 - M. Abdulaziz, 'A Formal Correctness Proof of Edmonds’ Blossom Shrinking Algorithm', Dec. 30, 2024, arXiv: arXiv:2412.20878. doi: [10.48550/arXiv.2412.20878](https://doi.org/10.48550/arXiv.2412.20878).

 - M. Abdulaziz and T. Ammer, 'A Formal Analysis of Capacity Scaling Algorithms for Minimum Cost Flows', in The 15th International Conference on Interactive Theorem Proving (ITP), 2024. doi: [10.4230/LIPIcs.ITP.2024.3](https://doi.org/10.4230/LIPIcs.ITP.2024.3)

 - M. Abdulaziz and C. Madlener, 'A Formal Analysis of RANKING', in The 14th Conference on Interactive Theorem Proving (ITP), 2023. doi: [10.48550/arXiv.2302.13747](https://doi.org/10.48550/arXiv.2302.13747).

 - M. Abdulaziz, K. Mehlhorn, and T. Nipkow, 'Trustworthy graph algorithms (invited paper)', in the 44th International Symposium on Mathematical Foundations of Computer Science (MFCS), 2019. doi: [10.4230/LIPIcs.MFCS.2019.1](https://doi.org/10.4230/LIPIcs.MFCS.2019.1).

# How to use

 - Go to https://isabelle.in.tum.de/, pick and download the version of Isabelle2025-2 specific to your OS
 - Go to https://www.isa-afp.org/download/ and download the 2025-2 version of the AFP (we build the library with the AFP snapshot of 17 March 2026)
 - Add the AFP as a collection of components to your local Isabelle: 'isabelle components -u [path to afp]/afp/thys'
 - Same for this directory: 'isabelle components -u [path to this directory]'
 - All theories in this formalisation should be available now!

## Using the library in your own development

Once this directory is registered as a component, its sessions can be used like those of the AFP. For example, a development that builds on the theory of matchings lists `Basic_Matching` among the `sessions` in its `ROOT` file and imports `Basic_Matching.Matching` in its theories. To check one session and the sessions it depends on, run `isabelle build SESSION`, e.g. `isabelle build Graph_Algorithms_Dev`. To check the whole library, run `isabelle build -D .` in this directory.

## Generated code

The executable algorithms are refined to imperative programs, from which the build generates code. Each export theory below writes its code into the directory named in the last column, next to the theory. Unless stated otherwise, the code is generated in SML, Scala and Go, and the SML and Scala code is also compiled during the build.

| Algorithm | Session | Export theory | Directory |
|---|---|---|---|
| BFS, on graphs as arrays (CSR) and as red-black trees | `Graph_Algorithms_Dev` | `Set_Graphs/Graph_Algorithms/Refinements/BFS_Code_Export.thy` | `BFS_code_exports` |
| DFS, on graphs as arrays (CSR), lists and red-black trees | `Graph_Algorithms_Dev` | `Set_Graphs/Graph_Algorithms/Refinements/DFS_Code_Export.thy` | `DFS_code_exports` |
| Dijkstra's algorithm | `Graph_Algorithms_Dev` | `Set_Graphs/Graph_Algorithms/Refinements/Dijkstra_Code_Export.thy` | `Dijkstra_code_exports` |
| Kruskal's algorithm | `Spanning_Trees` | `Spanning_Trees/Refinements/Kruskal_Code_Export.thy` | `Kruskal_code_exports` |
| Push-relabel | `Push_Relabel` | `Push_Relabel/Refinements/Push_Relabel_Code_Export.thy` | `Push_Relabel_code_exports` |
| FIFO push-relabel of the AFP, for comparison | `Push_Relabel` | `Push_Relabel/Refinements/AFP_FIFO_Push_Relabel_Code_Export.thy` | `AFP_FIFO_Push_Relabel_code_exports` |
| Hungarian method | `Hungarian_Method` | `Hungarian_Method/Refinements/Hungarian_Code_Export.thy` | `Hungarian_code_exports` |
| Assignment solver (SML only) | `Hungarian_Method` | `Hungarian_Method/Refinements/Assignment_Solver_Code_Export.thy` | `Assignment_Solver_code_exports` |
| Bipartite matching and b-matching, unweighted and weighted, by matroid intersection | `Matroid_Intersection` | `Matroid_Intersection/Applications/Bipartite_Matching_Code_Export.thy` | `Bipartite_Matching_code_exports` |
| Network simplex, as a solver for DIMACS minimum-cost flow instances (SML only) | `Use_Network_Simplex` | `Mincost_Flow_Algorithms/Use_Network_Simplex/Refinements/DIMACS_Solver_Code_Export.thy` | `DIMACS_Solver_code_exports` |

For example, `isabelle build Spanning_Trees` writes the code of Kruskal's algorithm to `Spanning_Trees/Refinements/Kruskal_code_exports`.

## TACAS 2027 artefact

The artefact of the TACAS 2027 paper on this library adds an index from the listings of the paper to the library and the scripts of the experiments. It is archived at https://doi.org/10.5281/zenodo.23805452 and kept on the branch `tacas27` (tag `tacas27-artefact`).

## Acknowledgements

This development reuses code from the following work, used under
[Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/):

> Lukas Stevens and Rebecca Ghidini. "Simplified and Verified: A Second Look at
> a Proof-Producing Union-Find Algorithm". In: *Automated Deduction – CADE 30*,
> Lecture Notes in Artificial Intelligence, vol. 15943, eds. Clark Barrett and
> Uwe Waldmann, Springer, 2025.
> DOI: [10.1007/978-3-031-99984-0](https://doi.org/10.1007/978-3-031-99984-0)
> (preprint: https://arxiv.org/abs/2504.10246)
>
> Artifact: https://doi.org/10.5281/zenodo.15557955

Some files are copied verbatim and some are adapted from the above; see
`NOTICES.txt` and individual file headers for details.
