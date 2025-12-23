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

 - Go to https://isabelle.in.tum.de/, pick and download the version of Isabelle2025 which is right for your OS
 - Go to https://www.isa-afp.org/download/ and download the 2025 version of the AFP
 - Add the AFP as a collection of components to your local Isabelle: 'isabelle components -u [path to afp]/af\
p/thys'
 - Same for this directory: 'isabelle components -u [path to this directory]'
 - All theories in this formalisation should be available now!
 - You also need to add https://github.com/lammich/Separation_Logic_Imperative_HOL_Partial/tree/7f24270bd9a37f2a61a5727f4e5a501a460dc896 as submodule, which should replace the empty directory Separation_Logic_Imperative_HOL_Partial in Imperative.
