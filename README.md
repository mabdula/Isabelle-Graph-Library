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
 
 - Background theory on independence systems/matroids and the Best-In-Greedy algorithm on independence systems/matroids.

 - Kruskal's algorithm for finding minimum spanning trees, implemented as an instance of the Best-In-Greedy algorithm.
 
 - Some fundamental theory for minimum cost flows and related algorithms, including Orlin's Algorithm, which is one of the most efficient methods for this class of problems.

For the more practically usable algorithms, we include an implementation. For others, we only focus on the mathematical analysis.

# Publications

 - M. Abdulaziz, T. Ammer, S. Meenakshisundaram, and A. Rimpapa. 'A Formal Analysis of Algorithms for Matroids and Greedoids'. Mar. 30, 2025, arXiv: arXiv:2412.20878. doi: [10.48550/arXiv.2412.20878](https://doi.org/10.48550/arXiv.2412.20878).

 - M. Abdulaziz, 'A Formal Correctness Proof of Edmonds’ Blossom Shrinking Algorithm', Dec. 30, 2024, arXiv: arXiv:2412.20878. doi: [10.48550/arXiv.2412.20878](https://doi.org/10.48550/arXiv.2412.20878).

 - M. Abdulaziz and T. Ammer, 'A Formal Analysis of Capacity Scaling Algorithms for Minimum Cost Flows', in The 15th International Conference on Interactive Theorem Proving (ITP 2024), Schloss Dagstuhl – Leibniz-Zentrum für Informatik, 2024. doi: [10.4230/LIPIcs.ITP.2024.3](https://doi.org/10.4230/LIPIcs.ITP.2024.3)

 - M. Abdulaziz and C. Madlener, 'A Formal Analysis of RANKING', in The 14th Conference on Interactive Theorem Proving (ITP), 2023. doi: [10.48550/arXiv.2302.13747](https://doi.org/10.48550/arXiv.2302.13747).

 - M. Abdulaziz, K. Mehlhorn, and T. Nipkow, 'Trustworthy graph algorithms (invited paper)', in the 44th International Symposium on Mathematical Foundations of Computer Science (MFCS), in LIPIcs, vol. 138. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2019, p. 1:1-1:22. doi: [10.4230/LIPIcs.MFCS.2019.1](https://doi.org/10.4230/LIPIcs.MFCS.2019.1).
