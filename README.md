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

 - A Formal Analysis of Algorithms for Matroids and Greedoids
   Mohammad Abdulaziz, Thomas Ammer, Shriya Meenakshisundaram, and Adem Rimpapa
   On arXiv, 2025 doi: [](https://)
   
 - A Formal Correctness Proof of Edmonds' Blossom Shrinking Algorithm
   Mohammad Abdulaziz 
   On arXiv, 2024 doi: [10.48550/arXiv.2412.20878](https://10.48550/arXiv.2412.20878).

 - A Formal Analysis of Capacity Scaling Algorithms for Minimum Cost Flows
   Mohammad Abdulaziz and Thomas Ammer
   In the International Conference on Interactive Theorem Proving (ITP), 2024 doi: [10.48550/arXiv.2302.13747](https://10.48550/arXiv.2302.13747)

 - A Formal Analysis of RANKING
   Mohammad Abdulaziz and Christoph Madlener
   In the International Conference on Interactive Theorem Proving (ITP), 2023 doi: [10.4230/LIPIcs.ITP.2024.3](https://10.4230/LIPIcs.ITP.2024.3)

 - Trustworthy Graph Algorithms (Invited Talk)
   Mohammad Abdulaziz, Kurt Mehlhorn, and Tobias Nipkow
   In the International Symposium on Mathematical Foundations of Computer Science (MFCS), 2019 doi: [10.4230/LIPIcs.MFCS.2019.1](https://10.4230/LIPIcs.MFCS.2019.1)