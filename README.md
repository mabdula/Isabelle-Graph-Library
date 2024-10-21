# Isabelle-Graph-Library

A formal mathematical library covering results in graph theory, with a focus on graph algorithms and results from combinatorial optimisation.
Results include:

 - A set-based simple representation of graphs (both directed and undirected). In this representation, we tried to port as many results from other graph libraries in Isabelle as possible, using representation adaptors, i.e. lemmas that connect different representations.

 - Simple graph algorithms, like Depth-First-Search, Breadth-First-Search or Bellman-Ford. 

 - Berge's lemma, which is a fundamental result from the theory of matching.

 - Edmonds' blossom shrinking algorithm.

 - The RANKING algorithm for online bi-partite matching, by Karp, Vazirani, and Vazirani.

 - An algorithm for vertex-weighted online matching.

 - The AdWords algorithm for online auction allocation, by Mehta, Saberi, Vazirani, and Vazirani.
 
 - Background theory on independence systems/matroids and the Best-In-Greedy algorithm on independence systems/matroids.

 - Kruskal's algorithm for finding minimum spanning trees, implemented as an instance of the Best-In-Greedy algorithm.
 
 - Some fundamental theory for minimum cost flows and related algorithms, including Orlin's Algorithm, which is one of the most efficient methods for these class of problems.

For the more practically usable algorithms, we include an implementation. For others, we only focus on the analysis.
