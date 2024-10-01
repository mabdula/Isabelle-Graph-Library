# Isabelle-Graph-Library

A formal mathematical library covering results in graph theory, with a focus on graph algorithms and results from combinatorial optimisation.
Results include:

 - A set-based simple representation of graphs (both directed and undirected). In this representation, we tried to port as many results from other graph libraries in Isabelle as possible, using representation adaptors, i.e. lemmas that connect different representations.

 - Simple graph algorithms, like DFS and BFS.

 - Berge's lemma, which is a fundamental result from the theory of matching.

 - Edmonds' blossom shrinking algorithm.

 - The RANKING algorithm for online bi-partite matching, by Karp, Vazirani, and Vazirani.

 - An algorithm for vertex-weighted online matching.

 - The AdWords algorithm for online auction allocation, by Mehta, Saberi, Vazirani, and Vazirani.

For the more practically usable algorithms, we include an implementation. For others, we only focus on the analysis.