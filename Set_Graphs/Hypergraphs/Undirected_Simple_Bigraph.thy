theory Undirected_Simple_Bigraph
  imports Undirected_Multibigraph Undirected_Simple_Hypergraph Simple_Bigraph
begin

locale undirected_simple_bigraph =
(*Corners of the cube that demand one step*)
multibigraph +
undirected_multihypergraph +
simple_hypergraph +
(*Corners of the cube that demand two steps*)
undirected_multibigraph +
simple_bigraph +
undirected_simple_hypergraph
begin







end
end