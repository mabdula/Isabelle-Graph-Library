theory Undirected_Multibigraph
  imports Undirected_Multihypergraph Multibigraph
begin


locale undirected_multibigraph =
multibigraph + undirected_multihypergraph
begin
end

end