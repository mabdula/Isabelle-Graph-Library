theory Simple_Bigraph
imports Multibigraph Simple_Hypergraph
begin

locale simple_bigraph =
multibigraph +  simple_hypergraph
begin
end

end