theory Simple_Hypergraph
  imports Multihypergraph
begin 

locale simple_hypergraph =
  fixes conn
  assumes "is_simple conn"
begin
end

end