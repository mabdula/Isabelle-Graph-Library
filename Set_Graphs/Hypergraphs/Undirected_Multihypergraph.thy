theory Undirected_Multihypergraph
  imports Multihypergraph
begin

locale undirected_multihypergraph = 
  fixes conn
  assumes "is_undirected conn"
begin
end

end