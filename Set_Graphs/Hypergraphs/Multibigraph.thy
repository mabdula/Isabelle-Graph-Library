theory Multibigraph
  imports Multihypergraph
begin
locale multibigraph =
  fixes conn
  assumes is_dbltn: "is_dbltn conn"
begin
lemmas two_endpoints = is_dbltnE_meta[OF is_dbltn]
                       is_dbltnE[OF is_dbltn]


end

end