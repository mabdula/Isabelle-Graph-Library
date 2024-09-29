theory Tree_Defs
  imports Pair_Graph Vwalk
begin

locale tree =
fixes
  root :: 'a
assumes
  root_in_T: "root \<in> dVs T" and
  unique_awalk: "v \<in> dVs T \<Longrightarrow> \<exists>!p. vwalk_bet T root p v"
begin

end
end