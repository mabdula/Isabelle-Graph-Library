(*
  Author: Thomas Ammer
*)

theory Path_Search_Result
  imports Main AI_Provenance.Provenance
begin

provenance human

datatype ('v, 'pot) path_search_result = 
  Dual_Unbounded | Lefts_Matched | Next_Iteration (the_path: "'v list") (the_pot: 'pot)
end