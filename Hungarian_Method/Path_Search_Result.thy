(*
  Author: Thomas Ammer
*)

theory Path_Search_Result
  imports Main AI_Provenance.Provenance
begin

provenance human

datatype 'v path_search_result = 
  Dual_Unbounded | Lefts_Matched | Next_Iteration (the_path: "'v list")

datatype imp_search_result = Imp_Unbounded | Imp_Matched | Imp_Path nat

text \<open>An imperative result refines a functional one; a path is the prefix of length @{term k}
      of the path array with contents @{term xs}.\<close>

definition "imp_result_rel xs res r =
  (case r of Dual_Unbounded \<Rightarrow> res = Imp_Unbounded
   | Lefts_Matched \<Rightarrow> res = Imp_Matched
   | Next_Iteration p \<Rightarrow> (\<exists>k. res = Imp_Path k \<and> k \<le> length xs \<and> take k xs = p))"

lemma imp_result_rel_simps[simp]:
  "imp_result_rel xs res Dual_Unbounded = (res = Imp_Unbounded)"
  "imp_result_rel xs res Lefts_Matched = (res = Imp_Matched)"
  "imp_result_rel xs res (Next_Iteration p) =
     (\<exists>k. res = Imp_Path k \<and> k \<le> length xs \<and> take k xs = p)"
  by (simp_all add: imp_result_rel_def)
end