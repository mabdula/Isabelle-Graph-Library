theory Imperative_Base
imports
  "Separation_Logic_Imperative_HOL_Partial.Array_Set_Impl"
  "Separation_Logic_Imperative_HOL_Partial.Array_Map_Impl"
  "Separation_Logic_Imperative_HOL_Partial.Hash_Set_Impl"
  "Separation_Logic_Imperative_HOL_Partial.Hash_Map_Impl"
  "Collections.Locale_Code"
begin



  (* TODO @M: Set-locale lacks is-empty operation *)

  no_notation Ref.update (\<open>_ := _\<close> 62)
end
