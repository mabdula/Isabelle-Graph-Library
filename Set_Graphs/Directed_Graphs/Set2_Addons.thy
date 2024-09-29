theory Set2_Addons
  imports "HOL-Data_Structures.Set_Specs"
begin

context Set2
begin
bundle automation =
       set_union[simp] set_inter[simp] 
       set_diff[simp] invar_union[simp]
       invar_inter[simp] invar_diff[simp]


  notation "inter" (infixl "\<inter>\<^sub>G" 100)
  notation "diff" (infixl "-\<^sub>G" 100)
  notation "union" (infixl "\<union>\<^sub>G" 100)
end

end