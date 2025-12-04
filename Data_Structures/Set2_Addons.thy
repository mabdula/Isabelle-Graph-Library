theory Set2_Addons
  imports "HOL-Data_Structures.Set_Specs" Set_Addons
begin

context Set2
begin
bundle automation2 = (* Peter: I renamed that, as it causes name conflict errors when imported together with Set_Addons, making the Set2-locale almost unworkable! *)
       set_empty[simp] set_isin[simp] set_insert[simp] set_delete[simp]
       invar_empty[simp] invar_insert[simp] invar_delete[simp]
                    
       set_union[simp] set_inter[simp] 
       set_diff[simp] invar_union[simp]
       invar_inter[simp] invar_diff[simp]

  notation "inter" (infixl "\<inter>\<^sub>G" 100)
  notation "diff" (infixl "-\<^sub>G" 100)
  notation "union" (infixl "\<union>\<^sub>G" 100)
end

end