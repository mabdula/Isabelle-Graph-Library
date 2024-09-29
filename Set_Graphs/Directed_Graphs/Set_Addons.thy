theory Set_Addons
  imports "HOL-Data_Structures.Set_Specs"
begin
context Set
begin
bundle automation = set_empty[simp] set_isin[simp] set_insert[simp] set_delete[simp]
                    invar_empty[simp] invar_insert[simp] invar_delete[simp]

end
end