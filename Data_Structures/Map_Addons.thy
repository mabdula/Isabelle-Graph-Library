theory Map_Addons
  imports "HOL-Data_Structures.Map_Specs"
begin
context Map
begin
bundle automation = map_empty[simp] map_update[simp] map_delete[simp] invar_empty[simp]
       invar_update[simp] invar_delete[simp]
end
end