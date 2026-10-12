theory Fixed_Univ_Map_Specs_Imp
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main Fixed_Univ_Map_Specs
begin

text \<open>The basic interface: immutable maps, with a lookup only. Update in place is an extension
      (@{text fixed_univ_map_imp}), as are the add-ons below.\<close>

locale fixed_univ_map_basic_imp =
  fixes K :: "'a set"
    and fixed_univ_map_invar :: "'array \<Rightarrow> bool"
    and fixed_univ_map_lookup :: "'array \<Rightarrow> 'a \<Rightarrow> 'b"
    and fixed_univ_map_val :: "'bi::heap \<Rightarrow> 'b"
    and fixed_univ_map_assn :: "'array \<Rightarrow> 'arrayi \<Rightarrow> assn"
    and fixed_univ_map_lookup_imp :: "'arrayi \<Rightarrow> 'a \<Rightarrow> 'bi Heap"
  assumes fixed_univ_map_lookup_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_map_invar A; k \<in> K\<rbrakk> \<Longrightarrow>
       <fixed_univ_map_assn A Ai> fixed_univ_map_lookup_imp Ai k
       <\<lambda>x. fixed_univ_map_assn A Ai * \<up>(fixed_univ_map_val x = fixed_univ_map_lookup A k)>"

text \<open>Mutable maps: update in place.\<close>

locale fixed_univ_map_imp =
  fixed_univ_map K fixed_univ_map_invar fixed_univ_map_upd fixed_univ_map_lookup +
  fixed_univ_map_basic_imp K fixed_univ_map_invar fixed_univ_map_lookup fixed_univ_map_val
    fixed_univ_map_assn fixed_univ_map_lookup_imp
  for K :: "'a set"
    and fixed_univ_map_invar :: "'array \<Rightarrow> bool"
    and fixed_univ_map_upd :: "'array \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'array"
    and fixed_univ_map_lookup :: "'array \<Rightarrow> 'a \<Rightarrow> 'b"
    and fixed_univ_map_val :: "'bi::heap \<Rightarrow> 'b"
    and fixed_univ_map_assn :: "'array \<Rightarrow> 'arrayi \<Rightarrow> assn"
    and fixed_univ_map_upd_imp :: "'arrayi \<Rightarrow> 'a \<Rightarrow> 'bi \<Rightarrow> unit Heap"
    and fixed_univ_map_lookup_imp :: "'arrayi \<Rightarrow> 'a \<Rightarrow> 'bi Heap" +
  assumes fixed_univ_map_upd_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_map_invar A; k \<in> K\<rbrakk> \<Longrightarrow>
       <fixed_univ_map_assn A Ai> fixed_univ_map_upd_imp Ai k v
       <\<lambda>_. fixed_univ_map_assn (fixed_univ_map_upd A k (fixed_univ_map_val v)) Ai>"

text \<open>Add-ons, combined as needed: allocating a map with the contents
      @{text fixed_univ_map_init}, resetting a map to these contents in place, and copying a map
      into another one in place.\<close>

locale fixed_univ_map_init_imp = fixed_univ_map_basic_imp +
  fixes fixed_univ_map_init :: "'array"
    and fixed_univ_map_init_imp :: "'arrayi Heap"
  assumes fixed_univ_map_init_rule[sep_heap_rules]:
      "<emp> fixed_univ_map_init_imp <fixed_univ_map_assn fixed_univ_map_init>"

locale fixed_univ_map_clear_imp = fixed_univ_map_basic_imp +
  fixes fixed_univ_map_init :: "'array"
    and fixed_univ_map_clear_imp :: "'arrayi \<Rightarrow> unit Heap"
  assumes fixed_univ_map_clear_rule[sep_heap_rules]:
      "fixed_univ_map_invar A \<Longrightarrow>
       <fixed_univ_map_assn A Ai> fixed_univ_map_clear_imp Ai
       <\<lambda>_. fixed_univ_map_assn fixed_univ_map_init Ai>"

locale fixed_univ_map_copy_imp = fixed_univ_map_basic_imp +
  fixes fixed_univ_map_copy_imp :: "'arrayi \<Rightarrow> 'arrayi \<Rightarrow> unit Heap"
  assumes fixed_univ_map_copy_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_map_invar A; fixed_univ_map_invar B\<rbrakk> \<Longrightarrow>
       <fixed_univ_map_assn A Ai * fixed_univ_map_assn B Bi> fixed_univ_map_copy_imp Ai Bi
       <\<lambda>_. fixed_univ_map_assn A Ai * fixed_univ_map_assn A Bi>"

end
