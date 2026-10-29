theory Fixed_Univ_Set_Specs_Imp
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main Fixed_Univ_Set_Specs
begin

text \<open>The basic interface: membership test, insertion and deletion in place. The add-ons below
      provide allocation of the empty set (@{text fixed_univ_set_imp}), clearing in place and
      copying into another set; bigger locales combine those they need.\<close>

locale fixed_univ_set_basic_imp =
  fixed_univ_set where U = U
    and fixed_univ_set_invar = fixed_univ_set_invar
    and fixed_univ_set_abstract = fixed_univ_set_abstract
    and fixed_univ_set_empty = fixed_univ_set_empty
    and fixed_univ_set_insert = fixed_univ_set_insert
    and fixed_univ_set_delete = fixed_univ_set_delete
    and fixed_univ_set_isin = fixed_univ_set_isin
  for U :: "'a set"
    and fixed_univ_set_invar :: "'set \<Rightarrow> bool"
    and fixed_univ_set_abstract :: "'set \<Rightarrow> 'a set"
    and fixed_univ_set_empty :: "'set"
    and fixed_univ_set_insert :: "'a \<Rightarrow> 'set \<Rightarrow> 'set"
    and fixed_univ_set_delete :: "'a \<Rightarrow> 'set \<Rightarrow> 'set"
    and fixed_univ_set_isin :: "'set \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes fixed_univ_set_assn :: "'set \<Rightarrow> 'seti \<Rightarrow> assn"
    and fixed_univ_set_insert_imp :: "'a \<Rightarrow> 'seti \<Rightarrow> unit Heap"
    and fixed_univ_set_delete_imp :: "'a \<Rightarrow> 'seti \<Rightarrow> unit Heap"
    and fixed_univ_set_isin_imp :: "'seti \<Rightarrow> 'a \<Rightarrow> bool Heap"
  assumes fixed_univ_set_insert_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_set_invar S; x \<in> U\<rbrakk> \<Longrightarrow>
       <fixed_univ_set_assn S Si> fixed_univ_set_insert_imp x Si
       <\<lambda>_. fixed_univ_set_assn (fixed_univ_set_insert x S) Si>"
    and fixed_univ_set_delete_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_set_invar S; x \<in> U\<rbrakk> \<Longrightarrow>
       <fixed_univ_set_assn S Si> fixed_univ_set_delete_imp x Si
       <\<lambda>_. fixed_univ_set_assn (fixed_univ_set_delete x S) Si>"
    and fixed_univ_set_isin_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_set_invar S; x \<in> U\<rbrakk> \<Longrightarrow>
       <fixed_univ_set_assn S Si> fixed_univ_set_isin_imp Si x
       <\<lambda>r. fixed_univ_set_assn S Si * \<up>(r = fixed_univ_set_isin S x)>"

text \<open>Initialisation: allocating the empty set.\<close>

locale fixed_univ_set_imp =
  fixed_univ_set_basic_imp U fixed_univ_set_invar fixed_univ_set_abstract fixed_univ_set_empty
    fixed_univ_set_insert fixed_univ_set_delete fixed_univ_set_isin fixed_univ_set_assn
    fixed_univ_set_insert_imp fixed_univ_set_delete_imp fixed_univ_set_isin_imp
  for U :: "'a set"
    and fixed_univ_set_invar :: "'set \<Rightarrow> bool"
    and fixed_univ_set_abstract fixed_univ_set_empty fixed_univ_set_insert fixed_univ_set_delete
      fixed_univ_set_isin
    and fixed_univ_set_assn :: "'set \<Rightarrow> 'seti \<Rightarrow> assn"
    and fixed_univ_set_empty_imp :: "'seti Heap"
    and fixed_univ_set_insert_imp fixed_univ_set_delete_imp fixed_univ_set_isin_imp +
  assumes fixed_univ_set_empty_rule[sep_heap_rules]:
      "<emp> fixed_univ_set_empty_imp <\<lambda>Si. fixed_univ_set_assn fixed_univ_set_empty Si>"

text \<open>Clearing a set in place.\<close>

locale fixed_univ_set_clear_imp = fixed_univ_set_basic_imp +
  fixes fixed_univ_set_clear_imp :: "'seti \<Rightarrow> unit Heap"
  assumes fixed_univ_set_clear_rule[sep_heap_rules]:
      "fixed_univ_set_invar S \<Longrightarrow>
       <fixed_univ_set_assn S Si> fixed_univ_set_clear_imp Si
       <\<lambda>_. fixed_univ_set_assn fixed_univ_set_empty Si>"

text \<open>Copying a set into another one, in place.\<close>

locale fixed_univ_set_copy_imp = fixed_univ_set_basic_imp +
  fixes fixed_univ_set_copy_imp :: "'seti \<Rightarrow> 'seti \<Rightarrow> unit Heap"
  assumes fixed_univ_set_copy_rule[sep_heap_rules]:
      "\<lbrakk>fixed_univ_set_invar S; fixed_univ_set_invar T\<rbrakk> \<Longrightarrow>
       <fixed_univ_set_assn S Si * fixed_univ_set_assn T Ti> fixed_univ_set_copy_imp Si Ti
       <\<lambda>_. fixed_univ_set_assn S Si * fixed_univ_set_assn S Ti>"

end
