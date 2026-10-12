theory Fixed_Univ_Set_Specs
  imports Main
begin

locale fixed_univ_set =
  fixes U :: "'a set"
  and fixed_univ_set_invar :: "'set \<Rightarrow> bool"
  and fixed_univ_set_abstract :: "'set \<Rightarrow> 'a set"
  and fixed_univ_set_empty :: "'set"
  and fixed_univ_set_insert :: "'a \<Rightarrow> 'set \<Rightarrow> 'set"
  and fixed_univ_set_delete :: "'a \<Rightarrow> 'set \<Rightarrow> 'set"
  and fixed_univ_set_isin :: "'set \<Rightarrow> 'a \<Rightarrow> bool"
  assumes fixed_univ_set_universe:
      "\<And> S. fixed_univ_set_invar S \<Longrightarrow> fixed_univ_set_abstract S \<subseteq> U"
  and fixed_univ_set_empty:
      "fixed_univ_set_invar fixed_univ_set_empty"
      "fixed_univ_set_abstract fixed_univ_set_empty = {}"
  and fixed_univ_set_insert:
      "\<And> x S. \<lbrakk>fixed_univ_set_invar S; x \<in> U\<rbrakk> \<Longrightarrow> fixed_univ_set_invar (fixed_univ_set_insert x S)"
      "\<And> x S. \<lbrakk>fixed_univ_set_invar S; x \<in> U\<rbrakk> \<Longrightarrow>
          fixed_univ_set_abstract (fixed_univ_set_insert x S) = insert x (fixed_univ_set_abstract S)"
  and fixed_univ_set_delete:
      "\<And> x S. fixed_univ_set_invar S \<Longrightarrow> fixed_univ_set_invar (fixed_univ_set_delete x S)"
      "\<And> x S. fixed_univ_set_invar S \<Longrightarrow>
          fixed_univ_set_abstract (fixed_univ_set_delete x S) = fixed_univ_set_abstract S - {x}"
  and fixed_univ_set_isin:
      "\<And> x S. fixed_univ_set_invar S \<Longrightarrow> fixed_univ_set_isin S x \<longleftrightarrow> x \<in> fixed_univ_set_abstract S"

text \<open>A set is its own model, over any universe.\<close>

lemma set_fixed_univ_set:
  "fixed_univ_set U (\<lambda>S. S \<subseteq> U) id {} insert (\<lambda>x S. S - {x}) (\<lambda>S x. x \<in> S)"
  by unfold_locales auto

end
