(*
  Author: Mohammad Abdulaziz
*)

theory Set_Addons
  imports "HOL-Data_Structures.Set_Specs" AI_Provenance.Provenance
begin

subsection \<open>Functional Models of the Iterations over Sets\<close>

definition "fset_iterate f init V = foldl f init (sorted_list_of_set V)"
definition "fset_filter P (V :: 'a set) = V \<inter> Collect P"
definition "fset_is_empty (V :: 'a set) = (V = {})"

lemma fset_iterate_foldl_set:
  "finite V \<Longrightarrow> \<exists>vs. set vs = V \<and> distinct vs \<and> fset_iterate f init V = foldl f init vs"
  by (auto simp: fset_iterate_def intro!: exI[of _ "sorted_list_of_set V"])

lemma fset_iterate_below:
  "V \<subseteq> {..<n::nat} \<Longrightarrow> \<exists>vs. id V = set vs \<and> distinct vs \<and> fset_iterate f init V = foldl f init vs"
  using finite_subset[OF _ finite_lessThan]
  by (auto simp: fset_iterate_def intro!: exI[of _ "sorted_list_of_set V"])

locale set_insert_spec =
  fixes bset_inv :: "'bset \<Rightarrow> bool"
    and bset_abs :: "'bset \<Rightarrow> 'b set"
    and bset_empty :: "'bset"
    and bset_insert :: "'b \<Rightarrow> 'bset \<Rightarrow> 'bset"
  assumes bset_empty: "bset_inv bset_empty" "bset_abs bset_empty = {}"
  assumes bset_insert: 
    "\<And> s b. bset_inv s \<Longrightarrow> bset_inv (bset_insert b s)"
    "\<And> s b. bset_inv s \<Longrightarrow> bset_abs (bset_insert b s) = insert b (bset_abs s)"
begin

lemma foldr_bset:
  "bset_inv (foldr (\<lambda> x. bset_insert (blk x)) xs bset_empty) \<and>
   bset_abs (foldr (\<lambda> x. bset_insert (blk x)) xs bset_empty) = blk ` set xs"
  by (induction xs) (simp_all add: bset_empty bset_insert)

end

provenance human

context Set
begin
bundle automation = set_empty[simp] set_isin[simp] set_insert[simp] set_delete[simp]
                    invar_empty[simp] invar_insert[simp] invar_delete[simp]

end
end
