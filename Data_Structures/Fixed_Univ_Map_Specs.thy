theory Fixed_Univ_Map_Specs
  imports Main
begin

locale fixed_univ_map =
fixes K::"'a set"
and fixed_univ_map_invar::"'array \<Rightarrow> bool"
and fixed_univ_map_upd::"'array \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'array"
and fixed_univ_map_lookup::"'array \<Rightarrow> 'a \<Rightarrow> 'b"
assumes fixed_univ_map_upd:
"\<And> A k v. 
 \<lbrakk>fixed_univ_map_invar A; k \<in> K\<rbrakk> \<Longrightarrow>
fixed_univ_map_lookup (fixed_univ_map_upd A k v) =
(fixed_univ_map_lookup A) (k := v)"
and fixed_univ_map_upd_invar:
"\<And> A k v. \<lbrakk>fixed_univ_map_invar A; k \<in> K\<rbrakk> 
\<Longrightarrow> fixed_univ_map_invar (fixed_univ_map_upd A k v)"


lemma nth_fun_list_update: "k < length A \<Longrightarrow> nth (A[k := v]) = (nth A)(k := v)"
  by (auto simp: fun_eq_iff nth_list_update)

text \<open>The @{locale fixed_univ_map} operations are read off a list directly: lookup is @{const nth}
      and update is @{const list_update} (\<open>xs[k := v]\<close>).  The invariant records that every allowed
      key is a valid index (\<open>\<forall>k\<in>K. k < length xs\<close>), which is exactly what makes the
      key-restricted update law hold.\<close>

lemma list_fixed_univ_map: "fixed_univ_map K (\<lambda>xs. \<forall>k\<in>K. k < length xs) list_update nth"
  by unfold_locales (simp_all add: nth_fun_list_update)

text \<open>A length-pinned variant: when the array's length is exactly @{term n} and the key set lies in
      @{term \<open>{0..<n}\<close>}, every key is in range and @{const list_update} preserves the length. Making
      the length part of the invariant is what lets the acyclifier's invariant carry it: the flow it
      returns is then known to have length @{term m}.\<close>

lemma list_fixed_univ_map_len:
  "K \<subseteq> {0..<n} \<Longrightarrow> fixed_univ_map K (\<lambda>xs. length xs = n) list_update nth"
  by unfold_locales (auto simp: nth_fun_list_update)

end