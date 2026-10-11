theory Imp_Array_Map
  imports
    Imp_Bool_Set
    Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

section \<open>Total Maps on Nats below a Bound as Arrays\<close>

text \<open>The array holds exactly the list of values of the map on \<open>[0..<n]\<close>. This is the analogue
      of @{const xset_assn} for total maps.\<close>

definition xmap_assn :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a::heap array \<Rightarrow> assn" where
  "xmap_assn n f Xi = Xi \<mapsto>\<^sub>a map f [0..<n]"

lemma xmap_assn_new: "<emp> Array.new n x <xmap_assn n (\<lambda> _. x)>"
  unfolding xmap_assn_def by (sep_auto simp: map_replicate_const)

lemma xmap_lookup_rule:
  "<xmap_assn n f Xi * \<up>(i < n)> Array.nth Xi i <\<lambda> r. xmap_assn n f Xi * \<up>(r = f i)>"
  unfolding xmap_assn_def by sep_auto

lemma map_fun_update:
  "i < n \<Longrightarrow> (map f [0..<n])[i := x] = map (f(i := x)) [0..<n]"
  by (rule nth_equalityI) (auto simp: nth_list_update)

lemma xmap_upd_rule:
  "<xmap_assn n f Xi * \<up>(i < n)> Array.upd i x Xi
     <\<lambda> r. xmap_assn n (f(i := x)) Xi * \<up>(r = Xi)>"
  unfolding xmap_assn_def by (sep_auto simp: map_fun_update)

lemma xmap_len: "xmap_assn n f Xi \<Longrightarrow>\<^sub>A len_assn n Xi"
  unfolding xmap_assn_def len_assn_def by sep_auto

text \<open>Clearing overwrites every entry by a constant, in place.\<close>

definition "xmap_clear_imp x n Xi = fill_range_imp (\<lambda> _. x) n Xi"

lemma xmap_clear_rule:
  "<len_assn n Xi> xmap_clear_imp x n Xi <\<lambda> r. xmap_assn n (\<lambda> _. x) Xi * \<up>(r = Xi)>"
proof-
  have "<Xi \<mapsto>\<^sub>a l * \<up>(length l = n)> xmap_clear_imp x n Xi
         <\<lambda> r. xmap_assn n (\<lambda> _. x) Xi * \<up>(r = Xi)>" for l
    unfolding xmap_clear_imp_def
    by (rule ht_cons_post[OF fill_range_imp_rule]) (sep_auto simp: xmap_assn_def)
  then show ?thesis
    unfolding len_assn_def by (rule ht_ex_pre)
qed

section \<open>The Arrays as Fixed-Universe Maps\<close>

text \<open>The functional model of an array of length \<open>n\<close> is the total function itself, on the
      universe \<open>{..<n}\<close>. Values are stored as they are.\<close>

definition "xmap_upd (f :: nat \<Rightarrow> 'a) k x = f(k := x)"
definition "xmap_lookup (f :: nat \<Rightarrow> 'a) = f"

definition "xmap_upd_imp Xi k x = do { _ \<leftarrow> Array.upd k x Xi; return () }"
definition "xmap_lookup_imp Xi k = Array.nth Xi k"

lemma xmap_fixed_univ_map_imp:
  "fixed_univ_map_imp {..<n} (\<lambda> _. True) xmap_upd xmap_lookup id (xmap_assn n)
     xmap_upd_imp xmap_lookup_imp"
  by unfold_locales
     (sep_auto simp: xmap_upd_def xmap_lookup_def xmap_upd_imp_def xmap_lookup_imp_def
               heap: xmap_lookup_rule xmap_upd_rule)+

section \<open>Arrays of Values Read by a Function\<close>

text \<open>The array holds values that are read into the values of the functional model by
      @{term h}, e.g. executable numbers read into the reals.\<close>

definition "xmap_val_assn h n f Xi = (\<exists>\<^sub>A g. xmap_assn n g Xi * \<up>(\<forall>i<n. h (g i) = f i))"

lemma xmap_val_fixed_univ_map_imp:
  "fixed_univ_map_imp {..<n} (\<lambda> _. True) xmap_upd xmap_lookup h (xmap_val_assn h n)
     xmap_upd_imp xmap_lookup_imp"
  by unfold_locales
     (sep_auto simp: xmap_upd_def xmap_lookup_def xmap_upd_imp_def xmap_lookup_imp_def
                     xmap_val_assn_def heap: xmap_lookup_rule xmap_upd_rule)+

lemma xmap_val_len: "xmap_val_assn h n f Xi \<Longrightarrow>\<^sub>A len_assn n Xi"
  unfolding xmap_val_assn_def xmap_assn_def len_assn_def by sep_auto

lemma xmap_val_clear_rule:
  "<len_assn n Xi> xmap_clear_imp x n Xi <\<lambda> r. xmap_val_assn h n (\<lambda> _. h x) Xi * \<up>(r = Xi)>"
  by (sep_auto heap: xmap_clear_rule simp: xmap_val_assn_def)

end
