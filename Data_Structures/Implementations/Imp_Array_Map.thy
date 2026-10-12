theory Imp_Array_Map
  imports
    Imp_Bool_Set
    Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

section \<open>Total Maps on Nats below a Bound as Arrays\<close>

text \<open>The array holds exactly the list of values of the map on \<open>[0..<n]\<close>. This is the analogue
      of @{const bool_array_set_assn} for total maps.\<close>

definition array_fun_assn :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a::heap array \<Rightarrow> assn" where
  "array_fun_assn n f Xi = Xi \<mapsto>\<^sub>a map f [0..<n]"

lemma array_fun_assn_new: "<emp> Array.new n x <array_fun_assn n (\<lambda> _. x)>"
  unfolding array_fun_assn_def by (sep_auto simp: map_replicate_const)

lemma array_fun_lookup_rule:
  "<array_fun_assn n f Xi * \<up>(i < n)> Array.nth Xi i <\<lambda> r. array_fun_assn n f Xi * \<up>(r = f i)>"
  unfolding array_fun_assn_def by sep_auto

lemma map_fun_update:
  "i < n \<Longrightarrow> (map f [0..<n])[i := x] = map (f(i := x)) [0..<n]"
  by (rule nth_equalityI) (auto simp: nth_list_update)

lemma array_fun_upd_rule:
  "<array_fun_assn n f Xi * \<up>(i < n)> Array.upd i x Xi
     <\<lambda> r. array_fun_assn n (f(i := x)) Xi * \<up>(r = Xi)>"
  unfolding array_fun_assn_def by (sep_auto simp: map_fun_update)

lemma array_fun_len: "array_fun_assn n f Xi \<Longrightarrow>\<^sub>A len_assn n Xi"
  unfolding array_fun_assn_def len_assn_def by sep_auto

text \<open>Clearing overwrites every entry by a constant, in place.\<close>

definition "array_fun_clear_imp x n Xi = fill_range_imp (\<lambda> _. x) n Xi"

lemma array_fun_clear_rule:
  "<len_assn n Xi> array_fun_clear_imp x n Xi <\<lambda> r. array_fun_assn n (\<lambda> _. x) Xi * \<up>(r = Xi)>"
proof-
  have "<Xi \<mapsto>\<^sub>a l * \<up>(length l = n)> array_fun_clear_imp x n Xi
         <\<lambda> r. array_fun_assn n (\<lambda> _. x) Xi * \<up>(r = Xi)>" for l
    unfolding array_fun_clear_imp_def
    by (rule ht_cons_post[OF fill_range_imp_rule]) (sep_auto simp: array_fun_assn_def)
  then show ?thesis
    unfolding len_assn_def by (rule ht_ex_pre)
qed

section \<open>The Arrays as Fixed-Universe Maps\<close>

text \<open>The functional model of an array of length \<open>n\<close> is the total function itself, on the
      universe \<open>{..<n}\<close>. Values are stored as they are.\<close>

definition "array_fun_upd (f :: nat \<Rightarrow> 'a) k x = f(k := x)"
definition "array_fun_lookup (f :: nat \<Rightarrow> 'a) = f"

definition "array_fun_upd_imp Xi k x = do { _ \<leftarrow> Array.upd k x Xi; return () }"
definition "array_fun_lookup_imp Xi k = Array.nth Xi k"

lemma array_fun_fixed_univ_map_imp:
  "fixed_univ_map_imp {..<n} (\<lambda> _. True) array_fun_upd array_fun_lookup id (array_fun_assn n)
     array_fun_upd_imp array_fun_lookup_imp"
  by unfold_locales
     (sep_auto simp: array_fun_upd_def array_fun_lookup_def array_fun_upd_imp_def array_fun_lookup_imp_def
               heap: array_fun_lookup_rule array_fun_upd_rule)+

section \<open>Arrays of Values Read by a Function\<close>

text \<open>The array holds values that are read into the values of the functional model by
      @{term h}, e.g. executable numbers read into the reals.\<close>

definition "array_fun_val_assn h n f Xi = (\<exists>\<^sub>A g. array_fun_assn n g Xi * \<up>(\<forall>i<n. h (g i) = f i))"

lemma array_fun_val_fixed_univ_map_imp:
  "fixed_univ_map_imp {..<n} (\<lambda> _. True) array_fun_upd array_fun_lookup h (array_fun_val_assn h n)
     array_fun_upd_imp array_fun_lookup_imp"
  by unfold_locales
     (sep_auto simp: array_fun_upd_def array_fun_lookup_def array_fun_upd_imp_def array_fun_lookup_imp_def
                     array_fun_val_assn_def heap: array_fun_lookup_rule array_fun_upd_rule)+

lemma array_fun_val_len: "array_fun_val_assn h n f Xi \<Longrightarrow>\<^sub>A len_assn n Xi"
  unfolding array_fun_val_assn_def array_fun_assn_def len_assn_def by sep_auto

lemma array_fun_val_clear_rule:
  "<len_assn n Xi> array_fun_clear_imp x n Xi <\<lambda> r. array_fun_val_assn h n (\<lambda> _. h x) Xi * \<up>(r = Xi)>"
  by (sep_auto heap: array_fun_clear_rule simp: array_fun_val_assn_def)

text \<open>Allocation and clearing in place, as the init and clear operations of the fixed-universe
      maps: every entry becomes \<open>x\<close>.\<close>

definition "array_fun_clear_unit x n Xi = do { _ \<leftarrow> array_fun_clear_imp x n Xi; return () }"

lemma array_fun_fixed_univ_map_init_imp:
  "fixed_univ_map_init_imp {..<n} (\<lambda> _. True) array_fun_lookup id (array_fun_assn n)
     array_fun_lookup_imp (\<lambda> _. x) (Array.new n x)"
  by (intro fixed_univ_map_init_imp.intro fixed_univ_map_imp.axioms(2)[OF array_fun_fixed_univ_map_imp]
        fixed_univ_map_init_imp_axioms.intro array_fun_assn_new)

lemma array_fun_fixed_univ_map_clear_imp:
  "fixed_univ_map_clear_imp {..<n} (\<lambda> _. True) array_fun_lookup id (array_fun_assn n)
     array_fun_lookup_imp (\<lambda> _. x) (array_fun_clear_unit x n)"
  by (intro fixed_univ_map_clear_imp.intro fixed_univ_map_imp.axioms(2)[OF array_fun_fixed_univ_map_imp]
        fixed_univ_map_clear_imp_axioms.intro)
     (sep_auto simp: array_fun_clear_unit_def heap: ht_cons_pre[OF array_fun_len array_fun_clear_rule])

lemma array_fun_val_fixed_univ_map_clear_imp:
  "fixed_univ_map_clear_imp {..<n} (\<lambda> _. True) array_fun_lookup h (array_fun_val_assn h n)
     array_fun_lookup_imp (\<lambda> _. h x) (array_fun_clear_unit x n)"
  by (intro fixed_univ_map_clear_imp.intro
        fixed_univ_map_imp.axioms(2)[OF array_fun_val_fixed_univ_map_imp]
        fixed_univ_map_clear_imp_axioms.intro)
     (sep_auto simp: array_fun_clear_unit_def
        heap: ht_cons_pre[OF array_fun_val_len array_fun_val_clear_rule])

end
