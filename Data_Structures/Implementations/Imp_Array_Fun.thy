theory Imp_Array_Fun
  imports
    Imp_Bool_Set
    Data_Structures.Fixed_Univ_Map_Specs_Imp
    Data_Structures.Fixed_Univ_List_Specs_Imp
begin

lemma array_rlist: "imp_rlist (\<lambda>xs a. a \<mapsto>\<^sub>a xs) Array.len Array.nth"
  by unfold_locales sep_auto+

section \<open>Total Maps on Nats below a Bound as Arrays\<close>

text \<open>The array holds exactly the list of values of the map on \<open>[0..<n]\<close>. This is the analogue
      of @{const bool_array_set_assn} for total maps.\<close>

definition array_fun_assn :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a::heap array \<Rightarrow> assn" where
  "array_fun_assn n f Xi = Xi \<mapsto>\<^sub>a map f [0..<n]"

lemma array_fun_assn_replicate: "array_fun_assn n (\<lambda>_. x) Xi = Xi \<mapsto>\<^sub>a replicate n x"
  by (simp add: array_fun_assn_def map_replicate_const)

lemma array_fun_assn_new: "<emp> Array.new n x <array_fun_assn n (\<lambda> _. x)>"
  by (sep_auto simp: array_fun_assn_def map_replicate_const)

lemma array_fun_lookup_rule:
  "<array_fun_assn n f Xi * \<up>(i < n)> Array.nth Xi i <\<lambda> r. array_fun_assn n f Xi * \<up>(r = f i)>"
  by (sep_auto simp: array_fun_assn_def)

lemma array_fun_upd_rule:
  "<array_fun_assn n f Xi * \<up>(i < n)> Array.upd i x Xi
     <\<lambda> r. array_fun_assn n (f(i := x)) Xi * \<up>(r = Xi)>"
  by (sep_auto simp: array_fun_assn_def map_fun_update)

lemma array_fun_len: "array_fun_assn n f Xi \<Longrightarrow>\<^sub>A len_assn n Xi"
  by (sep_auto simp: array_fun_assn_def len_assn_def)

text \<open>Clearing overwrites every entry by a constant, in place.\<close>

definition "array_fun_clear_imp x n Xi = fill_range_imp (\<lambda> _. x) n Xi"

lemma array_fun_clear_rule:
  "<len_assn n Xi> array_fun_clear_imp x n Xi <\<lambda> r. array_fun_assn n (\<lambda> _. x) Xi * \<up>(r = Xi)>"
  unfolding len_assn_def array_fun_clear_imp_def
  by (rule ht_ex_pre, rule ht_cons_post[OF fill_range_imp_rule])
     (sep_auto simp: array_fun_assn_def)

section \<open>The Arrays as Fixed-Universe Maps\<close>

text \<open>The functional model of an array of length \<open>n\<close> is the total function itself, on the
      universe \<open>{..<n}\<close>. Values are stored as they are.\<close>

definition "array_fun_upd (f :: nat \<Rightarrow> 'a) k x = f(k := x)"
definition "array_fun_lookup (f :: nat \<Rightarrow> 'a) = f"

lemma array_fun_fixed_univ_map: "fixed_univ_map {..<n} (\<lambda>_. True) array_fun_upd array_fun_lookup"
  by unfold_locales (auto simp: array_fun_upd_def array_fun_lookup_def)


definition "array_fun_upd_imp Xi k x = do { _ \<leftarrow> Array.upd k x Xi; return () }"
definition "array_fun_lookup_imp Xi k = Array.nth Xi k"

lemma array_fun_upd_imp_list_rule [sep_heap_rules]:
  "i < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs> array_fun_upd_imp a i x <\<lambda>_. a \<mapsto>\<^sub>a
     list_update xs i x>"
  unfolding array_fun_upd_imp_def by sep_auto

lemma array_fun_fixed_univ_map_imp:
  "fixed_univ_map_imp {..<n} (\<lambda> _. True) array_fun_upd array_fun_lookup id (array_fun_assn n)
     array_fun_upd_imp array_fun_lookup_imp"
  by unfold_locales
     (sep_auto simp: array_fun_upd_def array_fun_lookup_def array_fun_upd_imp_def array_fun_lookup_imp_def
               heap: array_fun_lookup_rule array_fun_upd_rule)+

section \<open>Generic array loops\<close>

text \<open>Fill a prefix of an array with a constant (used to clear the seen array before reuse).\<close>
partial_function (heap) arr_fill_imp ::
  "'a::heap array \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "arr_fill_imp a x v nn =
     (if nn \<le> v then return () else do { _ \<leftarrow> array_fun_upd_imp a v x; arr_fill_imp a x (Suc v) nn })"

text \<open>A single in-place write refines a list update; @{const arr_fill_imp} then refines the
      corresponding range operation on the abstract list.\<close>

lemma arr_fill_imp_rule:
  "\<lbrakk>v \<le> nn; nn \<le> length xs\<rbrakk> \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs> arr_fill_imp a x v nn <\<lambda>_. a \<mapsto>\<^sub>a
     (take v xs @ replicate (nn - v) x @ drop nn xs)>"
proof(induction "nn - v" arbitrary: v xs)
  case 0
  then show ?case by (subst arr_fill_imp.simps) (sep_auto)
next
  case (Suc d)
  then have "d = nn - Suc v" "Suc v \<le> nn" "nn \<le> length (list_update xs v x)" by simp_all
  note IH = Suc.hyps(1)[OF this]
  have "replicate (nn - v) x = x # replicate (nn - Suc v) x"
    using Suc.hyps(2) by (simp flip: replicate_Suc add: Suc_diff_Suc)
  with Suc.prems show ?case
    by (subst arr_fill_imp.simps)
       (sep_auto heap: IH simp: take_Suc_conv_app_nth list_update_append)
qed


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
  by (sep_auto simp: array_fun_val_assn_def array_fun_assn_def len_assn_def)

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
