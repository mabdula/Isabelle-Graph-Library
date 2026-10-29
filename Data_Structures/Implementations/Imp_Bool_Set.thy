theory Imp_Bool_Set
  imports Imp_Range_Iteration Data_Structures.Fixed_Univ_Set_Specs_Imp
begin

section \<open>Sets of Nats below a Bound as Boolean Arrays\<close>

text \<open>The array holds exactly the characteristic list of the set.\<close>

definition bool_array_set_assn :: "nat \<Rightarrow> nat set \<Rightarrow> bool array \<Rightarrow> assn" where
  "bool_array_set_assn n X Xi = Xi \<mapsto>\<^sub>a map (\<lambda> i. i \<in> X) [0..<n] * \<up>(X \<subseteq> {..<n})"

lemma bool_array_set_assn_replicate: "bool_array_set_assn n {} Xi = Xi \<mapsto>\<^sub>a replicate n False"
  by (simp add: bool_array_set_assn_def map_replicate_const)

lemma bool_array_set_assn_new: "<emp> Array.new n False <bool_array_set_assn n {}>"
  by (sep_auto simp: bool_array_set_assn_def map_replicate_const)

lemma bool_array_set_of_list_rule:
  "<\<up>(xs = map (\<lambda> i. i \<in> X) [0..<n] \<and> X \<subseteq> {..<n})> Array.of_list xs <bool_array_set_assn n X>"
  by (sep_auto simp: bool_array_set_assn_def)

lemma bool_array_set_memb_rule:
  "<bool_array_set_assn n X Xi * \<up>(i < n)> Array.nth Xi i
   <\<lambda> r. bool_array_set_assn n X Xi * \<up>(r \<longleftrightarrow> i \<in> X)>"
  by (sep_auto simp: bool_array_set_assn_def)

lemma bool_array_set_upd_rule:
  "<bool_array_set_assn n X Xi * \<up>(i < n)> Array.upd i b Xi
     <\<lambda> r. bool_array_set_assn n (if b then insert i X else X - {i}) Xi * \<up>(r = Xi)>"
  by (sep_auto simp: bool_array_set_assn_def map_mem_update split: if_split)

text \<open>An array of length \<open>n\<close> with arbitrary content, e.g. a workspace array between two
  uses; it is cleared in place.\<close>

definition len_assn :: "nat \<Rightarrow> 'a::heap array \<Rightarrow> assn" where
  "len_assn n a = (\<exists>\<^sub>A l. a \<mapsto>\<^sub>a l * \<up>(length l = n))"

lemma len_assn_new: "<emp> Array.new n x <len_assn n>"
  by (sep_auto simp: len_assn_def)

lemma bool_array_set_len: "bool_array_set_assn n X Xi \<Longrightarrow>\<^sub>A len_assn n Xi"
  by (sep_auto simp: bool_array_set_assn_def len_assn_def)

definition "bool_array_set_clear_imp n Xi = fill_range_imp (\<lambda> _. False) n Xi"

lemma bool_array_set_clear_rule:
  "<len_assn n Xi> bool_array_set_clear_imp n Xi <\<lambda> r. bool_array_set_assn n {} Xi * \<up>(r = Xi)>"
  unfolding len_assn_def bool_array_set_clear_imp_def
  by (rule ht_ex_pre, rule ht_cons_post[OF fill_range_imp_rule])
     (sep_auto simp: bool_array_set_assn_def)

section \<open>An Abstract Imperative Set of Nats below a Bound\<close>

text \<open>The interface through which the algorithms see a solution: the basic fixed-universe set
  interface on the set itself as model, whose assertion bounds the set. The handle may carry
  further data that its operations keep up to date (e.g. for oracles).\<close>

text \<open>Copying the set into a Boolean array, in place.\<close>

locale imp_nat_set_spec =
  fixes n :: nat
    and smemb_imp :: "nat \<Rightarrow> 'si \<Rightarrow> bool Heap"
begin

definition "bcopy_imp Si Bi = copy_range_imp (\<lambda> i. smemb_imp i Si) n Bi"

end

locale imp_nat_set =
  fixed_univ_set_basic_imp "{..<n}" "\<lambda> X. X \<subseteq> {..<n}" id "{}" insert "\<lambda> x X. X - {x}"
    "\<lambda> X x. x \<in> X" sol_assn sins_imp sdel_imp "\<lambda> Si x. smemb_imp x Si"
  for n :: nat
    and sol_assn :: "nat set \<Rightarrow> 'si \<Rightarrow> assn"
    and smemb_imp :: "nat \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and sins_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and sdel_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap" +
  assumes sol_bound: "sol_assn X Si \<Longrightarrow>\<^sub>A sol_assn X Si * \<up>(X \<subseteq> {..<n})"
begin

sublocale imp_nat_set_spec n smemb_imp .

lemma sol_rule: "(X \<subseteq> {..<n} \<Longrightarrow> <sol_assn X Si> c <Q>) \<Longrightarrow> <sol_assn X Si> c <Q>"
  by (rule ht_cons_pre[OF sol_bound], rule ht_extract_pre_pure(1))

lemma smemb_rule: "<sol_assn X Si * \<up>(x < n)> smemb_imp x Si <\<lambda> r. sol_assn X Si * \<up>(r = (x \<in> X))>"
  by (rule ht_extract_pre_pure(1), rule sol_rule) (simp add: fixed_univ_set_isin_rule[of X x Si])

lemma sins_rule: "<sol_assn X Si * \<up>(x < n)> sins_imp x Si <\<lambda> _. sol_assn (insert x X) Si>"
  by (rule ht_extract_pre_pure(1), rule sol_rule) (simp add: fixed_univ_set_insert_rule[of X x Si])

lemma sdel_rule: "<sol_assn X Si * \<up>(x < n)> sdel_imp x Si <\<lambda> _. sol_assn (X - {x}) Si>"
  by (rule ht_extract_pre_pure(1), rule sol_rule) (simp add: fixed_univ_set_delete_rule[of X x Si])

lemma smemb_pure_rule:
  "i < n \<Longrightarrow> <sol_assn X Si> smemb_imp i Si <\<lambda> r. sol_assn X Si * \<up>(r = (i \<in> X))>"
  using smemb_rule[of X Si i]
  by simp

lemma bcopy_rule:
  "<sol_assn X Si * len_assn n Bi> bcopy_imp Si Bi <\<lambda> _. sol_assn X Si * bool_array_set_assn n X Bi>"
  unfolding len_assn_def bcopy_imp_def
  by (rule ht_cons_pre[OF ent_star_mono[OF sol_bound ent_refl]])
     (sep_auto heap: copy_range_imp_rule[OF smemb_pure_rule] simp: bool_array_set_assn_def)

end

section \<open>The Boolean Arrays as Fixed-Universe Sets\<close>

text \<open>The functional model of a Boolean array of length \<open>n\<close> is the set itself, a subset of the
      universe \<open>{..<n}\<close>.\<close>

definition "bool_array_set_insert_imp x Xi = do { _ \<leftarrow> Array.upd x True Xi; return () }"
definition "bool_array_set_delete_imp x Xi = do { _ \<leftarrow> Array.upd x False Xi; return () }"
definition "bool_array_set_isin_imp Xi x = Array.nth Xi x"

text \<open>Keys of any type, mapped injectively into \<open>{..<N}\<close> by \<open>idx\<close>: the array holds the image
      of the set.\<close>

lemma bool_array_set_idx_fixed_univ_set_imp:
  assumes "inj_on idx K" "\<And> k. k \<in> K \<Longrightarrow> idx k < N"
  shows "fixed_univ_set_imp K (\<lambda> S. S \<subseteq> K) id {} insert (\<lambda> x S. S - {x}) (\<lambda> S x. x \<in> S)
     (\<lambda> S. bool_array_set_assn N (idx ` S)) (Array.new N False)
     (\<lambda> x. bool_array_set_insert_imp (idx x)) (\<lambda> x. bool_array_set_delete_imp (idx x))
     (\<lambda> Xi x. bool_array_set_isin_imp Xi (idx x))"
  using assms
  by (intro fixed_univ_set_imp.intro fixed_univ_set_basic_imp.intro set_fixed_univ_set
        fixed_univ_set_basic_imp_axioms.intro fixed_univ_set_imp_axioms.intro)
     (sep_auto simp: bool_array_set_insert_imp_def bool_array_set_delete_imp_def
        bool_array_set_isin_imp_def inj_on_image_set_diff[OF assms(1) Diff_subset[THEN order_trans]]
        inj_on_image_mem_iff[OF assms(1)]
        heap: bool_array_set_assn_new bool_array_set_memb_rule bool_array_set_upd_rule)+

lemma bool_array_set_fixed_univ_set_imp:
  "fixed_univ_set_imp {..<n} (\<lambda> X. X \<subseteq> {..<n}) id {} insert (\<lambda> x X. X - {x})
     (\<lambda> X x. x \<in> X) (bool_array_set_assn n) (Array.new n False) bool_array_set_insert_imp
     bool_array_set_delete_imp bool_array_set_isin_imp"
  using bool_array_set_idx_fixed_univ_set_imp[of id "{..<n}" n]
  by simp

text \<open>The Boolean array of a set below \<open>n\<close> at the fixed handle \<open>Vh\<close>.\<close>

lemma bool_array_set_at:
  "fixed_univ_set_basic_imp {..<n} (\<lambda>X. X \<subseteq> {..<n}) id {} insert (\<lambda>x X. X - {x}) (\<lambda>X x. x \<in> X)
     (\<lambda>X a. bool_array_set_assn n X a * \<up>(a = Vh)) bool_array_set_insert_imp
     bool_array_set_delete_imp bool_array_set_isin_imp"
proof -
  interpret ba: fixed_univ_set_basic_imp "{..<n}" "\<lambda>X. X \<subseteq> {..<n}" id "{}" insert "\<lambda>x X. X - {x}"
    "\<lambda>X x. x \<in> X" "bool_array_set_assn n" bool_array_set_insert_imp bool_array_set_delete_imp
    bool_array_set_isin_imp
    by (rule fixed_univ_set_imp.axioms(1)[OF bool_array_set_fixed_univ_set_imp])
  show ?thesis
    by (intro fixed_univ_set_basic_imp.intro ba.fixed_univ_set_axioms
              fixed_univ_set_basic_imp_axioms.intro)
       (sep_auto heap: ba.fixed_univ_set_insert_rule ba.fixed_univ_set_delete_rule
                       ba.fixed_univ_set_isin_rule)+
qed

text \<open>Clearing in place, as the clear operation of the fixed-universe set.\<close>

definition "bool_array_set_clear_unit n Xi = do { _ \<leftarrow> bool_array_set_clear_imp n Xi; return () }"

lemma bool_array_set_fixed_univ_set_clear_imp:
  "fixed_univ_set_clear_imp {..<n} (\<lambda> X. X \<subseteq> {..<n}) id {} insert (\<lambda> x X. X - {x})
     (\<lambda> X x. x \<in> X) (bool_array_set_assn n) bool_array_set_insert_imp bool_array_set_delete_imp
     bool_array_set_isin_imp (bool_array_set_clear_unit n)"
proof-
  interpret fixed_univ_set_imp "{..<n}" "\<lambda> X. X \<subseteq> {..<n}" id "{}" insert "\<lambda> x X. X - {x}"
    "\<lambda> X x. x \<in> X" "bool_array_set_assn n" "Array.new n False" bool_array_set_insert_imp
    bool_array_set_delete_imp bool_array_set_isin_imp
    by (rule bool_array_set_fixed_univ_set_imp)
  show ?thesis
    by unfold_locales
       (sep_auto simp: bool_array_set_clear_unit_def
          heap: ht_cons_pre[OF bool_array_set_len bool_array_set_clear_rule])
qed

end
