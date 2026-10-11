theory Imp_Bool_Set
  imports Imp_Range_Iteration Data_Structures.Fixed_Univ_Set_Specs_Imp
begin

section \<open>Sets of Nats below a Bound as Boolean Arrays\<close>

text \<open>The array holds exactly the characteristic list of the set.\<close>

definition xset_assn :: "nat \<Rightarrow> nat set \<Rightarrow> bool array \<Rightarrow> assn" where
  "xset_assn n X Xi = Xi \<mapsto>\<^sub>a map (\<lambda> i. i \<in> X) [0..<n] * \<up>(X \<subseteq> {..<n})"

lemma xset_assn_new: "<emp> Array.new n False <xset_assn n {}>"
  unfolding xset_assn_def by (sep_auto simp: map_replicate_const)

text \<open>Binding a freshly allocated object to a continuation.\<close>

lemma alloc_bind:
  assumes "<emp> c <Q>" "\<And> x. <Fm * Q x> f x <Qp>"
  shows "<Fm> c \<bind> f <Qp>"
proof-
  have "<emp * Fm> c <\<lambda> x. Q x * Fm>"
    by (rule ht_frame[OF assms(1)])
  then have "<Fm> c <\<lambda> x. Fm * Q x>"
    by (simp only: assn_one_left mult.commute[of "Q _" Fm])
  then show ?thesis
    by (rule ht_bind) (rule assms(2))
qed

lemma xset_of_list_rule:
  "<\<up>(xs = map (\<lambda> i. i \<in> X) [0..<n] \<and> X \<subseteq> {..<n})> Array.of_list xs <xset_assn n X>"
  unfolding xset_assn_def by sep_auto

lemma xset_memb_rule:
  "<xset_assn n X Xi * \<up>(i < n)> Array.nth Xi i <\<lambda> r. xset_assn n X Xi * \<up>(r \<longleftrightarrow> i \<in> X)>"
  unfolding xset_assn_def by sep_auto

lemma map_mem_update:
  "i < n \<Longrightarrow>
   (map (\<lambda> j. j \<in> X) [0..<n])[i := b] = map (\<lambda> j. j \<in> (if b then insert i X else X - {i})) [0..<n]"
  by (rule nth_equalityI) (auto simp: nth_list_update)

lemma xset_upd_rule:
  "<xset_assn n X Xi * \<up>(i < n)> Array.upd i b Xi
     <\<lambda> r. xset_assn n (if b then insert i X else X - {i}) Xi * \<up>(r = Xi)>"
  unfolding xset_assn_def by (sep_auto simp: map_mem_update split: if_split)

text \<open>An array of length \<open>n\<close> with arbitrary content, e.g. a workspace array between two
  uses; it is cleared in place.\<close>

definition len_assn :: "nat \<Rightarrow> 'a::heap array \<Rightarrow> assn" where
  "len_assn n a = (\<exists>\<^sub>A l. a \<mapsto>\<^sub>a l * \<up>(length l = n))"

lemma len_assn_new: "<emp> Array.new n x <len_assn n>"
  unfolding len_assn_def by sep_auto

lemma xset_len: "xset_assn n X Xi \<Longrightarrow>\<^sub>A len_assn n Xi"
  unfolding xset_assn_def len_assn_def by sep_auto

definition "xset_clear_imp n Xi = fill_range_imp (\<lambda> _. False) n Xi"

lemma xset_clear_rule: "<len_assn n Xi> xset_clear_imp n Xi <\<lambda> r. xset_assn n {} Xi * \<up>(r = Xi)>"
proof-
  have "<Xi \<mapsto>\<^sub>a l * \<up>(length l = n)> xset_clear_imp n Xi <\<lambda> r. xset_assn n {} Xi * \<up>(r = Xi)>" for l
    unfolding xset_clear_imp_def
    by (rule ht_cons_post[OF fill_range_imp_rule]) (sep_auto simp: xset_assn_def)
  then show ?thesis
    unfolding len_assn_def by (rule ht_ex_pre)
qed

section \<open>An Abstract Imperative Set of Nats below a Bound\<close>

text \<open>The interface through which the algorithms see a solution: a membership test and
  insertion and deletion, which are idempotent. The handle may carry further data that its
  operations keep up to date (e.g. for oracles).\<close>

text \<open>Copying the set into a Boolean array, in place.\<close>

locale imp_nat_set_spec =
  fixes n :: nat
    and smemb_imp :: "nat \<Rightarrow> 'si \<Rightarrow> bool Heap"
begin

definition "bcopy_imp Si Bi = copy_range_imp (\<lambda> i. smemb_imp i Si) n Bi"

end

locale imp_nat_set =
  fixes n :: nat
    and sol_assn :: "nat set \<Rightarrow> 'si \<Rightarrow> assn"
    and smemb_imp :: "nat \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and sins_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and sdel_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
  assumes sol_bound: "sol_assn X Si \<Longrightarrow>\<^sub>A sol_assn X Si * \<up>(X \<subseteq> {..<n})"
    and smemb_rule: "<sol_assn X Si * \<up>(x < n)> smemb_imp x Si <\<lambda> r. sol_assn X Si * \<up>(r = (x \<in> X))>"
    and sins_rule: "<sol_assn X Si * \<up>(x < n)> sins_imp x Si <\<lambda> _. sol_assn (insert x X) Si>"
    and sdel_rule: "<sol_assn X Si * \<up>(x < n)> sdel_imp x Si <\<lambda> _. sol_assn (X - {x}) Si>"
begin

sublocale imp_nat_set_spec n smemb_imp .

lemma bcopy_rule: "<sol_assn X Si * len_assn n Bi> bcopy_imp Si Bi <\<lambda> _. sol_assn X Si * xset_assn n X Bi>"
proof-
  have m: "<sol_assn X Si> smemb_imp i Si <\<lambda> r. sol_assn X Si * \<up>(r = (i \<in> X))>" if "i < n" for i
    using smemb_rule[of X Si i] that by simp
  have c: "<Bi \<mapsto>\<^sub>a l * sol_assn X Si * \<up>(length l = n)> bcopy_imp Si Bi
           <\<lambda> _. Bi \<mapsto>\<^sub>a map (\<lambda> i. i \<in> X) [0..<n] * sol_assn X Si>" for l
    unfolding bcopy_imp_def by (rule copy_range_imp_rule[OF m])
  have e: "Bi \<mapsto>\<^sub>a map (\<lambda> i. i \<in> X) [0..<n] * sol_assn X Si \<Longrightarrow>\<^sub>A sol_assn X Si * xset_assn n X Bi"
    by (rule ent_trans[OF ent_star_mono[OF ent_refl sol_bound]]) (sep_auto simp: xset_assn_def)
  have c': "<Bi \<mapsto>\<^sub>a l * sol_assn X Si * \<up>(length l = n)> bcopy_imp Si Bi
            <\<lambda> _. sol_assn X Si * xset_assn n X Bi>" for l
    by (rule ht_cons_post[OF c], rule ent_true_drop(2), rule e)
  show ?thesis
    unfolding len_assn_def
    by (sep_auto heap: c')
qed

end

section \<open>The Boolean Arrays as Fixed-Universe Sets\<close>

text \<open>The functional model of a Boolean array of length \<open>n\<close> is the set itself, a subset of the
      universe \<open>{..<n}\<close>.\<close>

definition "xset_insert_imp x Xi = do { _ \<leftarrow> Array.upd x True Xi; return () }"
definition "xset_delete_imp x Xi = do { _ \<leftarrow> Array.upd x False Xi; return () }"
definition "xset_isin_imp Xi x = Array.nth Xi x"

lemma xset_fixed_univ_set_imp:
  "fixed_univ_set_imp {..<n} (\<lambda> X. X \<subseteq> {..<n}) id {} insert (\<lambda> x X. X - {x})
     (\<lambda> X x. x \<in> X) (xset_assn n) (Array.new n False) xset_insert_imp xset_delete_imp
     xset_isin_imp"
  by unfold_locales
     (sep_auto simp: xset_insert_imp_def xset_delete_imp_def xset_isin_imp_def
               heap: xset_assn_new xset_memb_rule xset_upd_rule)+

end
