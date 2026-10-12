theory Imp_Array_Ring_Queue
  imports
    Imp_Array_Fun
    Bounded_Queue_Specs_Imp
begin

section \<open>Bounded Queues as Ring Buffers\<close>

text \<open>A FIFO queue of capacity \<open>cap\<close>: an array of length \<open>cap\<close>, allocated once, holding the
      elements from position \<open>h\<close> on, cyclically, and the number \<open>sz\<close> of elements. Pushing and
      popping take a constant number of array accesses; positions wrap around by one subtraction.
      The functional model is the array as a function together with \<open>h\<close> and \<open>sz\<close>.\<close>

type_synonym 'a arq = "(nat \<Rightarrow> 'a) \<times> nat \<times> nat"

definition wrap :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "wrap cap i = (if i < cap then i else i - cap)"

lemma wrap_mod: "i < 2 * cap \<Longrightarrow> wrap cap i = i mod cap"
  by (cases "i < cap") (simp_all add: wrap_def le_mod_geq)

definition arq_empty :: "'a \<Rightarrow> 'a arq" where
  "arq_empty d = ((\<lambda> _. d), 0, 0)"

definition arq_push :: "nat \<Rightarrow> 'a arq \<Rightarrow> 'a \<Rightarrow> 'a arq" where
  "arq_push cap = (\<lambda> (A, h, sz) x. (A(wrap cap (h + sz) := x), h, Suc sz))"

definition arq_pop :: "nat \<Rightarrow> 'a arq \<Rightarrow> 'a \<times> 'a arq" where
  "arq_pop cap = (\<lambda> (A, h, sz). (A h, (A, wrap cap (Suc h), sz - 1)))"

definition arq_is_empty :: "'a arq \<Rightarrow> bool" where
  "arq_is_empty = (\<lambda> (A, h, sz). sz = 0)"

definition arq_invar :: "nat \<Rightarrow> 'a arq \<Rightarrow> bool" where
  "arq_invar cap = (\<lambda> (A, h, sz). sz \<le> cap \<and> (0 < cap \<longrightarrow> h < cap))"

definition arq_abstract :: "nat \<Rightarrow> 'a arq \<Rightarrow> 'a list" where
  "arq_abstract cap = (\<lambda> (A, h, sz). map (\<lambda> i. A ((h + i) mod cap)) [0..<sz])"

lemma mod_neq_below:
  fixes h i j cap :: nat
  assumes "i < j" "j < cap"
  shows "(h + i) mod cap \<noteq> (h + j) mod cap"
proof
  assume "(h + i) mod cap = (h + j) mod cap"
  hence "cap dvd (h + j) - (h + i)"
    using mod_eq_dvd_iff_nat[of "h + i" "h + j" cap] assms(1) by simp
  hence "cap dvd j - i"
    by simp
  thus False
    using assms nat_dvd_not_less[of "j - i" cap] by simp
qed

lemma arq_bounded_queue:
  "bounded_queue cap (arq_invar cap) (arq_abstract cap) (arq_empty d) (arq_push cap) (arq_pop cap)
     arq_is_empty"
proof(unfold_locales, goal_cases)
  case (1 Q)
  thus ?case
    by (cases Q) (simp add: arq_invar_def arq_abstract_def)
next
  case 2
  show ?case
    by (simp add: arq_invar_def arq_empty_def)
next
  case 3
  show ?case
    by (simp add: arq_abstract_def arq_empty_def)
next
  case (4 Q x)
  thus ?case
    by (cases Q) (auto simp add: arq_invar_def arq_abstract_def arq_push_def)
next
  case (5 Q x)
  obtain A h sz where Q: "Q = (A, h, sz)"
    by (cases Q) auto
  have I: "sz < cap" "h < cap"
    using 5 by (auto simp add: arq_invar_def arq_abstract_def Q)
  have w: "wrap cap (h + sz) = (h + sz) mod cap"
    using I by (simp add: wrap_mod)
  have "map (\<lambda> i. (A((h + sz) mod cap := x)) ((h + i) mod cap)) [0..<sz] =
        map (\<lambda> i. A ((h + i) mod cap)) [0..<sz]"
    using mod_neq_below[of _ sz cap h] I(1) by (intro map_cong) auto
  thus ?case
    by (simp add: arq_abstract_def arq_push_def Q w)
next
  case (6 Q)
  thus ?case
    by (cases Q) (auto simp add: arq_invar_def arq_abstract_def arq_pop_def wrap_def)
next
  case (7 Q)
  obtain A h sz where Q: "Q = (A, h, sz)"
    by (cases Q) auto
  have "0 < sz" "h < cap"
    using 7 by (auto simp add: arq_invar_def arq_abstract_def Q)
  thus ?case
    by (simp add: arq_abstract_def arq_pop_def Q hd_map upt_conv_Cons)
next
  case (8 Q)
  obtain A h sz where Q: "Q = (A, h, sz)"
    by (cases Q) auto
  have I: "0 < sz" "h < cap"
    using 8 by (auto simp add: arq_invar_def arq_abstract_def Q)
  have w: "wrap cap (Suc h) = Suc h mod cap"
    using I by (simp add: wrap_mod)
  have "[0..<sz] = 0 # map Suc [0..<sz - 1]"
    using I(1) by (simp add: upt_conv_Cons map_Suc_upt)
  hence "tl (map (\<lambda> i. A ((h + i) mod cap)) [0..<sz]) =
         map (\<lambda> i. A ((Suc h mod cap + i) mod cap)) [0..<sz - 1]"
    by (simp add: mod_add_left_eq)
  thus ?case
    by (simp add: arq_abstract_def arq_pop_def Q w)
next
  case (9 Q)
  thus ?case
    by (cases Q) (simp add: arq_is_empty_def arq_abstract_def)
qed

section \<open>The Arrays\<close>

type_synonym 'a arqi = "'a array \<times> nat ref \<times> nat ref"

fun arq_assn :: "nat \<Rightarrow> 'a::heap arq \<Rightarrow> 'a arqi \<Rightarrow> assn" where
  "arq_assn cap (A, h, sz) (Aa, hr, sr) = array_fun_assn cap A Aa * hr \<mapsto>\<^sub>r h * sr \<mapsto>\<^sub>r sz"

definition arq_empty_imp :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a arqi Heap" where
  "arq_empty_imp cap d = do { Aa \<leftarrow> Array.new cap d; hr \<leftarrow> ref 0; sr \<leftarrow> ref 0; return (Aa, hr, sr) }"

definition arq_push_imp :: "nat \<Rightarrow> 'a::heap arqi \<Rightarrow> 'a \<Rightarrow> unit Heap" where
  "arq_push_imp cap = (\<lambda> (Aa, hr, sr) x. do {
     h \<leftarrow> !hr; s \<leftarrow> !sr;
     _ \<leftarrow> Array.upd (wrap cap (h + s)) x Aa;
     sr := Suc s })"

definition arq_pop_imp :: "nat \<Rightarrow> 'a::heap arqi \<Rightarrow> 'a Heap" where
  "arq_pop_imp cap = (\<lambda> (Aa, hr, sr). do {
     h \<leftarrow> !hr; s \<leftarrow> !sr;
     x \<leftarrow> Array.nth Aa h;
     hr := wrap cap (Suc h);
     sr := s - 1;
     return x })"

definition arq_is_empty_imp :: "'a::heap arqi \<Rightarrow> bool Heap" where
  "arq_is_empty_imp = (\<lambda> (Aa, hr, sr). do { s \<leftarrow> !sr; return (s = 0) })"

lemma arq_bounded_queue_imp:
  "bounded_queue_imp cap (arq_invar cap) (arq_abstract cap) (arq_empty d) (arq_push cap) (arq_pop cap)
     arq_is_empty (arq_assn cap) (arq_empty_imp cap d) (arq_push_imp cap) (arq_pop_imp cap)
     arq_is_empty_imp"
proof-
  show ?thesis
  proof(intro bounded_queue_imp.intro[OF arq_bounded_queue] bounded_queue_imp_axioms.intro, goal_cases)
    case 1
    show ?case
      unfolding arq_empty_imp_def arq_empty_def by (sep_auto heap: array_fun_assn_new)
  next
    case (2 Q Qi x)
    obtain A h sz where Q: "Q = (A, h, sz)"
      by (cases Q) auto
    have "wrap cap (h + sz) < cap"
      using 2 by (auto simp add: arq_invar_def arq_abstract_def wrap_def Q)
    thus ?case
      unfolding Q arq_push_imp_def arq_push_def
      by (cases Qi) (sep_auto heap: array_fun_upd_rule)
  next
    case (3 Q Qi)
    obtain A h sz where Q: "Q = (A, h, sz)"
      by (cases Q) auto
    have "h < cap"
      using 3 by (auto simp add: arq_invar_def arq_abstract_def Q)
    thus ?case
      unfolding Q arq_pop_imp_def arq_pop_def
      by (cases Qi) (sep_auto heap: array_fun_lookup_rule)
  next
    case (4 Q Qi)
    show ?case
      unfolding arq_is_empty_imp_def arq_is_empty_def
      by (cases Q; cases Qi) sep_auto
  qed
qed

end
