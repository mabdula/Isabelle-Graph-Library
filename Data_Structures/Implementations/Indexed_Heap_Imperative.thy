theory Indexed_Heap_Imperative
  imports Indexed_Heap   Data_Structures.Fixed_Univ_Key_Value_Queue_Specs_Imp
begin

section \<open>An Indexed Binary Min-Heap in Imperative HOL\<close>

text \<open>The heap of \<open>Indexed_Heap\<close> over the universe \<open>{..<n}\<close>. It
      consists of

        \<^item> the heap array \<open>H\<close> of size \<open>n\<close>, whose first \<open>sz\<close> entries are the heap list,
        \<^item> the position array \<open>P\<close>, mapping every element in the heap to its index in \<open>H\<close>,
        \<^item> the key array \<open>K\<close>, mapping every element in the heap to its (concrete) key, and
        \<^item> a reference holding the size \<open>sz\<close>.

      All memory is allocated once by the empty operation; the other operations work in place.
      The sifting loops move a \<^emph>\<open>hole\<close> instead of swapping: the sifted element and its key are
      kept in registers and written only once, at the final position. Entries of \<open>P\<close> and \<open>K\<close> for
      elements not in the heap are irrelevant, so neither is ever reset.

      Keys are compared concretely; the functional keys are their images under the strictly
      monotone @{term queue_key}, so both comparisons agree.\<close>

type_synonym 'ai heap_imp = "nat array \<times> nat array \<times> 'ai array \<times> nat ref"

subsection \<open>Programs\<close>

text \<open>The programs are global definitions, independent of the proof locale below, so that
      they can be used by the global interpretations of the algorithms and for code generation.
      The sifting loops move a hole; the key of the sifted element is kept in a register.\<close>

partial_function (heap) sift_up_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'ai::{heap, linorder} array \<Rightarrow> nat \<Rightarrow> 'ai \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "sift_up_imp Ha Pa Ka x kx i =
     (if i = 0 then do { Array.upd 0 x Ha; Array.upd x 0 Pa; return () }
      else do {
        let p = parent i;
        y \<leftarrow> Array.nth Ha p;
        ky \<leftarrow> Array.nth Ka y;
        if kx < ky then do {
          Array.upd i y Ha;
          Array.upd y i Pa;
          sift_up_imp Ha Pa Ka x kx p
        } else do { Array.upd i x Ha; Array.upd x i Pa; return () }
      })"

definition min_child_imp :: "nat array \<Rightarrow> 'ai::{heap, linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> 'ai) Heap" where
  "min_child_imp Ha Ka sz l = do {
     a \<leftarrow> Array.nth Ha l;
     ka \<leftarrow> Array.nth Ka a;
     if Suc l < sz then do {
       b \<leftarrow> Array.nth Ha (Suc l);
       kb \<leftarrow> Array.nth Ka b;
       return (if kb < ka then (Suc l, b, kb) else (l, a, ka))
     } else return (l, a, ka)
   }"

partial_function (heap) sift_down_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'ai::{heap, linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'ai \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "sift_down_imp Ha Pa Ka sz x kx i =
     (if 2 * i + 1 < sz then do {
        (c, z, kz) \<leftarrow> min_child_imp Ha Ka sz (2 * i + 1);
        if kz < kx then do {
          Array.upd i z Ha;
          Array.upd z i Pa;
          sift_down_imp Ha Pa Ka sz x kx c
        } else do { Array.upd i x Ha; Array.upd x i Pa; return () }
      } else do { Array.upd i x Ha; Array.upd x i Pa; return () })"

definition heap_empty_imp :: "nat \<Rightarrow> 'ai::heap \<Rightarrow> 'ai heap_imp Heap" where
  "heap_empty_imp n k0 = do {
     Ha \<leftarrow> Array.new n 0;
     Pa \<leftarrow> Array.new n 0;
     Ka \<leftarrow> Array.new n k0;
     Sr \<leftarrow> ref 0;
     return (Ha, Pa, Ka, Sr)
   }"

definition heap_insert_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> nat \<Rightarrow> 'ai \<Rightarrow> unit Heap" where
  "heap_insert_imp Hi x k = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     sz \<leftarrow> !Sr;
     Array.upd x k Ka;
     Sr := Suc sz;
     sift_up_imp Ha Pa Ka x k sz
   })"

definition heap_decrease_key_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> nat \<Rightarrow> 'ai \<Rightarrow> unit Heap" where
  "heap_decrease_key_imp Hi x k = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     i \<leftarrow> Array.nth Pa x;
     Array.upd x k Ka;
     sift_up_imp Ha Pa Ka x k i
   })"

definition heap_extract_min_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> nat option Heap" where
  "heap_extract_min_imp Hi = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     sz \<leftarrow> !Sr;
     if sz = 0 then return None
     else do {
       x \<leftarrow> Array.nth Ha 0;
       Sr := sz - 1;
       if sz - 1 = 0 then return (Some x)
       else do {
         y \<leftarrow> Array.nth Ha (sz - 1);
         ky \<leftarrow> Array.nth Ka y;
         sift_down_imp Ha Pa Ka (sz - 1) y ky 0;
         return (Some x)
       }
     }
   })"

definition heap_extract_min_key_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> (nat \<times> 'ai) option Heap" where
  "heap_extract_min_key_imp Hi = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     sz \<leftarrow> !Sr;
     if sz = 0 then return None
     else do {
       x \<leftarrow> Array.nth Ha 0;
       k \<leftarrow> Array.nth Ka x;
       r \<leftarrow> heap_extract_min_imp Hi;
       return (map_option (\<lambda>y. (y, k)) r) } })"

locale indexed_heap_imp =
  fixes n :: nat
    and U :: "nat set"
    and queue_key :: "'ai::{heap, linorder} \<Rightarrow> 'a::linorder"
    and k0 :: 'ai
  assumes U_bound: "U \<subseteq> {..<n}"
      and key_less_iff: "\<And>a b. queue_key a < queue_key b \<longleftrightarrow> a < b"
begin

subsection \<open>Representation\<close>

text \<open>The arrays represent the heap list @{term hs}: they agree with it on its positions. While an
      element is sifted, the position @{term i} of the hole is excepted.\<close>

definition heap_rel :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "heap_rel hs hl pl \<longleftrightarrow> length hl = n \<and> length pl = n \<and>
     (\<forall>j<length hs. hl ! j = hs ! j \<and> pl ! (hs ! j) = j)"

definition hole_rel :: "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "hole_rel hs i hl pl \<longleftrightarrow> length hl = n \<and> length pl = n \<and>
     (\<forall>j<length hs. j \<noteq> i \<longrightarrow> hl ! j = hs ! j \<and> pl ! (hs ! j) = j)"

definition key_rel :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat list \<Rightarrow> 'ai list \<Rightarrow> bool" where
  "key_rel ks hs kl \<longleftrightarrow> length kl = n \<and> (\<forall>v\<in>set hs. queue_key (kl ! v) = ks v)"

fun heap_assn :: "'a iheap \<Rightarrow> 'ai heap_imp \<Rightarrow> assn" where
  "heap_assn (hs, ks) (Ha, Pa, Ka, Sr) =
     (\<exists>\<^sub>Ahl pl kl. Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl * Sr \<mapsto>\<^sub>r length hs *
        \<up>(heap_rel hs hl pl \<and> key_rel ks hs kl \<and> length hs \<le> n))"

lemma heap_rel_hole: "heap_rel hs hl pl \<Longrightarrow> hole_rel hs i hl pl"
  unfolding heap_rel_def hole_rel_def
  by auto

lemma hole_fill:
  "\<lbrakk>hole_rel hs i hl pl; i < length hs; distinct hs; set hs \<subseteq> {..<n}\<rbrakk>
    \<Longrightarrow>
    heap_rel hs (hl[i := hs ! i]) (pl[hs ! i := i])"
  using More_Lists.distinct_length_le[of hs n] nth_mem[of i hs]
  unfolding heap_rel_def hole_rel_def
  by (auto simp: nth_list_update nth_eq_iff_index_eq subset_eq)

lemma hole_step:
  "\<lbrakk>hole_rel hs i hl pl; i < length hs; p < length hs; p \<noteq> i; distinct hs;
    set hs \<subseteq> {..<n}\<rbrakk> \<Longrightarrow>
    hole_rel (hs[i := hs ! p, p := hs ! i]) p (hl[i := hs ! p]) (pl[hs ! p := i])"
  using More_Lists.distinct_length_le[of hs n] nth_mem[of p hs]
  unfolding hole_rel_def
  by (auto simp: nth_list_update nth_eq_iff_index_eq subset_eq)

lemma key_rel_len: "key_rel ks hs kl \<Longrightarrow> length kl = n"
  unfolding key_rel_def
  by simp

lemma key_rel_perm: "\<lbrakk>key_rel ks hs kl; set hs' = set hs\<rbrakk> \<Longrightarrow> key_rel ks hs' kl"
  unfolding key_rel_def
  by simp

lemma key_rel_upd:
  "\<lbrakk>key_rel ks hs kl; x < n; set hs' \<subseteq> insert x (set hs)\<rbrakk>
   \<Longrightarrow> key_rel (ks(x := queue_key k)) hs' (kl[x := k])"
  unfolding key_rel_def
  by (auto simp: nth_list_update)

lemma key_less_rel:
  "\<lbrakk>key_rel ks hs kl; x \<in> set hs; y \<in> set hs\<rbrakk> \<Longrightarrow>
    kl ! x < kl ! y \<longleftrightarrow> ks x < ks y"
  using key_less_iff[of "kl ! x" "kl ! y"]
  by (simp add: key_rel_def)

subsection \<open>Sifting up\<close>

lemma sift_up_imp_rule:
  assumes "i < length hs" "hs ! i = x" "distinct hs" "set hs \<subseteq> {..<n}"
    "hole_rel hs i hl pl" "key_rel ks hs kl" "queue_key kx = ks x"
  shows "<Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl> sift_up_imp Ha Pa Ka x kx i
         <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
              \<up>(heap_rel (sift_up ks hs i) hl' pl')>"
  using assms
proof(induction i arbitrary: hs hl pl rule: less_induct)
  case (less i)
  have "length hl = n" "length pl = n" "length kl = n" "length hs \<le> n" "x < n"
    using less.prems More_Lists.distinct_length_le[of hs n] nth_mem[of i hs]
    by (auto simp: hole_rel_def key_rel_def)
  show ?case
  proof(cases "i = 0")
    case True
    thus ?thesis
      using less.prems hole_fill[of hs i hl pl] \<open>length hl = n\<close> \<open>length pl = n\<close> \<open>x < n\<close>
      by (subst sift_up_imp.simps) (sep_auto)
  next
    case False
    moreover have "kx < kl ! (hs ! parent i) \<longleftrightarrow> ks x < ks (hs ! parent i)"
      "hl ! parent i = hs ! parent i" "hs ! parent i < n"
      using less.prems False key_less_iff[of kx "kl ! (hs ! parent i)"] parent_less_trans[of i "length hs"]
        nth_mem[of "parent i" hs] parent_less[of i, THEN less_imp_neq]
      by (auto simp: key_rel_def hole_rel_def subset_eq)
    moreover have [sep_heap_rules]:
      "<Ha \<mapsto>\<^sub>a hl[i := hs ! parent i] * Pa \<mapsto>\<^sub>a pl[hs ! parent i := i] *
        Ka \<mapsto>\<^sub>a kl>
        sift_up_imp Ha Pa Ka x kx (parent i)
      <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' *
         Ka \<mapsto>\<^sub>a kl * \<up>(heap_rel
           (sift_up ks (hs[i := hs ! parent i, parent i := hs ! i]) (parent i)) hl' pl')>"
      by (intro less.IH)
         (use less.prems False hole_step[of hs i hl pl "parent i"]
           parent_less_trans[of i "length hs"] parent_less[of i] parent_less[of i, THEN less_imp_neq] key_rel_perm[of ks hs kl]
           in \<open>auto\<close>)
    ultimately show ?thesis
      using less.prems hole_fill[of hs i hl pl] parent_less_trans[of i "length hs"]
        \<open>length hl = n\<close> \<open>length pl = n\<close> \<open>length kl = n\<close>
        \<open>x < n\<close>
      by (subst sift_up_imp.simps) (sep_auto simp: sift_up_rec sift_up_stop)
  qed
qed

subsection \<open>Sifting down\<close>

text \<open>The smaller child of the hole, together with its element and key, read once each.\<close>

lemma key_rel_mono:
  "\<lbrakk>key_rel ks hs kl; set hs' \<subseteq> set hs\<rbrakk> \<Longrightarrow> key_rel ks hs' kl"
  unfolding key_rel_def
  by auto

lemma min_child_imp_rule:
  assumes "2 * i + 1 < length hs" "distinct hs" "set hs \<subseteq> {..<n}" "hole_rel hs i hl pl"
    "key_rel ks hs kl"
  shows "<Ha \<mapsto>\<^sub>a hl * Ka \<mapsto>\<^sub>a kl> min_child_imp Ha Ka (length hs) (2 * i + 1)
         <\<lambda>r. Ha \<mapsto>\<^sub>a hl * Ka \<mapsto>\<^sub>a kl *
              \<up>(r = (min_child ks hs i, hs ! min_child ks hs i, kl ! (hs ! min_child ks hs i)))>"
  using assms More_Lists.distinct_length_le[of hs n] nth_mem[of "2 * i + 1" hs] nth_mem[of "Suc (2 * i + 1)" hs]
    key_less_rel[of ks hs kl "hs ! Suc (2 * i + 1)" "hs ! (2 * i + 1)"]
  unfolding min_child_imp_def min_child_def
  by (sep_auto simp: hole_rel_def key_rel_def subset_eq)

lemma sift_down_imp_rule:
  assumes "i < length hs" "hs ! i = x" "distinct hs" "set hs \<subseteq> {..<n}"
    "hole_rel hs i hl pl" "key_rel ks hs kl" "queue_key kx = ks x"
  shows "<Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl> sift_down_imp Ha Pa Ka (length hs) x kx i
         <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
              \<up>(heap_rel (sift_down ks hs i) hl' pl')>"
  using assms
proof(induction ks hs i arbitrary: hl pl rule: sift_down.induct)
  case (1 ks hs i)
  have "length hl = n" "length pl = n" "length kl = n" "length hs \<le> n" "x < n"
    using "1.prems" More_Lists.distinct_length_le[of hs n] nth_mem[of i hs]
    by (auto simp: hole_rel_def key_rel_def)
  moreover have
    "kl ! (hs ! min_child ks hs i) < kx \<longleftrightarrow> ks (hs ! min_child ks hs i) < ks x"
    "hs ! min_child ks hs i < n" if "2 * i + 1 < length hs"
    using "1.prems" that key_less_iff[of "kl ! (hs ! min_child ks hs i)" kx]
      min_child_bounds[of i hs ks]
      nth_mem[of "min_child ks hs i" hs]
    by (auto simp: key_rel_def subset_eq)
  moreover have [sep_heap_rules]:
    "<Ha \<mapsto>\<^sub>a hl[i := hs ! min_child ks hs i] * Pa \<mapsto>\<^sub>a pl[hs ! min_child ks hs i := i] *
      Ka \<mapsto>\<^sub>a kl>
      sift_down_imp Ha Pa Ka (length hs) x kx (min_child ks hs i)
    <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
       \<up>(heap_rel (sift_down ks
       (hs[i := hs ! min_child ks hs i, min_child ks hs i := hs ! i]) (min_child ks hs i)) hl' pl')>"
    if "2 * i + 1 < length hs \<and> ks (hs ! min_child ks hs i) < ks x"
    by (intro "1.IH"[simplified length_list_update])
       (use "1.prems" that min_child_bounds[of i hs ks] hole_step[of hs i hl pl "min_child ks hs i"]
         key_rel_perm[of ks hs kl] in \<open>auto\<close>)
  ultimately show ?case
    using "1.prems" hole_fill[of hs i hl pl] min_child_bounds[of i hs ks]
    by (subst sift_down_imp.simps)
       (sep_auto heap: min_child_imp_rule simp: sift_down_stop sift_down.simps[of ks hs i])
qed

subsection \<open>Operations\<close>

lemma heap_empty_imp_rule: "<emp> heap_empty_imp n k0 <\<lambda>Hi. heap_assn heap_empty Hi>"
  unfolding heap_empty_imp_def heap_empty_def
  by (sep_auto simp: heap_rel_def key_rel_def)

lemma heap_rel_len: "heap_rel hs hl pl \<Longrightarrow> length hl = n \<and> length pl = n"
  unfolding heap_rel_def
  by simp

lemma heap_rel_lengths:
  "heap_rel hs hl pl \<Longrightarrow> length hl = n" "heap_rel hs hl pl \<Longrightarrow> length pl = n"
  unfolding heap_rel_def
  by simp_all

lemma heap_rel_nth: "\<lbrakk>heap_rel hs hl pl; j < length hs\<rbrakk> \<Longrightarrow> hl ! j = hs ! j"
  unfolding heap_rel_def
  by simp

lemma heap_rel_pos: "\<lbrakk>heap_rel hs hl pl; x \<in> set hs\<rbrakk> \<Longrightarrow> pl ! x = idx hs x"
  unfolding heap_rel_def
  using idx_less[of x hs]
  by (auto dest: spec[where x = "idx hs x"])

lemma heap_rel_hole_snoc: "heap_rel hs hl pl \<Longrightarrow> hole_rel (hs @ [x]) (length hs) hl pl"
  unfolding heap_rel_def hole_rel_def
  by (auto simp: nth_append)

lemma heap_insert_imp_rule:
  assumes "heap_invar U (hs, ks)" "x \<in> U" "\<nexists> k. (x, k) \<in> heap_abstract (hs, ks)"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_insert_imp (Ha, Pa, Ka, Sr) x k
         <\<lambda>_. heap_assn (heap_insert (hs, ks) x (queue_key k)) (Ha, Pa, Ka, Sr)>"
proof-
  have "distinct (hs @ [x])" "set (hs @ [x]) \<subseteq> {..<n}" "x < n"
    using assms U_bound
    by (auto simp: heap_abstract_iff simp del: heap_abstract.simps)
  moreover hence "length (sift_up (ks(x := queue_key k)) (hs @ [x]) (length hs)) = Suc (length hs)"
    "set (sift_up (ks(x := queue_key k)) (hs @ [x]) (length hs)) = insert x (set hs)"
    "length (hs @ [x]) \<le> n"
    using sift_up_perm[of "length hs" "hs @ [x]" "ks(x := queue_key k)"]
      More_Lists.distinct_length_le[of "hs @ [x]" n]
    by auto
  moreover have [sep_heap_rules]: "\<lbrakk>heap_rel hs hl pl; key_rel ks hs kl\<rbrakk> \<Longrightarrow>
      <Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl[x := k]> sift_up_imp Ha Pa Ka x k (length hs)
      <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl[x := k] *
           \<up>(heap_rel (sift_up (ks(x := queue_key k)) (hs @ [x]) (length hs)) hl' pl')>" for hl pl kl
    by (rule sift_up_imp_rule)
       (use calculation in \<open>auto intro: heap_rel_hole_snoc key_rel_upd\<close>)
  ultimately show ?thesis
    unfolding heap_insert_imp_def heap_assn.simps heap_insert.simps
    by (sep_auto simp: key_rel_len intro: key_rel_upd)
qed

lemma heap_decrease_key_imp_rule:
  assumes "heap_invar U (hs, ks)" "x \<in> U" "(x, k') \<in> heap_abstract (hs, ks)"
    "queue_key k < k'"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_decrease_key_imp (Ha, Pa, Ka, Sr) x k
         <\<lambda>_. heap_assn (heap_decrease_key (hs, ks) x (queue_key k)) (Ha, Pa, Ka, Sr)>"
proof-
  have "distinct hs" "set hs \<subseteq> {..<n}" "x \<in> set hs" "x < n" "idx hs x < length hs"
    "hs ! idx hs x = x"
    using assms U_bound idx_less[of x hs]
    by (auto simp: heap_abstract_iff simp del: heap_abstract.simps)
  moreover hence "length (sift_up (ks(x := queue_key k)) hs (idx hs x)) = length hs"
    "set (sift_up (ks(x := queue_key k)) hs (idx hs x)) = set hs"
    using sift_up_perm[of "idx hs x" hs "ks(x := queue_key k)"]
    by auto
  moreover have [sep_heap_rules]: "\<lbrakk>heap_rel hs hl pl; key_rel ks hs kl\<rbrakk> \<Longrightarrow>
      <Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl[x := k]> sift_up_imp Ha Pa Ka x k (idx hs x)
      <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl[x := k] *
           \<up>(heap_rel (sift_up (ks(x := queue_key k)) hs (idx hs x)) hl' pl')>" for hl pl kl
    by (rule sift_up_imp_rule)
       (use calculation in \<open>auto intro: heap_rel_hole key_rel_upd\<close>)
  ultimately show ?thesis
    unfolding heap_decrease_key_imp_def heap_assn.simps heap_decrease_key.simps
    by (sep_auto simp: key_rel_len heap_rel_pos intro: key_rel_upd dest: heap_rel_len)
qed

lemma heap_rel_hole_extract:
  "\<lbrakk>heap_rel hs hl pl; distinct hs; butlast hs \<noteq> []\<rbrakk> \<Longrightarrow>
    hole_rel ((butlast hs)[0 := last hs]) 0 hl pl"
  using extract_list(3,4)[of hs]
  unfolding heap_rel_def hole_rel_def
  by (auto)

lemma key_rel_nth: "\<lbrakk>key_rel ks hs kl; x \<in> set hs\<rbrakk> \<Longrightarrow> queue_key (kl ! x) = ks x"
  unfolding key_rel_def
  by simp

lemma heap_extract_min_imp_rule:
  assumes "heap_invar U (hs, ks)"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_extract_min_imp (Ha, Pa, Ka, Sr)
         <\<lambda>r. heap_assn (fst (heap_extract_min (hs, ks))) (Ha, Pa, Ka, Sr) *
              \<up>(r = snd (heap_extract_min (hs, ks)))>"
proof(cases "butlast hs = []")
  case True
  hence "hs = [] \<or> (\<exists> a. hs = [a])"
    by (cases hs) (auto split: if_splits)
  thus ?thesis
    unfolding heap_extract_min_imp_def
    by (elim disjE exE) (sep_auto simp: heap_rel_def key_rel_def)+
next
  case False
  have "Suc 0 < length hs"
    using False
    by (cases hs) (auto split: if_splits)
  moreover hence "distinct hs" "set hs \<subseteq> {..<n}" "length hs \<le> n" "hs \<noteq> []"
    "last hs \<in> set hs" "hs ! (length hs - 1) = last hs"
    using assms U_bound More_Lists.distinct_length_le[of hs n] last_conv_nth[of hs]
    by (auto)
  moreover have "length (sift_down ks ((butlast hs)[0 := last hs]) 0) = length hs - 1"
    "set (sift_down ks ((butlast hs)[0 := last hs]) 0) \<subseteq> set hs"
    using calculation sift_down_perm[of 0 "(butlast hs)[0 := last hs]" ks] extract_list(2,3)[of hs] False
    by (auto)
  moreover have [sep_heap_rules]: "\<lbrakk>heap_rel hs hl pl; key_rel ks hs kl\<rbrakk> \<Longrightarrow>
      <Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl>
        sift_down_imp Ha Pa Ka (length hs - 1) (last hs) (kl ! last hs) 0
      <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
           \<up>(heap_rel (sift_down ks ((butlast hs)[0 := last hs]) 0) hl' pl')>" for hl pl kl
    by (rule sift_down_imp_rule[of 0 "(butlast hs)[0 := last hs]",
          simplified length_list_update length_butlast])
       (use calculation extract_list(1,2)[of hs] False in
         \<open>auto intro: heap_rel_hole_extract key_rel_mono simp: key_rel_nth\<close>)
  moreover have [sep_heap_rules]: "\<lbrakk>heap_rel hs hl pl; key_rel ks hs kl\<rbrakk> \<Longrightarrow>
      <Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl * Sr \<mapsto>\<^sub>r length hs>
        heap_extract_min_imp (Ha, Pa, Ka, Sr)
      <\<lambda>r. heap_assn (sift_down ks ((butlast hs)[0 := last hs]) 0, ks) (Ha, Pa, Ka, Sr) *
         \<up>(r = Some (hs ! 0))>" for hl pl kl
    using calculation heap_rel_nth[of hs hl pl 0] heap_rel_nth[of hs hl pl "length hs - 1"]
      key_rel_mono[of ks hs kl "sift_down ks ((butlast hs)[0 := last hs]) 0"]
    unfolding heap_extract_min_imp_def prod.case heap_assn.simps
    by (sep_auto simp: heap_rel_lengths key_rel_len subset_eq)
  ultimately show ?thesis
    using False
    by (sep_auto)
qed
(*
subsection \<open>The heap is a key-value queue\<close>

sublocale iheap: key_value_queue_imp U heap_empty heap_extract_min
 heap_decrease_key heap_insert
    "heap_invar U" heap_abstract  queue_key heap_assn "heap_empty_imp n k0" 
heap_extract_min_imp
    heap_decrease_key_imp heap_insert_imp
proof (rule key_value_queue_imp.intro[OF heap_key_value_queue], unfold_locales, goal_cases)
  case 1 show ?case by (rule heap_empty_imp_rule)
next
  case (2 H Hi)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  show ?case using heap_extract_min_imp_rule 2 H Hi by simp
next
  case (3 H x Hi k)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  have "x \<notin> set hs" using 3 H by auto
  thus ?case using heap_insert_imp_rule 3 H Hi by simp
next
  case (4 H x k' k Hi)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  have "x \<in> set hs" using 4 H by auto
  thus ?case using heap_decrease_key_imp_rule 4 H Hi by simp
qed

qed
*)
end

definition heap_clear_imp :: "'ai heap_imp \<Rightarrow> unit Heap" where
  "heap_clear_imp Hi = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> (Sr := 0))"

definition heap_key_of_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> nat \<Rightarrow> 'ai option Heap" where
  "heap_key_of_imp Hi x = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     sz \<leftarrow> !Sr;
     i \<leftarrow> Array.nth Pa x;
     if i < sz then do {
       y \<leftarrow> Array.nth Ha i;
       if y = x then do { k \<leftarrow> Array.nth Ka x; return (Some k) } else return None }
     else return None })"

context indexed_heap_imp
begin

subsection \<open>Reading the Heap\<close>

lemma heap_read_size_rule:
  "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> !Sr
   <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(r = length hs)>"
  by sep_auto

lemma heap_read_at_rule:
  "i < length hs \<Longrightarrow>
   <heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Ha i
   <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(r = hs ! i)>"
  by (sep_auto simp: heap_rel_def)

lemma heap_read_pos_rule:
  "x < n \<Longrightarrow>
   <heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Pa x
   <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(x \<in> set hs \<longrightarrow> r = idx hs x)>"
  by (sep_auto simp: heap_rel_pos dest: heap_rel_len)

lemma heap_read_key_rule:
  "\<lbrakk>x \<in> set hs; x < n\<rbrakk> \<Longrightarrow>
   <heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Ka x
   <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(queue_key r = ks x)>"
  by (sep_auto simp: key_rel_def)

subsection \<open>The Additional Operations\<close>

lemma heap_clear_imp_rule:
  "<heap_assn H (Ha, Pa, Ka, Sr)> heap_clear_imp (Ha, Pa, Ka, Sr)
   <\<lambda>_. heap_assn heap_empty (Ha, Pa, Ka, Sr)>"
  by (cases H) (sep_auto simp: heap_clear_imp_def heap_empty_def heap_rel_def key_rel_def)

lemma heap_key_of_imp_rule:
  assumes "heap_invar U (hs, ks)" "x \<in> U"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_key_of_imp (Ha, Pa, Ka, Sr) x
         <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) *
              \<up>(case r of None \<Rightarrow> (\<nexists>k. (x, k) \<in> heap_abstract (hs, ks))
                        | Some k \<Rightarrow> (x, queue_key k) \<in> heap_abstract (hs, ks))>"
proof-
  note heap_assn.simps[simp del] heap_abstract.simps[simp del]
  have "x < n"
    using assms U_bound
    by auto
  show ?thesis
  proof(cases "x \<in> set hs")
    case True
    moreover have [sep_heap_rules]: "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Pa x
        <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(r = idx hs x)>"
      using True \<open>x < n\<close>
      by (sep_auto heap: heap_read_pos_rule)
    ultimately show ?thesis
      using \<open>x < n\<close> idx_less[of x hs]
      unfolding heap_key_of_imp_def prod.case
      by (sep_auto heap: heap_read_size_rule heap_read_at_rule heap_read_key_rule
          simp: heap_abstract_iff)
  next
    case False
    moreover have [sep_heap_rules]: "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Pa x
        <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr)>"
      using \<open>x < n\<close>
      by (sep_auto heap: heap_read_pos_rule)
    moreover have [sep_heap_rules]:
      "i < length hs \<Longrightarrow> <heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Ha i
        <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(r \<noteq> x)>" for i
      using False
      by (sep_auto heap: heap_read_at_rule)
    ultimately show ?thesis
      unfolding heap_key_of_imp_def prod.case
      by (sep_auto heap: heap_read_size_rule simp: heap_abstract_iff)
  qed
qed

lemma heap_extract_min_key_imp_rule:
  assumes "heap_invar U (hs, ks)"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_extract_min_key_imp (Ha, Pa, Ka, Sr)
         <\<lambda>r. heap_assn (fst (heap_extract_min (hs, ks))) (Ha, Pa, Ka, Sr) *
              \<up>(map_option fst r = snd (heap_extract_min (hs, ks)) \<and>
                (\<forall>x k. r = Some (x, k) \<longrightarrow> (x, queue_key k) \<in> heap_abstract (hs, ks)))>"
proof-
  note heap_abstract.simps[simp del]
  show ?thesis
    using assms U_bound nth_mem[of 0 hs]
    unfolding heap_extract_min_key_imp_def prod.case
    by (cases "hs = []")
       (sep_auto heap: heap_read_size_rule heap_read_at_rule heap_read_key_rule
         heap_extract_min_imp_rule
         simp: heap_abstract_iff subset_eq)+
qed

subsection \<open>The Heap is a Queue for the Hungarian Method\<close>

lemma heap_key_value_queue_hungarian:
  "key_value_queue U heap_empty heap_extract_min heap_decrease_key heap_insert
     (heap_invar U) heap_abstract"
  by (rule heap_key_value_queue)

sublocale hqueue: key_value_queue_imp U heap_empty heap_extract_min heap_decrease_key
    heap_insert "heap_invar U" heap_abstract queue_key heap_assn "heap_empty_imp n k0"
    heap_clear_imp heap_extract_min_key_imp heap_key_of_imp heap_decrease_key_imp heap_insert_imp
  by (intro key_value_queue_imp.intro heap_key_value_queue_hungarian
      key_value_queue_imp_axioms.intro)
     (simp_all only: split_paired_all heap_empty_imp_rule heap_clear_imp_rule
       heap_extract_min_key_imp_rule heap_key_of_imp_rule heap_insert_imp_rule
       heap_decrease_key_imp_rule
       not_False_eq_True)

end

end
