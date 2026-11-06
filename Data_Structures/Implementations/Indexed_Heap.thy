theory Indexed_Heap
  imports Main More_Lists Data_Structures.Fixed_Univ_Key_Value_Queue_Specs
begin

section \<open>An Indexed Binary Min-Heap: Functional Model\<close>

text \<open>A binary min-heap over elements that are natural numbers (indices into a fixed universe,
      e.g.\ vertex numbers), together with a key function. The heap is a list @{term hs} in which
      position @{term j} has parent @{term \<open>parent j\<close>} and the children \<open>2j+1\<close> and \<open>2j+2\<close>.

      This is the functional model of the imperative heap of
      \<open>Indexed_Heap_Imperative\<close>: there, the list is stored in an array of size \<open>n\<close> (with the
      current size in a reference), the keys in a key array indexed by elements, and the position
      of every element in a position array, which makes @{text decrease_key} logarithmic.
      The operations are the usual ones: insertion and key decrease sift the element up,
      extraction moves the last element to the root and sifts it down. The keys in the model
      are those of the functional algorithm; ties are broken exactly as by the imperative code,
      so that the model determines the result of every operation.\<close>

subsection \<open>Tree structure\<close>

definition parent :: "nat \<Rightarrow> nat" where
  "parent i = (i - 1) div 2"

lemma parent_less [simp]: "0 < i \<Longrightarrow> parent i < i"
  unfolding parent_def
  by linarith

lemma parent_less_trans: "\<lbrakk>0 < i; i < n\<rbrakk> \<Longrightarrow> parent i < n"
  unfolding parent_def
  by linarith

lemma parent_childI [simp]: "parent (2 * i + 1) = i" "parent (2 * i + 2) = i"
  unfolding parent_def
  by simp_all

lemma parent_eq_iff:
  "0 < j \<Longrightarrow> parent j = i \<longleftrightarrow> j = 2 * i + 1 \<or> j = 2 * i + 2"
  unfolding parent_def
  by linarith

lemma parent_eqD: "\<lbrakk>parent j = i; 0 < j\<rbrakk> \<Longrightarrow> 2 * i + 1 \<le> j"
  using parent_eq_iff
  by auto

subsection \<open>Sifting\<close>

text \<open>Swap an element with its parent while its key is smaller.\<close>

function sift_up :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "sift_up ks hs i =
     (if i = 0 then hs
      else if ks (hs ! i) < ks (hs ! parent i)
           then sift_up ks (hs[i := hs ! parent i, parent i := hs ! i]) (parent i)
           else hs)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(_, _, i). i)") simp_all

declare sift_up.simps [simp del]

lemma sift_up_0 [simp]: "sift_up ks hs 0 = hs"
  by (subst sift_up.simps) simp

lemma sift_up_rec:
  "\<lbrakk>0 < i; ks (hs ! i) < ks (hs ! parent i)\<rbrakk> \<Longrightarrow>
   sift_up ks hs i = sift_up ks (hs[i := hs ! parent i, parent i := hs ! i]) (parent i)"
  by (subst sift_up.simps) simp

lemma sift_up_stop: "\<not> ks (hs ! i) < ks (hs ! parent i) \<Longrightarrow> sift_up ks hs i = hs"
  by (subst sift_up.simps) simp

text \<open>The child with the smaller key; the right one only if it exists and is strictly smaller.\<close>

definition min_child :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "min_child ks hs i =
     (if Suc (2 * i + 1) < length hs \<and> ks (hs ! Suc (2 * i + 1)) < ks (hs ! (2 * i + 1))
      then Suc (2 * i + 1) else 2 * i + 1)"

lemma min_child_bounds:
  "2 * i + 1 < length hs \<Longrightarrow>
   i < min_child ks hs i \<and> min_child ks hs i < length hs"
  unfolding min_child_def
  by auto

lemma parent_min_child [simp]: "parent (min_child ks hs i) = i"
  unfolding min_child_def
  by (simp add: parent_def)

lemma min_child_min:
  "\<lbrakk>2 * i + 1 < length hs; j < length hs; 0 < j; parent j = i\<rbrakk>
   \<Longrightarrow> ks (hs ! min_child ks hs i) \<le> ks (hs ! j)"
  unfolding min_child_def
  by (auto simp: parent_eq_iff)

text \<open>Swap an element with its smaller child while that child's key is smaller.\<close>

function sift_down :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "sift_down ks hs i =
     (if 2 * i + 1 < length hs \<and> ks (hs ! min_child ks hs i) < ks (hs ! i)
      then sift_down ks (hs[i := hs ! min_child ks hs i, min_child ks hs i := hs ! i])
                        (min_child ks hs i)
      else hs)"
  by pat_completeness auto
termination
proof(relation "measure (\<lambda>(_, hs, i). length hs - i)", goal_cases)
  case (2 ks hs i)
  thus ?case
    using min_child_bounds[of i hs ks]
    by (simp; linarith)
qed simp

declare sift_down.simps [simp del]

lemma sift_down_stop:
  "\<not> (2 * i + 1 < length hs \<and> ks (hs ! min_child ks hs i) < ks (hs ! i)) \<Longrightarrow>
   sift_down ks hs i = hs"
  by (subst sift_down.simps) auto

lemma sift_up_perm:
  "i < length hs \<Longrightarrow>
   length (sift_up ks hs i) = length hs \<and> set (sift_up ks hs i) = set hs \<and>
   (distinct (sift_up ks hs i) \<longleftrightarrow> distinct hs)"
proof(induction ks hs i rule: sift_up.induct)
  case (1 ks hs i)
  thus ?case
    by (simp add: sift_up.simps[of ks hs i] parent_less_trans)
qed

lemma sift_down_perm:
  "i < length hs \<Longrightarrow>
   length (sift_down ks hs i) = length hs \<and> set (sift_down ks hs i) = set hs \<and>
   (distinct (sift_down ks hs i) \<longleftrightarrow> distinct hs)"
proof(induction ks hs i rule: sift_down.induct)
  case (1 ks hs i)
  thus ?case
    using min_child_bounds[of i hs ks]
    by (simp add: sift_down.simps[of ks hs i])
qed

subsection \<open>The heap property\<close>

definition heap_prop :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> bool" where
  "heap_prop ks hs \<longleftrightarrow> (\<forall>j<length hs. 0 < j \<longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j))"

text \<open>During sift-up at @{term i}: the heap property holds except between @{term i} and its
      parent, and the parent of @{term i} bounds the children of @{term i}.\<close>

definition up_inv :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "up_inv ks hs i \<longleftrightarrow>
     (\<forall>j<length hs. 0 < j \<longrightarrow> j \<noteq> i \<longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j)) \<and>
     (\<forall>j<length hs. 0 < j \<longrightarrow> parent j = i \<longrightarrow> 0 < i \<longrightarrow> ks (hs ! parent i) \<le> ks (hs ! j))"

text \<open>During sift-down at @{term i}: the heap property holds except between @{term i} and its
      children, and the parent of @{term i} bounds the children of @{term i}.\<close>

definition down_inv :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "down_inv ks hs i \<longleftrightarrow>
     (\<forall>j<length hs. 0 < j \<longrightarrow> parent j \<noteq> i \<longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j)) \<and>
     (\<forall>j<length hs. 0 < j \<longrightarrow> parent j = i \<longrightarrow> 0 < i \<longrightarrow> ks (hs ! parent i) \<le> ks (hs ! j))"

lemma heap_prop_min:
  "\<lbrakk>heap_prop ks hs; j < length hs\<rbrakk> \<Longrightarrow> ks (hs ! 0) \<le> ks (hs ! j)"
proof(induction j rule: less_induct)
  case (less j)
  thus ?case
    using less.IH[of "parent j"]
    by (cases "j = 0")
       (auto simp add: heap_prop_def parent_less_trans
         intro: order_trans[where y = "ks (hs ! parent j)"])
qed

lemma heap_prop_min_set:
  "\<lbrakk>heap_prop ks hs; x \<in> set hs\<rbrakk> \<Longrightarrow> ks (hs ! 0) \<le> ks x"
  by (auto simp add: in_set_conv_nth intro: heap_prop_min)

lemma up_inv_parent:
  "\<lbrakk>up_inv ks hs i; 0 < parent i; 0 < i; i < length hs\<rbrakk> \<Longrightarrow>
    ks (hs ! parent (parent i)) \<le> ks (hs ! parent i)"
  using parent_less_trans[of i "length hs"] parent_less[of i]
  by (auto simp add: up_inv_def)

lemma up_inv_step:
  "\<lbrakk>up_inv ks hs i; 0 < i; i < length hs; ks (hs ! i) < ks (hs ! parent i)\<rbrakk>
    \<Longrightarrow> up_inv ks (hs[i := hs ! parent i, parent i := hs ! i]) (parent i)"
  using parent_less_trans[of i "length hs"] up_inv_parent[of ks hs i]
  by (auto simp add: up_inv_def nth_list_update
    intro: less_imp_le order_trans[where y = "ks (hs ! parent i)"] dest: order.strict_trans1)

lemma up_inv_stop:
  "\<lbrakk>up_inv ks hs i; \<not> ks (hs ! i) < ks (hs ! parent i)\<rbrakk> \<Longrightarrow> heap_prop ks hs"
  by (auto simp add: heap_prop_def up_inv_def not_less)

lemma sift_up_heap:
  "\<lbrakk>i < length hs; up_inv ks hs i\<rbrakk> \<Longrightarrow> heap_prop ks (sift_up ks hs i)"
proof(induction ks hs i rule: sift_up.induct)
  case (1 ks hs i)
  thus ?case
    using up_inv_step[of ks hs i] up_inv_stop[of ks hs i]
    by (cases "i = 0"; cases "ks (hs ! i) < ks (hs ! parent i)";
      auto simp add: sift_up_rec sift_up_stop parent_less_trans up_inv_def heap_prop_def)
qed

lemma down_inv_step:
  "\<lbrakk>down_inv ks hs i; 2 * i + 1 < length hs; ks (hs ! min_child ks hs i) < ks (hs ! i)\<rbrakk>
    \<Longrightarrow>
    down_inv ks (hs[i := hs ! min_child ks hs i, min_child ks hs i := hs ! i]) (min_child ks hs i)"
  using min_child_bounds[of i hs ks] min_child_min[of i hs _ ks]
  by (auto simp add: down_inv_def nth_list_update intro: less_imp_le)

lemma down_inv_stop:
  assumes "down_inv ks hs i"
    "\<not> (2 * i + 1 < length hs \<and> ks (hs ! min_child ks hs i) < ks (hs ! i))"
  shows "heap_prop ks hs"
  unfolding heap_prop_def
proof(intro allI impI)
  fix j
  assume "j < length hs" "0 < j"
  thus "ks (hs ! parent j) \<le> ks (hs ! j)"
    using assms parent_eqD[of j i] min_child_min[of i hs j ks]
    by (cases "parent j = i")
       (auto simp add: down_inv_def not_less
         intro: order_trans[where y = "ks (hs ! min_child ks hs i)"])
qed

lemma sift_down_heap:
  "\<lbrakk>i < length hs; down_inv ks hs i\<rbrakk> \<Longrightarrow>
    heap_prop ks (sift_down ks hs i)"
proof(induction ks hs i rule: sift_down.induct)
  case (1 ks hs i)
  thus ?case
    using down_inv_step[of ks hs i] down_inv_stop[of ks hs i] min_child_bounds[of i hs ks]
    by (cases "2 * i + 1 < length hs \<and> ks (hs ! min_child ks hs i) < ks (hs ! i)";
      auto simp add: sift_down.simps[of ks hs i])
qed

subsection \<open>Position lookup\<close>

text \<open>The position of an element in the heap list. The imperative heap reads it from its position
      array instead.\<close>

fun idx :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "idx [] x = 0"
| "idx (y # ys) x = (if y = x then 0 else Suc (idx ys x))"

lemma idx_less: "x \<in> set hs \<Longrightarrow> idx hs x < length hs"
  by (induction hs) auto

lemma idx_nth [simp]: "x \<in> set hs \<Longrightarrow> hs ! idx hs x = x"
  by (induction hs) auto

lemma idx_unique:
  "\<lbrakk>distinct hs; j < length hs\<rbrakk> \<Longrightarrow> idx hs (hs ! j) = j"
  by (induction hs arbitrary: j) (auto simp add: nth_Cons split: nat.split)

subsection \<open>Operations\<close>

type_synonym 'a iheap = "nat list \<times> (nat \<Rightarrow> 'a)"

definition heap_empty :: "'a iheap" where
  "heap_empty = ([], \<lambda>_. undefined)"

fun heap_insert :: "'a::linorder iheap \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a iheap" where
  "heap_insert (hs, ks) x k = (sift_up (ks(x := k)) (hs @ [x]) (length hs), ks(x := k))"

fun heap_decrease_key :: "'a::linorder iheap \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a iheap" where
  "heap_decrease_key (hs, ks) x k = (sift_up (ks(x := k)) hs (idx hs x), ks(x := k))"

fun heap_extract_min :: "'a::linorder iheap \<Rightarrow> 'a iheap \<times> nat option" where
  "heap_extract_min (hs, ks) =
     (if hs = [] then ((hs, ks), None)
      else if butlast hs = [] then (([], ks), Some (hs ! 0))
      else ((sift_down ks ((butlast hs)[0 := last hs]) 0, ks), Some (hs ! 0)))"

fun heap_invar :: "nat set \<Rightarrow> 'a::linorder iheap \<Rightarrow> bool" where
  "heap_invar U (hs, ks) \<longleftrightarrow> distinct hs \<and> set hs \<subseteq> U \<and> heap_prop ks hs"

fun heap_abstract :: "'a iheap \<Rightarrow> (nat \<times> 'a) set" where
  "heap_abstract (hs, ks) = (\<lambda>v. (v, ks v)) ` set hs"

subsection \<open>Correctness\<close>

lemma heap_propD:
  "\<lbrakk>heap_prop ks hs; j < length hs; 0 < j\<rbrakk> \<Longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j)"
  by (simp add: heap_prop_def)

lemma up_inv_insert:
  assumes "heap_prop ks hs" "x \<notin> set hs"
  shows "up_inv (ks(x := k)) (hs @ [x]) (length hs)"
  unfolding up_inv_def
proof(intro conjI allI impI)
  fix j
  assume "j < length (hs @ [x])" "0 < j" "j \<noteq> length hs"
  thus "(ks(x := k)) ((hs @ [x]) ! parent j) \<le> (ks(x := k)) ((hs @ [x]) ! j)"
    using assms parent_less_trans[of j "length hs"]
    by (auto simp add: nth_append heap_prop_def dest: nth_mem)
next
  fix j
  assume "j < length (hs @ [x])" "0 < j" "parent j = length hs"
  thus "(ks(x := k)) ((hs @ [x]) ! parent (length hs)) \<le> (ks(x := k)) ((hs @ [x]) ! j)"
    using parent_less[of j]
    by simp
qed

lemma up_inv_decrease:
  assumes "heap_prop ks hs" "distinct hs" "x \<in> set hs" "k < ks x"
  shows "up_inv (ks(x := k)) hs (idx hs x)"
  unfolding up_inv_def
proof(intro conjI allI impI)
  fix j
  assume "j < length hs" "0 < j" "j \<noteq> idx hs x"
  thus "(ks(x := k)) (hs ! parent j) \<le> (ks(x := k)) (hs ! j)"
    using assms idx_less[of x hs] idx_unique[of hs] heap_propD[of ks hs j] parent_less_trans[of j
      "length hs"]
    by (auto dest: nth_mem)
next
  fix j
  assume "j < length hs" "0 < j" "parent j = idx hs x" "0 < idx hs x"
  thus "(ks(x := k)) (hs ! parent (idx hs x)) \<le> (ks(x := k)) (hs ! j)"
    using assms idx_less[of x hs] idx_unique[of hs] heap_propD[of ks hs j] heap_propD[of ks hs
      "idx hs x"]
    by (auto intro: order_trans[where y = "ks x"])
qed

lemma down_inv_extract:
  "\<lbrakk>heap_prop ks hs; distinct hs; butlast hs \<noteq> []\<rbrakk> \<Longrightarrow>
    down_inv ks ((butlast hs)[0 := last hs]) 0"
  using extract_list(3,4)[of hs]
  by (auto simp add: down_inv_def heap_prop_def parent_less_trans)

lemma heap_abstract_iff:
  "(x, k) \<in> heap_abstract (hs, ks) \<longleftrightarrow> x \<in> set hs \<and> k = ks x"
  by auto

lemma heap_extract_min_some:
  "Some x = snd (heap_extract_min (hs, ks)) \<longleftrightarrow> hs \<noteq> [] \<and> x = hs ! 0"
  by auto

lemma heap_extract_min_invar:
  "heap_invar U (hs, ks) \<Longrightarrow> heap_invar U (fst (heap_extract_min (hs, ks)))"
  using sift_down_perm[of 0 "(butlast hs)[0 := last hs]" ks] extract_list(1-3)[of hs]
    sift_down_heap[of 0 "(butlast hs)[0 := last hs]" ks] down_inv_extract[of ks hs]
  by (cases hs; auto simp add: heap_prop_def)

lemma heap_extract_min_abstract:
  "heap_invar U (hs, ks) \<Longrightarrow>
    heap_abstract (fst (heap_extract_min (hs, ks))) =
    heap_abstract (hs, ks) - {(hs ! 0, ks (hs ! 0))}"
  using sift_down_perm[of 0 "(butlast hs)[0 := last hs]" ks] extract_list(1-3)[of hs]
  by (cases hs; auto simp add: neq_Nil_conv)

lemma heap_extract_min_min:
  "\<lbrakk>heap_invar U (hs, ks); Some x = snd (heap_extract_min (hs, ks))\<rbrakk> \<Longrightarrow>
    (x, ks x) \<in> heap_abstract (hs, ks) \<and>
    (\<forall> x' k'. (x', k') \<in> heap_abstract (hs, ks) \<longrightarrow> ks x \<le> k')"
  by (auto split: if_splits dest: heap_prop_min_set)

lemma heap_insert_invar:
  "\<lbrakk>heap_invar U (hs, ks); x \<in> U; x \<notin> set hs\<rbrakk> \<Longrightarrow>
    heap_invar U (heap_insert (hs, ks) x k)"
  using sift_up_perm[of "length hs" "hs @ [x]" "ks(x := k)"] up_inv_insert[of ks hs x k]
    sift_up_heap[of "length hs" "hs @ [x]" "ks(x := k)"]
  by (auto)

lemma heap_insert_abstract:
  "x \<notin> set hs \<Longrightarrow>
    heap_abstract (heap_insert (hs, ks) x k) = heap_abstract (hs, ks) \<union> {(x, k)}"
  using sift_up_perm[of "length hs" "hs @ [x]" "ks(x := k)"]
  by (auto)

lemma heap_decrease_key_invar:
  "\<lbrakk>heap_invar U (hs, ks); x \<in> set hs; k < ks x\<rbrakk> \<Longrightarrow>
    heap_invar U (heap_decrease_key (hs, ks) x k)"
  using idx_less[of x hs] sift_up_perm[of "idx hs x" hs "ks(x := k)"] up_inv_decrease[of ks hs x k]
    sift_up_heap[of "idx hs x" hs "ks(x := k)"]
  by (auto)

lemma heap_decrease_key_abstract:
  "x \<in> set hs \<Longrightarrow>
    heap_abstract (heap_decrease_key (hs, ks) x k') =
    heap_abstract (hs, ks) - {(x, ks x)} \<union> {(x, k')}"
  using idx_less[of x hs] sift_up_perm[of "idx hs x" hs "ks(x := k')"]
  by (auto)

lemma heap_key_value_queue:
  "key_value_queue U heap_empty heap_extract_min heap_decrease_key heap_insert (heap_invar U)
     heap_abstract"
proof(unfold_locales, goal_cases)
  case (1 H x k)
  thus ?case
    by (cases H) auto
next
  case 2
  show ?case
    by (simp add: heap_empty_def heap_prop_def)
next
  case 3
  show ?case
    by (simp add: heap_empty_def)
next
  case (4 H)
  thus ?case
    by (cases H)
       (auto intro: heap_extract_min_invar simp del: heap_extract_min.simps heap_invar.simps)
next
  case (5 H x)
  thus ?case
    by (cases H) (blast dest: heap_extract_min_min)
next
  case (6 H)
  thus ?case
    by (cases H) (auto split: if_splits)
next
  case (7 H x k)
  thus ?case
    by (cases H)
       (auto simp add: heap_extract_min_some heap_extract_min_abstract heap_abstract_iff
         simp del: heap_extract_min.simps heap_abstract.simps)
next
  case (8 H)
  thus ?case
    by (cases H) (auto split: if_splits)
next
  case (9 H x k)
  thus ?case
    by (cases H) (auto intro: heap_insert_invar simp add: heap_abstract_iff
         simp del: heap_insert.simps heap_invar.simps heap_abstract.simps)
next
  case (10 H x k)
  thus ?case
    by (cases H)
       (simp add: heap_insert_abstract heap_abstract_iff del: heap_insert.simps heap_abstract.simps)
next
  case (11 H x k k')
  thus ?case
    by (cases H) (auto intro: heap_decrease_key_invar simp add: heap_abstract_iff
         simp del: heap_decrease_key.simps heap_invar.simps heap_abstract.simps)
next
  case (12 H x k k')
  thus ?case
    by (cases H) (auto simp add: heap_decrease_key_abstract heap_abstract_iff
         simp del: heap_decrease_key.simps heap_abstract.simps)
next
  case (13 H x k k')
  thus ?case
    by (cases H) auto
qed

end
