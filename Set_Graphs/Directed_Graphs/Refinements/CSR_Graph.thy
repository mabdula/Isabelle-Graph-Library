theory CSR_Graph
  imports CSR_Buildup_Imperative Weighted_Neighbourhoods_Imperative_Spec Directed_Set_Graphs.CSR_Graph_Spec
    Imperative.Array_Range_Iteration Data_Structures.More_Logic
begin

section \<open>Graphs in CSR Form\<close>

text \<open>The imperative refinement of the CSR graphs of @{theory Directed_Set_Graphs.CSR_Graph_Spec},
      built by @{theory Directed_Set_Graphs.CSR_Buildup_Imperative}: an array \<open>B\<close> of block
      starts, an array \<open>E\<close> of edges sorted by source, and a cursor array \<open>C\<close>,
      initially a copy of the start indices. Advancing the iterator of a vertex increments its
      cursor; resetting it copies the start index back.\<close>

subsection \<open>The imperative collection\<close>

text \<open>The entries of the arrays are stored on the heap, so their type has sort @{class heap}.\<close>

locale csr_blocks_imp = csr_blocks n K B H E
  for n K B H and E :: "'e::heap list"

locale csr_ranges_imp = csr_ranges n K B H E
  for n K B H and E :: "'e::heap list"
sublocale csr_ranges_imp \<subseteq> csr_blocks_imp ..


locale csr_graph_imp = csr_graph n K B E
  for n K B and E :: "'e::heap list"
sublocale csr_graph_imp \<subseteq> csr_ranges_imp n K B "\<lambda>v. B ! Suc v" E ..

text \<open>The imperative collection: the arrays \<open>B\<close> and \<open>E\<close> and the cursor array
      \<open>C\<close> of size \<open>n\<close>. The programs are global.\<close>

definition csr_has_imp ::
  "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "csr_has_imp = (\<lambda>(Ba, Ea, Ca) v. do { i \<leftarrow> Array.nth Ca v; e \<leftarrow> Array.nth Ba (Suc v); return (i < e) })"

definition csr_current_imp ::
  "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat \<Rightarrow> 'e Heap" where
  "csr_current_imp = (\<lambda>(Ba, Ea, Ca) v. do { i \<leftarrow> Array.nth Ca v; Array.nth Ea i })"

definition csr_move_imp ::
  "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_move_imp = (\<lambda>(Ba, Ea, Ca) v. do { i \<leftarrow> Array.nth Ca v; _ \<leftarrow> Array.upd v (Suc i) Ca; return () })"

definition csr_reset_imp ::
  "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_reset_imp = (\<lambda>(Ba, Ea, Ca) v. do { s \<leftarrow> Array.nth Ba v; _ \<leftarrow> Array.upd v s Ca; return () })"

text \<open>One step of the iterator of \<open>v\<close> over a range whose end is read from the array
      \<open>Ha\<close>: if entries remain, read the current one, advance the cursor and continue with
      \<open>f\<close>, otherwise continue with \<open>g\<close>. The cursor is read once. The step is inlined at
      its call sites.\<close>

definition csr_step_upto_imp ::
  "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> ('e \<Rightarrow> 'a Heap) \<Rightarrow> 'a Heap
   \<Rightarrow> 'a Heap" where
  "csr_step_upto_imp = (\<lambda>(Ba, Ea, Ca) Ha v f g. do {
     i \<leftarrow> Array.nth Ca v;
     h \<leftarrow> Array.nth Ha v;
     if i < h then do { e \<leftarrow> Array.nth Ea i; _ \<leftarrow> Array.upd v (Suc i) Ca; f e } else g })"

lemma csr_step_upto_imp_inline[code_unfold]:
  "csr_step_upto_imp (Ba, Ea, Ca) Ha v f g = do {
     i \<leftarrow> Array.nth Ca v;
     h \<leftarrow> Array.nth Ha v;
     if i < h then do { e \<leftarrow> Array.nth Ea i; _ \<leftarrow> Array.upd v (Suc i) Ca; f e } else g }"
  by (simp add: csr_step_upto_imp_def)

text \<open>The step may contain recursive calls of a heap @{command partial_function}.\<close>

lemma csr_step_upto_imp_mono[partial_function_mono]:
  assumes "\<And>e. mono_Heap (\<lambda>r. f r e)" "mono_Heap g"
  shows "mono_Heap (\<lambda>r. csr_step_upto_imp Ci Ha v (f r) (g r))"
  by (cases Ci) (simp add: csr_step_upto_imp_def, intro partial_function_mono assms)

text \<open>Appending to a range (@{const csr_append}): the end is read once.\<close>

definition csr_append_imp ::
  "'e::heap array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> unit Heap" where
  "csr_append_imp Ea Ha v x = do {
     h \<leftarrow> Array.nth Ha v;
     _ \<leftarrow> Array.upd h x Ea;
     _ \<leftarrow> Array.upd v (Suc h) Ha;
     return () }"

lemma csr_append_imp_rule:
  "\<lbrakk>v < length Hl; Hl ! v < length E\<rbrakk> \<Longrightarrow>
   <Ea \<mapsto>\<^sub>a E * Ha \<mapsto>\<^sub>a Hl> csr_append_imp Ea Ha v x
   <\<lambda>_. Ea \<mapsto>\<^sub>a snd (csr_append v x (Hl, E)) * Ha \<mapsto>\<^sub>a fst (csr_append v x (Hl, E))>"
  by (sep_auto simp: csr_append_imp_def csr_append_def)

text \<open>Emptiness of the block of a vertex (@{const csr_blocks.csr_empty}): two reads of \<open>B\<close>.\<close>

definition csr_empty_imp :: "nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "csr_empty_imp Ba v = do { a \<leftarrow> Array.nth Ba v; b \<leftarrow> Array.nth Ba (Suc v); return (a = b) }"

text \<open>The cursor array is initialised as a copy of the start indices.\<close>

definition csr_cursor_init :: "nat \<Rightarrow> nat array \<Rightarrow> nat array Heap" where
  "csr_cursor_init n Ba = do { Ca \<leftarrow> Array.new n 0; copy_prefix_imp n Ba Ca 0; return Ca }"

text \<open>Cursors and their reset need no distinct entries.\<close>

context csr_blocks_imp
begin

definition csr_assn ::
  "(nat \<Rightarrow> nat) \<Rightarrow> nat array \<times> 'e array \<times> nat array \<Rightarrow> assn" where
  "csr_assn c = (\<lambda>(Ba, Ea, Ca). Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E *
     (\<exists>\<^sub>Al. Ca \<mapsto>\<^sub>a l * \<up>(length l = n \<and> (\<forall>v\<in>K. l ! v = c v))))"

text \<open>Arrays become a collection, and a collection gives its arrays back, for clients that hand
      the arrays on to other programs. The cursors are given by the contents of the cursor array.\<close>

lemma csr_assn_intro:
  assumes "length l = n" "\<forall>v\<in>K. l ! v = c v"
  shows "Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E * Ca \<mapsto>\<^sub>a l \<Longrightarrow>\<^sub>A csr_assn c (Ba, Ea, Ca)"
  using assms
  by (sep_auto simp: csr_assn_def)

lemma csr_assn_release:
  "csr_assn c (Ba, Ea, Ca) \<Longrightarrow>\<^sub>A Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E * (\<exists>\<^sub>Al. Ca \<mapsto>\<^sub>a l * \<up>(length l = n))"
  by (sep_auto simp: csr_assn_def)

lemma csr_current_imp_rule:
  assumes "v \<in> K" "csr_invar c" "csr_remaining c v \<noteq> {}"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_current_imp (Ba, Ea, Ca) v
         <\<lambda>r. csr_assn c (Ba, Ea, Ca) * \<up>(r = csr_current c v)>"
  using assms H_hi[of v] B_bound[of v] K_less[of v]
  by (sep_auto simp: csr_assn_def csr_current_imp_def csr_current_def remaining_ne)

lemma csr_move_imp_rule:
  assumes "v \<in> K" "csr_remaining c v \<noteq> {}"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_move_imp (Ba, Ea, Ca) v
         <\<lambda>_. csr_assn (csr_move c v) (Ba, Ea, Ca)>"
  using K_less[of v] assms
  by (sep_auto simp: csr_assn_def csr_move_imp_def csr_move_def remaining_ne nth_list_update)

lemma csr_reset_imp_rule:
  assumes "v \<in> K"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_reset_imp (Ba, Ea, Ca) v
         <\<lambda>_. csr_assn (csr_reset c v) (Ba, Ea, Ca)>"
  using K_less[of v] assms B_length
  by (sep_auto simp: csr_assn_def csr_reset_imp_def csr_reset_def nth_list_update)

lemma csr_step_upto_imp_rule:
  assumes "v \<in> K" "v < length Hl" "Hl ! v = H v"
    and "csr_has c v \<Longrightarrow>
           <csr_assn (csr_move c v) (Ba, Ea, Ca) * Ha \<mapsto>\<^sub>a Hl * F> f (csr_current c v) <Q>"
    and "\<not> csr_has c v \<Longrightarrow> <csr_assn c (Ba, Ea, Ca) * Ha \<mapsto>\<^sub>a Hl * F> g <Q>"
  shows "<csr_assn c (Ba, Ea, Ca) * Ha \<mapsto>\<^sub>a Hl * F> csr_step_upto_imp (Ba, Ea, Ca) Ha v f g <Q>"
proof(cases "csr_has c v")
  case True
  hence post: "<csr_assn (fun_upd c v (Suc (c v))) (Ba, Ea, Ca) * Ha \<mapsto>\<^sub>a Hl * F> f (E ! c v) <Q>"
    and "c v < H v"
    using assms(4)
    by (simp_all add: csr_move_def csr_current_def csr_has_def)
  thus ?thesis
    using K_less[of v] assms(1-3) H_hi[of v] B_bound[of v]
    by (sep_auto simp: csr_step_upto_imp_def csr_assn_def nth_list_update
        heap: post[unfolded csr_assn_def prod.case])
next
  case False
  thus ?thesis
    using K_less[of v] assms(1-3)
    by (sep_auto simp: csr_step_upto_imp_def csr_assn_def csr_has_def
        heap: assms(5)[OF False, unfolded csr_assn_def prod.case])
qed

lemma csr_empty_imp_rule:
  assumes "v < n"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_empty_imp Ba v
         <\<lambda>r. csr_assn c (Ba, Ea, Ca) * \<up>(r = csr_empty v)>"
  using assms B_length
  by (sep_auto simp: csr_assn_def csr_empty_imp_def csr_empty_def)

text \<open>Copying the start indices into the cursor array, from index \<open>i\<close> on.\<close>

lemma csr_cursor_copy_rule:
  assumes "i \<le> n" "length l = n" "\<forall>j<i. l ! j = B ! j"
  shows "<Ba \<mapsto>\<^sub>a B * Ca \<mapsto>\<^sub>a l> copy_prefix_imp n Ba Ca i
         <\<lambda>_. Ba \<mapsto>\<^sub>a B * Ca \<mapsto>\<^sub>a take n B>"
  using copy_prefix_imp_rule[of i n B l Ba Ca] assms B_length nth_equalityI[of "take i l" "take i B"]
  by simp

lemma csr_cursor_init_rule:
  "<Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E> csr_cursor_init n Ba <\<lambda>Ca. csr_assn (\<lambda>v. B ! v) (Ba, Ea, Ca)>"
  unfolding csr_cursor_init_def csr_assn_def
  using B_length K_less
  by (sep_auto heap: csr_cursor_copy_rule)

sublocale csr_imp: indexed_set_reset_imp csr_invar csr_abstract K csr_iterated csr_remaining
    csr_reset csr_assn csr_reset_imp
  by unfold_locales (auto simp: split_paired_all intro: csr_reset_imp_rule)

end

context csr_graph_imp
begin

lemma csr_has_imp_rule:
  assumes "v \<in> K"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_has_imp (Ba, Ea, Ca) v
         <\<lambda>r. csr_assn c (Ba, Ea, Ca) * \<up>(r = csr_has c v)>"
  using K_less[of v] assms B_length
  by (sep_auto simp: csr_assn_def csr_has_imp_def csr_has_def)

sublocale csr_imp: indexed_iterable_set_imp csr_invar csr_abstract csr_current csr_has
    csr_iterated csr_remaining csr_move csr_reset K csr_assn csr_current_imp csr_has_imp
    csr_move_imp csr_reset_imp
  by unfold_locales
    (auto simp: split_paired_all intro: csr_current_imp_rule csr_has_imp_rule csr_move_imp_rule)

end

subsection \<open>Folding over a block\<close>

text \<open>The entries of the block of a vertex can also be folded over directly, without a cursor
      array: the fold reads the two bounds from \<open>B\<close> and runs over that range of \<open>E\<close>. It needs
      neither the cursor array nor distinct entries within a block, so its rule is stated for any
      arrays \<open>B\<close> and \<open>E\<close>.

      The rule of @{const iterate_range_strict} in @{theory Imperative.Array_Range_Iteration}
      requires the end of the range to be a valid index; the last block ends at the length of
      the array.\<close>

definition csr_fold_imp ::
  "nat array \<times> 'e::heap array \<Rightarrow> nat \<Rightarrow> ('e \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "csr_fold_imp = (\<lambda>(Ba, Ea) v f acc. do {
     i \<leftarrow> Array.nth Ba v;
     j \<leftarrow> Array.nth Ba (Suc v);
     iterate_range_strict Ea i j f acc })"

text \<open>The fold is inlined at its call sites, so a wrapper around it costs no call.\<close>

lemma csr_fold_imp_inline[code_unfold]:
  "csr_fold_imp (Ba, Ea) v f acc = do {
     i \<leftarrow> Array.nth Ba v;
     j \<leftarrow> Array.nth Ba (Suc v);
     iterate_range_strict Ea i j f acc }"
  by (simp add: csr_fold_imp_def)

declare iterate_range_strict.simps[code]

lemma csr_fold_imp_rule:
  assumes "Suc v < length B" "B ! Suc v \<le> length E"
    and "\<And>acc acci x. x \<in> set (nths E {B ! v..<B ! Suc v}) \<Longrightarrow>
           <acc_assn acc acci * F> fi x acci <\<lambda>r. acc_assn (f acc x) r * F>"
  shows "<Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E * acc_assn acc acci * F> csr_fold_imp (Ba, Ea) v fi acci
         <\<lambda>r. Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E * acc_assn (foldl f acc (nths E {B ! v..<B ! Suc v})) r * F>"
  using assms(1,2) unfolding csr_fold_imp_inline
  by (sep_auto heap: iterate_range_strict_le_rule[where f = f, OF assms(3)])

text \<open>The fold is the fold layer (@{locale indexed_set_fold_imp}) of the ranges that end where the
      next block starts. It needs no distinct entries and no cursor array: the collection is
      given by the arrays \<open>B\<close> and \<open>E\<close> only.\<close>

locale csr_graph_blocks_imp = csr_blocks n K B "\<lambda>v. B ! Suc v" E
  for n K B and E :: "'e::heap list"
begin

definition csr_blocks_assn ::
  "(nat \<Rightarrow> nat) \<Rightarrow> nat array \<times> 'e array \<Rightarrow> assn" where
  "csr_blocks_assn c = (\<lambda>(Ba, Ea). Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E)"

lemma csr_list_nths: "v < n \<Longrightarrow> csr_list v = nths E {B ! v..<B ! Suc v}"
  using B_bound
  by (simp add: csr_list_def map_nth_upt_take_drop nths_intervall_strict_as_drop_and_take drop_take)

lemma csr_fold_imp_refine:
  assumes "v \<in> K"
    and "\<And>acc acci x. x \<in> csr_abstract c v \<Longrightarrow>
           <acc_assn acc acci> fi x acci <\<lambda>r. acc_assn (f x acc) r>"
  shows "<csr_blocks_assn c Ci * acc_assn acc acci> csr_fold_imp Ci v fi acci
         <\<lambda>r. csr_blocks_assn c Ci * acc_assn (csr_fold c v f acc) r>"
proof-
  obtain Ba Ea where Ci: "Ci = (Ba, Ea)"
    by fastforce
  have "<Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E * acc_assn acc acci * emp> csr_fold_imp (Ba, Ea) v fi acci
        <\<lambda>r. Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E *
             acc_assn (foldl (\<lambda>acc x. f x acc) acc (nths E {B ! v..<B ! Suc v})) r * emp>"
    using K_less[OF assms(1)] csr_list_nths[of v] csr_list_set[of v c]
    by (intro csr_fold_imp_rule) (simp_all add: B_length B_bound assms(2))
  thus ?thesis
    using K_less[OF assms(1)]
    by (simp add: Ci csr_blocks_assn_def csr_fold_def csr_list_nths)
qed

sublocale csr_imp: indexed_set_fold_imp csr_invar csr_abstract K csr_fold csr_blocks_assn
    csr_fold_imp
  by unfold_locales (rule csr_fold_imp_refine)

end

sublocale csr_graph_imp \<subseteq> csr_graph_blocks_imp ..

subsection \<open>Reading the input\<close>

text \<open>The endpoints of the input edges (@{const e_src}, @{const e_tgt}) are read from the input
      arrays. The arrays are only read, so the assertion for them is carried as a frame.\<close>

definition ends_assn ::
  "nat list \<Rightarrow> nat list \<Rightarrow> nat array \<times> nat array \<Rightarrow> assn" where
  "ends_assn fs ts = (\<lambda>(Fa, Ta). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts)"

definition src_imp :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "src_imp = (\<lambda>(Fa, Ta) i. Array.nth Fa i)"

definition tgt_imp :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "tgt_imp = (\<lambda>(Fa, Ta) i. Array.nth Ta i)"

lemma src_imp_rule:
  "i < length fs \<Longrightarrow> <ends_assn fs ts Ei> src_imp Ei i <\<lambda>u. ends_assn fs ts Ei * \<up>(u = e_src fs i)>"
  by (cases Ei) (sep_auto simp: ends_assn_def src_imp_def)

lemma tgt_imp_rule:
  "\<lbrakk>i < length fs; length ts = length fs\<rbrakk> \<Longrightarrow>
   <ends_assn fs ts Ei> tgt_imp Ei i <\<lambda>v. ends_assn fs ts Ei * \<up>(v = e_tgt fs ts i)>"
  by (cases Ei) (sep_auto simp: ends_assn_def tgt_imp_def)

text \<open>The imperative input iterator: the container is the pair of endpoint arrays, the iterator
      state is the position, which is the edge.\<close>

definition edge_has_next :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "edge_has_next = (\<lambda>(Fa, Ta) i. do { l \<leftarrow> Array.len Fa; return (i < l) })"

definition edge_cur :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "edge_cur = (\<lambda>_ i. return i)"

definition edge_adv :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "edge_adv = (\<lambda>_ i. return (Suc i))"

subsection \<open>The CSR buildup for the input\<close>

text \<open>The global interpretation of the CSR buildup for the input iterator: the key of an edge is
      its tail, read by @{const src_imp}, and the edge itself is stored. The locale
      @{locale imp_csr_buildup_code} only fixes operations and has no assumptions.\<close>

global_interpretation csr_code: imp_csr_buildup_code n edge_has_next edge_cur edge_adv src_imp
    edge_cur
  for n
  defines csr_build_edges = csr_code.csr_build_imp
    and csr_build_into_edges = csr_code.csr_build_into
    and csr_count_edges = csr_code.count_imp
    and csr_prefix_sums = csr_code.prefix_imp
    and csr_init_edges = csr_code.init_E_imp
    and csr_fill_edges = csr_code.fill_imp
  done

text \<open>The heap @{command partial_function}s do not register their equations for code generation.\<close>

declare csr_code.count_imp.simps[code] csr_code.prefix_imp.simps[code] csr_code.fill_imp.simps[code]

section \<open>Weighted Neighbourhoods in CSR Representation\<close>

text \<open>The CSR collection of @{locale csr_graph} (start array \<open>B\<close>, element array \<open>E\<close>, cursor
      array) is extended to a collection of weighted neighbourhoods
      (@{locale weighted_neighbourhoods_imp_spec}):

        \<^item> the elements of the neighbourhood of \<open>v\<close> are the images under @{term tgt} of the
          entries of \<open>E\<close> in the segment of \<open>v\<close>; @{term tgt} must be injective on every
          segment (no parallel edges);
        \<^item> a weight array \<open>W\<close> runs parallel to \<open>E\<close>, so the weight at the cursor is read from the
          same index as the element, and the weights of a segment are read sequentially;
        \<^item> all cursors are reset in place by copying the start array into the cursor array.

      None of the operations allocates.\<close>

definition wnb_has_imp ::
  "(nat array \<times> 'e::heap array \<times> nat array) \<times> 'w::heap array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "wnb_has_imp = (\<lambda>(Ci, Wa) v. csr_has_imp Ci v)"

definition wnb_current_imp ::
  "('e \<Rightarrow> 'a) \<Rightarrow> (nat array \<times> 'e::heap array \<times> nat array) \<times> 'w::heap array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  "wnb_current_imp tgt = (\<lambda>(Ci, Wa) v. do { e \<leftarrow> csr_current_imp Ci v; return (tgt e) })"

definition wnb_current_cost_imp ::
  "(nat array \<times> 'e::heap array \<times> nat array) \<times> 'w::heap array \<Rightarrow> nat \<Rightarrow> 'w Heap" where
  "wnb_current_cost_imp = (\<lambda>((Ba, Ea, Ca), Wa) v. do { i \<leftarrow> Array.nth Ca v; Array.nth Wa i })"

definition wnb_move_imp ::
  "(nat array \<times> 'e::heap array \<times> nat array) \<times> 'w::heap array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "wnb_move_imp = (\<lambda>(Ci, Wa) v. csr_move_imp Ci v)"

definition wnb_reset_imp ::
  "(nat array \<times> 'e::heap array \<times> nat array) \<times> 'w::heap array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "wnb_reset_imp = (\<lambda>(Ci, Wa) v. csr_reset_imp Ci v)"

definition wnb_reset_all_imp ::
  "nat \<Rightarrow> (nat array \<times> 'e::heap array \<times> nat array) \<times> 'w::heap array \<Rightarrow> unit Heap" where
  "wnb_reset_all_imp n = (\<lambda>((Ba, Ea, Ca), Wa). copy_prefix_imp n Ba Ca 0)"

locale weighted_csr = csr_graph_imp n K B E
  for n K B and E :: "'e::heap list" +
  fixes tgt :: "'e \<Rightarrow> 'a::heap"
    and W :: "'w::heap list"
    and cost :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and wval :: "'w \<Rightarrow> real"
  assumes tgt_inj: "v \<in> K \<Longrightarrow> inj_on tgt ((!) E ` {B ! v..<B ! Suc v})"
    and W_length: "length W = length E"
    and W_cost: "\<lbrakk>v \<in> K; B ! v \<le> j; j < B ! Suc v\<rbrakk> \<Longrightarrow> wval (W ! j) = cost v (tgt (E ! j))"
begin

subsection \<open>The Functional Collection\<close>

definition "wnb_abstract c v = tgt ` csr_abstract c v"
definition "wnb_current c v = tgt (csr_current c v)"
definition "wnb_iterated c v = tgt ` csr_iterated c v"
definition "wnb_remaining c v = tgt ` csr_remaining c v"

lemma wnb_abstract_eq: "wnb_abstract c v = tgt ` (!) E ` {B ! v..<B ! Suc v}"
  by (simp add: wnb_abstract_def csr_abstract_eq)

lemma wnb_inj: "v \<in> K \<Longrightarrow> inj_on tgt (csr_abstract c v)"
  by (simp add: csr_abstract_def seg_def tgt_inj)

lemma wnb_remaining_ne: "wnb_remaining c v \<noteq> {} \<longleftrightarrow> csr_remaining c v \<noteq> {}"
  by (simp add: wnb_remaining_def)

sublocale wnb: indexed_iterable_set csr_invar wnb_abstract wnb_current csr_has
    wnb_iterated wnb_remaining csr_move csr_reset K
proof(unfold_locales, goal_cases)
  case (1 C i)
  thus ?case
    using csr.idx_partition_disjoint[OF 1]
      inj_on_image_Int[OF wnb_inj[OF 1(2)] iterated_sub[OF 1] remaining_sub[OF 1]]
    by (simp add: wnb_iterated_def wnb_remaining_def)
next
  case (2 C i)
  thus ?case
    using csr.idx_partition_union[OF 2]
    by (simp add: wnb_iterated_def wnb_remaining_def wnb_abstract_def flip: image_Un)
next
  case (7 C i)
  hence r: "csr_remaining C i \<noteq> {}"
    by (simp add: wnb_remaining_ne)
  have "tgt ` (csr_remaining C i - {csr_current C i})
        = tgt ` csr_remaining C i - tgt ` {csr_current C i}"
    using remaining_sub[OF 7(1,2)] csr.idx_current[OF 7(1,2) r]
    by (intro inj_on_image_set_diff[OF wnb_inj[OF 7(2)]]) auto
  thus ?case
    by (simp add: wnb_remaining_def wnb_current_def csr.idx_move_remaining[OF 7(1,2) r])
qed (auto simp: wnb_iterated_def wnb_remaining_def wnb_abstract_def wnb_current_def csr.idx_has
    csr.idx_current csr.idx_move_invar csr.idx_move_abstract csr.idx_move_iterated
    csr.idx_move_remaining_other csr.idx_move_iterated_other csr.idx_reset_invar
    csr.idx_reset_abstract csr.idx_reset_iterated csr.idx_reset_remaining
    csr.idx_reset_remaining_other csr.idx_reset_iterated_other)

subsection \<open>The Imperative Collection\<close>

definition wnb_assn ::
  "(nat \<Rightarrow> nat) \<Rightarrow> (nat array \<times> 'e array \<times> nat array) \<times> 'w array \<Rightarrow> assn" where
  "wnb_assn c = (\<lambda>(Ci, Wa). csr_assn c Ci * Wa \<mapsto>\<^sub>a W)"

lemma wnb_assn_split: "wnb_assn c (Ci, Wa) = csr_assn c Ci * Wa \<mapsto>\<^sub>a W"
  by (simp add: wnb_assn_def)

lemma wnb_has_imp_rule:
  "v \<in> K \<Longrightarrow>
   <wnb_assn c ((Ba, Ea, Ca), Wa)> wnb_has_imp ((Ba, Ea, Ca), Wa) v
   <\<lambda>r. wnb_assn c ((Ba, Ea, Ca), Wa) * \<up>(r = csr_has c v)>"
  by (sep_auto heap: csr_has_imp_rule simp: wnb_assn_def wnb_has_imp_def)

lemma wnb_current_imp_rule:
  assumes "v \<in> K" "csr_invar c" "csr_remaining c v \<noteq> {}"
  shows "<wnb_assn c ((Ba, Ea, Ca), Wa)> wnb_current_imp tgt ((Ba, Ea, Ca), Wa) v
         <\<lambda>r. wnb_assn c ((Ba, Ea, Ca), Wa) * \<up>(r = wnb_current c v)>"
  by (sep_auto heap: csr_current_imp_rule[OF assms]
               simp: wnb_assn_def wnb_current_imp_def wnb_current_def)

lemma wnb_current_cost_imp_rule:
  assumes "v \<in> K" "csr_invar c" "csr_remaining c v \<noteq> {}"
  shows "<wnb_assn c ((Ba, Ea, Ca), Wa)> wnb_current_cost_imp ((Ba, Ea, Ca), Wa) v
         <\<lambda>w. wnb_assn c ((Ba, Ea, Ca), Wa) * \<up>(wval w = cost v (wnb_current c v))>"
proof-
  have "B ! v \<le> c v" "c v < B ! Suc v"
    using assms
    by (simp_all add: csr_invar_def remaining_ne)
  hence "c v < length W" "wval (W ! c v) = cost v (wnb_current c v)"
    using W_cost[OF assms(1)] B_bound[of v] K_less[of v] assms(1) W_length
    by (simp_all add: wnb_current_def csr_current_def)
  thus ?thesis
    using K_less[OF assms(1)] assms(1)
    by (sep_auto simp: wnb_assn_def csr_assn_def wnb_current_cost_imp_def)
qed

lemma wnb_move_imp_rule:
  assumes "v \<in> K" "csr_remaining c v \<noteq> {}"
  shows "<wnb_assn c ((Ba, Ea, Ca), Wa)> wnb_move_imp ((Ba, Ea, Ca), Wa) v
         <\<lambda>_. wnb_assn (csr_move c v) ((Ba, Ea, Ca), Wa)>"
  by (sep_auto heap: csr_move_imp_rule[OF assms] simp: wnb_assn_def wnb_move_imp_def)

lemma wnb_reset_imp_rule:
  "v \<in> K \<Longrightarrow>
   <wnb_assn c ((Ba, Ea, Ca), Wa)> wnb_reset_imp ((Ba, Ea, Ca), Wa) v
   <\<lambda>_. wnb_assn (csr_reset c v) ((Ba, Ea, Ca), Wa)>"
  by (sep_auto heap: csr_reset_imp_rule simp: wnb_assn_def wnb_reset_imp_def)

lemma wnb_reset_all_imp_rule:
  "<wnb_assn c ((Ba, Ea, Ca), Wa)> wnb_reset_all_imp n ((Ba, Ea, Ca), Wa)
   <\<lambda>_. wnb_assn (\<lambda>v. B ! v) ((Ba, Ea, Ca), Wa)>"
  unfolding wnb_reset_all_imp_def wnb_assn_def csr_assn_def prod.case
  by (sep_auto heap: csr_cursor_copy_rule simp: K_less B_length)

sublocale wnb_imp: weighted_neighbourhoods_imp_spec csr_invar wnb_abstract wnb_current csr_has
    wnb_iterated wnb_remaining csr_move csr_reset K wnb_assn "wnb_current_imp tgt" wnb_has_imp
    wnb_move_imp wnb_reset_imp cost wval "\<lambda>v. B ! v" wnb_current_cost_imp "wnb_reset_all_imp n"
  by unfold_locales
    (auto simp: split_paired_all wnb_remaining_ne csr_init_invar intro: wnb_current_imp_rule
      wnb_has_imp_rule wnb_move_imp_rule wnb_reset_imp_rule wnb_current_cost_imp_rule
      wnb_reset_all_imp_rule)

end

end
