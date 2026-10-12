theory CSR_Graph
  imports CSR_Buildup_Imperative Weighted_Neighbourhoods_Imperative_Spec "../CSR_Graph_Spec"
    "../../../Imperative/Array_Range_Iteration"
begin

section \<open>Graphs in CSR Form\<close>

text \<open>The imperative refinement of the CSR graphs of @{theory Directed_Set_Graphs.CSR_Graph_Spec},
      built by @{theory Directed_Set_Graphs.CSR_Buildup_Imperative}: an array \<open>B\<close> of block
      starts, an array \<open>E\<close> of edges sorted by source, and a cursor array \<open>C\<close>, initially a copy of
      the start indices. Advancing the iterator of a vertex increments its cursor; resetting it
      copies the start index back.\<close>

subsection \<open>The imperative collection\<close>

text \<open>The entries of the arrays are stored on the heap, so their type has sort @{class heap}.\<close>

locale csr_ranges_imp = csr_ranges n K B H E
  for n K B H and E :: "'e::heap list"


locale csr_graph_imp = csr_graph n K B E
  for n K B and E :: "'e::heap list"
sublocale csr_graph_imp \<subseteq> csr_ranges_imp n K B "\<lambda>v. B ! Suc v" E ..

text \<open>The imperative collection: the arrays \<open>B\<close> and \<open>E\<close> and the cursor array \<open>C\<close> of size \<open>n\<close>.
      The programs are global.\<close>

definition csr_has_imp :: "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "csr_has_imp = (\<lambda>(Ba, Ea, Ca) v. do { i \<leftarrow> Array.nth Ca v; e \<leftarrow> Array.nth Ba (Suc v); return (i < e) })"

definition csr_current_imp :: "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat \<Rightarrow> 'e Heap" where
  "csr_current_imp = (\<lambda>(Ba, Ea, Ca) v. do { i \<leftarrow> Array.nth Ca v; Array.nth Ea i })"

definition csr_move_imp :: "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_move_imp = (\<lambda>(Ba, Ea, Ca) v. do { i \<leftarrow> Array.nth Ca v; _ \<leftarrow> Array.upd v (Suc i) Ca; return () })"

definition csr_reset_imp :: "nat array \<times> 'e::heap array \<times> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_reset_imp = (\<lambda>(Ba, Ea, Ca) v. do { s \<leftarrow> Array.nth Ba v; _ \<leftarrow> Array.upd v s Ca; return () })"

text \<open>One step of the iterator of \<open>v\<close> over a range whose end is read from the array \<open>Ha\<close>: if
      entries remain, read the current one, advance the cursor and continue with \<open>f\<close>, otherwise
      continue with \<open>g\<close>. The cursor is read once. The step is inlined at its call sites.\<close>

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

definition csr_append_imp :: "'e::heap array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> unit Heap" where
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

text \<open>Emptiness of the block of a vertex (@{const csr_ranges.csr_empty}): two reads of \<open>B\<close>.\<close>

definition csr_empty_imp :: "nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "csr_empty_imp Ba v = do { a \<leftarrow> Array.nth Ba v; b \<leftarrow> Array.nth Ba (Suc v); return (a = b) }"

text \<open>The cursor array is initialised as a copy of the start indices.\<close>

partial_function (heap) csr_copy_imp :: "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_copy_imp n Ba Ca i =
     (if i < n then do {
        s \<leftarrow> Array.nth Ba i;
        _ \<leftarrow> Array.upd i s Ca;
        csr_copy_imp n Ba Ca (Suc i) }
      else return ())"

definition csr_cursor_init :: "nat \<Rightarrow> nat array \<Rightarrow> nat array Heap" where
  "csr_cursor_init n Ba = do { Ca \<leftarrow> Array.new n 0; csr_copy_imp n Ba Ca 0; return Ca }"

context csr_ranges_imp
begin

definition csr_assn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat array \<times> 'e array \<times> nat array \<Rightarrow> assn" where
  "csr_assn c = (\<lambda>(Ba, Ea, Ca). Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E *
     (\<exists>\<^sub>Al. Ca \<mapsto>\<^sub>a l * \<up>(length l = n \<and> (\<forall>v\<in>K. l ! v = c v))))"

text \<open>The assertion of a collection given by its three arrays, for clients that hand the arrays on
      to other programs.\<close>

lemma csr_assn_split:
  "csr_assn c (Ba, Ea, Ca) =
   Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E * (\<exists>\<^sub>Al. Ca \<mapsto>\<^sub>a l * \<up>(length l = n \<and> (\<forall>v\<in>K. l ! v = c v)))"
  by (simp add: csr_assn_def)

lemma csr_current_imp_rule:
  assumes "v \<in> K" "csr_invar c" "csr_remaining c v \<noteq> {}"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_current_imp (Ba, Ea, Ca) v
         <\<lambda>r. csr_assn c (Ba, Ea, Ca) * \<up>(r = csr_current c v)>"
proof -
  have "c v < length E"
    using assms H_hi[OF K_less[OF assms(1)]] B_bound[OF K_less[OF assms(1)]]
    by (auto simp: remaining_ne)
  then show ?thesis
    using K_less[OF assms(1)] assms(1)
    by (sep_auto simp: csr_assn_def csr_current_imp_def csr_current_def)
qed

lemma csr_move_imp_rule:
  assumes "v \<in> K" "csr_remaining c v \<noteq> {}"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_move_imp (Ba, Ea, Ca) v
         <\<lambda>_. csr_assn (csr_move c v) (Ba, Ea, Ca)>"
proof -
  have m: "csr_move c v = c(v := Suc (c v))"
    using assms(2) by (simp add: csr_move_def remaining_ne)
  show ?thesis
    using K_less[OF assms(1)] assms(1)
    by (sep_auto simp: csr_assn_def csr_move_imp_def m nth_list_update)
qed

lemma csr_reset_imp_rule:
  assumes "v \<in> K"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_reset_imp (Ba, Ea, Ca) v
         <\<lambda>_. csr_assn (csr_reset c v) (Ba, Ea, Ca)>"
  using K_less[OF assms] assms B_length
  by (sep_auto simp: csr_assn_def csr_reset_imp_def csr_reset_def nth_list_update)

lemma csr_step_upto_imp_rule:
  assumes "v \<in> K" "v < length Hl" "Hl ! v = H v"
    and "csr_has c v \<Longrightarrow>
           <csr_assn (csr_move c v) (Ba, Ea, Ca) * Ha \<mapsto>\<^sub>a Hl * F> f (csr_current c v) <Q>"
    and "\<not> csr_has c v \<Longrightarrow> <csr_assn c (Ba, Ea, Ca) * Ha \<mapsto>\<^sub>a Hl * F> g <Q>"
  shows "<csr_assn c (Ba, Ea, Ca) * Ha \<mapsto>\<^sub>a Hl * F> csr_step_upto_imp (Ba, Ea, Ca) Ha v f g <Q>"
proof (cases "csr_has c v")
  case True
  have hv: "c v < H v" using True by (simp add: csr_has_def)
  have cE: "c v < length E"
    using hv H_hi[OF K_less[OF assms(1)]] B_bound[OF K_less[OF assms(1)]] by linarith
  have post: "<csr_assn (c(v := Suc (c v))) (Ba, Ea, Ca) * Ha \<mapsto>\<^sub>a Hl * F> f (E ! c v) <Q>"
    using assms(4)[OF True] hv by (simp add: csr_move_def csr_current_def)
  show ?thesis
    using K_less[OF assms(1)] assms(1-3) hv cE
    by (sep_auto simp: csr_step_upto_imp_def csr_assn_def nth_list_update
                 heap: post[unfolded csr_assn_def prod.case])
next
  case False
  have hv: "\<not> c v < H v" using False by (simp add: csr_has_def)
  show ?thesis
    using K_less[OF assms(1)] assms(1-3) hv
    by (sep_auto simp: csr_step_upto_imp_def csr_assn_def
                 heap: assms(5)[OF False, unfolded csr_assn_def prod.case])
qed

lemma csr_empty_imp_rule:
  assumes "v < n"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_empty_imp Ba v
         <\<lambda>r. csr_assn c (Ba, Ea, Ca) * \<up>(r = csr_empty v)>"
  using assms B_length by (sep_auto simp: csr_assn_def csr_empty_imp_def csr_empty_def)

lemma csr_copy_imp_rule:
  "\<lbrakk>i \<le> n; length l = n; \<forall>j<i. l ! j = B ! j\<rbrakk> \<Longrightarrow>
   <Ba \<mapsto>\<^sub>a B * Ca \<mapsto>\<^sub>a l> csr_copy_imp n Ba Ca i
   <\<lambda>_. Ba \<mapsto>\<^sub>a B * (\<exists>\<^sub>Al'. Ca \<mapsto>\<^sub>a l' * \<up>(length l' = n \<and> (\<forall>j<n. l' ! j = B ! j)))>"
proof (induction "n - i" arbitrary: i l)
  case 0
  then have "i = n" by simp
  with 0 show ?case by (subst csr_copy_imp.simps) sep_auto
next
  case (Suc k)
  then have i: "i < n" by simp
  have IH: "<Ba \<mapsto>\<^sub>a B * Ca \<mapsto>\<^sub>a l[i := B ! i]> csr_copy_imp n Ba Ca (Suc i)
            <\<lambda>_. Ba \<mapsto>\<^sub>a B * (\<exists>\<^sub>Al'. Ca \<mapsto>\<^sub>a l' * \<up>(length l' = n \<and> (\<forall>j<n. l' ! j = B ! j)))>"
    by (rule Suc.hyps(1)) (use Suc i in \<open>auto simp: nth_list_update less_Suc_eq\<close>)
  show ?case
    using i B_length Suc.prems by (subst csr_copy_imp.simps) (sep_auto heap: IH)
qed

lemma csr_cursor_init_rule:
  "<Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E> csr_cursor_init n Ba <\<lambda>Ca. csr_assn (\<lambda>v. B ! v) (Ba, Ea, Ca)>"
proof -
  have K': "\<And>l' v. length l' = n \<Longrightarrow> v \<in> K \<Longrightarrow> v < length l'" using K_less by auto
  show ?thesis
    unfolding csr_cursor_init_def csr_assn_def
    by (sep_auto heap: csr_copy_imp_rule simp: K')
qed

end

context csr_graph_imp
begin

lemma csr_has_imp_rule:
  assumes "v \<in> K"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_has_imp (Ba, Ea, Ca) v
         <\<lambda>r. csr_assn c (Ba, Ea, Ca) * \<up>(r = csr_has c v)>"
  using K_less[OF assms] assms B_length
  by (sep_auto simp: csr_assn_def csr_has_imp_def csr_has_def)

sublocale csr_imp: indexed_iterable_set_imp csr_invar csr_abstract csr_current csr_has
    csr_iterated csr_remaining csr_move csr_reset K csr_assn csr_current_imp csr_has_imp
    csr_move_imp csr_reset_imp
proof (unfold_locales, goal_cases)
  case (1 C i Ci) then show ?case
    by (cases Ci) (simp add: csr_current_imp_rule)
next
  case (2 C i Ci) then show ?case
    by (cases Ci) (simp add: csr_has_imp_rule)
next
  case (3 C i Ci) then show ?case
    by (cases Ci) (simp add: csr_move_imp_rule)
next
  case (4 C i Ci) then show ?case
    by (cases Ci) (simp add: csr_reset_imp_rule)
qed

end

subsection \<open>Folding over a block\<close>

text \<open>The entries of the block of a vertex can also be folded over directly, without a cursor
      array: the fold reads the two bounds from \<open>B\<close> and runs over that range of \<open>E\<close>. It needs
      neither the cursor array nor distinct entries within a block, so its rule is stated for any
      arrays \<open>B\<close> and \<open>E\<close>.

      The rule of @{const iterate_range_strict} in @{theory Imperative.Array_Range_Iteration}
      requires the end of the range to be a valid index; the last block ends at the length of
      the array.\<close>

lemma nths_strict_split_off_first_le:
  assumes "start < end" "end \<le> length list"
  shows "nths list {start..<end} = list ! start # nths list {Suc start..<end}"
proof -
  have "start < length (take end list)"
    using assms by simp
  then have "drop start (take end list) = take end list ! start # drop (Suc start) (take end list)"
    by (rule Cons_nth_drop_Suc[symmetric])
  then show ?thesis
    using assms(1) unfolding nths_intervall_strict_as_drop_and_take by simp
qed

lemma iterate_range_strict_le_rule:
  assumes "\<And> acc acci x. x \<in> set (nths list {start..<end}) \<Longrightarrow> <acc_assn acc acci * F> fi x acci
            <\<lambda> r. acc_assn (f acc x) r * F>"
  shows "<arr \<mapsto>\<^sub>a list * \<up> (end \<le> length list) *F * acc_assn acc acci>
          iterate_range_strict arr start end fi acci
         <\<lambda> r. arr \<mapsto>\<^sub>a list * acc_assn (foldl f acc (nths list {start..<end})) r * F>"
  using assms
proof(induction arbitrary: start acc acci rule: iterate_range_strict.fixp_induct, goal_cases)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case
    by simp
next
  case (3 fi start acc acci)
  note IH = this
  show ?case
     using IH(1)[of "Suc start" "f acc _"] IH(2)
     by (sep_auto simp: nths_strict_split_off_first_le[of start] split: if_split)
qed

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

subsection \<open>Reading the input\<close>

text \<open>The endpoints of the input edges (@{const e_src}, @{const e_tgt}) are read from the input
      arrays. The arrays are only read, so the assertion for them is carried as a frame.\<close>

definition ends_assn :: "nat list \<Rightarrow> nat list \<Rightarrow> nat array \<times> nat array \<Rightarrow> assn" where
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
  csr_copy_imp.simps[code]

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
  "wnb_reset_all_imp n = (\<lambda>((Ba, Ea, Ca), Wa). csr_copy_imp n Ba Ca 0)"

lemma wnb_handle_cases:
  obtains Ba Ea Ca Wa where "Ci = ((Ba, Ea, Ca), Wa)"
  by (cases Ci) (metis prod_cases3)

locale weighted_csr = csr_graph_imp n K B E
  for n K B and E :: "'e::heap list" +
  fixes tgt :: "'e \<Rightarrow> 'a"
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

lemma wnb_inj: "v \<in> K \<Longrightarrow> inj_on tgt (csr_abstract c v)"
  by (simp add: csr_abstract_def seg_def tgt_inj)

lemma iterated_sub: "\<lbrakk>csr_invar c; v \<in> K\<rbrakk> \<Longrightarrow> csr_iterated c v \<subseteq> csr_abstract c v"
  using csr.idx_partition_union by blast

lemma remaining_sub: "\<lbrakk>csr_invar c; v \<in> K\<rbrakk> \<Longrightarrow> csr_remaining c v \<subseteq> csr_abstract c v"
  using csr.idx_partition_union by blast

lemma wnb_remaining_ne: "wnb_remaining c v \<noteq> {} \<longleftrightarrow> csr_remaining c v \<noteq> {}"
  by (simp add: wnb_remaining_def)

sublocale wnb: indexed_iterable_set csr_invar wnb_abstract wnb_current csr_has
    wnb_iterated wnb_remaining csr_move csr_reset K
proof (unfold_locales, goal_cases)
  case (1 C i)
  have "csr_iterated C i \<inter> csr_remaining C i = {}" using 1 by (rule csr.idx_partition_disjoint)
  thus ?case
    using inj_on_image_Int[OF wnb_inj[OF 1(2)] iterated_sub[OF 1] remaining_sub[OF 1]]
    by (simp add: wnb_iterated_def wnb_remaining_def)
next
  case (2 C i)
  thus ?case using csr.idx_partition_union[OF 2]
    by (simp add: wnb_iterated_def wnb_remaining_def wnb_abstract_def flip: image_Un)
next
  case (3 C i)
  thus ?case using csr.idx_has[OF 3] by (simp add: wnb_remaining_def)
next
  case (4 C i)
  hence r: "csr_remaining C i \<noteq> {}" by (simp add: wnb_remaining_ne)
  thus ?case using csr.idx_current[OF 4(1,2) r] by (simp add: wnb_current_def wnb_remaining_def)
next
  case (5 C i)
  thus ?case by (rule csr.idx_move_invar)
next
  case (6 C i j)
  hence r: "csr_remaining C i \<noteq> {}" by (simp add: wnb_remaining_ne)
  thus ?case using csr.idx_move_abstract[OF 6(1,2) r] by (simp add: wnb_abstract_def)
next
  case (7 C i)
  hence r: "csr_remaining C i \<noteq> {}" by (simp add: wnb_remaining_ne)
  have cur: "csr_current C i \<in> csr_remaining C i" using csr.idx_current[OF 7(1,2) r] .
  have "tgt ` (csr_remaining C i - {csr_current C i}) =
        tgt ` csr_remaining C i - tgt ` {csr_current C i}"
    using remaining_sub[OF 7(1,2)] cur
    by (intro inj_on_image_set_diff[OF wnb_inj[OF 7(2)]]) auto
  thus ?case
    by (simp add: wnb_remaining_def wnb_current_def csr.idx_move_remaining[OF 7(1,2) r])
next
  case (8 C i)
  hence r: "csr_remaining C i \<noteq> {}" by (simp add: wnb_remaining_ne)
  thus ?case
    by (simp add: wnb_iterated_def wnb_current_def csr.idx_move_iterated[OF 8(1,2) r])
next
  case (9 C i j)
  hence r: "csr_remaining C i \<noteq> {}" by (simp add: wnb_remaining_ne)
  thus ?case
    by (simp add: wnb_remaining_def csr.idx_move_remaining_other[OF 9(1,2) r 9(4)])
next
  case (10 C i j)
  hence r: "csr_remaining C i \<noteq> {}" by (simp add: wnb_remaining_ne)
  thus ?case
    by (simp add: wnb_iterated_def csr.idx_move_iterated_other[OF 10(1,2) r 10(4)])
next
  case (11 C i)
  thus ?case by (rule csr.idx_reset_invar)
next
  case (12 C i j)
  thus ?case by (simp add: wnb_abstract_def csr.idx_reset_abstract)
next
  case (13 C i)
  thus ?case by (simp add: wnb_iterated_def csr.idx_reset_iterated)
next
  case (14 C i)
  thus ?case by (simp add: wnb_remaining_def wnb_abstract_def csr.idx_reset_remaining)
next
  case (15 C i j)
  thus ?case by (simp add: wnb_remaining_def csr.idx_reset_remaining_other)
next
  case (16 C i j)
  thus ?case by (simp add: wnb_iterated_def csr.idx_reset_iterated_other)
qed

subsection \<open>The Imperative Collection\<close>

definition wnb_assn :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat array \<times> 'e array \<times> nat array) \<times> 'w array \<Rightarrow> assn" where
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
proof -
  have lt: "c v < B ! Suc v" using assms(3) by (simp add: remaining_ne)
  have ge: "B ! v \<le> c v" using assms(1,2) by (simp add: csr_invar_def)
  have wl: "c v < length W" using lt B_bound[OF K_less[OF assms(1)]] W_length by simp
  have wc: "wval (W ! c v) = cost v (wnb_current c v)"
    using W_cost[OF assms(1) ge lt] by (simp add: wnb_current_def csr_current_def)
  show ?thesis
    using K_less[OF assms(1)] assms(1) wl wc
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
  by (sep_auto heap: csr_copy_imp_rule simp: K_less)

sublocale wnb_imp: weighted_neighbourhoods_imp_spec csr_invar wnb_abstract wnb_current csr_has
    wnb_iterated wnb_remaining csr_move csr_reset K cost wval "\<lambda>v. B ! v" wnb_assn
    wnb_has_imp "wnb_current_imp tgt" wnb_current_cost_imp wnb_move_imp wnb_reset_imp
    "wnb_reset_all_imp n"
proof (unfold_locales, goal_cases)
  case 1 show ?case by (rule csr_init_invar)
next
  case (2 C i Ci)
  obtain Ba Ea Ca Wa where Ci: "Ci = ((Ba, Ea, Ca), Wa)" by (rule wnb_handle_cases)
  show ?case unfolding Ci by (rule wnb_has_imp_rule[OF 2(2)])
next
  case (3 C i Ci)
  obtain Ba Ea Ca Wa where Ci: "Ci = ((Ba, Ea, Ca), Wa)" by (rule wnb_handle_cases)
  have r: "csr_remaining C i \<noteq> {}" using 3(3) by (simp add: wnb_remaining_ne)
  show ?case unfolding Ci by (rule wnb_current_imp_rule[OF 3(2,1) r])
next
  case (4 C i Ci)
  obtain Ba Ea Ca Wa where Ci: "Ci = ((Ba, Ea, Ca), Wa)" by (rule wnb_handle_cases)
  have r: "csr_remaining C i \<noteq> {}" using 4(3) by (simp add: wnb_remaining_ne)
  show ?case unfolding Ci by (rule wnb_current_cost_imp_rule[OF 4(2,1) r])
next
  case (5 C i Ci)
  obtain Ba Ea Ca Wa where Ci: "Ci = ((Ba, Ea, Ca), Wa)" by (rule wnb_handle_cases)
  have r: "csr_remaining C i \<noteq> {}" using 5(3) by (simp add: wnb_remaining_ne)
  show ?case unfolding Ci by (rule wnb_move_imp_rule[OF 5(2) r])
next
  case (6 C i Ci)
  obtain Ba Ea Ca Wa where Ci: "Ci = ((Ba, Ea, Ca), Wa)" by (rule wnb_handle_cases)
  show ?case unfolding Ci by (rule wnb_reset_imp_rule[OF 6(2)])
next
  case (7 C Ci)
  obtain Ba Ea Ca Wa where Ci: "Ci = ((Ba, Ea, Ca), Wa)" by (rule wnb_handle_cases)
  show ?case unfolding Ci by (rule wnb_reset_all_imp_rule)
qed

end

end
