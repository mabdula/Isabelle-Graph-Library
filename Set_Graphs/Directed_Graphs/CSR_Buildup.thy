theory CSR_Buildup
  imports Main Data_Structures.More_Lists
begin

section \<open>Building a CSR Representation of a Multigraph\<close>

text \<open>
  A multigraph is given by a collection of edges of an arbitrary type @{typ 'e}.
  Every edge has a source vertex, and vertices are mapped to indices \<open>0..<n\<close>.
  The CSR representation consists of
  \<^item> an edge array \<open>E\<close> of length \<open>m\<close> where the edges are grouped by (the index of) their source,
  \<^item> a boundary array \<open>B\<close> of length \<open>n+1\<close> with \<open>B!0 = 0\<close> and \<open>B!n = m\<close>,
    such that the edges leaving the vertex with index \<open>i\<close> are exactly \<open>E[B!i..<B!(i+1)]\<close>.

  The edges are not given as a list but by a restartable iterator.
  This covers both an explicit sequence of edges and a counter over a range of edge names.
\<close>

subsection \<open>Iterators\<close>

text \<open>
  An iterator state \<open>s\<close> is abstracted to the list \<open>it_seq s\<close> of elements still to be produced.
\<close>

locale iterator =
  fixes it_next :: "'s \<Rightarrow> ('e \<times> 's) option"
    and it_seq :: "'s \<Rightarrow> 'e list"
    and it_invar :: "'s \<Rightarrow> bool"
  assumes it_next_None: "it_invar s \<Longrightarrow> it_next s = None \<longleftrightarrow> it_seq s = []"
      and it_next_Some: "\<lbrakk>it_invar s; it_next s = Some (e, s')\<rbrakk>
                          \<Longrightarrow> it_invar s' \<and> it_seq s = e # it_seq s'"
begin

partial_function (tailrec) it_fold :: "('e \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a" where
  "it_fold f s acc =
     (case it_next s of None \<Rightarrow> acc
                      | Some (e, s') \<Rightarrow> it_fold f s' (f e acc))"

lemma it_fold_is_fold: "it_invar s \<Longrightarrow> it_fold f s acc = fold f (it_seq s) acc"
  by (induction "it_seq s" arbitrary: s acc)
    (subst it_fold.simps, auto simp: it_next_None dest: it_next_Some split: option.split)+

lemma it_fold_None: "it_next s = None \<Longrightarrow> it_fold f s acc = acc"
  by (subst it_fold.simps) simp

lemma it_fold_Some: "it_next s = Some (e, s') \<Longrightarrow> it_fold f s acc = it_fold f s' (f e acc)"
  by (subst it_fold.simps) simp

end

subsubsection \<open>Instances\<close>

text \<open>A counter over the range \<open>[lo..<hi]\<close>, needing constant memory.\<close>

definition range_next :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "range_next hi k = (if k < hi then Some (k, Suc k) else None)"

definition range_seq :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "range_seq hi k = [k..<hi]"

interpretation range_it: iterator "range_next hi" "range_seq hi" "\<lambda>_. True"
  by unfold_locales
     (auto simp add: range_next_def range_seq_def upt_conv_Cons split: if_splits)

text \<open>An explicit sequence of edges.\<close>

fun list_next :: "'e list \<Rightarrow> ('e \<times> 'e list) option" where
  "list_next [] = None"
| "list_next (x # xs) = Some (x, xs)"

interpretation list_it: iterator list_next id "\<lambda>_. True"
  by unfold_locales (auto elim: list_next.elims)

subsection \<open>Specification\<close>

text \<open>
  The construction only needs a key \<open>key e < n\<close> for every edge,
  which will be the index of the source vertex.
\<close>

locale csr_buildup = iterator it_next it_seq it_invar
  for it_next :: "'s \<Rightarrow> ('e \<times> 's) option"
    and it_seq :: "'s \<Rightarrow> 'e list"
    and it_invar :: "'s \<Rightarrow> bool" +
  fixes key :: "'e \<Rightarrow> nat"
    and n :: nat
    and s0 :: 's
  assumes s0_invar: "it_invar s0"
      and key_bound: "e \<in> set (it_seq s0) \<Longrightarrow> key e < n"
begin

definition "es = it_seq s0"

definition "blk i = filter (\<lambda>e. key e = i) es"

definition "E_spec = concat (map blk [0..<n])"

definition "B_spec = map (\<lambda>i. sum_list (map (length \<circ> blk) [0..<i])) [0..<Suc n]"

subsection \<open>Functional Algorithm\<close>

text \<open>
  A counting sort in three passes that uses no memory beyond \<open>B\<close> and \<open>E\<close>:
  \<^enum> Count: \<open>B!(k+2)\<close> counts the edges with key \<open>k\<close> (for \<open>k+2 \<le> n\<close>), and \<open>m\<close> counts all edges.
  \<^enum> Prefix sums over \<open>B\<close>: afterwards \<open>B!(k+1)\<close> is the start of block \<open>k\<close>.
  \<^enum> Fill with a restarted iterator: \<open>B!(k+1)\<close> serves as the cursor of block \<open>k\<close>.
    Once all edges are placed, \<open>B!(k+1)\<close> is the end of block \<open>k\<close>, i.e.\ the start of block \<open>k+1\<close>.
\<close>

definition count_step :: "'e \<Rightarrow> nat list \<times> nat \<Rightarrow> nat list \<times> nat" where
  "count_step e = (\<lambda>(B, m).
     (let k = key e in if k + 2 \<le> n then B[k + 2 := B ! (k + 2) + 1] else B, Suc m))"

definition "count_edges = it_fold count_step s0 (replicate (Suc n) 0, 0)"

definition prefix_step :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "prefix_step j B = B[j := B ! j + B ! (j - 1)]"

definition prefix_sums :: "nat list \<Rightarrow> nat list" where
  "prefix_sums B = fold prefix_step [1..<Suc n] B"

text \<open>The edge array is initialised with the first edge, so no default element of @{typ 'e} is needed.\<close>

definition init_E :: "nat \<Rightarrow> 'e list" where
  "init_E m = (case it_next s0 of None \<Rightarrow> [] | Some (e, _) \<Rightarrow> replicate m e)"

definition fill_step :: "'e \<Rightarrow> nat list \<times> 'e list \<Rightarrow> nat list \<times> 'e list" where
  "fill_step e = (\<lambda>(B, E).
     (let k = key e; p = B ! (k + 1) in (B[k + 1 := Suc p], E[p := e])))"

definition csr_build :: "nat list \<times> 'e list" where
  "csr_build =
     (let (B, m) = count_edges;
          B = prefix_sums B
      in it_fold fill_step s0 (B, init_E m))"

subsection \<open>Correctness\<close>

definition sel :: "nat \<Rightarrow> 'e list \<Rightarrow> 'e list" where
  "sel k xs = filter (\<lambda>e. key e = k) xs"

lemma sel_Nil[simp]: "sel k [] = []"
  by (simp add: sel_def)

lemma sel_Cons: "sel k (x # xs) = (if key x = k then x # sel k xs else sel k xs)"
  by (simp add: sel_def)

lemma sel_single[simp]: "sel k [x] = (if key x = k then [x] else [])"
  by (simp add: sel_def)

lemma sel_append[simp]: "sel k (xs @ ys) = sel k xs @ sel k ys"
  by (simp add: sel_def)

lemma blk_sel: "blk k = sel k es"
  by (simp add: blk_def sel_def)

lemma it_fold_s0: "it_fold f s0 acc = fold f es acc"
  by (simp add: it_fold_is_fold[OF s0_invar] es_def)

lemma key_es: "x \<in> set es \<Longrightarrow> key x < n"
  using key_bound
  by (simp add: es_def)

text \<open>Start of the block with key \<open>k\<close> in \<open>E_spec\<close>.\<close>

definition "start k = sum_list (map (length \<circ> blk) [0..<k])"

lemma start_0[simp]: "start 0 = 0"
  by (simp add: start_def)

lemma start_Suc: "start (Suc k) = start k + length (blk k)"
  by (simp add: start_def)

lemma start_mono: "k \<le> k' \<Longrightarrow> start k \<le> start k'"
  by (induction k') (auto simp add: start_Suc le_Suc_eq intro: trans_le_add1)

lemma start_n: "start n = length es"
  using sum_length_filter_key[of es key n] key_es
  by (simp add: start_def blk_def interv_sum_list_conv_sum_set_nat)

lemma start_blk_le: "k < n \<Longrightarrow> start k + length (blk k) \<le> length es"
  using start_mono[of "Suc k" n]
  by (simp add: start_Suc start_n)

lemma B_spec_start: "B_spec = map start [0..<Suc n]"
  by (simp add: B_spec_def start_def)

subsubsection \<open>Counting\<close>

definition count_B :: "'e list \<Rightarrow> nat list" where
  "count_B xs = map (\<lambda>i. if i < 2 then 0 else length (sel (i - 2) xs)) [0..<Suc n]"

lemma length_count_B[simp]: "length (count_B xs) = Suc n"
  by (simp add: count_B_def)

lemma count_B_nth: "i < Suc n \<Longrightarrow> count_B xs ! i = (if i < 2 then 0 else length (sel (i - 2) xs))"
  unfolding count_B_def
  by (subst nth_map_upt) auto

lemma count_step_count_B:
  "count_step x (count_B xs, length xs) = (count_B (xs @ [x]), length (xs @ [x]))"
  unfolding count_step_def Let_def
  by (auto intro!: nth_equalityI simp add: count_B_nth nth_list_update)

lemma fold_count_step: "fold count_step xs (replicate (Suc n) 0, 0) = (count_B xs, length xs)"
  by (induction xs rule: rev_induct)
    (auto intro: nth_equalityI simp: count_step_count_B count_B_nth simp del: replicate_Suc)

lemma count_edges: "count_edges = (count_B es, length es)"
  by (simp add: count_edges_def it_fold_s0 fold_count_step del: replicate_Suc)

subsubsection \<open>Prefix Sums\<close>

lemma fold_prefix_step:
  assumes "j \<le> n"
  shows "fold prefix_step [1..<Suc j] (map g [0..<Suc n])
         = map (\<lambda>i. if i \<le> j then sum_list (map g [0..<Suc i]) else g i) [0..<Suc n]"
  using assms
  by (induction j)
    (auto intro!: nth_equalityI simp: prefix_step_def nth_list_update upt_Suc_append[of "Suc 0"]
      upt_Suc_append[of 0 0] upt_Suc_append[of 0 "Suc m" for m] simp del: upt_Suc)

lemma sum_count_B:
  "sum_list (map (\<lambda>l. if l < 2 then 0 else length (blk (l - 2))) [0..<Suc i]) = start (i - 1)"
  by (induction i rule: induct_nat_012) (simp_all add: start_Suc)

lemma prefix_sums_count_B: "prefix_sums (count_B es) = map (\<lambda>i. start (i - 1)) [0..<Suc n]"
  using fold_prefix_step[of n "\<lambda>l. if l < 2 then 0 else length (blk (l - 2))"]
  unfolding prefix_sums_def count_B_def blk_sel[symmetric]
  by (auto intro!: map_cong simp: sum_count_B simp del: upt_Suc)

subsubsection \<open>Filling\<close>

definition fill_invar :: "'e list \<Rightarrow> nat list \<times> 'e list \<Rightarrow> bool" where
  "fill_invar xs = (\<lambda>(B, E).
     length B = Suc n \<and> length E = length es \<and> B ! 0 = 0 \<and>
     (\<forall>k<n. B ! Suc k = start k + length (sel k xs)) \<and>
     (\<forall>k<n. \<forall>i<length (sel k xs). E ! (start k + i) = sel k xs ! i))"

lemma length_init_E: "length (init_E (length es)) = length es"
  unfolding init_E_def
  by (auto split: option.split simp add: es_def it_next_None[OF s0_invar])

lemma fill_invar_init: "fill_invar [] (prefix_sums (count_B es), init_E (length es))"
  by (simp add: fill_invar_def prefix_sums_count_B length_init_E del: upt_Suc)

lemma start_disjoint:
  "\<lbrakk>k' \<noteq> k; i < length (blk k'); j < length (blk k)\<rbrakk> \<Longrightarrow> start k' + i \<noteq> start k + j"
  using start_mono[of "Suc k'" k] start_mono[of "Suc k" k']
  by (cases "k' < k") (auto simp: start_Suc)

lemma sel_prefix_le: "xs @ x # ys = es \<Longrightarrow> length (sel k (xs @ [x])) \<le> length (blk k)"
  by (drule sym) (simp add: blk_sel sel_Cons)

lemma fill_step_invar:
  assumes "xs @ x # ys = es" "fill_invar xs (B, E)"
  shows "fill_invar (xs @ [x]) (fill_step x (B, E))"
proof-
  have "key x < n" "B ! Suc (key x) = start (key x) + length (sel (key x) xs)"
    "Suc (length (sel (key x) xs)) \<le> length (blk (key x))"
    using key_es[of x, folded assms(1)] assms(2) sel_prefix_le[OF assms(1), of "key x"]
    by (auto simp: fill_invar_def)
  moreover have "start (key x) + length (sel (key x) xs) \<noteq> start k + i"
    if "k \<noteq> key x" "i < length (sel k xs)" for k i
    using that calculation(3) sel_prefix_le[OF assms(1), of k]
      start_disjoint[of k "key x" i "length (sel (key x) xs)"]
    by simp
  ultimately show ?thesis
    using assms(2) start_blk_le[of "key x"]
    by (auto simp: fill_invar_def fill_step_def Let_def nth_list_update nth_append)
qed

text \<open>The array accesses of a fill step are within bounds.\<close>

lemma fill_step_bounds:
  assumes "xs @ x # ys = es" "fill_invar xs (B, E)"
  shows "Suc (key x) < length B" "B ! Suc (key x) < length E"
  using key_es[of x, folded assms(1)] assms(2) start_blk_le[of "key x"]
    sel_prefix_le[OF assms(1), of "key x"]
  by (auto simp: fill_invar_def)

lemma fold_fill:
  assumes "xs @ ys = es" "fill_invar [] S"
  shows "fill_invar xs (fold fill_step xs S)"
  using assms(1)
proof(induction xs arbitrary: ys rule: rev_induct)
  case (snoc x xs)
  thus ?case
    using snoc.IH[of "x # ys"] fill_step_invar[of xs x ys]
    by (cases "fold fill_step xs S") simp
qed (simp add: assms(2))

subsubsection \<open>Main Theorem\<close>

text \<open>The fill pass does not depend on the initial contents of the edge array, only on its length.\<close>

lemma fill_correct:
  assumes "length E0 = length es"
  shows "fold fill_step es (prefix_sums (count_B es), E0) = (B_spec, E_spec)"
  using fold_fill[of es "[]" "(prefix_sums (count_B es), E0)"] assms
  by (cases "fold fill_step es (prefix_sums (count_B es), E0)")
    (auto intro!: nth_equalityI concat_eqI
      simp: E_spec_def fill_invar_def prefix_sums_count_B B_spec_start less_Suc_eq_0_disj start_Suc
      blk_sel take_map start_n[symmetric] start_def[symmetric] simp del: upt_Suc)

lemma csr_build_correct: "csr_build = (B_spec, E_spec)"
  using fill_correct[OF length_init_E]
  by (simp add: csr_build_def count_edges it_fold_s0)

subsubsection \<open>Reading off the Blocks\<close>

lemma E_spec_split:
  "k < n \<Longrightarrow> E_spec = concat (map blk [0..<k]) @ blk k @ concat (map blk [Suc k..<n])"
  using upt_add_eq_append[of 0 k "n - k"] upt_conv_Cons[of k n]
  by (simp add: E_spec_def)

lemma length_concat_blk: "length (concat (map blk [0..<k])) = start k"
  by (simp add: length_concat start_def)

lemma B_spec_nth: "i \<le> n \<Longrightarrow> B_spec ! i = start i"
  by (simp add: B_spec_start del: upt_Suc)

lemma B_spec_0: "B_spec ! 0 = 0"
  by (simp add: B_spec_nth)

lemma B_spec_n: "B_spec ! n = length es"
  by (simp add: B_spec_nth start_n)

lemma length_B_spec: "length B_spec = Suc n"
  by (simp add: B_spec_start)

lemma length_E_spec: "length E_spec = length es"
  using length_concat_blk[of n] start_n
  by (simp add: E_spec_def)

lemma csr_block:
  assumes "k < n"
  shows "take (B_spec ! Suc k - B_spec ! k) (drop (B_spec ! k) E_spec) = blk k"
  using assms
  by (simp add: B_spec_nth start_Suc E_spec_split length_concat_blk[symmetric])

lemma csr_build_block:
  assumes "csr_build = (B, E)" "k < n"
  shows "take (B ! Suc k - B ! k) (drop (B ! k) E) = filter (\<lambda>e. key e = k) (it_seq s0)"
  using assms csr_block
  by (simp add: csr_build_correct blk_def es_def)

end

subsection \<open>Multigraphs\<close>

text \<open>
  The CSR of an unweighted directed multigraph with edges and vertices of arbitrary types.
  The key of an edge is the index of its source vertex.
  Injectivity of the index is only needed to read off the out-edges of a vertex.
  The targets @{term tgt} play no role in the construction.

  This locale is not used yet; the algorithms use the CSR of \<open>csr_edge_spec\<close>, where edges
  and vertices are natural numbers. The iterator view and the imperative construction for
  arbitrary edge and vertex types are future work.
\<close>

locale csr_multigraph = iterator it_next it_seq it_invar
  for it_next :: "'s \<Rightarrow> ('e \<times> 's) option"
    and it_seq :: "'s \<Rightarrow> 'e list"
    and it_invar :: "'s \<Rightarrow> bool" +
  fixes src :: "'e \<Rightarrow> 'v"
    and tgt :: "'e \<Rightarrow> 'v"
    and V :: "'v set"
    and vidx :: "'v \<Rightarrow> nat"
    and n :: nat
    and s0 :: 's
  assumes s0_invar': "it_invar s0"
      and vidx_inj: "inj_on vidx V"
      and vidx_bound: "v \<in> V \<Longrightarrow> vidx v < n"
      and src_in_V: "e \<in> set (it_seq s0) \<Longrightarrow> src e \<in> V"
begin

sublocale csr: csr_buildup it_next it_seq it_invar "vidx \<circ> src" n s0
  by unfold_locales (auto intro: s0_invar' vidx_bound src_in_V)

definition "out_edges v = filter (\<lambda>e. src e = v) csr.es"

lemma blk_vidx: "v \<in> V \<Longrightarrow> csr.blk (vidx v) = out_edges v"
  unfolding csr.blk_def out_edges_def
  by (intro filter_cong) (auto dest: inj_onD[OF vidx_inj] src_in_V simp add: csr.es_def)

lemma csr_out_edges:
  assumes "csr.csr_build = (B, E)" "v \<in> V"
  shows "take (B ! Suc (vidx v) - B ! vidx v) (drop (B ! vidx v) E) = out_edges v"
  using assms csr.csr_block[of "vidx v"] vidx_bound[of v]
  by (simp add: csr.csr_build_correct blk_vidx)

end

end


