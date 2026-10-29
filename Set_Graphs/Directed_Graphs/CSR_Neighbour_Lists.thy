theory CSR_Neighbour_Lists
  imports Directed_Set_Graphs.CSR_Graph Data_Structures.Imp_Range_Iteration
begin

section \<open>Concatenated Blocks as a CSR\<close>

text \<open>The functional model of a CSR given by the block of every vertex: the starts of the blocks
      and the entries, the blocks of all vertices concatenated in vertex order.\<close>

subsection \<open>Abstract Construction\<close>

text \<open>Start of the block of vertex v in the entries.\<close>
definition csr_start :: "(nat \<Rightarrow> 'x list) \<Rightarrow> nat \<Rightarrow> nat" where
  "csr_start blk v = sum_list (map (\<lambda>u. length (blk u)) [0..<v])"

text \<open>The entries: the blocks of the vertices below n concatenated (as an Isabelle list).\<close>
definition csr_entries :: "(nat \<Rightarrow> 'x list) \<Rightarrow> nat \<Rightarrow> 'x list" where
  "csr_entries blk n = concat (map blk [0..<n])"

text \<open>Neighbours of vertex v in edge list es.\<close>
definition nbrs :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "nbrs es v = map snd (filter (\<lambda>e. fst e = v) es)"

subsection \<open>Basic Properties\<close>

lemma length_csr_entries: "length (csr_entries blk n) = csr_start blk n"
  unfolding csr_entries_def csr_start_def
  by (simp add: length_concat comp_def)

lemma csr_start_0 [simp]: "csr_start blk 0 = 0"
  unfolding csr_start_def
  by simp

lemma csr_start_Suc:
  "csr_start blk (Suc v) = csr_start blk v + length (blk v)"
  unfolding csr_start_def
  by simp

subsection \<open>Monotonicity of csr\_start\<close>

lemma csr_start_mono:
  "v \<le> n \<Longrightarrow> csr_start blk v \<le> csr_start blk n"
  by (induction n) (auto simp: csr_start_Suc le_Suc_eq)

subsection \<open>The Key Indexing Lemma\<close>

text \<open>
The strict-interval segment at vertex v in the entries equals blk v.
Proof: split the list at v using id\_take\_nth\_drop, then use
nths\_intervall\_strict\_as\_drop\_and\_take.
\<close>

lemma csr_entries_nths:
  "v < n \<Longrightarrow> nths (csr_entries blk n) {csr_start blk v ..< csr_start blk v + length (blk v)} = blk v"
  using upt_add_eq_append[of 0 v "n - v"] upt_conv_Cons[of v n]
  by (simp add: csr_entries_def csr_start_def nths_intervall_strict_as_drop_and_take length_concat comp_def)

lemma nbrs_append [simp]:
  "nbrs (xs @ ys) v = nbrs xs v @ nbrs ys v"
  unfolding nbrs_def
  by simp

subsection \<open>The Concatenated Blocks as a CSR\<close>

text \<open>The block starts of the vertices up to \<open>n\<close> and the entries form a CSR whose block of a
  vertex below \<open>n\<close> is its block under \<open>blk\<close>.\<close>

locale csr_concat =
  fixes blk :: "nat \<Rightarrow> 'x::heap list" and n :: nat
begin

sublocale csr_graph_blocks_imp n "{..<n}" "map (csr_start blk) [0..<Suc n]" "csr_entries blk n"
  using csr_start_mono[of "Suc v" n blk for v, unfolded csr_start_Suc]
  by unfold_locales (simp_all add: csr_start_Suc length_csr_entries del: upt_Suc)

lemma csr_list_blk: "u < n \<Longrightarrow> csr_list u = blk u"
  using csr_list_nths csr_entries_nths[of u n blk]
  by (simp add: csr_start_Suc del: upt_Suc)

end

subsection \<open>Building the CSR Block by Block\<close>

text \<open>When the blocks are produced vertex by vertex in vertex order, the CSR is built
  without sorting, in two passes over the vertices: the first writes the end of the block of
  every vertex \<open>u\<close> into entry \<open>u + 1\<close> of the block array, whose entry \<open>0\<close> is \<open>0\<close>, and returns
  the number of entries; the second writes the blocks into the entry array allocated in
  between, whose initial entries \<open>d\<close> are all overwritten. The step \<open>cnt u c\<close> adds the length
  of the block of \<open>u\<close> to \<open>c\<close>, the step \<open>wr u G p\<close> writes the block into \<open>G\<close> from position
  \<open>p\<close> on and returns the position after it.\<close>

definition "csr_concat_starts_imp cnt Ba n = foldl_range_imp (\<lambda> u c. do {
     c' \<leftarrow> cnt u c;
     Array.upd (Suc u) c' Ba;
     return c' }) 0 n 0"

definition "csr_concat_fill_imp wr Ga n = foldl_range_imp (\<lambda> u p. wr u Ga p) 0 n 0"

definition "csr_concat_build_imp d cnt wr n = do {
   Ba \<leftarrow> Array.new (Suc n) 0;
   m \<leftarrow> csr_concat_starts_imp cnt Ba n;
   Ga \<leftarrow> Array.new m d;
   csr_concat_fill_imp wr Ga n;
   return (Ba, Ga) }"

text \<open>Arrays whose entries below \<open>u\<close> are written.\<close>

definition "prefix_map f u n = map (\<lambda> v. if v < u then f v else (0 :: nat)) [0..<n]"

lemma length_prefix_map [simp]: "length (prefix_map f u n) = n"
  unfolding prefix_map_def
  by simp

lemma prefix_map_upd:
  "\<lbrakk>u < n; x = f u\<rbrakk> \<Longrightarrow> list_update (prefix_map f u n) u x = prefix_map f (Suc u) n"
  unfolding prefix_map_def
  by (auto intro!: nth_equalityI simp: nth_list_update)

lemma prefix_map_n: "prefix_map f n n = map f [0..<n]"
  unfolding prefix_map_def
  by simp

lemma prefix_map_Suc_0: "f 0 = 0 \<Longrightarrow> prefix_map f (Suc 0) n = replicate n 0"
  unfolding prefix_map_def
  by (auto intro!: nth_equalityI simp del: upt_Suc)

lemma csr_entries_Suc: "csr_entries blk (Suc u) = csr_entries blk u @ blk u"
  by (simp add: csr_entries_def)

locale csr_concat_build =
  fixes blk :: "nat \<Rightarrow> 'x::heap list" and n :: nat and F :: assn and d :: 'x
    and cnt :: "nat \<Rightarrow> nat \<Rightarrow> nat Heap" and wr :: "nat \<Rightarrow> 'x array \<Rightarrow> nat \<Rightarrow> nat Heap"
  assumes cnt_rule: "u < n \<Longrightarrow> <F> cnt u c <\<lambda> r. F * \<up>(r = c + length (blk u))>"
    and wr_rule: "\<lbrakk>u < n; p + length (blk u) \<le> length g\<rbrakk> \<Longrightarrow>
      <G \<mapsto>\<^sub>a g * F> wr u G p
      <\<lambda> r. G \<mapsto>\<^sub>a (take p g @ blk u @ drop (p + length (blk u)) g) * F *
            \<up>(r = p + length (blk u))>"
begin

lemma csr_concat_starts_rule:
  "<F * Ba \<mapsto>\<^sub>a replicate (Suc n) 0> csr_concat_starts_imp cnt Ba n
   <\<lambda> m. F * Ba \<mapsto>\<^sub>a map (csr_start blk) [0..<Suc n] * \<up>(m = csr_start blk n)>"
proof-
  define A where "A = (\<lambda> u (_ :: unit) c.
     Ba \<mapsto>\<^sub>a prefix_map (csr_start blk) (Suc u) (Suc n) * \<up>(c = csr_start blk u))"
  have "<A 0 () 0 * F> csr_concat_starts_imp cnt Ba n
        <\<lambda> r. A n (foldl (\<lambda> a j. ()) () [0..<n]) r * F>"
    unfolding csr_concat_starts_imp_def
    by (intro foldl_range_imp_idx_rule[where A = A and F = F and g = "\<lambda> _ _. ()"])
      (sep_auto heap: cnt_rule simp: A_def prefix_map_upd csr_start_Suc)+
  thus ?thesis
    by (rule ht_cons_prec[rotated 2]) (sep_auto simp: A_def prefix_map_Suc_0 prefix_map_n)+
qed

lemma csr_concat_fill_rule:
  "<F * Ga \<mapsto>\<^sub>a replicate (csr_start blk n) d> csr_concat_fill_imp wr Ga n
   <\<lambda> _. F * Ga \<mapsto>\<^sub>a csr_entries blk n>"
proof-
  define A where "A = (\<lambda> u (gl :: 'x list) p.
     Ga \<mapsto>\<^sub>a gl * \<up>(p = csr_start blk u \<and> length gl = csr_start blk n \<and>
                     take p gl = csr_entries blk u))"
  define g where "g = (\<lambda> u (gl :: 'x list).
     take (csr_start blk u) gl @ blk u @ drop (csr_start blk (Suc u)) gl)"
  have step: "<A u gl p * F> wr u Ga p <\<lambda> r. A (Suc u) (g u gl) r * F>" if "u < n" for u gl p
  proof(cases "p = csr_start blk u \<and> length gl = csr_start blk n")
    case True
    moreover have "p + length (blk u) \<le> length gl"
      using True csr_start_mono[of "Suc u" n blk] that
      by (simp add: csr_start_Suc)
    ultimately show ?thesis
      using that
      unfolding A_def g_def
      by (sep_auto heap: wr_rule simp: csr_start_Suc csr_entries_Suc length_csr_entries)
  qed (sep_auto simp: A_def)
  have "<A 0 (replicate (csr_start blk n) d) 0 * F> csr_concat_fill_imp wr Ga n
        <\<lambda> r. A n (foldl (\<lambda> a j. g j a) (replicate (csr_start blk n) d) [0..<n]) r * F>"
    unfolding csr_concat_fill_imp_def
    by (intro foldl_range_imp_idx_rule[where A = A and F = F and g = g]) (simp_all add: step)
  thus ?thesis
    by (rule ht_cons_prec[rotated 2]) (sep_auto simp: A_def csr_entries_def)+
qed

lemma csr_concat_build_rule:
  "<F> csr_concat_build_imp d cnt wr n
   <\<lambda> (Ba, Ga). F * Ba \<mapsto>\<^sub>a map (csr_start blk) [0..<Suc n] * Ga \<mapsto>\<^sub>a csr_entries blk n>"
  unfolding csr_concat_build_imp_def
  by (sep_auto heap: csr_concat_starts_rule csr_concat_fill_rule)

end

end

