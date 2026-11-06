theory CSR_Graph_Spec
  imports CSR_Buildup Directed_Set_Graphs.Multigraph Data_Structures.Iterable_Set_Specs
begin

section \<open>Graphs in CSR Form: the Functional Specification\<close>

text \<open>A graph in compressed sparse row (CSR) form: a list \<open>B\<close> of block starts and a list \<open>E\<close>
      of edges sorted by source, as built by @{locale csr_buildup}, together with a cursor per
      vertex. This theory holds the functional model only; the imperative arrays and programs are
      in \<open>CSR_Graph\<close>.

      The entries of \<open>E\<close> are generic: edge indices, which can index further arrays (e.g.\ of
      endpoints or weights), or directly what a search reads, e.g.\ the targets.\<close>

subsection \<open>Ranges of a CSR with a cursor array\<close>

text \<open>The entries of vertex \<open>v\<close> are \<open>E!i\<close> for \<open>B!v \<le> i < H v\<close>, a prefix of the block
      \<open>[B!v..<B!(v+1))\<close> reserved for \<open>v\<close> in \<open>E\<close>. The graph in CSR form (\<open>csr_graph\<close> below) is
      the case \<open>H v = B!(v+1)\<close>. Shorter ends describe a sub-collection stored in place, e.g.\ the
      entries of each block that satisfy a condition, moved to the front of the block by
      \<open>csr_append\<close>.

      The functional model of the collection of iterators is the cursor function \<open>c\<close>: the entries
      before \<open>c v\<close> are iterated, the ones from \<open>c v\<close> on remain. The lists \<open>B\<close>, \<open>H\<close> and \<open>E\<close> are not
      modified by the iteration, so the start index needed for a reset is always available in
      \<open>B\<close>.\<close>

locale csr_blocks =
  fixes n :: nat
    and K :: "nat set"
    and B :: "nat list"
    and H :: "nat \<Rightarrow> nat"
    and E :: "'e list"
  assumes K_bound: "K \<subseteq> {..<n}"
    and B_length: "length B = Suc n"
    and H_lo: "\<And>v. v < n \<Longrightarrow> B ! v \<le> H v"
    and B_bound: "\<And>v. v < n \<Longrightarrow> B ! Suc v \<le> length E"
    and H_hi: "\<And>v. v < n \<Longrightarrow> H v \<le> B ! Suc v"
begin

text \<open>A range may contain an entry more than once. The features that need no distinct entries
      are provided here: the static view, the fold over a range and the reset of a cursor.
      Iterating by a cursor needs distinct entries within each range (@{text csr_ranges} below).\<close>

definition "seg a b = (!) E ` {a..<b}"

definition "csr_invar c \<longleftrightarrow> (\<forall>v\<in>K. B ! v \<le> c v \<and> c v \<le> H v)"
definition "csr_abstract (c::nat \<Rightarrow> nat) v = seg (B ! v) (H v)"
definition "csr_current c v = E ! c v"
definition "csr_has c v \<longleftrightarrow> c v < H v"
definition "csr_iterated c v = seg (B ! v) (c v)"
definition "csr_remaining c v = seg (c v) (H v)"
definition "csr_move c v = (if c v < H v then c(v := Suc (c v)) else c)"
definition "csr_reset c v = c(v := B ! v)"

text \<open>Emptiness of the block reserved for \<open>v\<close>, which holds the range of \<open>v\<close>.\<close>

definition "csr_empty v \<longleftrightarrow> B ! v = B ! Suc v"

text \<open>The entries of the range of \<open>v\<close> as a list, which a fold runs over, and the ranges as a
      map from the vertices below \<open>n\<close>, e.g.\ the neighbour lists of a graph.\<close>

definition "csr_list v = map ((!) E) [B ! v..<H v]"

definition "csr_map v = (if v < n then Some (csr_list v) else None)"

lemma K_less: "v \<in> K \<Longrightarrow> v < n"
  using K_bound
  by auto

lemma B_mono: "v < n \<Longrightarrow> B ! v \<le> B ! Suc v"
  using H_lo H_hi order.trans
  by blast

lemma B_le: "\<lbrakk>i \<le> j; j \<le> n\<rbrakk> \<Longrightarrow> B ! i \<le> B ! j"
  by (induction j) (auto simp: le_Suc_eq intro: order.trans[OF _ B_mono])

text \<open>The block reserved for one vertex lies outside the ranges of all other vertices.\<close>

lemma block_disjoint:
  assumes "u < n" "v < n" "u \<noteq> v" "B ! v \<le> p" "p < B ! Suc v"
  shows "p \<notin> {B ! u..<H u}"
  using B_le[of "Suc u" v] B_le[of "Suc v" u] H_hi[OF assms(1)] assms
  by (cases "u < v") fastforce+

lemma seg_empty_iff: "seg a b = {} \<longleftrightarrow> b \<le> a"
  by (auto simp: seg_def)

lemma seg_Un: "\<lbrakk>a \<le> b; b \<le> c\<rbrakk> \<Longrightarrow> seg a b \<union> seg b c = seg a c"
  unfolding seg_def
  by (simp add: image_Un[symmetric] ivl_disj_un_two(3))

lemma seg_snoc: "a \<le> b \<Longrightarrow> seg a (Suc b) = seg a b \<union> {E ! b}"
  unfolding seg_def
  by (auto simp: less_Suc_eq)

lemma remaining_ne: "csr_remaining c v \<noteq> {} \<longleftrightarrow> c v < H v"
  by (simp add: csr_remaining_def seg_empty_iff not_le)

text \<open>A reset needs no invariant: it also starts the iterator of a vertex whose cursor is arbitrary.\<close>

lemma csr_reset_iterated: "csr_iterated (csr_reset c v) v = {}"
  by (simp add: csr_iterated_def csr_reset_def seg_def)

lemma csr_reset_remaining: "csr_remaining (csr_reset c v) v = csr_abstract c v"
  by (simp add: csr_remaining_def csr_reset_def csr_abstract_def)

lemma csr_reset_remaining_other: "j \<noteq> v \<Longrightarrow> csr_remaining (csr_reset c v) j = csr_remaining c j"
  by (simp add: csr_remaining_def csr_reset_def)

lemma csr_reset_iterated_other: "j \<noteq> v \<Longrightarrow> csr_iterated (csr_reset c v) j = csr_iterated c j"
  by (simp add: csr_iterated_def csr_reset_def)

text \<open>The facts clients need, so that they never unfold the definitions.\<close>

lemma csr_abstract_eq: "csr_abstract c v = (!) E ` {B ! v..<H v}"
  by (simp add: csr_abstract_def seg_def)

lemma csr_list_set: "set (csr_list v) = csr_abstract c v"
  by (simp add: csr_list_def csr_abstract_eq)

text \<open>The fold over a range runs over the range in the order of the block.\<close>

definition "csr_fold (c::nat \<Rightarrow> nat) v f acc = foldl (\<lambda>acc x. f x acc) acc (csr_list v)"

sublocale csr: indexed_set_fold csr_invar csr_abstract K csr_fold
proof(unfold_locales, goal_cases)
  case (1 C i)
  show ?case
    by (intro exI[of _ "csr_list i"]) (simp add: csr_fold_def csr_list_set)
qed

sublocale csr: indexed_set_reset csr_invar csr_abstract K csr_iterated csr_remaining csr_reset
  by unfold_locales
    (simp_all add: csr_abstract_def csr_reset_iterated csr_reset_remaining csr_reset_remaining_other
      csr_reset_iterated_other, auto simp: csr_invar_def csr_reset_def H_lo K_less)

text \<open>The cursors at the starts of the ranges.\<close>

lemma csr_init_invar: "csr_invar (\<lambda>v. B ! v)"
  by (simp add: csr_invar_def H_lo K_less)

lemma csr_init_iterated: "csr_iterated (\<lambda>v. B ! v) v = {}"
  by (simp add: csr_iterated_def seg_def)

end

subsection \<open>Ranges with distinct entries\<close>

text \<open>The entries are distinct within each range only; different ranges may share entries,
      e.g.\ when \<open>E\<close> holds the targets of the edges. Distinctness is what the set semantics of
      the cursor needs: moving past the current entry removes it from the remaining ones.\<close>

locale csr_ranges = csr_blocks +
  assumes E_distinct: "\<And>v. v < n \<Longrightarrow> inj_on ((!) E) {B ! v..<H v}"
begin

lemma seg_Int:
  assumes "v < n" "B ! v \<le> a" "b \<le> H v" "B ! v \<le> a'" "b' \<le> H v"
  shows "seg a b \<inter> seg a' b' = (!) E ` ({a..<b} \<inter> {a'..<b'})"
  unfolding seg_def
  using assms
  by (intro inj_on_image_Int[OF E_distinct[OF assms(1)], symmetric]) auto

lemma seg_Suc:
  assumes "v < n" "B ! v \<le> a" "a < b" "b \<le> H v"
  shows "seg (Suc a) b = seg a b - {E ! a}"
proof-
  have "(!) E ` ({a..<b} - {a}) = (!) E ` {a..<b} - (!) E ` {a}"
    using assms
    by (intro inj_on_image_set_diff[OF E_distinct[OF assms(1)]]) auto
  moreover have "{a..<b} - {a} = {Suc a..<b}"
    by auto
  ultimately show ?thesis
    by (simp add: seg_def)
qed

sublocale csr: indexed_set_cursor csr_invar csr_abstract K csr_current csr_has csr_iterated
    csr_remaining csr_move
proof(unfold_locales, goal_cases)
  case (1 C i)
  then have "B ! i \<le> C i" "C i \<le> H i"
    by (auto simp: csr_invar_def)
  then show ?case
    by (auto simp: csr_iterated_def csr_remaining_def seg_Int[OF K_less[OF 1(2)]])
next
  case (2 C i) then show ?case
    by (auto simp: csr_invar_def csr_iterated_def csr_remaining_def csr_abstract_def seg_Un)
next
  case (3 C i)
  then show ?case
    by (simp add: csr_has_def remaining_ne)
next
  case (4 C i) then show ?case
    by (auto simp: csr_current_def csr_remaining_def remaining_ne seg_def)
next
  case (5 C i) then show ?case
    by (auto simp: csr_invar_def csr_move_def)
next
  case (6 C i j)
  then show ?case
    by (simp add: csr_abstract_def)
next
  case (7 C i)
  then have "C i < H i" "B ! i \<le> C i"
    by (auto simp: remaining_ne csr_invar_def)
  then show ?case
    by (simp add: csr_remaining_def csr_move_def csr_current_def seg_Suc[OF K_less[OF 7(2)]])
next
  case (8 C i)
  then have "C i < H i" "B ! i \<le> C i"
    by (auto simp: remaining_ne csr_invar_def)
  then show ?case
    by (simp add: csr_iterated_def csr_move_def csr_current_def seg_snoc)
next
  case (9 C i j)
  then show ?case
    by (simp add: csr_remaining_def csr_move_def)
next
  case (10 C i j)
  then show ?case
    by (simp add: csr_iterated_def csr_move_def)
qed

sublocale csr: indexed_iterable_set csr_invar csr_abstract csr_current csr_has csr_iterated
    csr_remaining csr_move csr_reset K
  by intro_locales

lemma iterated_sub: "\<lbrakk>csr_invar c; v \<in> K\<rbrakk> \<Longrightarrow> csr_iterated c v \<subseteq> csr_abstract c v"
  using csr.idx_partition_union
  by blast

lemma remaining_sub: "\<lbrakk>csr_invar c; v \<in> K\<rbrakk> \<Longrightarrow> csr_remaining c v \<subseteq> csr_abstract c v"
  using csr.idx_partition_union
  by blast

lemma csr_card_abstract: "v < n \<Longrightarrow> card (csr_abstract c v) = H v - B ! v"
  by (simp add: csr_abstract_eq card_image[OF E_distinct])

end

text \<open>Empty ranges over the same lists: the start of a sub-collection built by \<open>csr_append\<close>.\<close>

lemma csr_ranges_start:
  assumes "csr_ranges n K B H E" "\<And>v. v < n \<Longrightarrow> H' v = B ! v"
  shows "csr_ranges n K B H' E"
proof-
  interpret csr_ranges n K B H E
    by (fact assms(1))
  show ?thesis
    by unfold_locales (simp_all add: assms(2) K_bound B_length B_bound B_mono)
qed

text \<open>The iterators of a growing set of vertices: initially none, then each one is added with its
      cursor reset. So the cursors of the other vertices need no initialisation.\<close>

lemma csr_blocks_subset: "\<lbrakk>csr_blocks n K B H E; K' \<subseteq> {..<n}\<rbrakk> \<Longrightarrow> csr_blocks n K' B H E"
  by (auto simp: csr_blocks_def)

lemma csr_ranges_subset: "\<lbrakk>csr_ranges n K B H E; K' \<subseteq> {..<n}\<rbrakk> \<Longrightarrow> csr_ranges n K' B H E"
  by (auto simp: csr_ranges_def csr_blocks_def)

lemma csr_invar_empty: "csr_blocks n K B H E \<Longrightarrow> csr_blocks.csr_invar {} B H c"
  using csr_blocks.csr_invar_def[OF csr_blocks_subset[of n K B H E "{}"]]
  by simp

lemma csr_invar_reset_insert:
  assumes "csr_blocks n K B H E" "csr_blocks.csr_invar K B H c" "v < n"
  shows "csr_blocks.csr_invar (insert v K) B H (csr_blocks.csr_reset B c v)"
  using assms csr_blocks.H_lo[OF assms(1)] csr_blocks_subset[OF assms(1), of "insert v K"]
    csr_blocks.K_bound[OF assms(1)]
  by (auto simp: csr_blocks.csr_invar_def csr_blocks.csr_reset_def)

text \<open>Appending entry \<open>x\<close> to the range of vertex \<open>v\<close>: \<open>x\<close> is written at the end of the range, which
      moves by one. The ends are a list, as stored by the imperative programs.\<close>

definition csr_append :: "nat \<Rightarrow> 'e \<Rightarrow> nat list \<times> 'e list \<Rightarrow> nat list \<times> 'e list" where
  "csr_append v x = (\<lambda>(Hl, E). (Hl[v := Suc (Hl ! v)], E[Hl ! v := x]))"

lemma length_csr_append[simp]:
  "length (fst (csr_append v x p)) = length (fst p)" "length (snd (csr_append v x p)) = length (snd p)"
  by (cases p, simp add: csr_append_def)+

lemma csr_blocks_append:
  assumes "csr_blocks n K B ((!) Hl) E" "v < n" "v < length Hl" "Hl ! v < B ! Suc v"
    "csr_append v x (Hl, E) = (Hl', E')"
  shows "csr_blocks n K B ((!) Hl') E'"
    and "u < n \<Longrightarrow> csr_blocks.csr_abstract B ((!) Hl') E' c u =
           (if u = v then insert x (csr_blocks.csr_abstract B ((!) Hl) E c u)
            else csr_blocks.csr_abstract B ((!) Hl) E c u)"
proof-
  interpret R: csr_blocks n K B "(!) Hl" E
    by (fact assms(1))
  have Hl': "Hl' = Hl[v := Suc (Hl ! v)]" and E': "E' = E[Hl ! v := x]"
    using assms(5)
    by (auto simp: csr_append_def)
  have p: "Hl ! v < length E" "B ! v \<le> Hl ! v"
    using assms(4) R.B_bound[OF assms(2)] R.H_lo[OF assms(2)]
    by auto
  show R': "csr_blocks n K B ((!) Hl') E'"
    using R.K_bound R.B_length R.H_lo R.B_bound R.H_hi assms(2-4) p
    by unfold_locales (auto simp: Hl' E' nth_list_update intro: le_SucI)
  have "(!) E' ` {B ! u..<Hl ! u} = (!) E ` {B ! u..<Hl ! u}" if "u < n" for u
    using R.block_disjoint[OF that assms(2) _ p(2) assms(4)]
    by (cases "u = v") (auto simp: E' intro!: image_cong)
  thus "u < n \<Longrightarrow> csr_blocks.csr_abstract B ((!) Hl') E' c u =
           (if u = v then insert x (csr_blocks.csr_abstract B ((!) Hl) E c u)
            else csr_blocks.csr_abstract B ((!) Hl) E c u)"
    unfolding csr_blocks.csr_abstract_eq[OF R'] R.csr_abstract_eq
    using p assms(3)
    by (auto simp: Hl' E' atLeastLessThanSuc)
qed

text \<open>Appending a new entry keeps the entries of the ranges distinct.\<close>

lemma csr_ranges_append:
  assumes "csr_ranges n K B ((!) Hl) E" "v < n" "v < length Hl" "Hl ! v < B ! Suc v"
    "x \<notin> csr_blocks.csr_abstract B ((!) Hl) E c v" "csr_append v x (Hl, E) = (Hl', E')"
  shows "csr_ranges n K B ((!) Hl') E'"
    and "u < n \<Longrightarrow> csr_blocks.csr_abstract B ((!) Hl') E' c u =
           (if u = v then insert x (csr_blocks.csr_abstract B ((!) Hl) E c u)
            else csr_blocks.csr_abstract B ((!) Hl) E c u)"
proof-
  interpret R: csr_ranges n K B "(!) Hl" E
    by (fact assms(1))
  note A = csr_blocks_append[OF R.csr_blocks_axioms assms(2-4,6)]
  show "u < n \<Longrightarrow> csr_blocks.csr_abstract B ((!) Hl') E' c u =
           (if u = v then insert x (csr_blocks.csr_abstract B ((!) Hl) E c u)
            else csr_blocks.csr_abstract B ((!) Hl) E c u)"
    by (fact A(2))
  have "card (csr_blocks.csr_abstract B ((!) Hl') E' c u) = Hl' ! u - B ! u" if "u < n" for u
    using A(2)[OF that] R.csr_card_abstract[OF that] R.H_lo[OF that] assms(3,5,6)
    by (auto simp: R.csr_abstract_eq csr_append_def)
  thus "csr_ranges n K B ((!) Hl') E'"
    by (intro csr_ranges.intro[OF A(1)] csr_ranges_axioms.intro)
      (auto simp: csr_blocks.csr_abstract_eq[OF A(1)] inj_on_iff_eq_card)
qed

subsection \<open>The graph in CSR form\<close>

text \<open>The out-edges of vertex \<open>v\<close> are the entries \<open>E!i\<close> for \<open>B!v \<le> i < B!(v+1)\<close>: the ranges
      end where the next one starts.\<close>

locale csr_graph = csr_ranges n K B "\<lambda>v. B ! Suc v" E
  for n K B and E :: "'e list"
begin

lemma csr_empty_iff: "v < n \<Longrightarrow> csr_empty v \<longleftrightarrow> csr_abstract c v = {}"
  using B_mono[of v]
  by (auto simp: csr_empty_def csr_abstract_def seg_empty_iff)

end

subsection \<open>Edges and the input\<close>

text \<open>The graph is given by two lists of equal length \<open>m\<close> holding the first and the second
      endpoints; the edges are the indices \<open>i < m\<close>, with endpoints \<open>fs ! i\<close> and \<open>ts ! i\<close>.

      The multigraph locales ask for an edge between any two vertices (@{term create_edge}). The
      indices from \<open>m\<close> on serve for this: they encode the pairs of vertices. They are no edges of
      the graph and only occur in the abstract model.\<close>

definition e_src :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "e_src fs i = (if i < length fs then fs ! i else fst (prod_decode (i - length fs)))"

definition e_tgt :: "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "e_tgt fs ts i = (if i < length fs then ts ! i else snd (prod_decode (i - length fs)))"

definition e_new :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_new fs u v = length fs + prod_encode (u, v)"

lemma e_new_simps[simp]: "e_src fs (e_new fs u v) = u" "e_tgt fs ts (e_new fs u v) = v"
  by (simp_all add: e_src_def e_tgt_def e_new_def)

lemma e_nth[simp]: "i < length fs \<Longrightarrow> e_src fs i = fs ! i"
  "i < length fs \<Longrightarrow> e_tgt fs ts i = ts ! i"
  by (simp_all add: e_src_def e_tgt_def)

definition edges :: "nat list \<Rightarrow> nat set" where
  "edges fs = {..<length fs}"

abbreviation verts :: "nat list \<Rightarrow> nat list \<Rightarrow> nat set" where
  "verts fs ts \<equiv> dVs (multigraph_spec.make_pair (e_src fs) (e_tgt fs ts) ` edges fs)"

lemma edges_iff[simp]: "i \<in> edges fs \<longleftrightarrow> i < length fs"
  by (simp add: edges_def)

definition edge_seq :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "edge_seq fs i = [i..<length fs]"

definition edge_next :: "nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "edge_next fs i = (if i < length fs then Some (i, Suc i) else None)"

lemma edges_seq: "edges fs = set (edge_seq fs 0)"
  by (auto simp: edges_def edge_seq_def)

lemma edge_seq_distinct: "distinct (edge_seq fs i)"
  by (simp add: edge_seq_def)

lemma edge_iterator: "iterator (edge_next fs) (edge_seq fs) (\<lambda>_. True)"
  by unfold_locales (auto simp: edge_next_def edge_seq_def upt_conv_Cons split: if_splits)

subsection \<open>The input edges in CSR form\<close>

text \<open>The input: \<open>n\<close> bounds the vertices, @{term fs} and @{term ts} are the endpoint lists. The
      CSR form groups the edges by @{term key}, one of the two endpoints. The neighbourhoods are
      indexed by the vertices of the input.\<close>

locale csr_edge_spec =
  fixes n :: nat
    and fs :: "nat list"
    and ts :: "nat list"
    and key :: "nat \<Rightarrow> nat"
  assumes ts_length: "length ts = length fs"
    and fs_bound: "\<And>u. u \<in> set fs \<Longrightarrow> u < n"
    and ts_bound: "\<And>v. v \<in> set ts \<Longrightarrow> v < n"
    and key_endpoint: "key = e_src fs \<or> key = e_tgt fs ts"
begin

lemma edge_bound: "e \<in> edges fs \<Longrightarrow> e_src fs e < n \<and> e_tgt fs ts e < n"
  using fs_bound[OF nth_mem] ts_bound[OF nth_mem] ts_length
  by auto

lemma verts_bound: "verts fs ts \<subseteq> {..<n}"
  using edge_bound
  by (auto simp: dVs_def multigraph_spec.make_pair_def)

lemma key_bound: "e \<in> edges fs \<Longrightarrow> key e < n"
  using key_endpoint edge_bound[of e]
  by (elim disjE) simp_all

sublocale inp: csr_buildup "edge_next fs" "edge_seq fs" "\<lambda>_. True" key n 0
  by (rule csr_buildup.intro[OF edge_iterator])
     (unfold_locales, auto simp: edge_seq_def intro!: key_bound)

lemma es_edges: "set inp.es = edges fs"
  by (simp add: inp.es_def edges_seq)

lemma E_spec_distinct: "distinct inp.E_spec"
proof-
  have "distinct (concat (map inp.blk [0..<k]))
        \<and> set (concat (map inp.blk [0..<k])) \<subseteq> {e. key e < k}" for k
    using edge_seq_distinct[of fs 0]
    by (induction k) (fastforce simp: inp.blk_def inp.es_def)+
  thus ?thesis
    by (simp add: inp.E_spec_def)
qed

lemma E_spec_edges: "set inp.E_spec = edges fs"
  using inp.key_es
  by (auto simp: inp.E_spec_def inp.blk_def es_edges[symmetric])

lemma E_spec_ids: "e \<in> set inp.E_spec \<Longrightarrow> e < length fs"
  by (simp add: E_spec_edges)

lemma verts_eq: "verts fs ts = set fs \<union> set ts"
  using ts_length
  by (auto simp: dVs_eq multigraph_spec.make_pair_def image_image in_set_conv_nth)

lemma B_spec_bound: "v < n \<Longrightarrow> inp.B_spec ! Suc v \<le> length inp.E_spec"
  using inp.start_mono[of "Suc v" n]
  by (simp add: inp.B_spec_nth inp.start_n inp.length_E_spec)

sublocale graph: csr_graph n "verts fs ts" inp.B_spec inp.E_spec
  using verts_bound B_spec_bound inp.length_B_spec
  by unfold_locales (auto simp: inp.B_spec_nth inp.start_mono intro!: inj_on_nth[OF E_spec_distinct]
      intro: less_le_trans)

text \<open>The block of a vertex holds exactly the edges whose key is that vertex.\<close>

lemma block_key:
  "v < n \<Longrightarrow> (!) inp.E_spec ` {inp.B_spec ! v..<inp.B_spec ! Suc v} = {e \<in> edges fs. key e = v}"
  using B_spec_bound[of v] inp.csr_block[of v]
  by (simp add: map_nth_upt_take_drop inp.blk_def es_edges[symmetric] flip: set_upt set_map)

lemma csr_abstract_key:
  assumes "v \<in> verts fs ts"
  shows "graph.csr_abstract c v = {e \<in> edges fs. key e = v}"
  using assms verts_bound block_key
  by (auto simp: graph.csr_abstract_eq)

end

end
