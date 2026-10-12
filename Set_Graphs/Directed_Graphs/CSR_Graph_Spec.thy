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

lemma map_nth_upt_take_drop:
  "b \<le> length xs \<Longrightarrow> map ((!) xs) [a..<b] = take (b - a) (drop a xs)"
  by (rule nth_equalityI) auto

locale csr_ranges =
  fixes n :: nat
    and K :: "nat set"
    and B :: "nat list"
    and H :: "nat \<Rightarrow> nat"
    and E :: "'e list"
  assumes K_bound: "K \<subseteq> {..<n}"
    and B_length: "length B = Suc n"
    and H_lo: "\<And>v. v < n \<Longrightarrow> B ! v \<le> H v"
    and B_bound: "\<And>v. v < n \<Longrightarrow> B ! Suc v \<le> length E"
    and E_distinct: "\<And>v. v < n \<Longrightarrow> inj_on ((!) E) {B ! v..<H v}"
    and H_hi: "\<And>v. v < n \<Longrightarrow> H v \<le> B ! Suc v"
begin

text \<open>The entries are distinct within each range only; different ranges may share entries,
      e.g.\ when \<open>E\<close> holds the targets of the edges.\<close>

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

lemma K_less: "v \<in> K \<Longrightarrow> v < n"
  using K_bound by auto

lemma B_mono: "v < n \<Longrightarrow> B ! v \<le> B ! Suc v"
  using H_lo H_hi order.trans by blast

lemma B_le: "\<lbrakk>i \<le> j; j \<le> n\<rbrakk> \<Longrightarrow> B ! i \<le> B ! j"
proof (induction j)
  case (Suc j)
  show ?case
  proof (cases "i = Suc j")
    case False
    then have "B ! i \<le> B ! j" using Suc by (simp add: le_Suc_eq)
    also have "\<dots> \<le> B ! Suc j" using Suc.prems(2) by (intro B_mono) simp
    finally show ?thesis .
  qed simp
qed simp

text \<open>The block reserved for one vertex lies outside the ranges of all other vertices.\<close>

lemma block_disjoint:
  assumes "u < n" "v < n" "u \<noteq> v" "B ! v \<le> p" "p < B ! Suc v"
  shows "p \<notin> {B ! u..<H u}"
proof
  assume p: "p \<in> {B ! u..<H u}"
  show False
  proof (cases "u < v")
    case True
    then have "B ! Suc u \<le> B ! v" using assms(2) by (intro B_le) auto
    then show False using p H_hi[OF assms(1)] assms(4) by auto
  next
    case False
    then have "B ! Suc v \<le> B ! u" using assms(1,3) by (intro B_le) auto
    then show False using p assms(5) by auto
  qed
qed

lemma seg_empty_iff: "seg a b = {} \<longleftrightarrow> b \<le> a"
  by (auto simp: seg_def)

lemma seg_Int:
  assumes "v < n" "B ! v \<le> a" "b \<le> H v" "B ! v \<le> a'" "b' \<le> H v"
  shows "seg a b \<inter> seg a' b' = (!) E ` ({a..<b} \<inter> {a'..<b'})"
  unfolding seg_def using assms
  by (intro inj_on_image_Int[OF E_distinct[OF assms(1)], symmetric]) auto

lemma seg_Un: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> seg a b \<union> seg b c = seg a c"
  unfolding seg_def by (metis image_Un ivl_disj_un_two(3))

lemma seg_Suc:
  assumes "v < n" "B ! v \<le> a" "a < b" "b \<le> H v"
  shows "seg (Suc a) b = seg a b - {E ! a}"
proof -
  have "(!) E ` ({a..<b} - {a}) = (!) E ` {a..<b} - (!) E ` {a}"
    using assms by (intro inj_on_image_set_diff[OF E_distinct[OF assms(1)]]) auto
  moreover have "{a..<b} - {a} = {Suc a..<b}" by auto
  ultimately show ?thesis by (simp add: seg_def)
qed

lemma seg_snoc: "a \<le> b \<Longrightarrow> seg a (Suc b) = seg a b \<union> {E ! b}"
  unfolding seg_def by (auto simp: less_Suc_eq)

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

sublocale csr: indexed_iterable_set csr_invar csr_abstract csr_current csr_has csr_iterated
    csr_remaining csr_move csr_reset K
proof (unfold_locales, goal_cases)
  case (1 C i)
  then have "B ! i \<le> C i" "C i \<le> H i" by (auto simp: csr_invar_def)
  then show ?case
    by (auto simp: csr_iterated_def csr_remaining_def seg_Int[OF K_less[OF 1(2)]])
next
  case (2 C i) then show ?case
    by (auto simp: csr_invar_def csr_iterated_def csr_remaining_def csr_abstract_def seg_Un)
next
  case (3 C i) then show ?case by (simp add: csr_has_def remaining_ne)
next
  case (4 C i) then show ?case
    by (auto simp: csr_current_def csr_remaining_def remaining_ne seg_def)
next
  case (5 C i) then show ?case
    by (auto simp: csr_invar_def csr_move_def)
next
  case (6 C i j) then show ?case by (simp add: csr_abstract_def)
next
  case (7 C i)
  then have "C i < H i" "B ! i \<le> C i" by (auto simp: remaining_ne csr_invar_def)
  then show ?case
    by (simp add: csr_remaining_def csr_move_def csr_current_def seg_Suc[OF K_less[OF 7(2)]])
next
  case (8 C i)
  then have "C i < H i" "B ! i \<le> C i" by (auto simp: remaining_ne csr_invar_def)
  then show ?case by (simp add: csr_iterated_def csr_move_def csr_current_def seg_snoc)
next
  case (9 C i j) then show ?case by (simp add: csr_remaining_def csr_move_def)
next
  case (10 C i j) then show ?case by (simp add: csr_iterated_def csr_move_def)
next
  case (11 C i) then show ?case
    by (auto simp: csr_invar_def csr_reset_def H_lo K_less)
next
  case (12 C i j) then show ?case by (simp add: csr_abstract_def)
next
  case (13 C i) show ?case by (rule csr_reset_iterated)
next
  case (14 C i) show ?case by (rule csr_reset_remaining)
next
  case (15 C i j) then show ?case by (simp add: csr_reset_remaining_other)
next
  case (16 C i j) then show ?case by (simp add: csr_reset_iterated_other)
qed

text \<open>The facts clients need, so that they never unfold the definitions.\<close>

lemma csr_abstract_eq: "csr_abstract c v = (!) E ` {B ! v..<H v}"
  by (simp add: csr_abstract_def seg_def)

lemma csr_card_abstract: "v < n \<Longrightarrow> card (csr_abstract c v) = H v - B ! v"
  by (simp add: csr_abstract_eq card_image[OF E_distinct])

text \<open>The cursors at the starts of the ranges.\<close>

lemma csr_init_invar: "csr_invar (\<lambda>v. B ! v)"
  by (simp add: csr_invar_def H_lo K_less)

lemma csr_init_iterated: "csr_iterated (\<lambda>v. B ! v) v = {}"
  by (simp add: csr_iterated_def seg_def)

end

text \<open>Empty ranges over the same lists: the start of a sub-collection built by \<open>csr_append\<close>.\<close>

lemma csr_ranges_start:
  assumes "csr_ranges n K B H E" "\<And>v. v < n \<Longrightarrow> H' v = B ! v"
  shows "csr_ranges n K B H' E"
proof -
  interpret csr_ranges n K B H E by (rule assms(1))
  show ?thesis
    by unfold_locales (simp_all add: assms(2) K_bound B_length B_bound B_mono)
qed

text \<open>The iterators of a growing set of vertices: initially none, then each one is added with its
      cursor reset. So the cursors of the other vertices need no initialisation.\<close>

lemma csr_ranges_subset: "csr_ranges n K B H E \<Longrightarrow> K' \<subseteq> {..<n} \<Longrightarrow> csr_ranges n K' B H E"
  by (auto simp: csr_ranges_def)

lemma csr_invar_empty:
  assumes "csr_ranges n K B H E"
  shows "csr_ranges.csr_invar {} B H c"
  using csr_ranges.csr_invar_def[OF csr_ranges_subset[OF assms, of "{}"]] by simp

lemma csr_invar_reset_insert:
  assumes R: "csr_ranges n K B H E" and "csr_ranges.csr_invar K B H c" "v < n"
  shows "csr_ranges.csr_invar (insert v K) B H (csr_ranges.csr_reset B c v)"
proof -
  have R': "csr_ranges n (insert v K) B H E"
    using assms(3) csr_ranges.K_bound[OF R] by (intro csr_ranges_subset[OF R]) auto
  show ?thesis
    using assms(2,3) csr_ranges.H_lo[OF R]
    by (auto simp: csr_ranges.csr_invar_def[OF R'] csr_ranges.csr_invar_def[OF R]
                   csr_ranges.csr_reset_def[OF R])
qed

text \<open>Appending entry \<open>x\<close> to the range of vertex \<open>v\<close>: \<open>x\<close> is written at the end of the range, which
      moves by one. The ends are a list, as stored by the imperative programs.\<close>

definition csr_append :: "nat \<Rightarrow> 'e \<Rightarrow> nat list \<times> 'e list \<Rightarrow> nat list \<times> 'e list" where
  "csr_append v x = (\<lambda>(Hl, E). (Hl[v := Suc (Hl ! v)], E[Hl ! v := x]))"

lemma length_csr_append[simp]:
  "length (fst (csr_append v x p)) = length (fst p)" "length (snd (csr_append v x p)) = length (snd p)"
  by (cases p, simp add: csr_append_def)+

lemma csr_ranges_append:
  assumes R: "csr_ranges n K B ((!) Hl) E"
    and v: "v < n" "v < length Hl" "Hl ! v < B ! Suc v"
    and x: "x \<notin> csr_ranges.csr_abstract B ((!) Hl) E c v"
    and app: "csr_append v x (Hl, E) = (Hl', E')"
  shows "csr_ranges n K B ((!) Hl') E'"
    and "u < n \<Longrightarrow> csr_ranges.csr_abstract B ((!) Hl') E' c u =
           (if u = v then insert x (csr_ranges.csr_abstract B ((!) Hl) E c u)
            else csr_ranges.csr_abstract B ((!) Hl) E c u)"
proof -
  interpret R: csr_ranges n K B "(!) Hl" E by (rule R)
  define p where "p = Hl ! v"
  have Hl': "Hl' = Hl[v := Suc p]" and E': "E' = E[p := x]"
    using app by (auto simp: csr_append_def p_def)
  have pE: "p < length E" using v(3) R.B_bound[OF v(1)] by (simp add: p_def)
  have pv: "B ! v \<le> p" using R.H_lo[OF v(1)] by (simp add: p_def)
  have pS: "p < B ! Suc v" using v(3) by (simp add: p_def)
  have Hl'_nth: "Hl' ! u = (if u = v then Suc p else Hl ! u)" for u
    using v(2) by (auto simp: Hl' nth_list_update)
  have E'_eq: "E' ! i = E ! i" if "i \<noteq> p" for i
    using that by (metis E' nth_list_update_neq)
  have Ex: "E' ! p = x" using pE by (simp add: E')
  have other: "E' ! i = E ! i" if "u < n" "u \<noteq> v" "i \<in> {B ! u..<Hl ! u}" for u i
    using R.block_disjoint[OF that(1) v(1) that(2) pv pS] that(3) E'_eq by auto
  have own: "E' ! i = E ! i" if "i \<in> {B ! v..<p}" for i
    using that E'_eq by auto
  have ivl: "{B ! v..<Suc p} = insert p {B ! v..<p}" using pv by auto
  have old: "R.csr_abstract c v = (!) E ` {B ! v..<p}"
    by (simp add: R.csr_abstract_eq p_def)
  have img_own: "(!) E' ` {B ! v..<p} = (!) E ` {B ! v..<p}"
    using own by (intro image_cong refl) auto
  have img_other: "(!) E' ` {B ! u..<Hl ! u} = (!) E ` {B ! u..<Hl ! u}"
    if "u < n" "u \<noteq> v" for u
    using other[OF that] by (intro image_cong refl) auto
  show R': "csr_ranges n K B ((!) Hl') E'"
  proof (unfold_locales, goal_cases)
    case 1 show ?case by (rule R.K_bound)
  next
    case 2 show ?case by (rule R.B_length)
  next
    case (3 u) then show ?case using R.H_lo[OF 3] pv by (auto simp: Hl'_nth)
  next
    case (4 u) then show ?case using R.B_bound[OF 4] by (simp add: E')
  next
    case (5 u)
    show ?case
    proof (cases "u = v")
      case True
      have "inj_on ((!) E') {B ! v..<p} = inj_on ((!) E) {B ! v..<p}"
        using own by (intro inj_on_cong) auto
      moreover have "inj_on ((!) E) {B ! v..<p}"
        using R.E_distinct[OF v(1)] by (simp add: p_def)
      moreover have "x \<notin> (!) E' ` {B ! v..<p}"
        using x old img_own by simp
      moreover have "p \<notin> {B ! v..<p}" by simp
      ultimately show ?thesis
        using True by (simp add: Hl'_nth ivl Ex)
    next
      case False
      have "inj_on ((!) E') {B ! u..<Hl ! u} = inj_on ((!) E) {B ! u..<Hl ! u}"
        using other[OF 5 False] by (intro inj_on_cong) auto
      then show ?thesis
        using R.E_distinct[OF 5] False by (simp add: Hl'_nth)
    qed
  next
    case (6 u) then show ?case using R.H_hi[OF 6] pS by (auto simp: Hl'_nth)
  qed
  interpret R': csr_ranges n K B "(!) Hl'" E' by (rule R')
  show "R'.csr_abstract c u = (if u = v then insert x (R.csr_abstract c u) else R.csr_abstract c u)"
    if "u < n"
  proof (cases "u = v")
    case True
    then show ?thesis
      using old img_own by (simp add: R'.csr_abstract_eq Hl'_nth ivl Ex)
  next
    case False
    then show ?thesis
      using img_other[OF that False] by (simp add: R'.csr_abstract_eq R.csr_abstract_eq Hl'_nth)
  qed
qed

subsection \<open>The graph in CSR form\<close>

text \<open>The out-edges of vertex \<open>v\<close> are the entries \<open>E!i\<close> for \<open>B!v \<le> i < B!(v+1)\<close>: the ranges
      end where the next one starts.\<close>

locale csr_graph = csr_ranges n K B "\<lambda>v. B ! Suc v" E
  for n K B and E :: "'e list"
begin

lemma csr_empty_iff: "v < n \<Longrightarrow> csr_empty v \<longleftrightarrow> csr_abstract c v = {}"
  using B_mono[of v] by (auto simp: csr_empty_def csr_abstract_def seg_empty_iff)

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
  using fs_bound[OF nth_mem] ts_bound[OF nth_mem] ts_length by auto

lemma verts_bound: "verts fs ts \<subseteq> {..<n}"
  using edge_bound by (auto simp: dVs_def multigraph_spec.make_pair_def)

lemma key_bound: "e \<in> edges fs \<Longrightarrow> key e < n"
  using key_endpoint edge_bound[of e] by (elim disjE) simp_all

sublocale inp: csr_buildup "edge_next fs" "edge_seq fs" "\<lambda>_. True" key n 0
  by (rule csr_buildup.intro[OF edge_iterator])
     (unfold_locales, auto simp: edge_seq_def intro!: key_bound)

lemma es_edges: "set inp.es = edges fs"
  by (simp add: inp.es_def edges_seq)

lemma E_spec_distinct: "distinct inp.E_spec"
proof -
  have "distinct (concat (map inp.blk [0..<k])) \<and> set (concat (map inp.blk [0..<k])) \<subseteq> {e. key e < k}"
    for k
  proof (induction k)
    case 0 show ?case by simp
  next
    case (Suc k) then show ?case
      using edge_seq_distinct[of fs 0] by (fastforce simp: inp.blk_def inp.es_def)
  qed
  then show ?thesis by (simp add: inp.E_spec_def)
qed

lemma E_spec_edges: "set inp.E_spec = edges fs"
  using inp.key_es by (auto simp: inp.E_spec_def inp.blk_def es_edges[symmetric])

lemma E_spec_ids: "e \<in> set inp.E_spec \<Longrightarrow> e < length fs"
  by (simp add: E_spec_edges)

lemma verts_eq: "verts fs ts = set fs \<union> set ts"
proof
  show "verts fs ts \<subseteq> set fs \<union> set ts"
    using ts_length by (auto simp: dVs_def multigraph_spec.make_pair_def)
next
  show "set fs \<union> set ts \<subseteq> verts fs ts"
  proof
    fix v
    assume "v \<in> set fs \<union> set ts"
    then obtain i where i: "i < length fs" "v = fs ! i \<or> v = ts ! i"
      using ts_length by (auto simp: in_set_conv_nth)
    have "(fs ! i, ts ! i) \<in> multigraph_spec.make_pair (e_src fs) (e_tgt fs ts) ` edges fs"
      using i(1) by (intro rev_image_eqI[of i]) (simp_all add: multigraph_spec.make_pair_def)
    thus "v \<in> verts fs ts"
      using i(2) unfolding dVs_def by blast
  qed
qed

lemma B_spec_bound: "v < n \<Longrightarrow> inp.B_spec ! Suc v \<le> length inp.E_spec"
  using inp.start_mono[of "Suc v" n] by (simp add: inp.B_spec_nth inp.start_n inp.length_E_spec)

sublocale graph: csr_graph n "verts fs ts" inp.B_spec inp.E_spec
proof (unfold_locales, goal_cases)
  case 1 show ?case by (rule verts_bound)
next
  case 2 show ?case by (rule inp.length_B_spec)
next
  case (3 v) then show ?case by (simp add: inp.B_spec_nth inp.start_mono)
next
  case (4 v) then show ?case by (rule B_spec_bound)
next
  case (5 v) then show ?case
    using B_spec_bound[OF 5] by (intro inj_on_nth[OF E_spec_distinct]) auto
next
  case (6 v) show ?case by (rule order.refl)
qed

text \<open>The block of a vertex holds exactly the edges whose key is that vertex.\<close>

lemma block_key:
  assumes "v < n"
  shows "(!) inp.E_spec ` {inp.B_spec ! v..<inp.B_spec ! Suc v} = {e \<in> edges fs. key e = v}"
proof -
  have "(!) inp.E_spec ` {inp.B_spec ! v..<inp.B_spec ! Suc v} =
        set (map ((!) inp.E_spec) [inp.B_spec ! v..<inp.B_spec ! Suc v])"
    by simp
  also have "\<dots> = set (take (inp.B_spec ! Suc v - inp.B_spec ! v) (drop (inp.B_spec ! v) inp.E_spec))"
    using B_spec_bound[OF assms] by (simp add: map_nth_upt_take_drop)
  also have "\<dots> = set (inp.blk v)"
    using inp.csr_block[OF assms] by simp
  also have "\<dots> = {e \<in> edges fs. key e = v}"
    by (auto simp: inp.blk_def es_edges[symmetric])
  finally show ?thesis .
qed

lemma csr_abstract_key:
  assumes "v \<in> verts fs ts"
  shows "graph.csr_abstract c v = {e \<in> edges fs. key e = v}"
  using assms verts_bound block_key by (auto simp: graph.csr_abstract_eq)

end

end
