theory CSR_Graph
  imports CSR_Buildup_Imperative Weighted_Neighbourhoods_Imperative_Spec Directed_Set_Graphs.Multigraph
begin

section \<open>Graphs in CSR Form\<close>

text \<open>A graph in compressed sparse row (CSR) form, built by
      @{theory Directed_Set_Graphs.CSR_Buildup_Imperative}: an array \<open>B\<close> of block starts, an
      array \<open>E\<close> of edges sorted by source, and a cursor array \<open>C\<close>, initially a copy of the start
      indices. Advancing the iterator of a vertex increments its cursor; resetting it copies the
      start index back.

      The entries of \<open>E\<close> are generic: edge indices, which can index further arrays (e.g.\ of
      endpoints or weights), or directly what a search reads, e.g.\ the targets.\<close>

subsection \<open>The graph in CSR form with a cursor array\<close>

text \<open>The out-edges of vertex \<open>v\<close> are the entries \<open>E!i\<close> for \<open>B!v \<le> i < B!(v+1)\<close>. The functional
      model of the collection of iterators is the cursor function \<open>c\<close>: the edges before \<open>c v\<close> are
      iterated, the ones from \<open>c v\<close> on remain. The arrays \<open>B\<close> and \<open>E\<close> are never modified, so the
      start index needed for a reset is always available in \<open>B\<close>.\<close>

lemma map_nth_upt_take_drop:
  "b \<le> length xs \<Longrightarrow> map ((!) xs) [a..<b] = take (b - a) (drop a xs)"
  by (rule nth_equalityI) auto

locale csr_graph =
  fixes n :: nat
    and K :: "nat set"
    and B :: "nat list"
    and E :: "'e::heap list"
  assumes K_bound: "K \<subseteq> {..<n}"
    and B_length: "length B = Suc n"
    and B_mono: "\<And>v. v < n \<Longrightarrow> B ! v \<le> B ! Suc v"
    and B_bound: "\<And>v. v < n \<Longrightarrow> B ! Suc v \<le> length E"
    and E_distinct: "\<And>v. v < n \<Longrightarrow> inj_on ((!) E) {B ! v..<B ! Suc v}"
begin

text \<open>The entries are distinct within each segment only; different segments may share entries,
      e.g.\ when \<open>E\<close> holds the targets of the edges.\<close>

definition "seg a b = (!) E ` {a..<b}"

definition "csr_invar c \<longleftrightarrow> (\<forall>v\<in>K. B ! v \<le> c v \<and> c v \<le> B ! Suc v)"
definition "csr_abstract (c::nat \<Rightarrow> nat) v = seg (B ! v) (B ! Suc v)"
definition "csr_current c v = E ! c v"
definition "csr_has c v \<longleftrightarrow> c v < B ! Suc v"
definition "csr_iterated c v = seg (B ! v) (c v)"
definition "csr_remaining c v = seg (c v) (B ! Suc v)"
definition "csr_move c v = (if c v < B ! Suc v then c(v := Suc (c v)) else c)"
definition "csr_reset c v = c(v := B ! v)"

lemma K_less: "v \<in> K \<Longrightarrow> v < n"
  using K_bound by auto

lemma seg_empty_iff: "seg a b = {} \<longleftrightarrow> b \<le> a"
  by (auto simp: seg_def)

lemma seg_Int:
  assumes "v < n" "B ! v \<le> a" "b \<le> B ! Suc v" "B ! v \<le> a'" "b' \<le> B ! Suc v"
  shows "seg a b \<inter> seg a' b' = (!) E ` ({a..<b} \<inter> {a'..<b'})"
  unfolding seg_def using assms
  by (intro inj_on_image_Int[OF E_distinct[OF assms(1)], symmetric]) auto

lemma seg_Un: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> seg a b \<union> seg b c = seg a c"
  unfolding seg_def by (metis image_Un ivl_disj_un_two(3))

lemma seg_Suc:
  assumes "v < n" "B ! v \<le> a" "a < b" "b \<le> B ! Suc v"
  shows "seg (Suc a) b = seg a b - {E ! a}"
proof -
  have "(!) E ` ({a..<b} - {a}) = (!) E ` {a..<b} - (!) E ` {a}"
    using assms by (intro inj_on_image_set_diff[OF E_distinct[OF assms(1)]]) auto
  moreover have "{a..<b} - {a} = {Suc a..<b}" by auto
  ultimately show ?thesis by (simp add: seg_def)
qed

lemma seg_snoc: "a \<le> b \<Longrightarrow> seg a (Suc b) = seg a b \<union> {E ! b}"
  unfolding seg_def by (auto simp: less_Suc_eq)

lemma remaining_ne: "csr_remaining c v \<noteq> {} \<longleftrightarrow> c v < B ! Suc v"
  by (simp add: csr_remaining_def seg_empty_iff not_le)

sublocale csr: indexed_iterable_set csr_invar csr_abstract csr_current csr_has csr_iterated
    csr_remaining csr_move csr_reset K
proof (unfold_locales, goal_cases)
  case (1 C i)
  then have "B ! i \<le> C i" "C i \<le> B ! Suc i" by (auto simp: csr_invar_def)
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
  then have "C i < B ! Suc i" "B ! i \<le> C i" by (auto simp: remaining_ne csr_invar_def)
  then show ?case
    by (simp add: csr_remaining_def csr_move_def csr_current_def seg_Suc[OF K_less[OF 7(2)]])
next
  case (8 C i)
  then have "C i < B ! Suc i" "B ! i \<le> C i" by (auto simp: remaining_ne csr_invar_def)
  then show ?case by (simp add: csr_iterated_def csr_move_def csr_current_def seg_snoc)
next
  case (9 C i j) then show ?case by (simp add: csr_remaining_def csr_move_def)
next
  case (10 C i j) then show ?case by (simp add: csr_iterated_def csr_move_def)
next
  case (11 C i) then show ?case
    by (auto simp: csr_invar_def csr_reset_def B_mono K_less)
next
  case (12 C i j) then show ?case by (simp add: csr_abstract_def)
next
  case (13 C i) then show ?case by (simp add: csr_iterated_def csr_reset_def seg_def)
next
  case (14 C i) then show ?case by (simp add: csr_remaining_def csr_reset_def csr_abstract_def)
next
  case (15 C i j) then show ?case by (simp add: csr_remaining_def csr_reset_def)
next
  case (16 C i j) then show ?case by (simp add: csr_iterated_def csr_reset_def)
qed

end



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

context csr_graph
begin

definition csr_assn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat array \<times> 'e array \<times> nat array \<Rightarrow> assn" where
  "csr_assn c = (\<lambda>(Ba, Ea, Ca). Ba \<mapsto>\<^sub>a B * Ea \<mapsto>\<^sub>a E *
     (\<exists>\<^sub>Al. Ca \<mapsto>\<^sub>a l * \<up>(length l = n \<and> (\<forall>v\<in>K. l ! v = c v))))"

lemma csr_has_imp_rule:
  assumes "v \<in> K"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_has_imp (Ba, Ea, Ca) v
         <\<lambda>r. csr_assn c (Ba, Ea, Ca) * \<up>(r = csr_has c v)>"
  using K_less[OF assms] assms B_length
  by (sep_auto simp: csr_assn_def csr_has_imp_def csr_has_def)

lemma csr_current_imp_rule:
  assumes "v \<in> K" "csr_invar c" "csr_remaining c v \<noteq> {}"
  shows "<csr_assn c (Ba, Ea, Ca)> csr_current_imp (Ba, Ea, Ca) v
         <\<lambda>r. csr_assn c (Ba, Ea, Ca) * \<up>(r = csr_current c v)>"
proof -
  have "c v < length E"
    using assms B_bound[OF K_less[OF assms(1)]] by (auto simp: remaining_ne)
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

text \<open>The endpoints are read from the input arrays. The arrays are only read, so the assertion
      for them is carried as a frame.\<close>

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

text \<open>The key of an edge is its tail; the edge itself is stored.\<close>

definition edge_key :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "edge_key = src_imp"

definition edge_val :: "nat array \<times> nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "edge_val _ i = return i"

subsection \<open>The CSR buildup for the input\<close>

text \<open>The global interpretation of the CSR buildup for the input iterator. The locale
      @{locale imp_csr_buildup_code} only fixes operations and has no assumptions.\<close>

global_interpretation csr_code: imp_csr_buildup_code n edge_has_next edge_cur edge_adv edge_key
    edge_val
  for n
  defines csr_build_edges = csr_code.csr_build_imp
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

locale weighted_csr = csr_graph n K B E
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

lemma csr_init_invar: "csr_invar (\<lambda>v. B ! v)"
  by (simp add: csr_invar_def B_mono K_less)

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
