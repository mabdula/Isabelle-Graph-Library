theory Network_Simplex_Initial_Basis
  imports Network_Simplex_Initial_Basis_Code
begin

text \<open>Proof layer of the list instantiation: it imports the single code theory
      \<open>Network_Simplex_Initial_Basis_Code\<close> (all executable definitions) and adds the
      cost-flow-network and acyclic-flow-instance interpretations, the eleven well-formedness
      assumptions, the proof-only constants (bigM, sized, dfs\_sized, is\_free) and every lemma.\<close>

locale initial_basis_lists =
  initial_basis_code_spec where capacity_list = capacity_list +
  real_embedding where h = "h :: 'n \<Rightarrow> real"
  for capacity_list :: "('n :: linordered_idom) list" and h :: "'n \<Rightarrow> real" +
  assumes length_edges: "length capacity_list = m"
      and length_cost: "length cost_list = length capacity_list"
      and length_fst:  "length fst_list  = length capacity_list"
      and length_snd:  "length snd_list  = length capacity_list"
      and length_flow: "length flow_list = length capacity_list"      and length_b:    "length b_list    = n"
      and cap_neg:     "\<forall> c \<in> set capacity_list. 0 \<le> c \<or> c = - 1"
      and edges_in_range: "set fst_list \<union> set snd_list \<subseteq> {1..n}"
      and num_edges_gtr_0: "m > 0"
      and isolated_zero: "\<And>i. i < n \<Longrightarrow> Suc i \<notin> set fst_list \<union> set snd_list \<Longrightarrow> b_list ! i = 0"
begin

text \<open>With the dense vertex model the vertex list is no longer an input: @{term vs_list} is the range
      @{term \<open>[Suc 0..<Suc n]\<close>} (materialised in the code locale), so distinctness, the absence of the
      null name @{term 0}, and the containment of every edge endpoint in @{term \<open>set vs_list\<close>} are all
      facts, not assumptions.  They keep their old names so downstream proofs are unaffected.\<close>

lemma no_zero_node: "0 \<notin> set vs_list" by (rule zero_notin_vs_list)
lemma distinct_vs_list: "distinct vs_list" by (rule distinct_vs_list_code)
lemma fst_snd_vs: "set fst_list \<union> set snd_list \<subseteq> set vs_list"
  using edges_in_range by (simp add: set_vs_list)


text \<open>We read the lists as a cost-flow network.  The genuine edges are the indices @{term \<open>{0..<m}\<close>};
      for such an edge the endpoints, cost and capacity are looked up in the parallel lists, a capacity
      of @{term \<open>- 1\<close>} being decoded as an infinite (@{term \<infinity>}) capacity.  The edge constructor
      @{term create_edge}, however, must return an edge for \<^emph>\<open>every\<close> pair of endpoints, so it maps a
      pair to @{term \<open>m + prod_encode (u, v)\<close>}, an index beyond the input range; the tail and head of
      such a synthetic edge are recovered through @{term prod_decode}, and its capacity is set to
      @{term \<infinity>}.  Discharging the multigraph and non-negativity axioms this way makes the context an
      instance of @{locale cost_flow_network}, and hence of @{locale cost_flow_spec}.\<close>

sublocale original_network: cost_flow_network
  where \<E>           = "{0..<m}"
    and fst          = "\<lambda> e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
    and snd          = "\<lambda> e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "\<lambda> u v. m + prod_encode (u, v)"    and \<u>           = "\<lambda> e. if e < m then (if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e))) else \<infinity>"
    and \<c>           = "\<lambda> e. h (cost_list ! e)"
proof(unfold_locales, goal_cases)
  case (1 x y)
  show ?case by simp
next
  case (2 x y)
  show ?case by simp
next
  case 3
  show ?case by simp
next
  case 4
  show ?case using num_edges_gtr_0 by simp
next
  case (5 e)
  show ?case
  proof(cases "e < m")
    case True
    hence "capacity_list ! e \<in> set capacity_list"
      by (metis length_edges nth_mem)
    thus ?thesis using cap_neg True by (auto simp add: zero_ereal_def)
  next
    case False
    thus ?thesis by simp
  qed
qed

lemma length_foldl_list_update:
  "length (foldl (\<lambda> arr (v, x). arr[v := x]) init ps) = length init"
  by (induct ps arbitrary: init) auto

lemma length_b_arr: "length b_arr = Suc vcount"
  by (simp add: b_arr_def length_foldl_list_update)

lemma le_foldr_max: "x \<in> set xs \<Longrightarrow> x \<le> foldr max xs (0::nat)"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  from Cons.prems have "x = a \<or> x \<in> set xs" by simp
  then show ?case
  proof
    assume "x = a" thus ?thesis by (simp add: max.cobounded1)
  next
    assume "x \<in> set xs"
    hence "x \<le> foldr max xs 0" using Cons.hyps by blast
    thus ?thesis by (simp add: max.coboundedI2)
  qed
qed

lemma vs_less_vcount: "v \<in> set vs_list \<Longrightarrow> v < vcount"
  using le_foldr_max[of _ vs_list] by (simp add: vcount_foldr less_Suc_eq_le)

text \<open>The balance of the artificial root.  Every name scattered into \<open>b_arr\<close> comes from
      vs\_list and is therefore smaller than vcount, so the last slot keeps the 0 it was initialised
      with.  The augmented network of the initial basis needs exactly this: the root neither supplies
      nor demands, and the artificial edges carry as much flow into it as out of it.\<close>

lemma foldl_scatter_miss:
  assumes "\<And>v x. (v, x) \<in> set ps \<Longrightarrow> v \<noteq> k"
  shows "foldl (\<lambda> arr (v, x). arr[v := x]) init ps ! k = init ! k"
  using assms
proof (induct ps arbitrary: init)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  obtain v x where p: "p = (v, x)" by (cases p)
  have vn: "v \<noteq> k" using Cons.prems p by auto
  have pr: "\<And>v' x'. (v', x') \<in> set ps \<Longrightarrow> v' \<noteq> k" using Cons.prems by auto
  show ?case using Cons.hyps[OF pr] vn by (simp add: p)
qed

lemma b_lookup_root: "b_lookup vcount = 0"
proof -
  have "\<And>v x. (v, x) \<in> set (zip vs_list b_list) \<Longrightarrow> v \<noteq> vcount"
    using vs_less_vcount by (auto dest: set_zip_leftD)
  hence "b_arr ! vcount = replicate (Suc vcount) (0::'n) ! vcount"
    unfolding b_arr_def by (rule foldl_scatter_miss)
  moreover have "replicate (Suc vcount) (0::'n) ! vcount = 0" by (rule nth_replicate) simp
  ultimately show ?thesis by (simp add: b_lookup_def)
qed

lemma fst_list_nth_vertex: "e < m \<Longrightarrow> fst_list ! e \<in> set vs_list"
  using fst_snd_vs length_fst length_edges by (metis UnI1 nth_mem subsetD)

lemma snd_list_nth_vertex: "e < m \<Longrightarrow> snd_list ! e \<in> set vs_list"
  using fst_snd_vs length_snd length_edges by (metis UnI2 nth_mem subsetD)

lemma V_lt_vcount:
  assumes "v \<in> original_network.\<V>"
  shows "v < vcount"
proof (rule vs_less_vcount)
  from assms obtain a b where ab: "(a, b) \<in> original_network.make_pair ` {0..<m}" "v \<in> {a, b}"
    by (auto simp: dVs_def)
  from ab(1) obtain e where e: "e < m" and me: "original_network.make_pair e = (a, b)" by auto
  have "a = fst_list ! e" and "b = snd_list ! e"
    using e me by (auto simp: original_network.make_pair_def)
  thus "v \<in> set vs_list"
    using ab(2) fst_list_nth_vertex[OF e] snd_list_nth_vertex[OF e] by auto
qed

text \<open>An endpoint of some edge really is a vertex of the network.  Under the dense model this is the
      right converse of @{thm V_lt_vcount}: not every name in @{term vs_list} is a vertex any more
      (the edge-less ones are not), only the endpoints are.\<close>

lemma edged_in_V:
  assumes "v \<in> set fst_list \<union> set snd_list"
  shows "v \<in> original_network.\<V>"
proof -
  from assms consider (f) "v \<in> set fst_list" | (s) "v \<in> set snd_list" by blast
  thus ?thesis
  proof cases
    case f
    then obtain e where e0: "e < length fst_list" and ve: "fst_list ! e = v"
      by (auto simp: in_set_conv_nth)
    have e: "e < m" using e0 length_fst length_edges by simp
    have "(v, snd_list ! e) \<in> original_network.make_pair ` {0..<m}"
      using e ve by (force simp: original_network.make_pair_def)
    thus ?thesis by (rule dVsI(1))
  next
    case s
    then obtain e where e0: "e < length snd_list" and ve: "snd_list ! e = v"
      by (auto simp: in_set_conv_nth)
    have e: "e < m" using e0 length_snd length_edges by simp
    have "(fst_list ! e, v) \<in> original_network.make_pair ` {0..<m}"
      using e ve by (force simp: original_network.make_pair_def)
    thus ?thesis by (rule dVsI(2))
  qed
qed

text \<open>The graph vertex set is exactly the set of edge endpoints.\<close>

lemma V_orig_eq: "original_network.\<V> = set fst_list \<union> set snd_list"
proof
  show "original_network.\<V> \<subseteq> set fst_list \<union> set snd_list"
  proof
    fix v assume "v \<in> original_network.\<V>"
    then obtain a b where ab: "(a, b) \<in> original_network.make_pair ` {0..<m}" "v \<in> {a, b}"
      by (auto simp: dVs_def)
    from ab(1) obtain e where e: "e < m" and me: "original_network.make_pair e = (a, b)" by auto
    have "a = fst_list ! e" "b = snd_list ! e" using e me by (auto simp: original_network.make_pair_def)
    thus "v \<in> set fst_list \<union> set snd_list"
      using ab(2) e length_fst length_snd length_edges by (auto simp: in_set_conv_nth)
  qed
next
  show "set fst_list \<union> set snd_list \<subseteq> original_network.\<V>" using edged_in_V by blast
qed

text \<open>The two CSRs of the input edges (@{locale csr_edge_spec}), grouped by tail resp.\ head.
      Every endpoint is a name below @{term vcount}, and the vertex set of the input is the graph
      vertex set.\<close>

sublocale out: csr_edge_spec vcount fst_list snd_list "e_src fst_list"
  by unfold_locales (use fst_snd_vs vs_less_vcount length_fst length_snd in auto)

sublocale inc: csr_edge_spec vcount fst_list snd_list "e_tgt fst_list snd_list"
  by unfold_locales (use fst_snd_vs vs_less_vcount length_fst length_snd in auto)

lemma verts_V: "verts fst_list snd_list = original_network.\<V>"
  by (simp add: out.verts_eq V_orig_eq)

text \<open>The acyclic-flow procedure is now an instance.  The two edge iterators are the CSRs
      @{locale csr_graph} of tails resp.\ heads, with the cursor function as state; the flow and
      vertex-state arrays are plain lists read with @{const nth} and written with
      @{const list_update} (\<open>xs[k := v]\<close>); the vertex iterator is the vertex list with a cursor;
      \<open>fst_exec\<close> / \<open>snd_exec\<close> are the \<open>O(1)\<close> tail / head array reads; and the program capacity
      \<open>cap\<close> decodes the @{term \<open>- 1\<close>} sentinel as an infinite capacity.\<close>

sublocale acyclic_flow_impl
  where fst = "\<lambda> e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
    and snd = "\<lambda> e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
    and \<E> = "{0..<m}"
    and create_edge = "\<lambda> u v. m + prod_encode (u, v)"    and \<u> = "\<lambda> e. if e < m then (if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e))) else \<infinity>"
    and \<c> = "\<lambda> e. h (cost_list ! e)"
    and out_invar = out.graph.csr_invar and out_abstract = out.graph.csr_abstract
    and out_current = out.graph.csr_current and out_has = out.graph.csr_has
    and out_iterated = out.graph.csr_iterated and out_remaining = out.graph.csr_remaining
    and out_move = out.graph.csr_move and out_reset = out.graph.csr_reset
    and in_invar = inc.graph.csr_invar and in_abstract = inc.graph.csr_abstract
    and in_current = inc.graph.csr_current and in_has = inc.graph.csr_has
    and in_iterated = inc.graph.csr_iterated and in_remaining = inc.graph.csr_remaining
    and in_move = inc.graph.csr_move and in_reset = inc.graph.csr_reset
    and flow_invar = "\<lambda>xs. length xs = m" and flow_upd = list_update and flow_lookup = nth
    and st_invar = "\<lambda>xs. \<forall>v\<in>original_network.\<V>. v < length xs" and st_upd = list_update and st_lookup = nth
    and vit_invar = vtx_invar and vit_abstract = vtx_abstract and current_vertex = vtx_current
    and has_vertex = vtx_has and vit_iterated = vtx_iterated and vit_remaining = vtx_remaining
    and move_on_vertex = vtx_move
    and out_arr = "(!) out.inp.B_spec"
    and in_arr = "(!) inc.inp.B_spec"
    and all_vertices = "\<lparr> vi_list = edged_vs_list, vi_pos = 0 \<rparr>"
    and cap = "\<lambda> e.  capacity_list ! e "
    and cost = "\<lambda> e. cost_list ! e"
    and h = "h :: 'n \<Rightarrow> real"
    and state_init = "replicate vcount Unseen"
    and fst_exec = "\<lambda> e. fst_list ! e"
    and snd_exec = "\<lambda> e. snd_list ! e"
  apply (rule acyclic_flow_impl.intro)
  apply (all \<open>(rule list_fixed_univ_map list_fixed_univ_map_len vtx_iterable_set)?\<close>)
  apply (all \<open>(unfold outgoing_edge_iterator_def ingoing_edge_iterator_def)?\<close>)
  apply (all \<open>(subst verts_V[symmetric], rule out.graph.csr.indexed_iterable_set_axioms
                    inc.graph.csr.indexed_iterable_set_axioms)?\<close>)
  apply unfold_locales
  using V_lt_vcount apply auto
  done

lemma length_out_lo: "length out_lo = vcount"
  by (simp add: out_lo_def out.inp.length_B_spec)

lemma length_in_lo: "length in_lo = vcount"
  by (simp add: in_lo_def inc.inp.length_B_spec)

lemma length_out_E: "length out.inp.E_spec = m"
  by (simp add: out.inp.length_E_spec out.inp.es_def edge_seq_def length_fst length_edges)

lemma length_in_E: "length inc.inp.E_spec = m"
  by (simp add: inc.inp.length_E_spec inc.inp.es_def edge_seq_def length_fst length_edges)

lemma out_lo_nth: "v < vcount \<Longrightarrow> out_lo ! v = out.inp.B_spec ! v"
  by (simp add: out_lo_def nth_butlast out.inp.length_B_spec)

lemma in_lo_nth: "v < vcount \<Longrightarrow> in_lo ! v = inc.inp.B_spec ! v"
  by (simp add: in_lo_def nth_butlast inc.inp.length_B_spec)

text \<open>The block of a name holds exactly the edges with that tail resp.\ head.\<close>

lemma out_block: "v < vcount \<Longrightarrow> out.graph.csr_abstract c v = {e. e < m \<and> fst_list ! e = v}"
  using out.block_key[of v] by (auto simp: out.graph.csr_abstract_eq length_fst length_edges)

lemma in_block: "v < vcount \<Longrightarrow> inc.graph.csr_abstract c v = {e. e < m \<and> snd_list ! e = v}"
  using inc.block_key[of v] by (auto simp: inc.graph.csr_abstract_eq length_fst length_edges)


subsection \<open>The CSR arrays are a faithful multigraph\<close>

text \<open>The two CSRs really do represent the outgoing / ingoing incidences: their abstraction at a
      vertex is exactly @{const original_network.delta_plus} / @{const original_network.delta_minus}.
      This discharges the standing @{term \<open>multigraph_inv out_arr in_arr\<close>} hypothesis of the
      acyclifier's correctness theorems.\<close>

lemma out_graph_inv_csr: "out_graph_inv ((!) out.inp.B_spec)"
  unfolding out_graph_inv_def
proof (intro conjI ballI)
  show "out.graph.csr_invar ((!) out.inp.B_spec)"
    by (rule out.graph.csr_init_invar)
next
  fix v assume v: "v \<in> original_network.\<V>"
  show "out.graph.csr_abstract ((!) out.inp.B_spec) v = original_network.delta_plus v"
    using out.csr_abstract_key[of v] v
    by (auto simp: verts_V original_network.delta_plus_def length_fst length_edges)
qed

lemma in_graph_inv_csr: "in_graph_inv ((!) inc.inp.B_spec)"
  unfolding in_graph_inv_def
proof (intro conjI ballI)
  show "inc.graph.csr_invar ((!) inc.inp.B_spec)"
    by (rule inc.graph.csr_init_invar)
next
  fix v assume v: "v \<in> original_network.\<V>"
  show "inc.graph.csr_abstract ((!) inc.inp.B_spec) v = original_network.delta_minus v"
    using inc.csr_abstract_key[of v] v
    by (auto simp: verts_V original_network.delta_minus_def length_fst length_edges)
qed

lemma multigraph_inv_csr: "multigraph_inv ((!) out.inp.B_spec) ((!) inc.inp.B_spec)"
  by (simp add: multigraph_inv_def out_graph_inv_csr in_graph_inv_csr)

text \<open>A name is @{const is_lonely} iff it carries no edge: its two CSR blocks are empty exactly when
      no edge has it as tail or head.  This is what makes the lonely guard skip precisely the
      edge-less names.\<close>

lemma is_lonely_blocks:
  assumes "v < vcount"
  shows "is_lonely v \<longleftrightarrow>
           {e. e < m \<and> fst_list ! e = v} = {} \<and> {e. e < m \<and> snd_list ! e = v} = {}"
  using assms
  by (simp add: is_lonely_def out.graph.csr_empty_iff[where c = id] inc.graph.csr_empty_iff[where c = id]
                out_block in_block)

lemma edged_not_lonely:
  assumes v: "v \<in> set fst_list \<union> set snd_list"
  shows "\<not> is_lonely v"
proof -
  have vlt: "v < vcount" using v fst_snd_vs vs_less_vcount by blast
  have "\<exists>e < m. fst_list ! e = v \<or> snd_list ! e = v"
    using v by (auto simp: in_set_conv_nth length_fst length_snd length_edges)
  thus ?thesis using is_lonely_blocks[OF vlt] by blast
qed

lemma not_lonely_edged:
  assumes vlt: "v < vcount" and nl: "\<not> is_lonely v"
  shows "v \<in> set fst_list \<union> set snd_list"
proof -
  obtain e where "e < m" "fst_list ! e = v \<or> snd_list ! e = v"
    using nl is_lonely_blocks[OF vlt] by blast
  thus ?thesis by (auto simp: in_set_conv_nth length_fst length_snd length_edges)
qed

lemma is_lonely_iff:
  assumes v: "v \<in> set vs_list"
  shows "is_lonely v \<longleftrightarrow> v \<notin> set fst_list \<union> set snd_list"
  using edged_not_lonely not_lonely_edged[OF vs_less_vcount[OF v]] by blast

text \<open>The graph vertex set is exactly the set of edge endpoints, and --- since every endpoint lies in
      the dense range and is non-lonely --- exactly @{term \<open>set edged_vs_list\<close>}, the list fed to the
      acyclifier.  This is what keeps the acyclifier's @{term \<open>vit_abstract all_vertices = \<V>\<close>}
      hypothesis intact under the dense model.\<close>

lemma set_edged_vs_list: "set edged_vs_list = set fst_list \<union> set snd_list"
proof
  show "set edged_vs_list \<subseteq> set fst_list \<union> set snd_list"
    using not_lonely_edged vs_less_vcount by (auto simp: edged_vs_list_def)
next
  show "set fst_list \<union> set snd_list \<subseteq> set edged_vs_list"
    using edged_not_lonely fst_snd_vs by (auto simp: edged_vs_list_def)
qed

lemma V_orig_eq_edged: "original_network.\<V> = set edged_vs_list"
  by (simp add: V_orig_eq set_edged_vs_list)

text \<open>The provable replacement for the (now false) \<open>v \<in> set vs_list \<Longrightarrow> v \<in> \<V>\<close>: every graph vertex is
      a name in the dense range, i.e. the inclusion holds one way only.\<close>

lemma V_sub_vs_list: "original_network.\<V> \<subseteq> set vs_list"
  using V_orig_eq fst_snd_vs by simp
text \<open>All arrays keep their sizes through the fold.\<close>

definition sized ::
  "edge_tag list \<times> 'n list \<times> (nat list \<times> nat list) \<times> (nat list \<times> nat list) \<Rightarrow> bool" where
  "sized s \<longleftrightarrow> (case s of (est, exc, fo, fi) \<Rightarrow>
     length est = m \<and> length exc = Suc vcount \<and> length (fst fo) = vcount \<and> length (snd fo) = m
     \<and> length (fst fi) = vcount \<and> length (snd fi) = m)"

lemma passA_step_sized: "sized s \<Longrightarrow> sized (passA_step fl e s)"
  by (cases s) (simp add: sized_def passA_step_def Let_def split: if_split)

lemma sized_passA: "sized (passA fl)"
  unfolding passA_def
  apply (rule fold_invariant[where Q = "\<lambda>_. True" and P = sized])
    apply simp
   apply (simp add: sized_def length_out_lo length_in_lo length_out_E length_in_E)
  apply (erule passA_step_sized)
  done

lemma length_excess[simp]: "length excess = Suc vcount"
  using sized_passA[of flow_list]
  by (auto simp: sized_def excess_def split: prod.splits)

lemma length_edge_state[simp]: "length (edge_state fl) = m"
  and length_free_out[simp]: "length (fst (free_out fl)) = vcount" "length (snd (free_out fl)) = m"
  and length_free_in[simp]: "length (fst (free_in fl)) = vcount" "length (snd (free_in fl)) = m"
  using sized_passA[of fl]
  by (auto simp: sized_def edge_state_def free_out_def free_in_def split: prod.splits)


definition is_free :: "'n list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_free fl e \<longleftrightarrow> edge_state fl ! e = InTree"
 
lemma length_fold_add_body:
  "length (fold (\<lambda>v arr. arr[v := arr ! v + b_lookup v]) xs init) = length init"
  by (induct xs arbitrary: init) simp_all

lemma length_imbalance[simp]: "length imbalance = Suc vcount"
  by (simp add: imbalance_def length_fold_add_body)

subsection \<open>Big-M, artificial-edge orientation and the augmented endpoints\<close>

text \<open>A single large cost @{term bigM} makes the tagged-pair potential representation faithful
      (\<open>bigM > 6 * sum of the absolute edge costs\<close>) and is the artificial-edge cost ({\isasymsection}2).\<close>

definition bigM :: real where
  "bigM = 6 * h (sum_list (map abs cost_list)) + 1"

lemma bigM_gt: "bigM > 6 * h (sum_list (map abs cost_list))"
  by (simp add: bigM_def)

text \<open>The potential/reduced-cost descriptor abstraction.  It sends the code-level tagged pair
      @{typ \<open>mtag \<times> 'n\<close>} to a real value: the tagged M-coefficient scaled by the (proof-time)
      constant @{term bigM}, plus the homomorphic image of the ordinary part.  This is the \<^emph>\<open>only\<close>
      place the homomorphism @{term h} enters the potential abstraction; keeping it here (rather than
      in the executable code locale) is what makes the whole executable pipeline compute over @{typ 'n}.\<close>

definition pval_abstract :: "real \<Rightarrow> mtag \<times> 'n \<Rightarrow> real" where
  "pval_abstract M p = real_of_int (of_mtag (fst p)) * M + h (snd p)"

text \<open>Every vertex-indexed array keeps length @{term \<open>Suc vcount\<close>} across the non-recursive state
      transformers (the recursive @{const build_dfs} is handled with its induction rule in the
      correctness development).\<close>

definition dfs_sized :: "'n dfs_state \<Rightarrow> bool" where
  "dfs_sized s \<longleftrightarrow> length (ds_seen s) = Suc vcount \<and> length (ds_prnt s) = Suc vcount \<and>
     length (ds_par s) = Suc vcount \<and> length (ds_dir s) = Suc vcount \<and>
     length (ds_pot s) = Suc vcount \<and> length (ds_thrd s) = Suc vcount \<and>
     length (ds_rvth s) = Suc vcount \<and> length (ds_lsuc s) = Suc vcount \<and>
     length (ds_snum s) = Suc vcount"

lemma dfs_init_sized: "dfs_sized dfs_init"
  by (simp add: dfs_sized_def dfs_init_def del: replicate_Suc)

lemma dfs_discover_sized: "dfs_sized s \<Longrightarrow> dfs_sized (dfs_discover s v w e)"
  by (simp add: dfs_sized_def dfs_discover_def dfs_push_def Let_def)

lemma dfs_finish_sized: "dfs_sized s \<Longrightarrow> dfs_sized (dfs_finish s v rest)"
  by (simp add: dfs_sized_def dfs_finish_def Let_def)

lemma emit_U_edge_sized: "dfs_sized s \<Longrightarrow> dfs_sized (emit_U_edge s v)"
  by (simp add: dfs_sized_def emit_U_edge_def Let_def)

end

end
