theory Network_Simplex_Preservation
  imports Network_Simplex
begin

text \<open>\<^bold>\<open>Unique-path characterisation of an arborescence.\<close>
      @{thm unique_walks_arborescence} states that a finite graph in
      which every vertex is joined to the designated root @{term r} by \<^emph>\<open>exactly one\<close>
      simple (vertex-disjoint) path --- more precisely, any two vertices are joined by a unique distinct
      walk --- is a rooted spanning arborescence. This is the bridge from the
      \<open>arborescense_adt\<close> axioms (which supply exactly the unique-distinct-walk property,
      \<open>general(3)\<close>) to the graph-library predicate \<open>graph_abs.arborescence\<close>
      used by \<open>spanning_tree_partition\<close>. Connectivity of the root component follows from
      existence of the walks; acyclicity follows from uniqueness, via
      \<open>graph_abs.decycle_edge_path\<close>: a cycle through an edge \<open>{a,b}\<close> yields a
      second distinct \<open>b\<close>--\<open>a\<close> walk avoiding that edge, contradicting the
      unique walk given by the edge.\<close>

section \<open>Preservation of the loop invariants and the termination measure\<close>

text \<open>For each of the two \<^emph>\<open>recursive\<close> branches of @{const
      network_simplex_spec.ns_loop} --- the degenerate flip @{const network_simplex_spec.ns_flip} (@{term
      \<open>leaving = None\<close>}, KV's @{term \<open>e = e0\<close>}) and the full pivot @{const
      network_simplex_spec.ns_pivot} --- we prove that the loop invariant @{const
      network_simplex.ns_invar} is preserved and that a lexicographic termination measure strictly
      decreases. The two terminal branches (@{const network_simplex_spec.ns_optimal}, @{const
      network_simplex_spec.ns_unbounded_upd}) only set the return flag, so they preserve every invariant
      trivially and never recurse.

      The two recursive-case proofs are \<^emph>\<open>conditional\<close> on a family of auxiliary facts
      about the helper functions. Following the design notes, each auxiliary function has a
      \<^emph>\<open>single\<close> bundled lemma stating all the properties its callers consume under
      one shared set of hypotheses, so the recursive-case proofs can reuse the whole lemma context in one
      step. The informal arguments these lemmas discharge are \S{}0--\S{}4 of
      \<open>Network_Simplex_Design_Notes.md\<close>; the lexicographic measure is that file's
      ``Termination'' section.\<close>

named_theorems invar_holds_intros and termination_intros and call_cond_elims

context network_simplex
begin

subsection \<open>Destructor/intro bundle for @{const spanning_tree_partition}\<close>

text \<open>Feeding the eight conjuncts of @{const spanning_tree_partition} inline via @{text "dest:"}
      instead of hand-counted @{text "THEN conjunctN"} chains.\<close>

lemma spanning_tree_partitionD:
  "spanning_tree_partition r T L U \<Longrightarrow> \<E> = T \<union> U \<union> L"
  "spanning_tree_partition r T L U \<Longrightarrow> T \<inter> U = {}"
  "spanning_tree_partition r T L U \<Longrightarrow> T \<inter> L = {}"
  "spanning_tree_partition r T L U \<Longrightarrow> L \<inter> U = {}"
  "spanning_tree_partition r T L U \<Longrightarrow>
     graph_abs.arborescence ((\<lambda>e. {fst e, snd e}) ` T) r ((\<lambda>e. {fst e, snd e}) ` T)"
  "spanning_tree_partition r T L U \<Longrightarrow> graph_abs ((\<lambda>e. {fst e, snd e}) ` T)"
  "spanning_tree_partition r T L U \<Longrightarrow>
     (\<forall>e e'. {e, e'} \<subseteq> T \<and> {fst e, snd e} = {fst e', snd e'} \<longrightarrow> e = e')"
  "spanning_tree_partition r T L U \<Longrightarrow> dVs (make_pair ` T) = \<V>"
  by (simp_all add: spanning_tree_partition_def)

lemma spanning_tree_partitionI:
  "\<lbrakk>\<E> = T \<union> U \<union> L; T \<inter> U = {}; T \<inter> L = {}; L \<inter> U = {};
    graph_abs.arborescence ((\<lambda>e. {fst e, snd e}) ` T) r ((\<lambda>e. {fst e, snd e}) ` T);
    graph_abs ((\<lambda>e. {fst e, snd e}) ` T);
    \<forall>e e'. {e, e'} \<subseteq> T \<and> {fst e, snd e} = {fst e', snd e'} \<longrightarrow> e = e';
    dVs (make_pair ` T) = \<V>\<rbrakk> \<Longrightarrow> spanning_tree_partition r T L U"
  unfolding spanning_tree_partition_def
  by blast

text \<open>Moving a non-tree edge @{term e} between @{term U} and @{term L} keeps the partition.\<close>

lemma spanning_tree_partition_flip:
  assumes "spanning_tree_partition r T (L \<union> SL) (U \<union> SU)" "if fwd then e \<in> U else e \<in> L"
    "e \<notin> SL" "e \<notin> SU"
    "L' = (if fwd then insert e L else L - {e})" "U' = (if fwd then U - {e} else insert e U)"
  shows "spanning_tree_partition r T (L' \<union> SL) (U' \<union> SU)"
proof-
  note P = spanning_tree_partitionD[OF assms(1)]
  show ?thesis
    by (rule spanning_tree_partitionI; (fact P(5-8))?; use P(1-4) assms(2-6) in \<open>cases fwd; auto\<close>)
qed

text \<open>Exchanging a tree edge @{term a} for a non-tree edge @{term e} keeps the partition of the
      edges, once the new tree is known to be a spanning arborescence.\<close>

lemma spanning_tree_partition_exchange:
  assumes "spanning_tree_partition r T (L \<union> SL) (U \<union> SU)" "e \<in> L \<union> U" "e \<notin> SL"
    "e \<notin> SU" "a \<in> T"
    "L' = L - {e} \<union> (if fwd then {} else {a})" "U' = U - {e} \<union> (if fwd then {a} else {})"
    "graph_abs.arborescence ((\<lambda>x. {fst x, snd x}) ` (T - {a} \<union> {e})) r
      ((\<lambda>x. {fst x, snd x}) ` (T - {a} \<union> {e}))"
    "graph_abs ((\<lambda>x. {fst x, snd x}) ` (T - {a} \<union> {e}))"
    "\<forall>x y. {x, y} \<subseteq> T - {a} \<union> {e} \<and> {fst x, snd x} = {fst y, snd y} \<longrightarrow> x
      = y"
    "dVs (make_pair ` (T - {a} \<union> {e})) = \<V>"
  shows "spanning_tree_partition r (T - {a} \<union> {e}) (L' \<union> SL) (U' \<union> SU)"
proof-
  note P = spanning_tree_partitionD(1-4)[OF assms(1)]
  have N: "a \<notin> L \<union> U \<union> SL \<union> SU" "e \<notin> T"
    using P assms(2,5)
    by blast+
  show ?thesis
    by (rule spanning_tree_partitionI; (fact assms(8-11))?; use P N assms(2-7) in \<open>cases fwd; auto\<close>)
qed

subsection \<open>Scan helpers\<close>

text \<open>The vertex returned by a bottleneck scan is always a member of the scanned path. Both scans
      fold an accumulator @{term \<open>(m, best)\<close>} over the path; the second component is only
      ever set to a vertex taken from the list, so on a @{term \<open>Some v\<close>} result @{term v}
      lies on the path. Proved by induction on the path from the right (the accumulator is
      generalised).\<close>

lemma singleton_not_dblton: "dblton_graph G \<Longrightarrow> {x} \<notin> G"
  by (auto simp: dblton_graph_def)

lemma scan_up_snd_mem: "\<lbrakk>scan_up s p = (m, v); m \<noteq> - 1\<rbrakk> \<Longrightarrow> v \<in> set p"
  by (induct p arbitrary: m v rule: rev_induct) (auto simp: scan_up_def Let_def split: if_splits prod.splits)

lemma scan_down_snd_mem: "\<lbrakk>scan_down s p = (m, v); m \<noteq> - 1\<rbrakk> \<Longrightarrow> v \<in> set p"
  by (induct p arbitrary: m v rule: rev_induct) (auto simp: scan_down_def Let_def split: if_splits prod.splits)

text \<open>The value component a scan returns is the residual at the returned vertex whenever a vertex
      was recorded (i.e.\ @{term \<open>m \<noteq> - 1\<close>}).\<close>

lemma scan_up_snoc:
  "scan_up s (p @ [x]) = (case scan_up s p of (m, b) \<Rightarrow>
     if res_up s x = - 1 then (m, b) else if m = - 1 \<or> res_up s x \<le> m then (res_up s x, x) else (m, b))"
  by (simp add: scan_up_def Let_def split: prod.splits)

lemma scan_down_snoc:
  "scan_down s (p @ [x]) = (case scan_down s p of (m, b) \<Rightarrow>
     if res_down s x = - 1 then (m, b) else if m = - 1 \<or> res_down s x < m then (res_down s x, x) else (m, b))"
  by (simp add: scan_down_def Let_def split: prod.splits)

lemma scan_up_val_at: "\<lbrakk>scan_up s p = (m, v0); m \<noteq> - 1\<rbrakk> \<Longrightarrow> res_up s v0 = m"
  by (induct p arbitrary: m v0 rule: rev_induct)
     (simp add: scan_up_def, auto simp only: scan_up_snoc split: prod.splits if_splits)

lemma scan_down_val_at: "\<lbrakk>scan_down s p = (m, v0); m \<noteq> - 1\<rbrakk> \<Longrightarrow> res_down s v0 = m"
  by (induct p arbitrary: m v0 rule: rev_induct)
     (simp add: scan_down_def, auto simp only: scan_down_snoc split: prod.splits if_splits)

lemma mininf_sign: "\<lbrakk>0 \<le> x \<or> x = - 1; 0 \<le> y \<or> y = - 1\<rbrakk> \<Longrightarrow> 0 \<le>
  mininf x y \<or> mininf x y = - 1"
  by (auto simp: mininf_def)

lemma mininf_snd_of_neq_fst: "mininf (x::'n) y \<noteq> x \<Longrightarrow> mininf x y = y"
  by (cases "x = - 1"; cases "y = - 1") (auto simp: mininf_def min_def)

lemma mininf_snd_attains:
  "\<lbrakk>mininf (x::'n) y \<noteq> - 1; \<not> (x \<noteq> - 1 \<and> x = mininf x y)\<rbrakk> \<Longrightarrow> y
    = mininf x y \<and> y \<noteq> - 1"
  by (cases "x = - 1"; cases "y = - 1") (auto simp: mininf_def min_def)

text \<open>Bounds on the scan minimum: the scanned value is the infinity sentinel or is below every
      finite residual on the path.\<close>

lemma scan_up_min:
  "\<lbrakk>scan_up s p = (m, best); w \<in> set p; res_up s w \<noteq> - 1\<rbrakk> \<Longrightarrow> m \<noteq> - 1
    \<and> m \<le> res_up s w"
  by (induct p arbitrary: m best rule: rev_induct)
     (simp add: scan_up_def, auto simp: scan_up_snoc split: prod.splits if_splits)

lemma scan_down_min:
  "\<lbrakk>scan_down s p = (m, best); w \<in> set p; res_down s w \<noteq> - 1\<rbrakk> \<Longrightarrow> m \<noteq>
    - 1 \<and> m \<le> res_down s w"
  by (induct p arbitrary: m best rule: rev_induct)
     (simp add: scan_down_def, auto simp: scan_down_snoc split: prod.splits if_splits)

lemma bottleneck_delta:
  "\<lbrakk>bottleneck s e in_U p1 p2 = (\<delta>, is_flip, v, e0fwd, up_side); \<delta> \<noteq> - 1;
    scan_up s (if in_U then p1 else p2) = (mu, vu); scan_down s (if in_U then p2 else p1) = (md, vd)\<rbrakk>
   \<Longrightarrow> \<delta> = mininf (if in_U then res_bwd s e else res_fwd s e) (mininf mu md)"
  by (auto simp: bottleneck_def Let_def split: if_splits)

subsection \<open>Flow and sum helpers\<close>

text \<open>\<^bold>\<open>\S{}4.2 Conservation (circulation)\<close>. For @{term \<open>\<delta> >
      0\<close>} the flow produced by @{const augment_flow} is a @{term \<delta>}-scaled unit circulation
      around the fundamental circuit: it leaves every vertex balance unchanged, hence stays a @{term
      b}-flow, and every circuit edge is pushed by at most its own residual so the capacity bounds are
      kept. A single flow update shifts the excess of its two endpoints by opposite signed amounts, and
      folding such updates accumulates those shifts additively.\<close>

definition "ns_flow_cost s = (\<C> (ns_flow_of s))"

lemma sum_fun_upd_delta:
  "finite S \<Longrightarrow> sum (g(a := g a + (\<delta>::real))) S = sum g S + (if a \<in> S then \<delta> else 0)"
  by (subst sum.cong[OF refl, of _ _ "\<lambda>x. g x + (if x = a then \<delta> else 0)"]) (auto simp: sum.distrib)

lemma flow_upd_ex:
  assumes "flow_invar f" "a \<in> \<E>"
  shows "ex (h \<circ> flow_lookup (flow_upd f a (flow_lookup f a + c))) v
           = ex (h \<circ> flow_lookup f) v + h c * ((if snd a = v then 1 else 0) - (if fst a = v then 1 else 0))"
proof-
  have fl: "(\<lambda>e. h (flow_lookup (flow_upd f a (flow_lookup f a + c)) e)) =
    (\<lambda>e. h (flow_lookup f e))(a := h (flow_lookup f a) + h c)"
    using assms
    by (simp add: fun_eq_iff flow_arr.fixed_univ_map_upd h_add)
  have "(a \<in> \<delta>\<^sup>- v) = (snd a = v)" "(a \<in> \<delta>\<^sup>+ v) = (fst a = v)"
    using assms(2)
    by (auto simp: delta_minus_def delta_plus_def)
  then show ?thesis
    unfolding ex_def comp_def fl
    by (simp only: sum_fun_upd_delta[of _ "\<lambda>e. h (flow_lookup f e)" a "h c"] delta_minus_finite delta_plus_finite)
      (simp add: algebra_simps)
qed

lemma fold_flow_upd_invar:
  "\<lbrakk>flow_invar f0; \<forall>w\<in>set xs. par_edge s w \<in> \<E>\<rbrakk>
   \<Longrightarrow> flow_invar (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0)"
  by (induction xs arbitrary: f0) (simp_all add: flow_arr.fixed_univ_map_upd_invar)

lemma fold_flow_upd_ex:
  "\<lbrakk>flow_invar f0; \<forall>w\<in>set xs. par_edge s w \<in> \<E>\<rbrakk> \<Longrightarrow>
   ex (h \<circ> flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0)) v
     = ex (h \<circ> flow_lookup f0) v
       + (\<Sum>w\<leftarrow>xs. h (g w) * ((if snd (par_edge s w) = v then 1 else 0) -
         (if fst (par_edge s w) = v then 1 else 0)))"
  by (induction xs arbitrary: f0) (simp_all add: flow_upd_ex flow_arr.fixed_univ_map_upd_invar)

text \<open>Capacity infrastructure: the exact per-edge value after the fold (accumulation form, no
      distinctness).\<close>

lemma fold_flow_upd_lookup:
  "\<lbrakk>flow_invar f0; \<forall>w\<in>set xs. par_edge s w \<in> \<E>\<rbrakk> \<Longrightarrow>
   flow_lookup (fold (\<lambda>v f. flow_upd f (par_edge s v) (flow_lookup f (par_edge s v) + g v)) xs f0) a
     = flow_lookup f0 a + (\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0)"
  by (induction xs arbitrary: f0)
     (auto simp: flow_arr.fixed_univ_map_upd flow_arr.fixed_univ_map_upd_invar algebra_simps)

text \<open>\<^bold>\<open>Shared flow-lookup characterisation.\<close> Both recursive branches augment
      the flow the same way, so the per-arc lookup formula for @{const augment_flow} is factored out
      here.\<close>

lemma augment_flow_lookup_char:
  assumes "flow_invar (current_flow s)" "0 \<le> \<delta>" "e \<in> \<E>"
    "\<forall>w\<in>set (if in_U then p1 else p2). par_edge s w \<in> \<E>"
    "\<forall>w\<in>set (if in_U then p2 else p1). par_edge s w \<in> \<E>"
  shows "flow_lookup (augment_flow s e in_U \<delta> p1 p2) a =
           flow_lookup (current_flow s) a + (if a = e then (if in_U then - \<delta> else \<delta>) else 0)
         + (\<Sum>w\<leftarrow>(if in_U then p1 else p2). if par_edge s w = a then
           (if par_up s w then \<delta> else - \<delta>) else 0)
         + (\<Sum>w\<leftarrow>(if in_U then p2 else p1). if par_edge s w = a then
           (if par_up s w then - \<delta> else \<delta>) else 0)"
proof(cases "\<delta> \<le> 0")
  case True
  then show ?thesis
    using assms(2)
    by (simp add: augment_flow_def cong: if_cong)
next
  case False
  then show ?thesis
    using assms
    by (simp add: augment_flow_def Let_def fold_flow_upd_lookup fold_flow_upd_invar
      flow_arr.fixed_univ_map_upd_invar flow_arr.fixed_univ_map_upd)
qed

lemma telescope_succ_gen:
  assumes "\<And>i. Suc i < length ys \<Longrightarrow> f (ys ! i) = ys ! Suc i" "ys \<noteq> []"
  shows "(\<Sum>w\<leftarrow>butlast ys. \<phi> (f w) - \<phi> w) = \<phi> (last ys) - (\<phi> (hd ys) :: real)"
proof-
  have "(\<Sum>w\<leftarrow>butlast ys. \<phi> (f w) - \<phi> w) = (\<Sum>i<length ys - 1. \<phi> (ys ! Suc i) - \<phi> (ys ! i))"
    using assms(1)
    by (auto simp: sum_list_sum_nth atLeast0LessThan nth_butlast intro!: sum.cong)
  also have "\<dots> = \<phi> (ys ! (length ys - 1)) - \<phi> (ys ! 0)"
    by (rule sum_lessThan_telescope)
  finally show ?thesis
    using assms(2)
    by (simp add: last_conv_nth hd_conv_nth)
qed

lemma sum_list_scale: "(\<Sum>x\<leftarrow>xs. (c::real) * f x) = c * (\<Sum>x\<leftarrow>xs. f x)"
  by (induct xs) (auto simp: algebra_simps)

lemma sum_list_mult_right: "(\<Sum>x\<leftarrow>xs. f x) * (c::real) = (\<Sum>x\<leftarrow>xs. f x * c)"
  by (induct xs) (auto simp: algebra_simps)

lemma sum_sum_list_swap: "finite A \<Longrightarrow> (\<Sum>a\<in>A. (\<Sum>w\<leftarrow>xs. hf a w)) = (\<Sum>w\<leftarrow>xs. (\<Sum>a\<in>A. hf a w))"
  by (induct xs) (simp_all add: sum.distrib)

lemma sum_list_if_eq_notin: "w0 \<notin> set xs \<Longrightarrow> (\<Sum>w\<leftarrow>xs. if w = w0 then g w else 0) = 0"
  by (induct xs) auto

lemma sum_list_if_eq_distinct:
  "\<lbrakk>distinct xs; w0 \<in> set xs\<rbrakk> \<Longrightarrow> (\<Sum>w\<leftarrow>xs. if w = w0 then g w else 0) = g w0"
  by (induct xs) (auto simp: sum_list_if_eq_notin)

lemma h_sum_list: "h (\<Sum>w\<leftarrow>xs. g w) = (\<Sum>w\<leftarrow>xs. h (g w))"
  by (induct xs) (auto simp: h_add)

lemma h_if0: "h (if c then (x::'n) else 0) = (if c then h x else 0)"
  by (simp add: if_distrib[where f=h])

text \<open>Weighting a per-arc contribution concentrated on parent edges by the arc costs.\<close>

lemma sum_E_par_edge:
  assumes "\<forall>w\<in>set xs. par_edge s w \<in> \<E>"
  shows "(\<Sum>a\<in>\<E>. (\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0) * \<c> a) =
    (\<Sum>w\<leftarrow>xs. \<c> (par_edge s w) * (g w :: real))"
proof-
  have "(\<Sum>a\<in>\<E>. (if par_edge s w = a then g w else 0) * \<c> a) = \<c> (par_edge s w) * g w" if
    "w \<in> set xs" for w
    using assms that finite_E
    by (simp add: if_distrib[of "\<lambda>x. x * _"] cong: if_cong)
  then show ?thesis
    by (simp add: sum_list_mult_right sum_sum_list_swap finite_E cong: map_cong)
qed

subsection \<open>Potential shifts and re-parenting\<close>

definition "ns_pot_sum s = (\<Sum> v \<in> \<V>. ns_pot_of s v)"

abbreviation (input) "tree_subtree s v \<equiv>
  {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r \<and> distinct p \<and> v \<in> set p}"

lemma foldr_pot_upd_invar:
  "\<lbrakk>\<forall>x\<in>set xs. x \<in> \<V>; pot_invar acc\<rbrakk> \<Longrightarrow> pot_invar (foldr (\<lambda>x a. pot_upd a x (val a x)) xs acc)"
  by (induct xs) (simp_all add: pot_arr.fixed_univ_map_upd_invar)

lemma foldr_pot_upd_lookup:
  "\<lbrakk>distinct xs; \<forall>x\<in>set xs. x \<in> \<V>; pot_invar acc\<rbrakk> \<Longrightarrow>
   pot_lookup (foldr (\<lambda>x a. pot_upd a x (hop (pot_lookup a x))) xs acc)
     = (\<lambda>u. if u \<in> set xs then hop (pot_lookup acc u) else pot_lookup acc u)"
  by (induct xs) (auto simp: pot_arr.fixed_univ_map_upd foldr_pot_upd_invar fun_eq_iff)

text \<open>The conditional descriptor axioms, with the guard stated as @{const good_pot_val}.\<close>

lemmas pot_plus_good = pot_value_plus_spec[folded good_pot_val_def]
  and pot_minus_good = pot_value_minus_spec[folded good_pot_val_def]

text \<open>\<^bold>\<open>\S{}4.5 Re-parenting.\<close> Re-parenting reverses the spine \<open>hd P \<dots> v\<close>: off-spine
      vertices keep their parent data, the spine head gets the entering edge, and each later spine
      vertex inherits its predecessor's old edge with flipped orientation.\<close>

lemma reparent_walk_invar:
  "\<lbrakk>set ws \<subseteq> \<V> - {r}; case pd of (p0, d0) \<Rightarrow> parent_invar p0 \<and> dir_invar d0\<rbrakk>
   \<Longrightarrow> (case reparent_walk s e v first pe pup ws pd of (p, d) \<Rightarrow> parent_invar p \<and> dir_invar d)"
proof(induction ws arbitrary: first pe pup pd)
  case (Cons w ws)
  then show ?case
    by (cases pd) (auto simp: Let_def parent_arr.fixed_univ_map_upd_invar dir_arr.fixed_univ_map_upd_invar)
qed simp

lemma reparent_walk_full:
  "\<lbrakk>distinct ws; v \<in> set ws; parent_invar pp0; dir_invar dd0; set ws \<subseteq> \<V> - {r}\<rbrakk> \<Longrightarrow>
   (case reparent_walk s e v first pe pup ws (pp0, dd0) of (pr, dr) \<Rightarrow>
      (\<forall>x. x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws)) \<longrightarrow>
           parent_lookup pr x = parent_lookup pp0 x \<and> dir_lookup dr x = dir_lookup dd0 x)
    \<and> parent_lookup pr (hd ws) = (if first then e else pe)
    \<and> dir_lookup dr (hd ws) = (if first then (hd ws = fst_exec e) else (\<not> pup))
    \<and> (\<forall>i. Suc i < length ws \<longrightarrow> ws ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) ws) \<longrightarrow>
         parent_lookup pr (ws ! Suc i) = par_edge s (ws ! i) \<and> dir_lookup dr (ws ! Suc i) = (\<not> par_up s (ws ! i))))"
proof(induction ws arbitrary: first pe pup pp0 dd0)
  case (Cons w ws')
  define vw where "vw = (if first then e else pe)"
  define dvw where "dvw = (if first then (w = fst_exec e) else (\<not> pup))"
  have w: "w \<in> \<V> - {r}" "w \<notin> set ws'"
    using Cons.prems(1,5)
    by auto
  note lu = parent_arr.fixed_univ_map_upd dir_arr.fixed_univ_map_upd Cons.prems(3,4) w(1)[simplified]
  have step: "reparent_walk s e v first pe pup (w # ws') (pp0, dd0) = (if w = v
      then (parent_upd pp0 w vw, dir_upd dd0 w dvw)
      else reparent_walk s e v False (par_edge s w) (par_up s w) ws' (parent_upd pp0 w vw, dir_upd dd0 w dvw))"
    by (cases first) (simp_all add: vw_def dvw_def)
  show ?case
  proof(cases "w = v")
    case False
    obtain pr dr where res: "reparent_walk s e v False (par_edge s w) (par_up s w) ws'
      (parent_upd pp0 w vw, dir_upd dd0 w dvw) = (pr, dr)"
      by fastforce
    have pre: "ws' \<noteq> []" "v \<in> set ws'" "w \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) ws'))"
      "distinct ws'" "set ws' \<subseteq> \<V> - {r}"
      "parent_invar (parent_upd pp0 w vw)" "dir_invar (dir_upd dd0 w dvw)"
      using Cons.prems False w
      by (auto dest: set_takeWhileD simp: parent_arr.fixed_univ_map_upd_invar dir_arr.fixed_univ_map_upd_invar)
    note IH = Cons.IH[OF pre(4,2,6,7,5), of False "par_edge s w" "par_up s w", unfolded res prod.case]
    have "parent_lookup pr ((w # ws') ! Suc i) = par_edge s ((w # ws') ! i)
        \<and> dir_lookup dr ((w # ws') ! Suc i) = (\<not> par_up s ((w # ws') ! i))"
      if "Suc i < length (w # ws')" "(w # ws') ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) (w # ws'))" for i
    proof(cases i)
      case (Suc j)
      then have "ws' ! j \<in> set (takeWhile (\<lambda>y. y \<noteq> v) ws')"
        using that w(2) False nth_mem[of j ws']
        by auto
      with IH that(1) Suc show ?thesis
        by simp
    qed (use IH pre(1) in \<open>simp add: hd_conv_nth\<close>)
    with IH pre(3) False show ?thesis
      unfolding step res prod.case
      by (auto simp: lu vw_def dvw_def) 
  qed (use lu in \<open>simp add: step vw_def dvw_def\<close>)
qed simp

text \<open>\<^bold>\<open>Abstract admissibility (\S{}4.4b).\<close> The reusable core, purely on the
      abstract layer (edge set \<open>T\<close>, real potential \<open>\<pi>\<close>): for
      \<^emph>\<open>any\<close> spanning-tree partition and any potential fitting it, every vertex
      potential \<open>\<pi> v\<close> is the signed cost-sum along \<open>v\<close>'s (distinct) tree
      path to \<open>r\<close> --- telescoped via \<open>zt\<close> over the walk's consecutive pairs,
      each mapped to its unique directed tree edge (\<open>de\<close>) --- and the only path edge
      touching \<open>r\<close> is the first, so \<open>\<pi> v\<close> is @{const good_pot_val}.\<close>

lemma potential_fits_imp_good:
  assumes "T \<subseteq> \<E>" "graph_abs ((\<lambda>e. {fst e, snd e}) ` T)"
    "graph_abs.arborescence ((\<lambda>e. {fst e, snd e}) ` T) r ((\<lambda>e. {fst e, snd e}) ` T)"
    "dVs (make_pair ` T) = \<V>" "potential_fits_spanning_tree_partition r T \<pi>" "v \<in> \<V>"
  shows "good_pot_val (\<pi> v)"
proof-
  define GT where "GT = (\<lambda>e. {fst e, snd e}) ` T"
  define Q where "Q u p w A D \<longleftrightarrow> A \<union> D \<subseteq> T \<and> finite (A \<union> D) \<and> A \<inter> D = {}
    \<and> (\<forall>e\<in>A \<union> D. {fst e, snd e} \<subseteq> set p) \<and> (u = w \<longrightarrow> A \<union> D = {})
    \<and> (\<forall>e\<in>A \<union> D. \<forall>e'\<in>A \<union> D. w \<in> {fst e, snd e} \<longrightarrow> w \<in> {fst e', snd e'} \<longrightarrow> e = e')
    \<and> \<pi> u = \<pi> w + sum \<c> A - sum \<c> D"
    for u p w A D
  have Q: "distinct p \<longrightarrow> (\<exists>A D. Q u p w A D)" if "walk_betw GT u p w" for u p w
    using that
  proof(induction rule: induct_walk_betw)
    case (path1 x)
    show ?case
      by (intro impI exI[of _ "{}"]) (simp add: Q_def)
  next
    case (path2 x y vs w)
    show ?case
    proof
      assume "distinct (x # y # vs)"
      moreover have "w \<in> set (y # vs)"
        using walk_between_nonempty_pathD(4)[OF path2.hyps(2)] last_in_set[of "y # vs"]
        by simp
      ultimately obtain A D where AD: "Q y (y # vs) w A D" "x \<notin> set (y # vs)" "x \<noteq> w"
        using path2.IH
        by auto
      obtain e where e: "e \<in> T" "{fst e, snd e} = {x, y}"
        using path2.hyps(1)
        by (auto simp: GT_def)
      have o: "fst e = x \<and> snd e = y \<or> fst e = y \<and> snd e = x"
        using e(2)
        by (auto simp: doubleton_eq_iff)
      have AD': "e \<notin> A" "e \<notin> D" "finite A" "finite D" "\<pi> y = \<pi> w + sum \<c> A - sum \<c> D" "A \<inter> D = {}"
        using AD o
        by (auto simp: Q_def)
      have ce: "\<c> e + \<pi> (fst e) - \<pi> (snd e) = 0"
        using assms(5) e(1)
        by (simp add: potential_fits_spanning_tree_partition_def)
      have touch: "w \<in> {fst e, snd e} \<Longrightarrow> A \<union> D = {}"
        using AD o
        by (auto simp: Q_def)
      have Qx: "Q x (x # y # vs) w A' D'"
        if "A' \<union> D' = insert e (A \<union> D)" "A' \<inter> D' = {}" "\<pi> x = \<pi> w + sum \<c> A' - sum \<c> D'" for A' D'
        unfolding Q_def that(1)
      proof(intro conjI)
        show "\<forall>a\<in>insert e (A \<union> D). \<forall>b\<in>insert e (A \<union> D). w \<in> {fst a, snd a} \<longrightarrow> w \<in> {fst b, snd b}
          \<longrightarrow> a = b"
          using AD(1) touch
          unfolding Q_def
          by blast
        show "\<forall>a\<in>insert e (A \<union> D). {fst a, snd a} \<subseteq> set (x # y # vs)"
          using AD(1) o
          unfolding Q_def
          by auto
      qed (use AD(1,3) e(1) that(2,3) in \<open>auto simp: Q_def\<close>)
      consider "fst e = x" "snd e = y" | "fst e = y" "snd e = x"
        using o
        by blast
      then show "\<exists>A D. Q x (x # y # vs) w A D"
      proof cases
        case 1
        have "\<pi> x = \<pi> w + sum \<c> A - sum \<c> (insert e D)"
          using AD'(5) ce[unfolded 1] sum.insert[OF AD'(4,2), of \<c>]
          by linarith
        then have "Q x (x # y # vs) w A (insert e D)"
          using AD'(1,6)
          by (auto intro!: Qx)
        then show ?thesis
          by blast
      next
        case 2
        have "\<pi> x = \<pi> w + sum \<c> (insert e A) - sum \<c> D"
          using AD'(5) ce[unfolded 2] sum.insert[OF AD'(3,1), of \<c>]
          by linarith
        then have "Q x (x # y # vs) w (insert e A) D"
          using AD'(2,6)
          by (auto intro!: Qx)
        then show ?thesis
          by blast
      qed
    qed
  qed
  have "Vs GT = dVs (make_pair ` T)"
    by (auto simp: GT_def Vs_def dVs_def make_pair_def)
  then have "graph_abs GT" "graph_abs.arborescence GT r GT" "Vs GT = \<V>"
    using assms(2-4)
    by (simp_all add: GT_def)
  moreover from this(3) have "GT \<noteq> {}"
    using assms(6)
    by (auto simp: Vs_def)
  ultimately have vr: "v \<in> connected_component GT r" "r \<in> Vs GT"
    using assms(6) graph_abs.arborescenceD(2)[of GT r GT] in_own_connected_component[of r GT]
    by auto
  obtain p where "walk_betw GT v p r" "distinct p"
  proof(cases "v = r")
    case False
    obtain q where "walk_betw GT r q v"
      using in_connected_component_has_walk[OF vr]
      by blast
    then show ?thesis
      using that walk_betw_different_verts_to_ditinct[OF walk_symmetric False]
      by blast
  qed (use that[of "[r]"] vr in \<open>simp add: walk_betw_def\<close>)
  then obtain A D where "Q v p r A D"
    using Q
    by blast
  then show ?thesis
    using assms(1,5)
    unfolding good_pot_val_def
    by (intro exI[of _ A] exI[of _ D])
       (auto simp: Q_def potential_fits_spanning_tree_partition_def card_le_Suc0_iff_eq)
qed

subsection \<open>Termination measure (lexicographic)\<close>

text \<open>The measure follows the notes' two-level construction. The \<^emph>\<open>outer\<close> level
      is the pair (flow cost, @{term \<open>- \<Sum>\<pi>\<close>}): a genuine augment (@{term
      \<open>\<delta> > 0\<close>}) strictly decreases the flow cost; a degenerate non-flip pivot (@{term
      \<open>\<delta> = 0\<close>}, @{term \<open>e \<noteq> e0\<close>}) keeps the cost but strictly
      increases @{term \<open>\<Sum>\<pi>\<close>}. The \<^emph>\<open>inner\<close> level, reached only
      when both are flat (a degenerate flip with @{term \<open>u e = 0\<close>}), is the number of edges
      violating the optimality certificate, which strictly decreases. Well-foundedness of the outer level
      rests on the finiteness of spanning-tree structures (KV Prop 9.25) and is deferred; here we
      establish the per-step \<^emph>\<open>strict decrease\<close> relation defined below, which is what
      the two recursive cases must show.\<close>

definition "possible_trees s =
  {(T, L, U) | T L U f' \<pi>'.
       spanning_tree_partition r T L U \<and>
       flow_fits_spanning_tree_partition T L U f' \<and>
       potential_fits_spanning_tree_partition r T \<pi>' \<and>
       (f' is b flow) \<and>
       (\<C> f' < ns_flow_cost s
        \<or> (\<C> f' = ns_flow_cost s \<and> (\<Sum> v \<in> \<V>. \<pi>' v) \<ge> ns_pot_sum s))}"

definition "ns_violation s =
  card {e \<in> ns_L_of s. reduced_cost (potentials s) e < 0}
  + card {e \<in> ns_U_of s. reduced_cost (potentials s) e > 0}"

definition "ns_less s' s \<longleftrightarrow>
    (card (possible_trees s') < card (possible_trees s))
  \<or> (card (possible_trees s') = card (possible_trees s)
      \<and> ns_violation s' < ns_violation s)"

text \<open>\<^bold>\<open>Vanishing of a parent-indexed sum.\<close> If @{term a} is not a tree edge, no
      vertex on a non-root list carries it as parent, so the signed contribution telescopes to
      zero.\<close>

lemma sum_par_vanish:
  "\<lbrakk>set xs \<subseteq> \<V> - {r}; a \<notin> ns_tree_edges s\<rbrakk> \<Longrightarrow> (\<Sum>w\<leftarrow>xs. if par_edge s w = a then g w else 0) = 0"
  by (induction xs) (auto simp: par_edge_def)

text \<open>\<^bold>\<open>Finiteness of the tree-structure search space.\<close> Every member of @{const
      possible_trees} partitions @{term \<E>}, so the set injects into @{term "Pow \<E> \<times> Pow \<E>
      \<times> Pow \<E>"}.\<close>

lemma finite_possible_trees: "finite (possible_trees x)"
  by (rule finite_subset[where B = "Pow \<E> \<times> Pow \<E> \<times> Pow \<E>"])
    (auto simp: possible_trees_def finite_E dest!: spanning_tree_partitionD(1))

lemma card_filter_remove_less: "\<lbrakk>finite A; x \<in> A; P x\<rbrakk> \<Longrightarrow> card {y \<in> A - {x}. P y} < card {y \<in> A. P y}"
  by (rule psubset_card_mono) auto

text \<open>The two pivot arms of @{const bottleneck}: the leaving vertex is the result of the scan on
      its side, and on the down side the up-scan and the entering edge lie strictly above @{term
      \<delta>}.\<close>

lemma bottleneck_pivot_up:
  "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, True)
   \<Longrightarrow> scan_up s (if in_U then p1 else p2) = (\<delta>, v) \<and> e0fwd = par_up s v"
  by (auto simp: bottleneck_def Let_def split: prod.splits if_splits)

lemma bottleneck_pivot_down:
  "\<lbrakk>bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, False); scan_up s (if in_U then p1 else p2) = (mu, vu)\<rbrakk>
   \<Longrightarrow> scan_down s (if in_U then p2 else p1) = (\<delta>, v) \<and> e0fwd = (\<not> par_up s v) \<and> (mu = - 1 \<or> \<delta> < mu)
     \<and> ((if in_U then res_bwd s e else res_fwd s e) = - 1 \<or> \<delta> < (if in_U then res_bwd s e else res_fwd s e))"
  by (auto simp: bottleneck_def Let_def mininf_def min_def split: prod.splits if_splits)

text \<open>Every re-parented spine vertex but the first has its spine predecessor in the re-parented
      part.\<close>

lemma takeWhile_spine_pred:
  "\<lbrakk>v \<in> set P; x \<in> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) P)); x \<noteq> hd P\<rbrakk>
   \<Longrightarrow> \<exists>i. Suc i < length P \<and> P ! Suc i = x \<and> P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
proof(induction P)
  case (Cons a P)
  then have "a \<noteq> v" "P \<noteq> []"
    by auto
  show ?case
  proof(cases "x = hd P")
    case False
    then obtain i where "Suc i < length P" "P ! Suc i = x" "P ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)"
      using Cons \<open>a \<noteq> v\<close>
      by auto
    then show ?thesis
      using \<open>a \<noteq> v\<close>
      by (intro exI[of _ "Suc i"]) simp
  qed (use \<open>a \<noteq> v\<close> \<open>P \<noteq> []\<close> in \<open>auto simp: hd_conv_nth intro!: exI[of _ 0]\<close>)
qed simp

text \<open>An arborescence whose edges are the parent links @{term \<open>{x, g x}\<close>} has @{term
      \<open>g w\<close>} as the successor of @{term w} on its simple walk to the root.\<close>

lemma arborescense_parent_walk:
  assumes "arborescense_invar T" "abstract_arborescense T = (\<lambda>x. {x, g x}) ` (\<V> - {r})" "w \<in> \<V> - {r}"
  shows "\<exists>q. distinct (w # g w # q) \<and> walk_betw (abstract_arborescense T) w (w # g w # q) r"
proof-
  note U = general(3)[OF assms(1) general(1)]
  have *: "\<exists>q. distinct (w # g w # q) \<and> walk_betw (abstract_arborescense T) w (w # g w # q) r"
    if "walk_betw (abstract_arborescense T) w (w # p) r" "distinct (w # p)" "w \<in> \<V> - {r}" for w p
    using that
  proof(induction p arbitrary: w)
    case (Cons u p)
    have "{w, u} \<in> abstract_arborescense T" "walk_betw (abstract_arborescense T) u (u # p) r"
      using Cons.prems(1)
      by (auto simp: walk_betw_cons walk_betw_def)
    then obtain x where "x \<in> \<V> - {r}" "{w, u} = {x, g x}"
      using assms(2)
      by auto
    then consider "u = g w" | "u = x" "w = g x"
      using Cons.prems(2)
      by (auto simp: doubleton_eq_iff)
    then show ?case
    proof cases
      case 2
      obtain q where q: "distinct (u # g u # q)" "walk_betw (abstract_arborescense T) u (u # g u # q) r"
        using Cons.IH \<open>walk_betw _ u (u # p) r\<close> Cons.prems(2) \<open>x \<in> \<V> - {r}\<close> 2
        by auto
      have "u # p = u # g u # q"
        using the1_equality[OF U, of u "u # p"] the1_equality[OF U, of u "u # g u # q"] q
          \<open>walk_betw _ u (u # p) r\<close> Cons.prems(2) \<open>x \<in> \<V> - {r}\<close> 2
        by auto
      then show ?thesis
        using Cons.prems(2) 2
        by simp
    qed (use Cons.prems in auto)
  qed (simp add: walk_betw_def)
  obtain p where p: "walk_betw (abstract_arborescense T) w p r" "distinct p"
    using U[of w] assms(3)
    by blast
  moreover obtain p' where "p = w # p'"
    using p(1)
    by (cases p) (auto simp: walk_betw_def)
  ultimately show ?thesis
    using *[of w p'] assms(3)
    by simp
qed

text \<open>A set @{term A} of directed edges whose undirected image is the arborescence of a valid tree,
      with one edge per non-root vertex, satisfies the tree conditions of @{const
      spanning_tree_partition}.\<close>

lemma arborescense_tree_edges:
  assumes "arborescense_invar T" "(\<lambda>a. {fst a, snd a}) ` A = abstract_arborescense T" "finite A"
    "card A = card \<V> - 1"
  shows "graph_abs.arborescence ((\<lambda>a. {fst a, snd a}) ` A) r ((\<lambda>a. {fst a, snd a}) ` A)"
    "graph_abs ((\<lambda>a. {fst a, snd a}) ` A)"
    "\<forall>x y. {x, y} \<subseteq> A \<and> {fst x, snd x} = {fst y, snd y} \<longrightarrow> x = y"
    "dVs (make_pair ` A) = \<V>"
proof-
  let ?G = "abstract_arborescense T"
  note G = general(2-4)[OF assms(1)]
  have ga: "graph_abs ?G"
    using G(1)
    by (simp add: graph_abs_def)
  then interpret graph_abs ?G .
  have arb: "arborescence r ?G"
    by (rule unique_walks_arborescence) (simp_all add: G general(1) \<V>_finite)
  show "graph_abs.arborescence ((\<lambda>a. {fst a, snd a}) ` A) r ((\<lambda>a. {fst a, snd a}) ` A)"
    "graph_abs ((\<lambda>a. {fst a, snd a}) ` A)"
    using ga arb
    by (simp_all add: assms(2))
  have "?G \<noteq> {}"
    using G(3) general(1)
    by auto
  then have "connected_components ?G = {\<V>}"
    using arb G(3) general(1)
    by (auto simp: connected_def_via_components connected_components_def dest!: arborescense_connected) blast
  then have "card ?G = card \<V> - 1"
    using dblton_E connected_components_card[of ?G] arb G(3)
    by (simp add: arborescence_def dblton_graph_def)
  then have "inj_on (\<lambda>a. {fst a, snd a}) A"
    by (intro eq_card_imp_inj_on assms(3)) (simp add: assms(2,4))
  then show "\<forall>x y. {x, y} \<subseteq> A \<and> {fst x, snd x} = {fst y, snd y} \<longrightarrow> x = y"
    by (auto simp: inj_on_def)
  have "dVs (make_pair ` A) = Vs ((\<lambda>a. {fst a, snd a}) ` A)"
    by (auto simp: dVs_def make_pair_def Vs_def)
  then show "dVs (make_pair ` A) = \<V>"
    using G(3) assms(2)
    by simp
qed

text \<open>The tree invariant from its edge part: the parent walks follow from the arborescence.\<close>

lemma ns_invar_tree_parentI:
  assumes "arborescense_invar (spanning_tree s)"
    "(\<lambda>a. {fst a, snd a}) ` ns_tree_edges s = abstract_arborescense (spanning_tree s)"
    "\<And>w. w \<in> \<V> - {r} \<Longrightarrow> par_edge s w \<in> \<E> \<and>
      (if par_up s w then fst (par_edge s w) = w else snd (par_edge s w) = w)"
  shows "ns_invar_tree s"
proof(intro ns_invar_treeI assms(2))
  have "{fst (par_edge s w), snd (par_edge s w)} = {w, par_vx s w}" if "w \<in> \<V> - {r}" for w
    using that assms(3)
    by (auto simp: par_vx_def split: if_splits)
  then have T: "abstract_arborescense (spanning_tree s) = (\<lambda>w. {w, par_vx s w}) ` (\<V> - {r})"
    unfolding assms(2)[symmetric] image_image par_edge_def[symmetric]
    by (auto intro!: image_cong)
  show "par_edge s v \<in> \<E> \<and> (if par_up s v then fst (par_edge s v) = v else snd (par_edge s v) = v)
      \<and> (\<exists>q. distinct (v # par_vx s v # q) \<and> walk_betw (abstract_arborescense (spanning_tree s)) v
        (v # par_vx s v # q) r)"
    if "v \<in> \<V> - {r}" for v
    using that assms(3) arborescense_parent_walk[OF assms(1) T that]
    by simp
qed

text \<open>\<^bold>\<open>Scan tie-break lemmas.\<close> The heart of strong-feasibility preservation.
      @{const scan_up} keeps the \<^emph>\<open>last\<close> minimiser (updates on \<open>\<le>\<close>),
      @{const scan_down} the \<^emph>\<open>first\<close> (updates on \<open><\<close>). Hence on the
      reversed spine there is \<^emph>\<open>no\<close> minimiser but the leaving vertex itself:
      everything strictly before a @{const scan_down} minimiser (resp. after a @{const scan_up} one) has
      a \<^emph>\<open>strictly larger\<close> residual. The proofs go by induction over the scanned
      prefix: the running best changes only to the current element.\<close>

lemma scan_down_before:
  "\<lbrakk>scan_down s p = (m, v); m \<noteq> - 1; distinct p; w \<in> set (takeWhile (\<lambda>y. y \<noteq> v) p); res_down s w \<noteq> - 1\<rbrakk>
   \<Longrightarrow> m < res_down s w"
proof(induction p arbitrary: m v rule: rev_induct)
  case (snoc x p)
  obtain m' b' where "scan_down s p = (m', b')"
    by fastforce
  moreover have "x \<notin> set p" "takeWhile (\<lambda>y. y \<noteq> x) (p @ [x]) = p"
    using snoc.prems(3)
    by (simp, subst takeWhile_append2) auto
  ultimately show ?case
    using snoc scan_down_snd_mem[of s p m' b'] scan_down_min[of s p m' b' w] snoc.IH[of m' b']
    by (cases "v = x") (auto simp: scan_down_snoc split: if_splits)
qed (simp add: scan_down_def)

lemma scan_up_after:
  "\<lbrakk>scan_up s p = (m, v); m \<noteq> - 1; distinct p; w \<in> set p; w \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) p));
    res_up s w \<noteq> - 1\<rbrakk> \<Longrightarrow> m < res_up s w"
proof(induction p arbitrary: m v rule: rev_induct)
  case (snoc x p)
  obtain m' b' where "scan_up s p = (m', b')"
    by fastforce
  moreover have "x \<notin> set p" "takeWhile (\<lambda>y. y \<noteq> x) (p @ [x]) = p"
    using snoc.prems(3)
    by (simp, subst takeWhile_append2) auto
  ultimately show ?case
    using snoc scan_up_snd_mem[of s p m' b'] snoc.IH[of m' b']
    by (cases "v = x") (auto simp: scan_up_snoc split: if_splits)
qed simp

lemma takeWhile_nth_succ:
  "\<lbrakk>v \<in> set P; w \<in> set (takeWhile (\<lambda>y. y \<noteq> v) P)\<rbrakk> \<Longrightarrow> \<exists>i. Suc i < length P \<and> P ! i = w"
proof(induction P)
  case (Cons a P)
  then have "a \<noteq> v" "P \<noteq> []"
    by auto
  show ?case
  proof(cases "w = a")
    case False
    then obtain i where "Suc i < length P" "P ! i = w"
      using Cons \<open>a \<noteq> v\<close>
      by auto
    then show ?thesis
      by (intro exI[of _ "Suc i"]) simp
  qed (use \<open>P \<noteq> []\<close> in \<open>auto intro!: exI[of _ 0]\<close>)
qed simp

subsection \<open>Consequences of the invariant\<close>

text \<open>Throughout this subsection @{term s} is a state satisfying @{const ns_invar}.

      \<^bold>\<open>(H1)\<close> @{const par_edge} is injective on the non-root vertices. If two
      vertices shared a parent edge, the child endpoint would be ambiguous and one vertex's simple walk
      to the root would begin with a repeat, contradicting the walk conjunct of @{const ns_invar_tree}
      and the uniqueness of simple walks. \<^bold>\<open>(H2)\<close> @{const par_vx} is the successor of
      @{term v} on its unique simple walk to the root.\<close>

context
  fixes s
  assumes inv: "ns_invar s"
begin

private lemmas inv_impl = ns_invar_implD[OF ns_invarD(1)[OF inv]]
  and inv_tree = ns_invarD(7)[OF inv]
  and inv_bflow = ns_invar_bflowD[OF ns_invarD(2)[OF inv]]
  and inv_strict = ns_invar_strictD[OF ns_invarD(6)[OF inv]]
  and inv_pot_fits = ns_invar_pot_fitsD[OF ns_invarD(5)[OF inv]]
  and inv_stp = ns_invar_partitionD[OF ns_invarD(3)[OF inv]]
  and inv_partition = spanning_tree_partitionD[OF ns_invar_partitionD[OF ns_invarD(3)[OF inv]]]
  and inv_parts = ns_invarD[OF inv]
  and inv_flow_fits = ns_invar_flow_fitsD[OF ns_invarD(4)[OF inv]]

private lemmas inv_walk = general(3)[OF inv_impl(7) general(1)]
  and inv_Vs = general(4)[OF inv_impl(7)]
  and inv_get_path_pair = get_path_pair(1)[OF inv_impl(7)]
  and inv_tree_dir = ns_invar_tree_dirD[OF inv_tree]
  and inv_tree_walk = ns_invar_tree_walkD[OF inv_tree]
  and inv_tree_edge = ns_invar_tree_edgeD[OF inv_tree]
  and inv_pot = inv_impl(2)[unfolded pot_valid_def, THEN conjunct1]
    inv_impl(2)[unfolded pot_valid_def, THEN conjunct2, rule_format]

text \<open>\<^bold>\<open>Measure decrease.\<close> A step that lowers the flow cost, or keeps it and
      raises the potential sum, strictly shrinks the candidate tree structures: every candidate of the
      new state is one of the old state, and the old tree structure drops out because its flow and
      potential are unique.\<close>

lemma possible_trees_shrink:
  assumes "ns_flow_cost s' < ns_flow_cost s \<or> (ns_flow_cost s' = ns_flow_cost s \<and> ns_pot_sum s < ns_pot_sum s')"
  shows "card (possible_trees s') < card (possible_trees s)"
proof(intro psubset_card_mono finite_possible_trees psubsetI)
  have "\<C> f' < ns_flow_cost s \<or> (\<C> f' = ns_flow_cost s \<and> (\<Sum> v \<in> \<V>. \<pi>' v) \<ge> ns_pot_sum s)"
    if "\<C> f' < ns_flow_cost s' \<or> (\<C> f' = ns_flow_cost s' \<and> (\<Sum> v \<in> \<V>. \<pi>' v) \<ge> ns_pot_sum s')" for f' \<pi>'
    using that assms
    by auto
  then show "possible_trees s' \<subseteq> possible_trees s"
    unfolding possible_trees_def
    by blast
  have ffit: "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s \<union> ns_selfloops_L)
      (ns_U_of s \<union> ns_selfloops_U) (ns_flow_of s)"
    using inv_parts(4,8)
    by (auto simp: ns_invar_flow_fits_def flow_fits_spanning_tree_partition_def
      ns_selfloops_L_def ns_selfloops_U_def ns_invar_selfloop_def)
  have pfit: "potential_fits_spanning_tree_partition r (ns_tree_edges s) (ns_pot_of s)"
    using inv_parts(5)
    by (simp add: ns_invar_pot_fits_def)
  let ?z = "(ns_tree_edges s, ns_L_of s \<union> ns_selfloops_L, ns_U_of s \<union> ns_selfloops_U)"
  have "?z \<in> possible_trees s"
    unfolding possible_trees_def
    using inv_stp ffit pfit inv_bflow
    by (auto simp: ns_flow_cost_def ns_pot_sum_def)
  moreover have "?z \<notin> possible_trees s'"
  proof
    assume "?z \<in> possible_trees s'"
    then obtain f' \<pi>' where "flow_fits_spanning_tree_partition (ns_tree_edges s) (ns_L_of s \<union> ns_selfloops_L)
        (ns_U_of s \<union> ns_selfloops_U) f'" "potential_fits_spanning_tree_partition r (ns_tree_edges s) \<pi>'"
      "f' is b flow" "\<C> f' < ns_flow_cost s' \<or> (\<C> f' = ns_flow_cost s' \<and> (\<Sum> v \<in> \<V>. \<pi>' v) \<ge> ns_pot_sum s')"
      unfolding possible_trees_def
      by blast
    moreover have "\<C> f' = ns_flow_cost s"
      unfolding \<C>_def ns_flow_cost_def
      using spanning_flow_unique[OF calculation(3) inv_bflow inv_stp calculation(1) ffit]
      by (intro sum.cong) auto
    moreover have "(\<Sum> v \<in> \<V>. \<pi>' v) = ns_pot_sum s"
      unfolding ns_pot_sum_def
      using spanning_potential_unqiue[OF inv_stp pfit calculation(2)]
      by (intro sum.cong) auto
    ultimately show False
      using assms
      by linarith
  qed
  ultimately show "possible_trees s' \<noteq> possible_trees s"
    by blast
qed
lemma tree_walk_unique:
  "\<lbrakk>x \<in> \<V>; walk_betw (abstract_arborescense (spanning_tree s)) x p r; distinct p;
    walk_betw (abstract_arborescense (spanning_tree s)) x p' r; distinct p'\<rbrakk> \<Longrightarrow> p = p'"
  using inv_walk[of x]
  by blast

lemma par_edge_set: "v \<in> \<V> - {r} \<Longrightarrow> {fst (par_edge s v), snd (par_edge s v)} = {v, par_vx s v}"
  by (drule inv_tree_dir) (auto simp: par_vx_def split: if_splits)

lemma par_vx_no_swap:
  assumes "v \<in> \<V> - {r}" "v' \<in> \<V> - {r}" "par_vx s v = v'" "par_vx s v' = v"
  shows False
proof-
  obtain q where "distinct (v # v' # q)" "walk_betw (abstract_arborescense (spanning_tree s)) v' (v' # q) r"
    using inv_tree_walk[OF assms(1)]
    unfolding assms(3)
    by (blast dest: walk_betw_cons[THEN iffD1])
  moreover obtain q' where "distinct (v' # v # q')"
    "walk_betw (abstract_arborescense (spanning_tree s)) v' (v' # v # q') r"
    using inv_tree_walk[OF assms(2)]
    unfolding assms(4)
    by blast
  ultimately have "v' # q = v' # v # q'"
    using tree_walk_unique[of v' "v' # q" "v' # v # q'"] assms(2)
    by simp
  then show False
    using \<open>distinct (v # v' # q)\<close>
    by simp
qed

lemma par_edge_inj: "\<lbrakk>v \<in> \<V> - {r}; v' \<in> \<V> - {r}; par_edge s v = par_edge s v'\<rbrakk>
  \<Longrightarrow> v = v'"
  using par_edge_set[of v] par_edge_set[of v'] par_vx_no_swap[of v v']
  by (auto simp: doubleton_eq_iff)

lemma par_vx_walk_succ:
  "v \<in> \<V> - {r} \<Longrightarrow>
    \<exists>q. distinct (v # par_vx s v # q) \<and> walk_betw (abstract_arborescense (spanning_tree s)) v
      (v # par_vx s v # q) r"
  by (rule inv_tree_walk)

text \<open>\<^bold>\<open>Residual signs (\S{}0).\<close> Every residual is non-negative or the
      @{term \<open>- 1\<close>} infinity sentinel: the backward residual is the (non-negative) flow, and
      the forward residual is \<open>cap - f \<ge> 0\<close> whenever it is finite (using @{thm cap_nonneg}
      to complete the sentinel encoding). On the strict side, an \<^emph>\<open>upward-traversed\<close>
      parent edge has a \<^emph>\<open>strictly positive\<close> residual (KV strong feasibility).\<close>

lemma res_bwd_nonneg: "e \<in> \<E> \<Longrightarrow> 0 \<le> res_bwd s e"
  using inv_bflow
  by (auto simp: isbflow_def isuflow_def res_bwd_def)

lemma res_fwd_sign: "e \<in> \<E> \<Longrightarrow> 0 \<le> res_fwd s e \<or> res_fwd s e = - 1"
  using inv_bflow cap_nonneg[of e] cap_finite[of e]
  by (cases "cap e = - 1") (auto simp: isbflow_def isuflow_def res_fwd_def)

lemma res_down_sign: "v \<in> \<V> - {r} \<Longrightarrow> 0 \<le> res_down s v \<or> res_down s v = - 1"
  using res_bwd_nonneg res_fwd_sign inv_tree_edge[of v]
  by (auto simp: res_down_def)

lemma res_up_pos: "v \<in> \<V> - {r} \<Longrightarrow> 0 < res_up s v \<or> res_up s v = - 1"
  using inv_strict[of v] inv_tree_edge[of v] cap_nonneg[of "par_edge s v"] cap_finite[of "par_edge s v"]
  by (cases "cap (par_edge s v) = - 1") (auto simp: res_up_def res_fwd_def res_bwd_def split: if_splits)

text \<open>Lifting the residual signs through a scan: if every scanned vertex is a non-root vertex, the
      scan's value component is again non-negative or @{term \<open>- 1\<close>}.\<close>

lemma scan_up_val_sign: "\<lbrakk>set p \<subseteq> \<V> - {r}; scan_up s p = (m, v0)\<rbrakk> \<Longrightarrow> 0
  \<le> m \<or> m = - 1"
  using scan_up_val_at[of s p m v0] scan_up_snd_mem[of s p m v0] res_up_pos[of v0]
  by (cases "m = - 1") (auto simp: subset_iff)

lemma scan_down_val_sign: "\<lbrakk>set p \<subseteq> \<V> - {r}; scan_down s p = (m, v0)\<rbrakk> \<Longrightarrow> 0
  \<le> m \<or> m = - 1"
  using scan_down_val_at[of s p m v0] scan_down_snd_mem[of s p m v0] res_down_sign[of v0]
  by (cases "m = - 1") auto

text \<open>The walk-successor fact (H2 lifted): on \<^emph>\<open>any\<close> distinct walk to the root,
      the successor of a non-root vertex is its @{const par_vx}, since the suffix from that vertex is
      \<^emph>\<open>the\<close> unique distinct walk to @{term r} (@{thm general(3)}). Applied to a
      spine @{term \<open>P @ a # p3\<close>} it gives both the interior links and the apex link @{term
      \<open>par_vx s (last P) = a\<close>}.\<close>

lemma walk_succ_is_par_vx:
  assumes "walk_betw (abstract_arborescense (spanning_tree s)) u W r" "distinct W" "Suc i < length W"
    "W ! i \<in> \<V> - {r}"
  shows "par_vx s (W ! i) = W ! Suc i"
proof-
  have "walk_betw (abstract_arborescense (spanning_tree s)) (W ! i) (W ! i # drop (Suc i) W) r"
    "distinct (W ! i # drop (Suc i) W)"
    using walk_suff[of _ u "take i W" "W ! i" "drop (Suc i) W" r] assms(1-3)
    by (simp_all add: Cons_nth_drop_Suc)
  moreover obtain q where "distinct (W ! i # par_vx s (W ! i) # q)"
    "walk_betw (abstract_arborescense (spanning_tree s)) (W ! i) (W ! i # par_vx s (W ! i) # q) r"
    using inv_tree_walk assms(4)
    by blast
  ultimately have "drop (Suc i) W = par_vx s (W ! i) # q"
    using tree_walk_unique assms(4)
    by blast
  then show ?thesis
    using hd_drop_conv_nth[of "Suc i" W] assms(3)
    by simp
qed

text \<open>Both tree paths returned by \<open>get_path_pair\<close> consist of non-root vertices: their
      vertices lie on a simple walk to @{term r} inside the arborescence, so they are in @{term
      \<open>\<V>\<close>}, and @{term r} (the walk's endpoint) cannot repeat inside a prefix by
      distinctness.\<close>

lemma get_path_pair_verts:
  assumes "e \<in> \<E>" "fst e \<noteq> snd e" "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
  shows "set p1 \<subseteq> \<V> - {r}" "set p2 \<subseteq> \<V> - {r}"
proof-
  obtain a p3 where "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r"
      "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r"
      "distinct (p1 @ a # p3)" "distinct (p2 @ a # p3)"
    using inv_get_path_pair[OF assms(3,2) fst_E_V snd_E_V] assms(1)
    by blast
  moreover have "r \<in> set (a # p3)"
    using calculation(1) last_in_set[of "a # p3"]
    by (simp add: walk_betw_def del: last.simps)
  ultimately show "set p1 \<subseteq> \<V> - {r}" "set p2 \<subseteq> \<V> - {r}"
    by (auto dest!: walk_in_Vs simp: inv_Vs)
qed

text \<open>When the selector fires, the entering edge is a real @{term L}/@{term U} edge --- hence a
      graph edge that is not (yet) a tree edge --- and it is never a self-loop. Its reduced cost equals
      its plain cost (the potentials cancel when @{term \<open>fst e = snd e\<close>}), so a self-loop
      entering edge would contradict the self-loop classification invariant @{const
      ns_invar_selfloop}.\<close>

lemma ns_select_facts:
  assumes "ns_select s = Some (e, in_U, \<gamma>, sel')"
  shows "sel_invar sel'" "rcost_invar \<gamma>" "rcost_abstract \<gamma> = reduced_cost (potentials s) e"
    "entering_edge (potentials s) (edge_state s) e in_U" "if in_U then e \<in> ns_U_of s else e \<in> ns_L_of s"
proof-
  have "selection_precond (edge_sel s) (potentials s) (edge_state s)"
    using inv_impl inv_pot_fits
    by (simp add: selection_precond_def potential_fits_spanning_tree_partition_def)
  then show "sel_invar sel'" "rcost_invar \<gamma>" "rcost_abstract \<gamma> = reduced_cost (potentials s) e"
    "entering_edge (potentials s) (edge_state s) e in_U"
    using sel_select_SomeD assms
    by (simp_all add: ns_select_def)
  then show "if in_U then e \<in> ns_U_of s else e \<in> ns_L_of s"
    by (auto simp: entering_edge_def ns_L_of_def ns_U_of_def)
qed

lemmas ns_select_entering = ns_select_facts(4)

lemma ns_select_SomeD:
  assumes "ns_select s = Some (e, in_U, \<gamma>, sel')"
  shows "e \<in> ns_L_of s \<union> ns_U_of s" "e \<in> \<E>" "e \<notin> ns_tree_edges s"
  using ns_select_entering[OF assms] inv_partition(2,3)
  by (auto simp: entering_edge_def ns_L_of_def ns_U_of_def split: if_splits)

lemma entering_not_selfloop: "ns_select s = Some (e, in_U, \<gamma>, sel') \<Longrightarrow> fst e \<noteq> snd e"
  by (drule ns_select_entering) (auto simp: entering_edge_def split: if_splits)

lemma select_path_verts:
  assumes "ns_select s = Some (e, in_U, \<gamma>, sel')" "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
  shows "set p1 \<subseteq> \<V> - {r}" "set p2 \<subseteq> \<V> - {r}"
  using get_path_pair_verts[OF ns_select_SomeD(2)[OF assms(1)] entering_not_selfloop[OF assms(1)] assms(2)]
  by simp_all

text \<open>A tree edge is never a self-loop: the tree edges form a @{const dblton_graph}.\<close>

lemma tree_edge_not_selfloop: "e \<in> ns_tree_edges s \<Longrightarrow> fst e \<noteq> snd e"
  using singleton_not_dblton[OF graph_abs.dblton_E[OF inv_partition(6)], of "fst e"]
    image_eqI[of "{fst e, snd e}" "\<lambda>e. {fst e, snd e}" e]
  by auto

text \<open>\<^bold>\<open>\S{}4.1 Path/array alignment\<close> --- the linchpin. Here the selector has fired
      (@{term \<open>ns_select s = Some (e, in_U, \<gamma>, sel')\<close>}), and @{term p1}, @{term p2} are the two
      tree paths @{term \<open>get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)\<close>}. The
      \<open>get_path_pair\<close> specification names an apex @{term a} and a shared tail @{term p3};
      the consequence used downstream is that consecutive path vertices are parent-linked (@{const
      par_vx} of one is the next), that the two paths are disjoint, and that @{const par_edge} is
      injective on their union (H1). The degenerate case @{term \<open>p1 = []\<close>} / @{term
      \<open>p2 = []\<close>} (one endpoint of @{term e} is an ancestor of the other) is
      admitted.\<close>

lemma get_path_pair_align:
  assumes "ns_select s = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
  shows "\<exists> a p3.
           walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r \<and>
           walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r \<and>
           distinct (p1 @ a # p3) \<and> distinct (p2 @ a # p3) \<and> set p1 \<inter> set p2 = {}"
    and "\<And>i. Suc i < length p1 \<Longrightarrow> par_vx s (p1 ! i) = p1 ! Suc i"
    and "\<And>i. Suc i < length p2 \<Longrightarrow> par_vx s (p2 ! i) = p2 ! Suc i"
    and "set p1 \<inter> set p2 = {}"
    and "inj_on (par_edge s) (set p1 \<union> set p2)"
proof-
  obtain a p3 where w: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r"
      "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r"
      "distinct (p1 @ a # p3)" "distinct (p2 @ a # p3)" "set p1 \<inter> set p2 = {}"
    using inv_get_path_pair[OF assms(2) entering_not_selfloop[OF assms(1)] fst_E_V snd_E_V]
      ns_select_SomeD(2)[OF assms(1)]
    by blast
  note pV = select_path_verts[OF assms]
  from w show "\<exists>a p3. walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r \<and>
      walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r \<and>
      distinct (p1 @ a # p3) \<and> distinct (p2 @ a # p3) \<and> set p1 \<inter> set p2 = {}"
    "set p1 \<inter> set p2 = {}"
    by blast+
  show "par_vx s (p1 ! i) = p1 ! Suc i" if "Suc i < length p1" for i
    using walk_succ_is_par_vx[OF w(1,3), of i] subsetD[OF pV(1) nth_mem[of i p1]] that
    by (simp add: nth_append)
  show "par_vx s (p2 ! i) = p2 ! Suc i" if "Suc i < length p2" for i
    using walk_succ_is_par_vx[OF w(2,4), of i] subsetD[OF pV(2) nth_mem[of i p2]] that
    by (simp add: nth_append)
  show "inj_on (par_edge s) (set p1 \<union> set p2)"
    using pV
    by (auto intro!: inj_onI par_edge_inj)
qed

lemma bottleneck_delta_bounds:
  assumes "ns_select s = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    "bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus)" "\<delta> \<noteq> - 1"
  shows "0 \<le> \<delta>"
    and "\<And>w. \<lbrakk>w \<in> set (if in_U then p1 else p2); res_up s w \<noteq> - 1\<rbrakk> \<Longrightarrow>
      \<delta> \<le> res_up s w"
    and "\<And>w. \<lbrakk>w \<in> set (if in_U then p2 else p1); res_down s w \<noteq> - 1\<rbrakk> \<Longrightarrow>
      \<delta> \<le> res_down s w"
    and "(if in_U then res_bwd s e else res_fwd s e) \<noteq> - 1
      \<Longrightarrow> \<delta> \<le> (if in_U then res_bwd s e else res_fwd s e)"
proof-
  obtain mu vu md vd where su: "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    and sd: "scan_down s (if in_U then p2 else p1) = (md, vd)"
    by fastforce
  have "set (if in_U then p1 else p2) \<subseteq> \<V> - {r}" "set (if in_U then p2 else p1) \<subseteq> \<V> - {r}" "e \<in> \<E>"
    using select_path_verts[OF assms(1,2)] ns_select_SomeD(2)[OF assms(1)]
    by simp_all
  then have "0 \<le> mu \<or> mu = - 1" "0 \<le> md \<or> md = - 1"
    "0 \<le> (if in_U then res_bwd s e else res_fwd s e) \<or> (if in_U then res_bwd s e else res_fwd s e) = - 1"
    using su sd scan_up_val_sign scan_down_val_sign res_bwd_nonneg res_fwd_sign
    by (blast, blast, simp)
  note sg = this and \<delta> = bottleneck_delta[OF assms(3,4) su sd]
  have "0 \<le> \<delta> \<or> \<delta> = - 1"
    unfolding \<delta>
    by (intro mininf_sign sg)
  then show "0 \<le> \<delta>"
    using assms(4)
    by simp
  show "\<delta> \<le> res_up s w" if "w \<in> set (if in_U then p1 else p2)" "res_up s w \<noteq> - 1" for w
    using scan_up_min[OF su that] \<delta> sg(1,2)
    by (auto simp: mininf_def)
  show "\<delta> \<le> res_down s w" if "w \<in> set (if in_U then p2 else p1)" "res_down s w \<noteq> - 1" for w
    using scan_down_min[OF sd that] \<delta> sg(1,2)
    by (auto simp: mininf_def)
  show "(if in_U then res_bwd s e else res_fwd s e) \<noteq> - 1 \<Longrightarrow> \<delta> \<le> (if in_U then res_bwd s e else res_fwd s e)"
    using \<delta>
    by (auto simp: mininf_def)
qed

text \<open>\<^bold>\<open>\S{}4.6 @{const bottleneck}-return facts\<close> for the pivot branch: the
      leaving child @{term v} lies on the spine @{term P} it was scanned from, is a non-root vertex, its
      parent edge is the leaving tree edge @{term e0}, and the entering edge @{term e} is not yet a tree
      edge. The positivity fact from \S{}0 (no up-side residual is @{term 0}, so an up-side leaving edge
      forces @{term \<open>\<delta> > 0\<close>}) is bundled here too.\<close>

lemma bottleneck_pivot_facts:
  assumes "ns_select s = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)"
  shows "v \<in> set (if in_U = up_side then p1 else p2)"
    and "v \<in> \<V> - {r}"
    and "par_edge s v \<in> ns_tree_edges s"
    and "e \<notin> ns_tree_edges s"
    and "\<delta> \<ge> 0"
    and "up_side \<Longrightarrow> \<delta> > 0"
proof-
  obtain mu vu md vd where su: "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    and sd: "scan_down s (if in_U then p2 else p1) = (md, vd)"
    by fastforce
  have "\<delta> \<noteq> - 1" "(up_side \<and> mu \<noteq> - 1 \<and> mu = \<delta> \<and> vu = v) \<or>
    (\<not> up_side \<and> md = \<delta> \<and> md \<noteq> - 1 \<and> vd = v)"
    using assms(3) mininf_snd_of_neq_fst[of "if in_U then res_bwd s e else res_fwd s e" "mininf mu md"]
      mininf_snd_attains[of mu md]
    by (auto simp: bottleneck_def Let_def su sd split: if_splits)
  moreover note select_path_verts[OF assms(1,2)]
  ultimately show "v \<in> set (if in_U = up_side then p1 else p2)" "v \<in> \<V> - {r}"
    using scan_up_snd_mem[OF su] scan_down_snd_mem[OF sd]
    by (auto split: if_splits)
  then show "par_edge s v \<in> ns_tree_edges s"
    by (auto simp: par_edge_def)
  show "e \<notin> ns_tree_edges s"
    using ns_select_SomeD(3) assms(1)
    by blast
  show "0 \<le> \<delta>"
    using bottleneck_delta_bounds(1) assms \<open>\<delta> \<noteq> - 1\<close>
    by blast
  show "up_side \<Longrightarrow> 0 < \<delta>"
    using \<open>(up_side \<and> _) \<or> _\<close> scan_up_val_at[OF su] res_up_pos \<open>v \<in> \<V> - {r}\<close>
    by fastforce
qed

text \<open>\<^bold>\<open>Pushing along an arc.\<close> Pushing @{term \<delta>} forwards (resp.\ backwards) by
      at most the residual keeps the capacity bounds; strictly below the residual it keeps strict
      feasibility, and pushing against the strict direction of a parent edge keeps it strict.\<close>

lemma push_fwd_bound:
  assumes "a \<in> \<E>" "0 \<le> \<delta>" "res_fwd s a = - 1 \<or> \<delta> \<le> res_fwd s a"
  shows "0 \<le> flow_lookup (current_flow s) a + \<delta>
    \<and> ereal (h (flow_lookup (current_flow s) a + \<delta>)) \<le> \<u> a"
proof-
  have "0 \<le> flow_lookup (current_flow s) a" "ereal (h (flow_lookup (current_flow s) a)) \<le> \<u> a"
    using inv_bflow assms(1)
    by (auto simp: isbflow_def isuflow_def)
  then show ?thesis
    using assms cap_infinite[OF assms(1)] cap_nonneg[OF assms(1)] cap_finite[OF assms(1)]
    by (cases "cap a = - 1") (auto simp: res_fwd_def)
qed

lemma push_bwd_bound:
  assumes "a \<in> \<E>" "0 \<le> \<delta>" "\<delta> \<le> res_bwd s a"
  shows "0 \<le> flow_lookup (current_flow s) a - \<delta>
    \<and> ereal (h (flow_lookup (current_flow s) a - \<delta>)) \<le> \<u> a"
proof-
  have u: "ereal (h (flow_lookup (current_flow s) a)) \<le> \<u> a"
    using inv_bflow assms(1)
    by (auto simp: isbflow_def isuflow_def)
  show ?thesis
    using assms(2,3) order_trans[OF _ u, of "ereal (h (flow_lookup (current_flow s) a - \<delta>))"]
    by (auto simp: res_bwd_def)
qed

lemma push_bound:
  assumes "a \<in> \<E>" "0 \<le> \<delta>" "\<lbrakk>fwd; res_fwd s a \<noteq> - 1\<rbrakk> \<Longrightarrow> \<delta> \<le> res_fwd s a"
    "\<not> fwd \<Longrightarrow> \<delta> \<le> res_bwd s a"
  shows "0 \<le> flow_lookup (current_flow s) a + (if fwd then \<delta> else - \<delta>)
         \<and> ereal (h (flow_lookup (current_flow s) a + (if fwd then \<delta> else - \<delta>))) \<le> \<u> a"
  using push_fwd_bound[OF assms(1,2)] push_bwd_bound[OF assms(1,2)] assms(3,4)
  by (cases fwd) auto

lemma strict_push:
  "\<lbrakk>a \<in> \<E>; if fwd then res_fwd s a = - 1 \<or> \<delta> < res_fwd s a else \<delta> < res_bwd s a\<rbrakk>
   \<Longrightarrow> if fwd then ereal (h (flow_lookup (current_flow s) a + \<delta>)) < \<u> a
       else 0 < flow_lookup (current_flow s) a - \<delta>"
  using inv_bflow cap_infinite[of a] cap_nonneg[of a] cap_finite[of a]
  by (cases fwd; cases "cap a = - 1") (auto simp: res_fwd_def res_bwd_def isbflow_def isuflow_def)

lemma strict_relax:
  "\<lbrakk>v \<in> \<V> - {r}; 0 \<le> \<delta>\<rbrakk> \<Longrightarrow>
    if par_up s v then ereal (h (flow_lookup (current_flow s) (par_edge s v) - \<delta>)) < \<u> (par_edge s v)
    else 0 < flow_lookup (current_flow s) (par_edge s v) + \<delta>"
  using inv_strict[of v] order.strict_trans1[of "ereal (h (flow_lookup (current_flow s) (par_edge s v) - \<delta>))"
      "ereal (h (flow_lookup (current_flow s) (par_edge s v)))" "\<u> (par_edge s v)"]
  by (cases "par_up s v") simp_all

text \<open>\<^bold>\<open>Telescoping along a tree path.\<close> A parent edge contributes to the
      balances of its two endpoints, and its cost is the potential difference of its endpoints (its
      reduced cost is zero). So signed sums of either along a tree path collapse to the two boundary
      vertices.\<close>

lemma up_contrib:
  "w \<in> \<V> - {r} \<Longrightarrow> (if par_up s w then \<delta> else - \<delta>) *
    ((if snd (par_edge s w) = v then 1 else 0) - (if fst (par_edge s w) = v then 1 else 0))
       = \<delta> * ((if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0))"
  by (drule inv_tree_dir) (cases "par_up s w"; auto simp: par_vx_def)

lemma cval_lemma:
  assumes "w \<in> \<V> - {r}"
  shows "\<c> (par_edge s w) = (if par_up s w then ns_pot_of s (par_vx s w) - ns_pot_of s w
                                          else ns_pot_of s w - ns_pot_of s (par_vx s w))"
proof-
  have "\<c> (par_edge s w) + ns_pot_of s (fst (par_edge s w)) = ns_pot_of s (snd (par_edge s w))"
    using inv_pot_fits assms
    by (simp add: potential_fits_spanning_tree_partition_def par_edge_def)
  then show ?thesis
    using inv_tree_dir[OF assms]
    by (cases "par_up s w") (auto simp: par_vx_def)
qed

lemma up_cost_contrib:
  "w \<in> \<V> - {r} \<Longrightarrow>
    \<c> (par_edge s w) * (if par_up s w then \<delta> else - \<delta>) = \<delta> * (ns_pot_of s (par_vx s w) - ns_pot_of s w)"
  by (cases "par_up s w") (simp_all add: cval_lemma algebra_simps)

context
  fixes u P a p3
  assumes path: "walk_betw (abstract_arborescense (spanning_tree s)) u (P @ a # p3) r" "distinct (P @ a # p3)"
    "set P \<subseteq> \<V> - {r}"
begin

lemma path_telescope_gen: "(\<Sum>w\<leftarrow>P. \<phi> (par_vx s w) - \<phi> w) = \<phi> a - (\<phi> u :: real)"
proof-
  have "(\<Sum>w\<leftarrow>butlast (P @ [a]). \<phi> (par_vx s w) - \<phi> w) = \<phi> (last (P @ [a])) - \<phi> (hd (P @ [a]))"
  proof(rule telescope_succ_gen)
    show "par_vx s ((P @ [a]) ! i) = (P @ [a]) ! Suc i" if "Suc i < length (P @ [a])" for i
      using walk_succ_is_par_vx[OF path(1,2), of i] subsetD[OF path(3) nth_mem[of i P]] that
      by (auto simp: nth_append)
  qed simp
  moreover have "hd (P @ a # p3) = u"
    using path(1)
    by (simp add: walk_betw_def)
  ultimately show ?thesis
    by (cases P) auto
qed

lemma path_telescope:
  "(\<Sum>w\<leftarrow>P. (if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0))
     = (if a = v then 1 else 0) - (if u = v then 1 else 0)"
  by (rule path_telescope_gen[where \<phi> = "\<lambda>x. if x = v then 1 else 0"])

lemma up_sum:
  "(\<Sum>w\<leftarrow>P. (if par_up s w then \<delta> else - \<delta>) *
    ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
     = \<delta> * ((if a = v then 1 else 0) - (if u = v then 1 else 0))"
proof-
  have "map (\<lambda>w. (if par_up s w then \<delta> else - \<delta>) *
    ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0))) P
      = map (\<lambda>w. \<delta> * ((if par_vx s w = v then (1::real) else 0) - (if w = v then 1 else 0))) P"
    using path(3)
    by (intro map_cong refl up_contrib) auto
  then show ?thesis
    by (simp only: sum_list_scale path_telescope)
qed

lemma down_sum:
  "(\<Sum>w\<leftarrow>P. (if par_up s w then - \<delta> else \<delta>) *
    ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
     = \<delta> * ((if u = v then 1 else 0) - (if a = v then 1 else 0))"
  using up_sum[of "- \<delta>" v]
  by (simp add: algebra_simps cong: if_cong)

lemma up_sum_h:
  "(\<Sum>w\<leftarrow>P. h (if par_up s w then \<delta> else - \<delta>) *
    ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
     = h \<delta> * ((if a = v then 1 else 0) - (if u = v then 1 else 0))"
  using up_sum[of "h \<delta>" v]
  by (simp add: if_distrib[where f = h] cong: if_cong)

lemma down_sum_h:
  "(\<Sum>w\<leftarrow>P. h (if par_up s w then - \<delta> else \<delta>) *
    ((if snd (par_edge s w) = v then (1::real) else 0) - (if fst (par_edge s w) = v then 1 else 0)))
     = h \<delta> * ((if u = v then 1 else 0) - (if a = v then 1 else 0))"
  using down_sum[of "h \<delta>" v]
  by (simp add: if_distrib[where f = h] cong: if_cong)

lemma up_cost_sum:
  "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * (if par_up s w then \<delta> else - \<delta>)) = \<delta> * (ns_pot_of s a - ns_pot_of s u)"
proof-
  have "map (\<lambda>w. \<c> (par_edge s w) * (if par_up s w then \<delta> else - \<delta>)) P
      = map (\<lambda>w. \<delta> * (ns_pot_of s (par_vx s w) - ns_pot_of s w)) P"
    using path(3)
    by (intro map_cong refl up_cost_contrib) auto
  then show ?thesis
    by (simp only: sum_list_scale path_telescope_gen[where \<phi> = "ns_pot_of s"])
qed

lemma down_cost_sum:
  "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * (if par_up s w then - \<delta> else \<delta>)) = \<delta> * (ns_pot_of s u - ns_pot_of s a)"
  using up_cost_sum[of "- \<delta>"]
  by (simp add: algebra_simps cong: if_cong)

lemma up_cost_sum_h:
  "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * h (if par_up s w then \<delta> else - \<delta>)) = h \<delta> * (ns_pot_of s a - ns_pot_of s u)"
  using up_cost_sum[of "h \<delta>"]
  by (simp add: if_distrib[where f = h] cong: if_cong)

lemma down_cost_sum_h:
  "(\<Sum>w\<leftarrow>P. \<c> (par_edge s w) * h (if par_up s w then - \<delta> else \<delta>)) = h \<delta> * (ns_pot_of s u - ns_pot_of s a)"
  using down_cost_sum[of "h \<delta>"]
  by (simp add: if_distrib[where f = h] cong: if_cong)

end

text \<open>\<^bold>\<open>\S{}4.4 Shift set and cut.\<close> @{term shift_pot} adds @{term \<gamma>} (signed) over exactly the moved
      subtree @{term \<open>tree_subtree s v\<close>}, the component of @{term v} in \<open>(V, T - {e0})\<close>, which
      excludes @{term r}. Every tree edge other than \<open>e0\<close> has both ends on one side of the cut.\<close>

lemma shift_pot_lookup:
  assumes "v \<in> \<V>"
  shows "pot_invar (shift_pot (spanning_tree s) v (potentials s) \<gamma> up)"
    and "pot_lookup (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u = (if u \<in> tree_subtree s v
      then (if up then pot_value_plus else pot_value_minus) (pot_lookup (potentials s) u) \<gamma>
      else pot_lookup (potentials s) u)"
    and "tree_subtree s v \<subseteq> \<V>"
proof-
  obtain xs where xs: "set xs = tree_subtree s v" "distinct xs" "shift_pot (spanning_tree s) v (potentials s) \<gamma> up
      = foldr (\<lambda>x a. pot_upd a x ((if up then pot_value_plus else pot_value_minus) (pot_lookup a x) \<gamma>)) xs (potentials s)"
    using shift_pot_spec[OF inv_impl(7) assms inv_pot]
    by blast
  show "tree_subtree s v \<subseteq> \<V>"
    using inv_Vs
    by (auto dest: walk_endpoints(1))
  with xs(1) have "\<forall>x\<in>set xs. x \<in> \<V>"
    by auto
  from foldr_pot_upd_invar[OF this inv_pot(1)] foldr_pot_upd_lookup[OF xs(2) this inv_pot(1),
      where hop = "\<lambda>a. (if up then pot_value_plus else pot_value_minus) a \<gamma>"]
  show "pot_invar (shift_pot (spanning_tree s) v (potentials s) \<gamma> up)"
    "pot_lookup (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u = (if u \<in> tree_subtree s v
      then (if up then pot_value_plus else pot_value_minus) (pot_lookup (potentials s) u) \<gamma>
      else pot_lookup (potentials s) u)"
    unfolding xs(3)
    by (simp_all add: xs(1))
qed

lemma shift_pot_abstract:
  assumes "v \<in> \<V>" "rcost_invar \<gamma>" "\<And>u. u \<in> tree_subtree s v \<Longrightarrow>
    good_pot_val (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)"
  shows "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u = (if u \<in> tree_subtree s v
      then (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)
      else ns_pot_of s u)"
    and "pot_valid (shift_pot (spanning_tree s) v (potentials s) \<gamma> up)"
proof-
  have "pot_value_abstract ((if up then pot_value_plus else pot_value_minus) (pot_lookup (potentials s) u) \<gamma>)
      = (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)
    \<and> pot_value_invar ((if up then pot_value_plus else pot_value_minus) (pot_lookup (potentials s) u) \<gamma>)"
    if "u \<in> tree_subtree s v" for u
  proof-
    have "u \<in> \<V>"
      using shift_pot_lookup(3)[OF assms(1)] that
      by blast
    then show ?thesis
      using pot_plus_good[OF inv_pot(2) assms(2)] pot_minus_good[OF inv_pot(2) assms(2)] assms(3)[OF that]
      by (cases up) simp_all
  qed
  then show "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> up) u = (if u \<in> tree_subtree s v
      then (if up then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u - rcost_abstract \<gamma>)
      else ns_pot_of s u)" "pot_valid (shift_pot (spanning_tree s) v (potentials s) \<gamma> up)"
    using shift_pot_lookup(1,2)[OF assms(1), of \<gamma> up] inv_pot(2)
    by (auto simp: pot_valid_def) blast+
qed

lemma S_via_walk:
  "\<lbrakk>walk_betw (abstract_arborescense (spanning_tree s)) x W r; distinct W\<rbrakk>
   \<Longrightarrow> (x \<in> tree_subtree s v) = (v \<in> set W)"
  using tree_walk_unique[of x W] walk_endpoints(1)[of _ x W r] inv_Vs
  by blast

lemma cut_4c: "\<lbrakk>w \<in> \<V> - {r}; w \<noteq> v\<rbrakk> \<Longrightarrow> (w \<in> tree_subtree s v) = (par_vx s w \<in> tree_subtree s v)"
proof-
  assume "w \<in> \<V> - {r}" "w \<noteq> v"
  moreover obtain q where "distinct (w # par_vx s w # q)"
    "walk_betw (abstract_arborescense (spanning_tree s)) w (w # par_vx s w # q) r"
    using inv_tree_walk[OF calculation(1)]
    by blast
  moreover note S_via_walk[OF this(2,1)] S_via_walk[OF conjunct1[OF walk_betw_cons[THEN iffD1, OF this(2)]]]
  ultimately show ?thesis
    by simp
qed

lemma par_edge_inj_on: "inj_on (par_edge s) (\<V> - {r})"
  by (rule inj_onI) (rule par_edge_inj)

text \<open>\<^bold>\<open>Single-vertex pick.\<close> On a distinct non-root list the parent-indexed sum
      collapses to the single contribution of @{term v} (if present), by injectivity of @{const
      par_edge}.\<close>

lemma par_sum_pick:
  "\<lbrakk>distinct xs; set xs \<subseteq> \<V> - {r}; v \<in> \<V> - {r}\<rbrakk>
   \<Longrightarrow> (\<Sum>w\<leftarrow>xs. if par_edge s w = par_edge s v then g w else 0) = (if v \<in> set xs then g v else 0)"
proof(induction xs)
  case (Cons w xs)
  then have "(par_edge s w = par_edge s v) = (w = v)"
    using par_edge_inj[of w v]
    by auto
  with Cons show ?case
    by auto
qed simp

lemma card_tree_edges: "card (ns_tree_edges s) = card \<V> - 1"
  using card_image[OF par_edge_inj_on]
  by (simp add: par_edge_def[abs_def] card_Diff_singleton general(1) \<V>_finite)

subsection \<open>One step of the loop\<close>

text \<open>In the following contexts @{term s} satisfies the invariant, the selector has returned the
      entering edge @{term e}, and @{term p1}, @{term p2} are its two tree paths. The facts shared by the
      flip and the pivot come first.\<close>

context
  fixes e in_U \<gamma> sel' p1 p2
  assumes step: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
begin

lemmas step_sel = ns_select_facts[OF step(1)]
  and step_walks = get_path_pair_align[OF step]
  and step_verts = select_path_verts[OF step]

lemma step_entering:
  "e \<in> \<E>" "e \<notin> ns_tree_edges s" "fst e \<noteq> snd e"
    "if in_U then e \<in> ns_U_of s else e \<in> ns_L_of s"
  "e \<notin> ns_selfloops_L" "e \<notin> ns_selfloops_U" "e \<in> ns_L_of s \<union> ns_U_of s" "fst e \<in> \<V>" "snd e \<in> \<V>"
  using ns_select_SomeD(1-3) entering_not_selfloop step(1) step_sel(5)
  by (auto simp: ns_selfloops_L_def ns_selfloops_U_def fst_E_V snd_E_V)

lemmas step_es = es_arr.fixed_univ_map_upd[OF inv_impl(5) step_entering(1)]
    es_arr.fixed_univ_map_upd_invar[OF inv_impl(5) step_entering(1)]
  and step_flow = flow_arr.fixed_univ_map_upd_invar[OF inv_impl(1) step_entering(1)]
    flow_upd_ex[OF inv_impl(1) step_entering(1)]

lemma step_paths:
  "set (if in_U then p1 else p2) \<subseteq> \<V> - {r}" "set (if in_U then p2 else p1) \<subseteq> \<V> - {r}"
  "distinct (if in_U then p1 else p2)" "distinct (if in_U then p2 else p1)"
  "set (if in_U then p1 else p2) \<inter> set (if in_U then p2 else p1) = {}"
  using step_verts step_walks(1,4)
  by auto

lemma step_path_edges:
  "\<forall>w\<in>set p1. par_edge s w \<in> \<E>" "\<forall>w\<in>set p2. par_edge s w \<in> \<E>"
  "\<forall>w\<in>set (if in_U then p1 else p2). par_edge s w \<in> \<E>"
    "\<forall>w\<in>set (if in_U then p2 else p1). par_edge s w \<in> \<E>"
  using step_verts
  by (auto intro!: inv_tree_edge)

lemmas step_fold = fold_flow_upd_ex[OF _ step_path_edges(1)] fold_flow_upd_ex[OF _ step_path_edges(2)]
  fold_flow_upd_invar[OF _ step_path_edges(1)] fold_flow_upd_invar[OF _ step_path_edges(2)]
lemma step_off_tree: "a \<in> ns_L_of s \<union> ns_U_of s \<Longrightarrow> a \<notin> ns_tree_edges s"
  using inv_partition(2,3)
  by blast

lemma step_par_edge_ne: "w \<in> \<V> - {r} \<Longrightarrow> par_edge s w \<noteq> e"
  using step_entering(2)
  by (auto simp: par_edge_def)

lemma step_entering_flow:
  "if in_U then \<u> e = ereal (h (flow_lookup (current_flow s) e)) else flow_lookup (current_flow s) e = 0"
  using inv_flow_fits step_entering(4)
  by (auto simp: flow_fits_spanning_tree_partition_def)

lemma step_reduced_cost: "if in_U then 0 < reduced_cost (potentials s) e else reduced_cost (potentials s) e < 0"
  using step_sel(4)
  by (simp add: entering_edge_def)

subsubsection \<open>The augmentation along the fundamental circuit\<close>

text \<open>For @{term \<open>\<delta> > 0\<close>} the flow produced by @{const augment_flow} is a
      @{term \<delta>}-scaled unit circulation around the fundamental circuit: every balance is
      unchanged, and every circuit edge is pushed by at most its own residual, so the flow stays a @{term
      b}-flow. Its cost changes by the entering edge's reduced cost times the signed amount pushed along
      @{term e}.\<close>

lemma augment_flow_flow_invar: "flow_invar (augment_flow s e in_U \<delta> p1 p2)"
  using inv_impl(1) step_entering(1) step_path_edges(3,4)
  by (simp add: augment_flow_def Let_def fold_flow_upd_invar flow_arr.fixed_univ_map_upd_invar)

lemma augment_flow_ex: "ex (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) v = ex
  (h \<circ> flow_lookup (current_flow s)) v"
proof(cases "\<delta> \<le> 0")
  case False
  obtain a p3 where w: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r"
      "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r"
      "distinct (p1 @ a # p3)" "distinct (p2 @ a # p3)"
    using step_walks(1)
    by blast
  note ex = step_fold step_flow up_sum_h down_sum_h
  show ?thesis
    using False w step_verts
    by (cases in_U; simp only: augment_flow_def Let_def if_True if_False ex) (simp_all add: algebra_simps)
qed (simp add: augment_flow_def)

lemmas augment_flow_val = augment_flow_lookup_char[OF inv_impl(1) _ step_entering(1) step_path_edges(3,4)]

lemma augment_flow_nontree:
  "\<lbrakk>0 \<le> \<delta>; a \<notin> ns_tree_edges s\<rbrakk> \<Longrightarrow> flow_lookup
    (augment_flow s e in_U \<delta> p1 p2) a
     = flow_lookup (current_flow s) a + (if a = e then (if in_U then - \<delta> else \<delta>) else 0)"
  using step_paths(1,2)
  by (simp add: augment_flow_val sum_par_vanish)

lemma augment_flow_off_tree:
  "\<lbrakk>0 \<le> \<delta>; a \<notin> ns_tree_edges s; a \<noteq> e\<rbrakk>
   \<Longrightarrow> flow_lookup (augment_flow s e in_U \<delta> p1 p2) a = flow_lookup (current_flow s) a"
  by (simp add: augment_flow_nontree)

lemma augment_flow_entering:
  "0 \<le> \<delta> \<Longrightarrow>
   flow_lookup (augment_flow s e in_U \<delta> p1 p2) e = flow_lookup (current_flow s) e +
     (if in_U then - \<delta> else \<delta>)"
  by (simp add: augment_flow_nontree step_entering(2))

lemma augment_flow_tree_val:
  "\<lbrakk>0 \<le> \<delta>; w \<in> \<V> - {r}\<rbrakk> \<Longrightarrow> flow_lookup
    (augment_flow s e in_U \<delta> p1 p2) (par_edge s w)
   = flow_lookup (current_flow s) (par_edge s w)
     + (if w \<in> set (if in_U then p1 else p2) then (if par_up s w then \<delta> else - \<delta>) else 0)
     + (if w \<in> set (if in_U then p2 else p1) then (if par_up s w then - \<delta> else \<delta>) else 0)"
  using step_paths
  by (simp add: augment_flow_val step_par_edge_ne par_sum_pick)

lemma augment_flow_isuflow:
  assumes "bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus)" "\<delta> \<noteq> - 1"
  shows "isuflow (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2))"
proof-
  note d = bottleneck_delta_bounds[OF step assms]
  have bu: "0 \<le> flow_lookup (current_flow s) a \<and> ereal (h (flow_lookup (current_flow s) a)) \<le> \<u> a" if
    "a \<in> \<E>" for a
    using inv_bflow that
    by (simp add: isbflow_def isuflow_def)
  have B: "0 \<le> flow_lookup (augment_flow s e in_U \<delta> p1 p2) a
      \<and> ereal (h (flow_lookup (augment_flow s e in_U \<delta> p1 p2) a)) \<le> \<u> a" if "a \<in> \<E>" for a
  proof(cases "a \<in> ns_tree_edges s")
    case True
    then obtain w where w: "w \<in> \<V> - {r}" "a = par_edge s w"
      by (auto simp: par_edge_def)
    show ?thesis
    proof(cases "w \<in> set (if in_U then p1 else p2) \<union> set (if in_U then p2 else p1)")
      case True
      have "0 \<le> flow_lookup (current_flow s) a +
        (if par_up s w = (w \<in> set (if in_U then p1 else p2)) then \<delta> else - \<delta>)
          \<and> ereal (h (flow_lookup (current_flow s) a +
            (if par_up s w = (w \<in> set (if in_U then p1 else p2)) then \<delta> else - \<delta>)))
            \<le> \<u> a"
        by (rule push_bound)
           (use that True d(1) d(2,3)[of w] w(2) res_bwd_nonneg[of a] in \<open>auto simp: res_up_def res_down_def\<close>)
      then show ?thesis
        using True step_paths(5) d(1) w
        by (auto simp: augment_flow_tree_val split: if_splits)
    qed (use bu that d(1) w in \<open>simp add: augment_flow_tree_val\<close>)
  next
    case False
    have "0 \<le> flow_lookup (current_flow s) e + (if \<not> in_U then \<delta> else - \<delta>)
        \<and> ereal (h (flow_lookup (current_flow s) e + (if \<not> in_U then \<delta> else - \<delta>))) \<le> \<u>
          e"
      by (rule push_bound) (use step_entering(1) d res_bwd_nonneg[of e] in auto)
    then show ?thesis
      using bu that d(1) False
      by (simp add: augment_flow_nontree split: if_splits)
  qed
  show ?thesis
    by (rule isuflowI) (simp_all add: B)
qed

lemma augment_flow_bflow:
  "\<lbrakk>bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus); \<delta> \<noteq> - 1\<rbrakk>
   \<Longrightarrow> (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) is b flow"
  by (drule (1) augment_flow_isuflow)
     (use augment_flow_ex inv_bflow in
       \<open>auto intro!: isbflowI elim!: isbflowE\<close>)

lemma augment_flow_cost:
  assumes "bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus)" "\<delta> \<noteq> - 1"
  shows "\<C> (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2))
       = ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e"
proof-
  obtain a0 p3 where w: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a0 # p3) r"
      "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a0 # p3) r"
      "distinct (p1 @ a0 # p3)" "distinct (p2 @ a0 # p3)"
    using step_walks(1)
    by blast
  from step assms have "0 \<le> \<delta>"
    by (rule bottleneck_delta_bounds(1))
  moreover have "(if c then x else (0::real)) * y = (if c then x * y else 0)" for c x y
    by simp
  ultimately have "\<C> (h \<circ> flow_lookup (augment_flow s e in_U \<delta> p1 p2)) = ns_flow_cost s + h
    (if in_U then - \<delta> else \<delta>) * \<c> e
      + (\<Sum>w\<leftarrow>(if in_U then p1 else p2). \<c> (par_edge s w) * h
        (if par_up s w then \<delta> else - \<delta>))
      + (\<Sum>w\<leftarrow>(if in_U then p2 else p1). \<c> (par_edge s w) * h
        (if par_up s w then - \<delta> else \<delta>))"
    using step_entering(1) finite_E step_path_edges(1,2)
    by (simp only: \<C>_def comp_def augment_flow_val)
       (cases in_U; simp add: \<C>_def ns_flow_cost_def h_add h_sum_list h_if0 distrib_right sum.distrib sum_E_par_edge)
  then show ?thesis
    using w step_verts
    by (cases in_U; simp only: if_True if_False up_cost_sum_h down_cost_sum_h)
       (simp_all add: reduced_cost_def algebra_simps)
qed

text \<open>Strict feasibility of an untouched parent edge after the augmentation, given that on the up
      path its residual exceeds @{term \<delta>}.\<close>

lemma augment_flow_strict:
  assumes "0 \<le> \<delta>" "w \<in> \<V> - {r}" "w \<in> set (if in_U then p1 else p2) \<Longrightarrow> res_up s w
    = - 1 \<or> \<delta> < res_up s w"
  shows "if par_up s w then ereal (h (flow_lookup (augment_flow s e in_U \<delta> p1 p2) (par_edge s w))) < \<u>
    (par_edge s w)
         else 0 < flow_lookup (augment_flow s e in_U \<delta> p1 p2) (par_edge s w)"
proof(cases "w \<in> set (if in_U then p1 else p2)")
  case True
  have pE: "par_edge s w \<in> \<E>"
    using assms(2) by (rule inv_tree_edge)
  have "if par_up s w then res_fwd s (par_edge s w) = - 1 \<or> \<delta> < res_fwd s (par_edge s w)
        else \<delta> < res_bwd s (par_edge s w)"
    using assms(3) True pE res_bwd_nonneg[of "par_edge s w"]
    by (auto simp: res_up_def)
  then show ?thesis
    using strict_push[of "par_edge s w" "par_up s w"] pE True step_paths(5) assms(1,2)
    by (cases "par_up s w") (auto simp: augment_flow_tree_val)
next
  case False
  then show ?thesis
    using strict_relax[of w] inv_strict[of w] assms(1,2)
    by (cases "w \<in> set (if in_U then p2 else p1)"; cases "par_up s w") (simp_all add: augment_flow_tree_val)
qed

lemma invar_bflow_augment:
  "\<lbrakk>bottleneck s e in_U p1 p2 = (\<delta>, isf, lv, lfw, lus); \<delta> \<noteq> - 1; current_flow s' =
    augment_flow s e in_U \<delta> p1 p2\<rbrakk>
   \<Longrightarrow> ns_invar_bflow s'"
  by (simp add: ns_invar_bflow_def augment_flow_bflow)

lemma invar_selfloop_augment:
  assumes "0 \<le> \<delta>" "current_flow s' = augment_flow s e in_U \<delta> p1 p2"
  shows "ns_invar_selfloop s'"
proof-
  have "flow_lookup (current_flow s') a = flow_lookup (current_flow s) a" if "fst a = snd a" for a
    using that tree_edge_not_selfloop[of a] step_entering(3)
    by (auto simp: assms(2) intro: augment_flow_off_tree[OF assms(1)])
  then show ?thesis
    using inv_parts(8)
    by (simp add: ns_invar_selfloop_def)
qed


subsubsection \<open>The flip branch\<close>

text \<open>@{const ns_flip} augments the flow along the whole circuit, toggles @{term e} between @{term
      L} and @{term U}, and leaves the tree, the potentials and the parent arrays untouched. The measure
      drops via the flow cost when @{term \<open>\<delta> > 0\<close>} and via the violation count
      otherwise.\<close>

context
  fixes \<delta> v e0fwd up_side
  assumes flip: "bottleneck s e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side)" "\<delta> \<noteq> - 1"
begin

lemma flip_upd:
  "current_flow (ns_flip_upd s) = augment_flow s e in_U \<delta> p1 p2" "potentials (ns_flip_upd s) = potentials s"
  "spanning_tree (ns_flip_upd s) = spanning_tree s" "parent_edge (ns_flip_upd s) = parent_edge s"
  "edge_dir (ns_flip_upd s) = edge_dir s" "edge_sel (ns_flip_upd s) = sel'"
  "edge_state (ns_flip_upd s) = es_upd (edge_state s) e (if in_U then InL else InU)"
  using step flip(1) step_entering(1)
  by (simp_all add: ns_flip_upd_def ns_flip_def Let_def)

lemma flip_tree:
  "par_edge (ns_flip_upd s) = par_edge s" "par_up (ns_flip_upd s) = par_up s" "par_vx (ns_flip_upd s) = par_vx s"
  by (simp_all add: fun_eq_iff par_edge_def par_up_def par_vx_def flip_upd)

lemma flip_LU:
  "ns_L_of (ns_flip_upd s) = (if in_U then insert e (ns_L_of s) else ns_L_of s - {e})"
  "ns_U_of (ns_flip_upd s) = (if in_U then ns_U_of s - {e} else insert e (ns_U_of s))"
  using step_entering(1,3) step_es(1)
  by (auto simp: ns_L_of_def ns_U_of_def flip_upd)

lemma flip_delta: "0 \<le> \<delta>" "(if in_U then res_bwd s e else res_fwd s e) = \<delta>"
  using bottleneck_delta_bounds(1)[OF step flip] flip
  by (auto simp: bottleneck_def Let_def split: prod.splits if_splits)

lemma flip_up_res:
  assumes "w \<in> set (if in_U then p1 else p2)"
  shows "res_up s w = - 1 \<or> \<delta> < res_up s w"
proof-
  obtain mu vu where su: "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    by fastforce
  then have "mu = - 1 \<or> \<delta> < mu"
    using flip
    by (auto simp: bottleneck_def Let_def mininf_def min_def split: prod.splits if_splits)
  then show ?thesis
    using scan_up_min[OF su assms]
    by force
qed

lemma invar_impl_holds_upd_flip[invar_holds_intros]: "ns_invar_impl (ns_flip_upd s)"
  using inv_impl augment_flow_flow_invar step_sel(1)
    step_es(2)
  by (auto intro!: ns_invar_implI simp: flip_upd)

lemma invar_bflow_holds_upd_flip[invar_holds_intros]: "ns_invar_bflow (ns_flip_upd s)"
  using flip flip_upd(1) by (rule invar_bflow_augment)

lemma invar_partition_holds_upd_flip[invar_holds_intros]: "ns_invar_partition (ns_flip_upd s)"
  unfolding ns_invar_partition_def flip_LU flip_upd(4)
  using inv_stp step_entering(4-6) by (rule spanning_tree_partition_flip) simp_all

lemma invar_flow_fits_holds_upd_flip[invar_holds_intros]: "ns_invar_flow_fits (ns_flip_upd s)"
proof-
  have "if in_U then flow_lookup (augment_flow s e in_U \<delta> p1 p2) e = 0
        else ereal (h (flow_lookup (augment_flow s e in_U \<delta> p1 p2) e)) = \<u> e"
    using step_entering_flow flip_delta flip(2) cap_nonneg[of e] cap_finite[of e] step_entering(1)
      augment_flow_entering[of \<delta>]
    by (auto simp: res_bwd_def res_fwd_def Let_def split: if_splits)
  then show ?thesis
    using inv_flow_fits inv_partition(4) step_entering(4) flip_delta(1) augment_flow_nontree[of \<delta>]
    by (auto simp: ns_invar_flow_fits_def flow_fits_spanning_tree_partition_def flip_LU flip_upd step_off_tree
        split: if_splits)
qed

lemma invar_pot_fits_holds_upd_flip[invar_holds_intros]: "ns_invar_pot_fits (ns_flip_upd s)"
  using inv_parts(5)
  by (simp add: ns_invar_pot_fits_def flip_upd)

lemma invar_strict_holds_upd_flip[invar_holds_intros]: "ns_invar_strict (ns_flip_upd s)"
  by (rule ns_invar_strictI) (simp add: flip_tree flip_upd augment_flow_strict flip_delta(1) flip_up_res)

lemma invar_tree_holds_upd_flip[invar_holds_intros]: "ns_invar_tree (ns_flip_upd s)"
  using inv_tree
  by (simp add: ns_invar_tree_def flip_tree flip_upd)

lemma invar_selfloop_holds_upd_flip[invar_holds_intros]: "ns_invar_selfloop (ns_flip_upd s)"
  using flip_delta(1) flip_upd(1) by (rule invar_selfloop_augment)

lemma ns_less_upd_flip: "ns_less (ns_flip_upd s) s"
proof-
  have rc: "reduced_cost (potentials (ns_flip_upd s)) = reduced_cost (potentials s)"
    and pots: "ns_pot_sum (ns_flip_upd s) = ns_pot_sum s"
    and cost: "ns_flow_cost (ns_flip_upd s) = ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) *
      reduced_cost (potentials s) e"
    using flip augment_flow_cost
    by (simp_all add: flip_upd ns_pot_sum_def ns_flow_cost_def)
  have "ns_L_of s \<union> ns_U_of s \<subseteq> \<E>"
    using inv_partition(1)
    by blast
  then have fin: "finite (ns_L_of s)" "finite (ns_U_of s)"
    by (auto intro: finite_subset[OF _ finite_E])
  show ?thesis
  proof(cases "\<delta> = 0")
    case True
    have viol: "ns_violation (ns_flip_upd s) < ns_violation s"
    proof(cases in_U)
      case True
      have "{y \<in> insert e (ns_L_of s). reduced_cost (potentials s) y < 0} =
        {y \<in> ns_L_of s. reduced_cost (potentials s) y < 0}"
        using step_reduced_cost True
        by auto
      then show ?thesis
        using card_filter_remove_less[of _ e "\<lambda>y. 0 < reduced_cost (potentials s) y"] fin step_entering(4)
          step_reduced_cost True
        by (simp add: ns_violation_def rc flip_LU)
    next
      case False
      have "{y \<in> insert e (ns_U_of s). 0 < reduced_cost (potentials s) y} =
        {y \<in> ns_U_of s. 0 < reduced_cost (potentials s) y}"
        using step_reduced_cost False
        by auto
      then show ?thesis
        using card_filter_remove_less[of _ e "\<lambda>y. reduced_cost (potentials s) y < 0"] fin step_entering(4)
          step_reduced_cost False
        by (simp add: ns_violation_def rc flip_LU)
    qed
    have "ns_flow_cost (ns_flip_upd s) = ns_flow_cost s"
      using cost True
      by simp
    then have "possible_trees (ns_flip_upd s) = possible_trees s"
      by (simp only: possible_trees_def pots)
    then show ?thesis
      using viol
      by (simp add: ns_less_def)
  next
    case False
    have "(if in_U then - h \<delta> else h \<delta>) * reduced_cost (potentials s) e < 0"
      using step_reduced_cost flip_delta(1) False
      by (cases in_U) (auto simp: mult_less_0_iff)
    then have "ns_flow_cost (ns_flip_upd s) < ns_flow_cost s"
      using cost
      by simp
    then show ?thesis
      using possible_trees_shrink[of "ns_flip_upd s"]
      by (simp add: ns_less_def)
  qed
qed

end

subsubsection \<open>The pivot branch\<close>

text \<open>The pivot exchanges the leaving tree edge @{term \<open>par_edge s v\<close>} for @{term e},
      shifts the potentials of the subtree hanging below @{term v} by the entering reduced cost, and
      re-parents the spine from the far endpoint of @{term e} up to @{term v}. Strong feasibility on the
      spine rests on the scan tie-break lemmas above.\<close>

context
  fixes \<delta> v e0fwd up_side
  assumes piv: "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" "\<delta> \<noteq> - 1"
begin

abbreviation (input) "pivot_spine \<equiv> if in_U = up_side then p1 else p2"
abbreviation (input) "pivot_subtree \<equiv> {x. \<exists>p. walk_betw (abstract_arborescense (spanning_tree s)) x p r
  \<and> distinct p \<and> v \<in> set p}"
abbreviation (input) "pivot_shift \<equiv> if in_U \<noteq> up_side then rcost_abstract \<gamma> else - rcost_abstract
  \<gamma>"

lemma pivot_facts:
  "v \<in> \<V> - {r}" "par_edge s v \<in> ns_tree_edges s" "0 \<le> \<delta>"
    "up_side \<Longrightarrow> 0 < \<delta>" "v \<in> set pivot_spine"
  using bottleneck_pivot_facts(1,2,3,5,6)[OF step piv(1)]
  by auto

lemma pivot_scan:
  "up_side \<Longrightarrow> scan_up s (if in_U then p1 else p2) = (\<delta>, v)" "up_side \<Longrightarrow> e0fwd = par_up s v"
  "\<not> up_side \<Longrightarrow> scan_down s (if in_U then p2 else p1) = (\<delta>, v)"
  "\<not> up_side \<Longrightarrow> e0fwd = (\<not> par_up s v)"
  using piv(1)
  by (cases "scan_up s (if in_U then p1 else p2)"; auto dest: bottleneck_pivot_up bottleneck_pivot_down)+

lemma pivot_scan_down:
  "\<lbrakk>\<not> up_side; scan_up s (if in_U then p1 else p2) = (mu, vu)\<rbrakk>
   \<Longrightarrow> scan_down s (if in_U then p2 else p1) = (\<delta>, v) \<and> e0fwd = (\<not> par_up s v) \<and>
     (mu = - 1 \<or> \<delta> < mu)
     \<and> ((if in_U then res_bwd s e else res_fwd s e) = - 1 \<or> \<delta> <
       (if in_U then res_bwd s e else res_fwd s e))"
  by (rule bottleneck_pivot_down) (use piv(1) in simp_all)

lemma pivot_leaving:
  "par_edge s v \<in> \<E>" "par_edge s v \<noteq> e" "fst (par_edge s v) \<noteq> snd (par_edge s v)"
  "par_edge s v \<notin> ns_L_of s \<union> ns_U_of s"
  using inv_tree_edge[of v] tree_edge_not_selfloop[of "par_edge s v"] pivot_facts(1,2) step_entering(2)
    step_off_tree
  by auto

lemma pivot_spine:
  "distinct pivot_spine" "set pivot_spine \<subseteq> \<V> - {r}"
  "pivot_spine = (if up_side then (if in_U then p1 else p2) else (if in_U then p2 else p1))"
  using step_paths
  by (auto split: if_splits)

lemma pivot_spine_hd: "hd pivot_spine = (if in_U = up_side then fst e else snd e)"
proof-
  obtain a p3 where "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r"
    "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r"
    using step_walks(1)
    by blast
  then have "p1 \<noteq> [] \<Longrightarrow> hd p1 = fst e" "p2 \<noteq> [] \<Longrightarrow> hd p2 = snd e"
    by (simp_all add: walk_betw_def)
  moreover have "pivot_spine \<noteq> []"
    using pivot_facts(5)
    by auto
  ultimately show ?thesis
    by (cases "in_U = up_side") simp_all
qed

lemma pivot_spine_succ: "Suc i < length pivot_spine \<Longrightarrow> par_vx s (pivot_spine ! i) = pivot_spine ! Suc i"
  using step_walks(2,3)
  by (auto split: if_splits)

lemma pivot_spine_cases:
  obtains (off) "w \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) pivot_spine))" | (hd)
    "w = hd pivot_spine"
    | (nth) i where "Suc i < length pivot_spine" "pivot_spine ! Suc i = w"
      "pivot_spine ! i \<in> set (takeWhile (\<lambda>y. y \<noteq> v) pivot_spine)"
  using takeWhile_spine_pred[OF pivot_facts(5)]
  by blast

text \<open>\<^bold>\<open>Basis exchange.\<close> Swapping the leaving edge for @{term e} keeps a valid
      arborescence and realises the exchange on the undirected tree.\<close>

lemma swap_edge_pivot:
  "arborescense_invar
     (swap_edge (spanning_tree s) v (if in_U = up_side then fst e else snd e)
       (if in_U = up_side then snd e else fst e))"
  "abstract_arborescense
     (swap_edge (spanning_tree s) v (if in_U = up_side then fst e else snd e)
       (if in_U = up_side then snd e else fst e))
   = abstract_arborescense (spanning_tree s) - {{fst (par_edge s v), snd (par_edge s v)}} \<union> {{fst e, snd e}}"
proof-
  let ?u = "if in_U = up_side then fst e else snd e" and ?w = "if in_U = up_side then snd e else fst e"
  obtain a p3 where w: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r"
      "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r"
      "distinct (p1 @ a # p3)" "distinct (p2 @ a # p3)"
    using step_walks(1)
    by blast
  then have wP: "walk_betw (abstract_arborescense (spanning_tree s)) ?u (pivot_spine @ a # p3) r"
    "distinct (pivot_spine @ a # p3)"
      by simp_all
  obtain j where j: "j < length pivot_spine" "pivot_spine ! j = v"
    using pivot_facts(5)
    by (auto simp: in_set_conv_nth)
  then have Pa: "(pivot_spine @ [a]) ! j = v" "Suc j < length (pivot_spine @ [a])"
    by (simp_all add: nth_append)
  have "(pivot_spine @ [a]) ! Suc j = par_vx s v"
    using walk_succ_is_par_vx[of ?u "pivot_spine @ a # p3" j] wP j pivot_facts(1)
    by (cases "Suc j = length pivot_spine") (simp_all add: nth_append)
  then have edge: "(v, par_vx s v) \<in> set (edges_of_vwalk (pivot_spine @ [a]))"
    using edges_of_vwalk_index[of j "pivot_spine @ [a]"] nth_mem[of j "edges_of_vwalk (pivot_spine @ [a])"] Pa
    by (simp add: edges_of_vwalk_length)
  have GP: "get_path_pair (spanning_tree s) ?u ?w = (pivot_spine, if in_U = up_side then p2 else p1)"
    using step(2) get_path_pair(2)[of "spanning_tree s" "fst e" "snd e" p1 p2] inv_impl(7) step_entering(3,8,9)
    by simp
  have u: "?u \<noteq> ?w" "?u \<in> \<V>" "?w \<in> \<V>"
    using step_entering(3,8,9) by auto
  show "arborescense_invar (swap_edge (spanning_tree s) v ?u ?w)"
    using inv_impl(7) GP u(1) wP edge u(2,3) by (rule swap_edge(1))
  have "abstract_arborescense (swap_edge (spanning_tree s) v ?u ?w)
      = abstract_arborescense (spanning_tree s) - {{v, par_vx s v}} \<union> {{?u, ?w}}"
    using inv_impl(7) GP u(1) wP edge u(2,3) by (rule swap_edge(2))
  then show "abstract_arborescense (swap_edge (spanning_tree s) v ?u ?w)
      = abstract_arborescense (spanning_tree s) - {{fst (par_edge s v), snd (par_edge s v)}} \<union> {{fst e, snd e}}"
    using par_edge_set[of v] pivot_facts(1)
    by (simp add: insert_commute)
qed

lemma pivot_new_tree:
  "(\<lambda>a. {fst a, snd a}) ` (ns_tree_edges s - {par_edge s v} \<union> {e})
   = abstract_arborescense
       (swap_edge (spanning_tree s) v (if in_U = up_side then fst e else snd e)
         (if in_U = up_side then snd e else fst e))"
  "finite (ns_tree_edges s - {par_edge s v} \<union> {e})"
    "card (ns_tree_edges s - {par_edge s v} \<union> {e}) = card \<V> - 1"
proof-
  have "inj_on (\<lambda>a. {fst a, snd a}) (ns_tree_edges s)"
    using inv_partition(7) unfolding inj_on_def
    by blast
  then have "(\<lambda>a. {fst a, snd a}) ` (ns_tree_edges s - {par_edge s v})
      = (\<lambda>a. {fst a, snd a}) ` ns_tree_edges s - {{fst (par_edge s v), snd (par_edge s v)}}"
    using inj_on_image_set_diff[OF _ Diff_subset, of _ "ns_tree_edges s" "{par_edge s v}"] pivot_facts(2)
    by simp
  then show "(\<lambda>a. {fst a, snd a}) ` (ns_tree_edges s - {par_edge s v} \<union> {e})
   = abstract_arborescense
       (swap_edge (spanning_tree s) v (if in_U = up_side then fst e else snd e)
         (if in_U = up_side then snd e else fst e))"
    using ns_invar_tree_edgesD[OF inv_tree] swap_edge_pivot(2)
    by (simp add: image_Un)
  show "finite (ns_tree_edges s - {par_edge s v} \<union> {e})"
    by (simp add: \<V>_finite)
  have "card (ns_tree_edges s - {par_edge s v} \<union> {e}) = Suc (card (ns_tree_edges s - {par_edge s v}))"
    using step_entering(2)
    by (simp add: \<V>_finite)
  also have "\<dots> = card \<V> - 1"
    using card_Suc_Diff1[OF _ pivot_facts(2)] card_tree_edges
    by (simp add: \<V>_finite)
  finally show "card (ns_tree_edges s - {par_edge s v} \<union> {e}) = card \<V> - 1" .
qed

lemma pivot_subtree:
  "(fst e \<in> pivot_subtree) = (in_U = up_side)" "(snd e \<in> pivot_subtree) = (in_U \<noteq> up_side)"
  "r \<notin> pivot_subtree" "pivot_subtree \<subseteq> \<V>"
proof-
  obtain a p3 where w: "walk_betw (abstract_arborescense (spanning_tree s)) (fst e) (p1 @ a # p3) r"
      "walk_betw (abstract_arborescense (spanning_tree s)) (snd e) (p2 @ a # p3) r"
      "distinct (p1 @ a # p3)" "distinct (p2 @ a # p3)" "set p1 \<inter> set p2 = {}"
    using step_walks(1)
    by blast
  then show "(fst e \<in> pivot_subtree) = (in_U = up_side)" "(snd e \<in> pivot_subtree) = (in_U \<noteq> up_side)"
    using S_via_walk[OF w(1,3)] S_via_walk[OF w(2,4)] pivot_facts(5)
    by (cases "in_U = up_side"; auto)+
  have "r \<in> Vs (abstract_arborescense (spanning_tree s))"
    using general(1,4) inv_impl(7)
    by simp
  then show "r \<notin> pivot_subtree"
    using S_via_walk[of r "[r]"] walk_reflexive[of r] pivot_facts(1)
    by simp
  show "pivot_subtree \<subseteq> \<V>"
    by (rule shift_pot_lookup(3)) (use pivot_facts(1) in simp)
qed

text \<open>The shifted explicit potential fits the exchanged tree: tree edges other than the leaving one
      do not cross the cut, and the entering edge crosses it with reduced cost @{term \<gamma>}.\<close>

lemma expl_fits:
  "potential_fits_spanning_tree_partition r (ns_tree_edges s - {par_edge s v} \<union> {e})
     (\<lambda>u. ns_pot_of s u + (if u \<in> pivot_subtree then pivot_shift else 0))"
  unfolding potential_fits_spanning_tree_partition_def
proof(intro conjI ballI)
  note pf = inv_pot_fits[unfolded potential_fits_spanning_tree_partition_def]
  show "ns_pot_of s r + (if r \<in> pivot_subtree then pivot_shift else 0) = 0"
    unfolding if_not_P[OF pivot_subtree(3)]
    using pf
    by simp
  fix t assume "t \<in> ns_tree_edges s - {par_edge s v} \<union> {e}"
  then consider "t = e" | w where "w \<in> \<V> - {r}" "w \<noteq> v" "t = par_edge s w"
    by (auto simp: par_edge_def)
  then show "\<c> t + (ns_pot_of s (fst t) + (if fst t \<in> pivot_subtree then pivot_shift else 0))
      - (ns_pot_of s (snd t) + (if snd t \<in> pivot_subtree then pivot_shift else 0)) = 0"
  proof cases
    case 1
    show ?thesis unfolding 1 pivot_subtree(1,2)
      using step_sel(3)
      by (cases "in_U = up_side") (simp_all add: reduced_cost_def)
  next
    case (2 w)
    then have "{fst t, snd t} = {w, par_vx s w}"
      using par_edge_set[OF 2(1)]
      by simp
    then have "(fst t \<in> pivot_subtree) = (snd t \<in> pivot_subtree)"
      using cut_4c[OF 2(1,2)]
      by (auto simp only: doubleton_eq_iff)
    moreover have "\<c> t + ns_pot_of s (fst t) - ns_pot_of s (snd t) = 0"
      using pf 2
      by (auto simp: par_edge_def)
    ultimately show ?thesis
      by simp
  qed
qed

lemma shift_good:
  assumes "u \<in> pivot_subtree"
  shows "good_pot_val (if in_U \<noteq> up_side then ns_pot_of s u + rcost_abstract \<gamma> else ns_pot_of s u -
    rcost_abstract \<gamma>)"
proof-
  have "ns_tree_edges s - {par_edge s v} \<union> {e} \<subseteq> \<E>"
    using inv_partition(1) step_entering(1)
    by blast
  then have "good_pot_val ((\<lambda>u. ns_pot_of s u + (if u \<in> pivot_subtree then pivot_shift else 0)) u)"
    by (rule potential_fits_imp_good[OF _ arborescense_tree_edges(2,1,4)[OF swap_edge_pivot(1) pivot_new_tree]
        expl_fits subsetD[OF pivot_subtree(4) assms]])
  then show ?thesis
    using assms
    by (cases "in_U = up_side") simp_all
qed

lemma shift_pot_props:
  "pot_valid (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side))"
  "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side))
     = (\<lambda>u. ns_pot_of s u + (if u \<in> pivot_subtree then pivot_shift else 0))"
  "potential_fits_spanning_tree_partition r (ns_tree_edges s - {par_edge s v} \<union> {e})
     (abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)))"
  "(\<Sum>u\<in>\<V>. abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)) u)
     = ns_pot_sum s + pivot_shift * card pivot_subtree"
proof-
  note sh = shift_pot_abstract[OF _ step_sel(2) shift_good]
  show "pot_valid (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side))"
    using sh(2) pivot_facts(1)
    by simp
  show A: "abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side))
     = (\<lambda>u. ns_pot_of s u + (if u \<in> pivot_subtree then pivot_shift else 0))"
    using sh(1) pivot_facts(1)
    by (auto simp: fun_eq_iff)
  show "potential_fits_spanning_tree_partition r (ns_tree_edges s - {par_edge s v} \<union> {e})
     (abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)))"
    unfolding A
    by (rule expl_fits)
  show "(\<Sum>u\<in>\<V>. abstract_pot (shift_pot (spanning_tree s) v (potentials s) \<gamma>
    (in_U \<noteq> up_side)) u)
     = ns_pot_sum s + pivot_shift * card pivot_subtree"
    unfolding A ns_pot_sum_def sum.distrib
    by (simp only: sum.inter_restrict[OF \<V>_finite, symmetric] Int_absorb1[OF pivot_subtree(4)] sum_constant
        mult.commute)
qed

text \<open>The flow on the leaving edge is pushed by exactly its residual, in its own direction.\<close>

lemma pivot_leaving_flow:
  "flow_lookup (augment_flow s e in_U \<delta> p1 p2) (par_edge s v)
     = flow_lookup (current_flow s) (par_edge s v) + (if e0fwd then \<delta> else - \<delta>)
   \<and> (if e0fwd then res_fwd s (par_edge s v) else res_bwd s (par_edge s v)) = \<delta>"
proof(cases up_side)
  case True
  then have "v \<in> set (if in_U then p1 else p2)" "res_up s v = \<delta>"
    using pivot_scan(1) piv(2) by (simp_all add: scan_up_snd_mem scan_up_val_at)
  then show ?thesis
    using True pivot_scan(2) step_paths(5) pivot_facts(3,1) by (auto simp: augment_flow_tree_val res_up_def)
next
  case False
  then have "v \<in> set (if in_U then p2 else p1)" "res_down s v = \<delta>"
    using pivot_scan(3) piv(2) by (simp_all add: scan_down_snd_mem scan_down_val_at)
  then show ?thesis
    using False pivot_scan(4) step_paths(5) pivot_facts(3,1) by (auto simp: augment_flow_tree_val res_down_def)
qed

lemma pivot_up_res:
  assumes "w \<in> set (if in_U then p1 else p2)" "w \<notin> insert v
    (set (takeWhile (\<lambda>y. y \<noteq> v) pivot_spine))"
  shows "res_up s w = - 1 \<or> \<delta> < res_up s w"
proof(cases up_side)
  case True
  then show ?thesis
    using pivot_scan(1) scan_up_after[where m = \<delta> and v = v] piv(2) step_paths(3) assms
    by auto
next
  case False
  obtain mu vu where "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    by (cases "scan_up s (if in_U then p1 else p2)")
  then show ?thesis
    using False pivot_scan_down[of mu vu] scan_up_min[where m = mu] assms(1)
    by force
qed

lemma pivot_entering_strict:
  "if hd pivot_spine = fst e then ereal (h (flow_lookup (augment_flow s e in_U \<delta> p1 p2) e)) < \<u> e
   else 0 < flow_lookup (augment_flow s e in_U \<delta> p1 p2) e"
proof(cases up_side)
  case True
  then show ?thesis
    using pivot_facts(3,4) step_entering(3) step_entering_flow augment_flow_entering[of \<delta>] pivot_spine_hd
    by (cases in_U) simp_all
next
  case False
  obtain mu vu where "scan_up s (if in_U then p1 else p2) = (mu, vu)"
    by (cases "scan_up s (if in_U then p1 else p2)")
  then have "if \<not> in_U then res_fwd s e = - 1 \<or> \<delta> < res_fwd s e else \<delta> < res_bwd s e"
    using False pivot_scan_down[of mu vu] res_bwd_nonneg[of e] step_entering(1)
    by (cases in_U) force+
  then show ?thesis
    using strict_push[of e "\<not> in_U"] False step_entering(1,3) pivot_facts(3) augment_flow_entering[of \<delta>]
      pivot_spine_hd
    by (cases in_U) auto
qed

lemma pivot_spine_strict:
  assumes "w \<in> set (takeWhile (\<lambda>y. y \<noteq> v) pivot_spine)"
  shows "if \<not> par_up s w then ereal (h (flow_lookup (augment_flow s e in_U \<delta> p1 p2) (par_edge s w))) <
    \<u> (par_edge s w)
         else 0 < flow_lookup (augment_flow s e in_U \<delta> p1 p2) (par_edge s w)"
proof-
  have wP: "w \<in> set pivot_spine"
    using assms
    by (auto dest: set_takeWhileD)
  then have wV: "w \<in> \<V> - {r}" "par_edge s w \<in> \<E>"
    using pivot_spine(2) inv_tree_edge[of w]
    by auto
  have "if \<not> par_up s w then res_fwd s (par_edge s w) = - 1 \<or> (if up_side then - \<delta> else \<delta>) <
    res_fwd s (par_edge s w)
        else (if up_side then - \<delta> else \<delta>) < res_bwd s (par_edge s w)"
  proof(cases up_side)
    case True
    then show ?thesis
      using pivot_facts(4) wV(2) res_fwd_sign[of "par_edge s w"] res_bwd_nonneg[of "par_edge s w"]
      by auto
  next
    case False
    have "w \<in> set (takeWhile (\<lambda>y. y \<noteq> v) (if in_U then p2 else p1))"
      using assms False
      by (cases in_U) simp_all
    then have "res_down s w = - 1 \<or> \<delta> < res_down s w"
      using False pivot_scan(3) piv(2) step_paths(4) scan_down_before[where m = \<delta> and v = v]
      by blast
    then show ?thesis
      using False wV(2) res_bwd_nonneg[of "par_edge s w"]
      by (auto simp: res_down_def)
  qed
  then show ?thesis
    using strict_push[of "par_edge s w" "\<not> par_up s w" "if up_side then - \<delta> else \<delta>"] wP wV pivot_spine(3)
      step_paths(5) pivot_facts(3)
    by (cases up_side; cases "par_up s w") (auto simp: augment_flow_tree_val)
qed

text \<open>\<^bold>\<open>Re-parenting.\<close> With the arrays returned by @{const reparent} fixed, the
      pivot state is determined. Off the spine the parent data is unchanged, the far endpoint of @{term
      e} gets @{term e}, and every later spine vertex inherits its predecessor's old edge, reversed. So
      the new tree edges are exactly the old ones with the leaving edge exchanged for @{term e}.\<close>

context
  fixes parr darr
  assumes rp: "reparent s e pivot_spine v = (parr, darr)"
begin

lemma pivot_upd:
  "current_flow (ns_pivot_upd s) = augment_flow s e in_U \<delta> p1 p2"
  "potentials (ns_pivot_upd s) = shift_pot (spanning_tree s) v (potentials s) \<gamma> (in_U \<noteq> up_side)"
  "spanning_tree (ns_pivot_upd s)
     = swap_edge (spanning_tree s) v (if in_U = up_side then fst e else snd e)
       (if in_U = up_side then snd e else fst e)"
  "parent_edge (ns_pivot_upd s) = parr" "edge_dir (ns_pivot_upd s) = darr" "edge_sel (ns_pivot_upd s) = sel'"
  "edge_state (ns_pivot_upd s) = es_upd (es_upd (edge_state s) e InTree) (par_edge s v) (if e0fwd then InU else InL)"
  using step piv rp step_entering(1)
  by (simp_all add: ns_pivot_upd_def ns_pivot_def Let_def)

lemma pivot_LU:
  "ns_L_of (ns_pivot_upd s) = ns_L_of s - {e} \<union> (if e0fwd then {} else {par_edge s v})"
  "ns_U_of (ns_pivot_upd s) = ns_U_of s - {e} \<union> (if e0fwd then {par_edge s v} else {})"
  using pivot_leaving step_entering(1) step_es
  by (auto simp: ns_L_of_def ns_U_of_def pivot_upd es_arr.fixed_univ_map_upd)

lemma pivot_arrays: "parent_invar parr" "dir_invar darr"
  using reparent_walk_invar[where pd = "(parent_edge s, edge_dir s)" and s = s and e = e and v = v
      and ws = pivot_spine and first = True and pe = e and pup = False] pivot_spine(2) inv_impl(3,4) rp
  by (simp_all add: reparent_def)

lemmas pivot_reparent_walk = reparent_walk_full[where ws = pivot_spine and ?pp0.0 = "parent_edge s"
    and ?dd0.0 = "edge_dir s" and first = True and pe = e and pup = False and s = s and e = e,
    OF pivot_spine(1) pivot_facts(5) inv_impl(3,4) pivot_spine(2), folded reparent_def, unfolded rp prod.case]

lemma pivot_reparent:
  "x \<notin> insert v (set (takeWhile (\<lambda>y. y \<noteq> v) pivot_spine))
   \<Longrightarrow> par_edge (ns_pivot_upd s) x = par_edge s x \<and> par_up (ns_pivot_upd s) x = par_up s x"
  "par_edge (ns_pivot_upd s) (hd pivot_spine) = e \<and> par_up (ns_pivot_upd s) (hd pivot_spine) =
    (hd pivot_spine = fst e)"
  "\<lbrakk>Suc i < length pivot_spine; pivot_spine ! i \<in> set
    (takeWhile (\<lambda>y. y \<noteq> v) pivot_spine)\<rbrakk>
   \<Longrightarrow> par_edge (ns_pivot_upd s) (pivot_spine ! Suc i) = par_edge s (pivot_spine ! i)
     \<and> par_up (ns_pivot_upd s) (pivot_spine ! Suc i) = (\<not> par_up s (pivot_spine ! i))"
  using pivot_reparent_walk step_entering(1)
  by (auto simp: par_edge_def par_up_def pivot_upd)

lemma pivot_tree_edges: "parent_lookup parr ` (\<V> - {r}) = ns_tree_edges s - {par_edge s v} \<union> {e}"
proof(intro equalityI subsetI)
  fix t assume "t \<in> parent_lookup parr ` (\<V> - {r})"
  then obtain w where w: "w \<in> \<V> - {r}" "t = parent_lookup parr w"
    by blast
  show "t \<in> ns_tree_edges s - {par_edge s v} \<union> {e}"
  proof(cases w rule: pivot_spine_cases)
    case off
    then show ?thesis
      using w pivot_reparent(1) par_edge_inj[of w v] pivot_facts(1)
      by (auto simp: par_edge_def pivot_upd)
  next
    case (nth i)
    have "pivot_spine ! i \<in> \<V> - {r}" "pivot_spine ! i \<noteq> v"
      using nth(3) pivot_spine(2)
      by (auto dest: set_takeWhileD)
    then show ?thesis
      using w nth pivot_reparent(3)[of i] par_edge_inj[of "pivot_spine ! i" v] pivot_facts(1)
      by (auto simp: par_edge_def pivot_upd)
  qed (use w pivot_reparent(2) in \<open>auto simp: par_edge_def pivot_upd\<close>)
next
  fix t assume "t \<in> ns_tree_edges s - {par_edge s v} \<union> {e}"
  then consider "t = e" | w where "w \<in> \<V> - {r}" "w \<noteq> v" "t = par_edge s w"
    by (auto simp: par_edge_def)
  then show "t \<in> parent_lookup parr ` (\<V> - {r})"
  proof cases
    case 1
    have "hd pivot_spine \<in> \<V> - {r}"
      using pivot_facts(5) pivot_spine(2)
      by (cases pivot_spine) auto
    then show ?thesis
      using 1 pivot_reparent(2)
      by (auto simp: par_edge_def pivot_upd)
  next
    case (2 w)
    show ?thesis
    proof(cases "w \<in> set (takeWhile (\<lambda>y. y \<noteq> v) pivot_spine)")
      case True
      then obtain i where i: "Suc i < length pivot_spine" "pivot_spine ! i = w"
        using takeWhile_nth_succ[of v pivot_spine w] pivot_facts(5)
        by blast
      have "pivot_spine ! Suc i \<in> \<V> - {r}"
        using nth_mem[of "Suc i" pivot_spine] i(1) pivot_spine(2)
        by blast
      moreover have "t = parent_lookup parr (pivot_spine ! Suc i)"
        using pivot_reparent(3)[of i] i True 2(3)
        by (simp add: par_edge_def pivot_upd)
      ultimately show ?thesis
        by (rule rev_image_eqI)
    next
      case False
      then have "t = parent_lookup parr w"
        using 2 pivot_reparent(1)[of w]
        by (auto simp: par_edge_def pivot_upd)
      with 2(1) show ?thesis
        by (rule rev_image_eqI)
    qed
  qed
qed

lemma pivot_tree_proj:
  "(\<lambda>a. {fst a, snd a}) ` ns_tree_edges (ns_pivot_upd s) = abstract_arborescense
    (spanning_tree (ns_pivot_upd s))"
  unfolding pivot_upd(3,4) pivot_tree_edges
  by (rule pivot_new_tree(1))

lemma pivot_tree_card: "finite (ns_tree_edges (ns_pivot_upd s))"
  "card (ns_tree_edges (ns_pivot_upd s)) = card \<V> - 1"
  by (simp_all only: pivot_upd(4) pivot_tree_edges pivot_new_tree(2,3))

lemma pivot_arb: "arborescense_invar (spanning_tree (ns_pivot_upd s))"
  by (simp add: pivot_upd swap_edge_pivot(1))

lemma pivot_par_edge:
  assumes "w \<in> \<V> - {r}"
  shows "par_edge (ns_pivot_upd s) w \<in> \<E>
    \<and> (if par_up (ns_pivot_upd s) w then fst (par_edge (ns_pivot_upd s) w) = w else snd
      (par_edge (ns_pivot_upd s) w) = w)"
proof(cases w rule: pivot_spine_cases)
  case off
  then show ?thesis
    using pivot_reparent(1) ns_invar_tree_vertexD[of s w] inv_tree assms
    by simp
next
  case hd
  then show ?thesis
    using pivot_reparent(2) pivot_spine_hd step_entering(1,3)
    by auto
next
  case (nth i)
  have "pivot_spine ! i \<in> \<V> - {r}"
    using nth(3) pivot_spine(2)
    by (auto dest: set_takeWhileD)
  then show ?thesis
    using nth pivot_reparent(3)[of i] pivot_spine_succ[of i] ns_invar_tree_vertexD[of s "pivot_spine ! i"]
      inv_tree
    by (auto simp: par_vx_def split: if_splits)
qed

lemma invar_impl_holds_upd_pivot[invar_holds_intros]: "ns_invar_impl (ns_pivot_upd s)"
  using augment_flow_flow_invar shift_pot_props(1) pivot_arrays step_sel(1) pivot_arb step_es(2) pivot_leaving(1)
  by (auto intro!: ns_invar_implI simp: pivot_upd es_arr.fixed_univ_map_upd_invar)

lemma invar_bflow_holds_upd_pivot[invar_holds_intros]: "ns_invar_bflow (ns_pivot_upd s)"
  using piv pivot_upd(1) by (rule invar_bflow_augment)

lemma invar_partition_holds_upd_pivot[invar_holds_intros]: "ns_invar_partition (ns_pivot_upd s)"
  unfolding ns_invar_partition_def pivot_upd(4) pivot_tree_edges
  using inv_stp step_entering(7,5,6) pivot_facts(2) pivot_LU
  by (rule spanning_tree_partition_exchange)
     (use swap_edge_pivot(1) pivot_new_tree in \<open>rule arborescense_tree_edges\<close>)+

lemma invar_flow_fits_holds_upd_pivot[invar_holds_intros]: "ns_invar_flow_fits (ns_pivot_upd s)"
proof-
  have "if e0fwd then ereal (h (flow_lookup (augment_flow s e in_U \<delta> p1 p2) (par_edge s v))) = \<u>
    (par_edge s v)
        else flow_lookup (augment_flow s e in_U \<delta> p1 p2) (par_edge s v) = 0"
    using pivot_leaving_flow piv(2) pivot_leaving(1) cap_nonneg[of "par_edge s v"] cap_finite[of "par_edge s v"]
    by (auto simp: res_fwd_def res_bwd_def Let_def split: if_splits)
  then show ?thesis
    using inv_flow_fits pivot_leaving(2) pivot_facts(3) augment_flow_off_tree[of \<delta>]
    by (auto simp: ns_invar_flow_fits_def flow_fits_spanning_tree_partition_def pivot_LU pivot_upd step_off_tree
        split: if_splits)
qed

lemma invar_pot_fits_holds_upd_pivot[invar_holds_intros]: "ns_invar_pot_fits (ns_pivot_upd s)"
  using shift_pot_props(3)
  by (simp add: ns_invar_pot_fits_def pivot_upd pivot_tree_edges)

lemma invar_strict_holds_upd_pivot[invar_holds_intros]: "ns_invar_strict (ns_pivot_upd s)"
proof(rule ns_invar_strictI)
  fix w assume w: "w \<in> \<V> - {r}"
  then show "if par_up (ns_pivot_upd s) w
    then ereal (h (flow_lookup (current_flow (ns_pivot_upd s)) (par_edge (ns_pivot_upd s) w))) < \<u>
      (par_edge (ns_pivot_upd s) w)
    else 0 < flow_lookup (current_flow (ns_pivot_upd s)) (par_edge (ns_pivot_upd s) w)"
  proof(cases w rule: pivot_spine_cases)
    case off
    then show ?thesis
      using w pivot_facts(3)
      by (simp add: pivot_reparent(1) pivot_upd(1) augment_flow_strict pivot_up_res)
  next
    case hd
    show ?thesis unfolding hd pivot_reparent(2)[THEN conjunct1] pivot_reparent(2)[THEN conjunct2] pivot_upd(1)
      by (rule pivot_entering_strict)
  next
    case (nth i)
    then show ?thesis
      using pivot_spine_strict[of "pivot_spine ! i"]
      by (simp add: nth(2)[symmetric] pivot_reparent(3) pivot_upd(1))
  qed
qed

lemma invar_tree_holds_upd_pivot[invar_holds_intros]: "ns_invar_tree (ns_pivot_upd s)"
  using pivot_arb pivot_tree_proj pivot_par_edge by (rule ns_invar_tree_parentI)

lemma invar_selfloop_holds_upd_pivot[invar_holds_intros]: "ns_invar_selfloop (ns_pivot_upd s)"
  using pivot_facts(3) pivot_upd(1) by (rule invar_selfloop_augment)

text \<open>The pivot decreases the measure: the flow cost drops when @{term \<open>\<delta> >
      0\<close>}; a degenerate pivot (@{term \<open>\<delta> = 0\<close>}, never on the up-side) keeps
      the cost and raises the potential sum by the entering reduced cost times the size of the re-hung
      subtree.\<close>

lemma ns_less_upd_pivot: "ns_less (ns_pivot_upd s) s"
proof-
  have cost: "ns_flow_cost (ns_pivot_upd s) = ns_flow_cost s + (if in_U then - h \<delta> else h \<delta>) *
    reduced_cost (potentials s) e"
    using piv augment_flow_cost
    by (simp add: ns_flow_cost_def pivot_upd)
  have pots: "ns_pot_sum (ns_pivot_upd s) = ns_pot_sum s + pivot_shift * real (card pivot_subtree)"
    using shift_pot_props(4)
    by (simp add: ns_pot_sum_def pivot_upd)
  obtain q where "walk_betw (abstract_arborescense (spanning_tree s)) v (v # par_vx s v # q) r \<and> distinct
    (v # par_vx s v # q)"
    using par_vx_walk_succ[of v] pivot_facts(1)
    by blast
  then have "v \<in> pivot_subtree"
    by auto
  then have "0 < card pivot_subtree"
    using finite_subset[of _ \<V>] \<V>_finite pivot_subtree(4)
    by (auto simp: card_gt_0_iff)
  then have "ns_flow_cost (ns_pivot_upd s) < ns_flow_cost s
      \<or> (ns_flow_cost (ns_pivot_upd s) = ns_flow_cost s \<and> ns_pot_sum s < ns_pot_sum (ns_pivot_upd s))"
    using pivot_facts(3,4) cost pots step_reduced_cost step_sel(3)
    by (cases "\<delta> = 0"; cases in_U) (auto simp: zero_less_mult_iff mult_less_0_iff)
  then show ?thesis
    using possible_trees_shrink[of "ns_pivot_upd s"]
    by (simp add: ns_less_def)
qed

end

end

end

end

subsection \<open>Preservation and decrease per branch\<close>

lemma ns_flip_branch[call_cond_elims]:
  assumes "ns_invar s" "ns_flip_cond s"
  obtains e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where "ns_select s = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    "bottleneck s e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side)" "\<delta> \<noteq> - 1"
proof-
  obtain e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
    and "bottleneck s e in_U p1 p2 = (\<delta>, True, v, e0fwd, up_side)" "\<delta> \<noteq> - 1"
    using assms(2)
    by (rule ns_flip_condE)
  then show ?thesis
    using ns_select_SomeD(2)[of s e] assms(1) sel
    by (auto intro!: that[OF sel])
qed

lemma ns_pivot_branch[call_cond_elims]:
  assumes "ns_invar s" "ns_pivot_cond s"
  obtains e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side parr darr where
    "ns_select s = Some (e, in_U, \<gamma>, sel')"
    "get_path_pair (spanning_tree s) (fst e) (snd e) = (p1, p2)"
    "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" "\<delta> \<noteq> - 1"
    "reparent s e (if in_U = up_side then p1 else p2) v = (parr, darr)"
proof-
  obtain e in_U \<gamma> sel' p1 p2 \<delta> v e0fwd up_side where sel: "ns_select s = Some (e, in_U, \<gamma>, sel')"
    and "get_path_pair (spanning_tree s) (fst_exec e) (snd_exec e) = (p1, p2)"
    and "bottleneck s e in_U p1 p2 = (\<delta>, False, v, e0fwd, up_side)" "\<delta> \<noteq> - 1"
    using assms(2)
    by (rule ns_pivot_condE)
  moreover obtain parr darr where "reparent s e (if in_U = up_side then p1 else p2) v = (parr, darr)"
    by (cases "reparent s e (if in_U = up_side then p1 else p2) v")
  ultimately show ?thesis
    using ns_select_SomeD(2)[of s e] assms(1) sel
    by (auto intro!: that[OF sel])
qed

lemma invar_holds_upd_flip[invar_holds_intros]: "\<lbrakk>ns_invar s; ns_flip_cond s\<rbrakk> \<Longrightarrow>
  ns_invar (ns_flip_upd s)"
  by (rule ns_flip_branch[of s]) (blast intro: ns_invarI invar_holds_intros)+

lemma call_flip_terminates[termination_intros]: "\<lbrakk>ns_invar s; ns_flip_cond s\<rbrakk> \<Longrightarrow>
  ns_less (ns_flip_upd s) s"
  by (rule ns_flip_branch[of s]) (blast intro: ns_less_upd_flip)+

lemma invar_holds_upd_pivot[invar_holds_intros]: "\<lbrakk>ns_invar s; ns_pivot_cond s\<rbrakk> \<Longrightarrow>
  ns_invar (ns_pivot_upd s)"
  by (rule ns_pivot_branch[of s]) (blast intro: ns_invarI invar_holds_intros)+

lemma call_pivot_terminates[termination_intros]: "\<lbrakk>ns_invar s; ns_pivot_cond s\<rbrakk> \<Longrightarrow>
  ns_less (ns_pivot_upd s) s"
  by (rule ns_pivot_branch[of s]) (blast intro: ns_less_upd_pivot)+

lemmas ns_flip_preservation = invar_holds_upd_flip call_flip_terminates
lemmas ns_pivot_preservation = invar_holds_upd_pivot call_pivot_terminates

end
end