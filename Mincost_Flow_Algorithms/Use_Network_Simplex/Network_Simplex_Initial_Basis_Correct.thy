theory Network_Simplex_Initial_Basis_Correct
  imports Network_Simplex_Initial_Basis
begin

provenance ai


section \<open>Correctness of the initial-basis construction\<close>

text \<open>We prove the construction correct in a context that adds the only genuine hypothesis on the frozen
      input flow @{term flow_list}: it is \<^emph>\<open>capacity-complying\<close> --- every real edge
      carries a non-negative flow that does not exceed its (finite) capacity. The \<open>- 1\<close> capacity
      encodes an infinite capacity, which no flow can exceed, so that case carries no constraint. We also
      assume the instance is \<^emph>\<open>balanced\<close> --- the target balances sum to zero
      (\<open>sum b_list = 0\<close>) --- which is the feasibility precondition making the root vertex balance
      automatically (an unbalanced instance admits no \<open>b\<close>-flow at all). One further hypothesis,
      acyclicity of @{term flow_list} (needed for the free edges to form a forest, L1), will be added as the
      tree-shaped obligations demand it.\<close>

locale \<^marker>\<open>provenance ai_human\<close> initial_basis_correct =
  initial_basis_lists where capacity_list = capacity_list and h = h
  for capacity_list :: "('n :: linordered_idom) list" and h :: "'n \<Rightarrow> real" +
  assumes flow_nonneg: "\<And>e. e < m \<Longrightarrow> 0 \<le> flow_list ! e"
      and flow_le_cap: "\<And>e. \<lbrakk>e < m; capacity_list ! e \<noteq> - 1\<rbrakk> \<Longrightarrow> flow_list ! e \<le> capacity_list ! e"
      and balance_sum_zero: "sum_list b_list = 0"
begin


subsection \<open>Pass A records each real edge's status faithfully\<close>

text \<open>The classification a single Pass-A step assigns to edge @{term e}: at its lower bound when it
      carries no flow, at its (finite) upper bound when saturated, and \<^emph>\<open>free\<close> (a tree candidate)
      otherwise. These three cases are exactly @{const passA_step}'s inner @{term st}.\<close>

definition classify :: "'n list \<Rightarrow> nat \<Rightarrow> edge_tag" where
  "classify fl e = (if fl ! e = 0 then InL
                 else if capacity_list ! e \<noteq> - 1 \<and> fl ! e = capacity_list ! e then InU
                 else InTree)"

text \<open>The first component of the Pass-A tuple is the status array; a step overwrites exactly its own
      edge's slot with that edge's @{const classify}.  (A nested wildcard tuple pattern
      \<open>case s of (est, _, _, _) \<Rightarrow> est\<close> is definitionally \<open>fst s\<close>; we phrase the
      projections with @{const fst} to keep the rewriting robust.)\<close>

lemma case4_is_fst: "(case s of (est, _, _, _) \<Rightarrow> est) = fst s"
  by (cases s) auto

lemma passA_step_fst: "fst (passA_step fl e s) = (fst s)[e := classify fl e]"
  by (cases s) (auto simp: passA_step_def classify_def Let_def)

lemma passA_fold_fst:
  "\<lbrakk>sized s; e < m\<rbrakk>
   \<Longrightarrow> fst (fold (passA_step fl) xs s) ! e = (if e \<in> set xs then classify fl e else fst s ! e)"
proof(induction xs arbitrary: s)
  case (Cons a xs)
  moreover have "length (fst s) = m"
    using Cons.prems(1) by (cases s) (simp add: sized_def)
  ultimately show ?case
    by (simp add: passA_step_sized passA_step_fst nth_list_update)
qed simp

lemma edge_state_nth: "e < m \<Longrightarrow> edge_state fl ! e = classify fl e"
  unfolding edge_state_def case4_is_fst passA_def Let_def
  by (subst passA_fold_fst) (simp_all add: sized_def length_out_lo length_in_lo length_out_E length_in_E)

subsection \<open>Status characterisation: the L / U / free partition of the real edges\<close>

text \<open>Under capacity-compliance the three tags mean exactly what the simplex partition needs: an
      @{const InTree} (free) edge is \<^emph>\<open>strictly interior in both directions\<close>
      (\<open>0 < f\<close> and \<open>f < u\<close>, the \<open>- 1\<close> case being genuinely unbounded above),
      which is the residual-in-both-directions fact underpinning ``free edges form a forest'' (L1). An
      @{const InL} edge carries no flow; an @{const InU} edge is saturated at a finite positive
      capacity. Every real edge is exactly one of the three.\<close>

text \<open>@{const edge_state}'s \<open>InTree\<close> characterisation and @{const is_free} need
      capacity-compliance of \<open>fl\<close>; they are stated in the \<open>fl\<close>-fixing context
      (\<open>flow_props\<close>) near the forest lemmas below, not here at locale level.\<close>

lemma edge_state_InL_iff: "e < m \<Longrightarrow> edge_state fl ! e = InL \<longleftrightarrow> fl ! e = 0"
  by (simp add: edge_state_nth classify_def)

lemma edge_state_InU_iff:
  "e < m \<Longrightarrow>
   edge_state fl ! e = InU \<longleftrightarrow> fl ! e \<noteq> 0 \<and> capacity_list ! e \<noteq> - 1 \<and> fl ! e = capacity_list ! e"
  by (auto simp: edge_state_nth classify_def)

lemma edge_state_cases:
  "e < m \<Longrightarrow> edge_state fl ! e = InL \<or> edge_state fl ! e = InU \<or> edge_state fl ! e = InTree"
  by (simp add: edge_state_nth classify_def)

subsection \<open>Pass A computes the achieved balance (excess), and the imbalance\<close>

text \<open>The second Pass-A component is the excess accumulator.  A step adds the edge's flow at its head
      and subtracts it at its tail; a self-loop cancels.  Pointwise this is a signed indicator update.\<close>

lemma case4_snd: "(case s of (_, exc, _, _) \<Rightarrow> exc) = fst (snd s)"
  by (cases s) auto

lemma passA_step_exc:
  "fst (snd (passA_step fl e s)) =
     (let x = fst_list ! e; y = snd_list ! e; f = fl ! e; exc = fst (snd s)
      in (exc[y := exc ! y + f])[x := (exc[y := exc ! y + f]) ! x - f])"
  by (cases s) (auto simp: passA_step_def Let_def)

lemma exc_upd_nth:
  "v < length (exc :: 'n list) \<Longrightarrow>
   ((exc[y := exc ! y + f])[x := (exc[y := exc ! y + f]) ! x - f]) ! v =
   exc ! v + (if y = v then f else 0) - (if x = v then f else 0)"
  by (cases "x = v"; cases "y = v") (auto simp: nth_list_update)

text \<open>Hence over the whole edge sweep the excess at @{term v} is the signed net flow into @{term v}: the
      flow on edges \<^emph>\<open>headed\<close> at @{term v} minus the flow on edges
      \<^emph>\<open>tailed\<close> at @{term v} --- i.e. the balance the frozen flow
      \<^emph>\<open>achieves\<close> at @{term v} (@{text "b\<^sub>0 v = - ex flow_list v"}).\<close>

lemma passA_fold_exc:
  "\<lbrakk>sized s; v < Suc vcount\<rbrakk> \<Longrightarrow>
   fst (snd (fold (passA_step fl) xs s)) ! v =
   fst (snd s) ! v + (\<Sum>e\<leftarrow>xs. (if snd_list ! e = v then fl ! e else 0))
   - (\<Sum>e\<leftarrow>xs. (if fst_list ! e = v then fl ! e else 0))"
proof(induction xs arbitrary: s)
  case (Cons a xs)
  moreover have "length (fst (snd s)) = Suc vcount"
    using Cons.prems(1) by (cases s) (simp add: sized_def)
  ultimately show ?case
    by (simp add: passA_step_sized passA_step_exc Let_def exc_upd_nth)
qed simp

lemma excess_nth:
  "v < Suc vcount \<Longrightarrow>
   excess ! v = (\<Sum>e\<leftarrow>[0..<m]. (if snd_list ! e = v then flow_list ! e else 0))
   - (\<Sum>e\<leftarrow>[0..<m]. (if fst_list ! e = v then flow_list ! e else 0))"
  unfolding excess_def case4_snd passA_def Let_def
  by (subst passA_fold_exc)
    (simp_all add: sized_def length_out_lo length_in_lo length_out_E length_in_E del: replicate_Suc)

text \<open>The imbalance is the achieved balance minus the target balance --- the signed amount that
      @{term v}'s artificial edge must ship toward the root.  It is @{const excess} transformed in
      place by one vertex sweep, subtracting @{const b_lookup} at each real vertex; the root slot
      (index @{term vcount}, outside the sweep range) is untouched.\<close>

lemma fold_add_nth:
  "\<lbrakk>w < length init; distinct xs\<rbrakk> \<Longrightarrow>
   fold (\<lambda>v arr. arr[v := arr ! v + g v]) xs init ! w = (if w \<in> set xs then init ! w + g w else init ! w)"
proof(induction xs arbitrary: init)
  case (Cons a xs)
  then show ?case by (cases "w = a") auto
qed simp

lemma imbalance_nth: "v < vcount \<Longrightarrow> imbalance ! v = excess ! v + b_lookup v"
  by (simp add: imbalance_def fold_add_nth)

lemma imbalance_root: "imbalance ! vcount = excess ! vcount"
  by (simp add: imbalance_def fold_add_nth)

subsection \<open>Conservation: the imbalances sum to zero, so the root balances\<close>

text \<open>Both endpoints of a real edge are genuine vertices, hence below @{term \<open>Suc vcount\<close>} --- every
      edge's flow is counted once as an inflow and once as an outflow across the vertex range.\<close>

lemma fst_lt_Suc_vcount: "e < m \<Longrightarrow> fst_list ! e < Suc vcount"
  using fst_list_nth_vertex vs_less_vcount by (simp add: less_Suc_eq)

lemma snd_lt_Suc_vcount: "e < m \<Longrightarrow> snd_list ! e < Suc vcount"
  using snd_list_nth_vertex vs_less_vcount by (simp add: less_Suc_eq)

text \<open>The excess as a finite-set sum (rather than a list sum), so Fubini applies.\<close>

lemma excess_nth_sum:
  "v < Suc vcount \<Longrightarrow>
   excess ! v = (\<Sum>e\<in>{0..<m}. (if snd_list ! e = v then flow_list ! e else 0))
   - (\<Sum>e\<in>{0..<m}. (if fst_list ! e = v then flow_list ! e else 0))"
  by (simp add: excess_nth interv_sum_list_conv_sum_set_nat)

text \<open>Summing the achieved balance over all augmented vertices telescopes to
      @{term \<open>(\<Sum>e\<in>{0..<m}. flow_list ! e) - (\<Sum>e\<in>{0..<m}. flow_list ! e)\<close>},
      hence zero: the total excess of any flow is zero (Fubini over the vertex/edge double sum).\<close>

lemma sum_excess_zero: "(\<Sum>v\<in>{0..<Suc vcount}. excess ! v) = 0"
  by (simp add: excess_nth_sum sum_subtractf sum.swap[where A = "{0..<Suc vcount}"] fst_lt_Suc_vcount
      snd_lt_Suc_vcount del: sum.op_ivl_Suc)

text \<open>A scatter into an array with \<^emph>\<open>distinct\<close> keys writes each slot at most once;
      summing the result adds, per key, its written value minus the slot's initial content (over a group so
      the ordinary @{const sum_list} update law holds --- the library's is restricted to truncated
      subtraction).\<close>

lemma sum_list_update_group:
  "k < length xs \<Longrightarrow> sum_list (xs[k := x]) = sum_list xs - xs ! k + (x :: 'a::ab_group_add)"
  by (induction xs arbitrary: k) (auto simp: algebra_simps split: nat.split)

lemma foldl_scatter_sum_list:
  "\<lbrakk>distinct (map fst ps); \<forall>(k,x)\<in>set ps. k < length init\<rbrakk> \<Longrightarrow>
   sum_list (foldl (\<lambda>arr (k, x). arr[k := x]) init ps) = sum_list init + (\<Sum>(k,x)\<leftarrow>ps. x - init ! k)"
  for init :: "'a::ab_group_add list"
proof(induction ps arbitrary: init)
  case (Cons kx ps)
  obtain k x where kx: "kx = (k, x)" by fastforce
  with Cons.prems have "(\<Sum>(k',x')\<leftarrow>ps. x' - init[k := x] ! k') = (\<Sum>(k',x')\<leftarrow>ps. x' - init ! k')"
    by (intro arg_cong[where f = sum_list] map_cong) (auto simp: nth_list_update image_iff)
  with Cons kx show ?case by (simp add: sum_list_update_group)
qed simp

text \<open>Applied to @{const b_arr}: the balance array (scattered from the distinct vertex names) sums to
      @{term \<open>sum_list b_list\<close>}.\<close>

lemma sum_b_arr: "sum_list b_arr = sum_list b_list"
proof-
  have "map (\<lambda>(k,x). x - replicate (Suc vcount) (0::'n) ! k) (zip vs_list b_list) = map snd (zip vs_list b_list)"
    by (auto dest!: set_zip_leftD vs_less_vcount simp del: replicate_Suc)
  with distinct_vs_list show ?thesis
    unfolding b_arr_def
    by (subst foldl_scatter_sum_list) (auto simp: sum_list_replicate length_b length_vs_list
        dest!: set_zip_leftD vs_less_vcount simp del: replicate_Suc)
qed

text \<open>The array now has a slot for the artificial root as well, so the sum over its indices runs to
      @{term \<open>Suc vcount\<close>}. That extra slot holds @{term \<open>0::'n\<close>}
      (@{thm b_lookup_root}), hence the sum over the real vertex names is unchanged.\<close>

lemma sum_b_lookup: "(\<Sum>v\<in>{0..<vcount}. b_lookup v) = sum_list b_list"
  using b_lookup_root sum_b_arr
  by (simp add: b_lookup_def sum_list_sum_nth atLeast0LessThan length_b_arr)

text \<open>Hence the imbalances telescope to @{term \<open>- sum_list b_list\<close>}; with the instance balanced
      (@{thm balance_sum_zero}) they sum to zero, so the artificial edges ship a globally consistent
      amount and the root vertex balances automatically.\<close>

lemma sum_imbalance: "(\<Sum>v\<in>{0..<Suc vcount}. imbalance ! v) = sum_list b_list"
  using sum_excess_zero imbalance_root
  by (simp add: imbalance_nth sum.distrib sum_b_lookup sum.atLeast0_lessThan_Suc algebra_simps)

lemma sum_imbalance_zero: "(\<Sum>v\<in>{0..<Suc vcount}. imbalance ! v) = 0"
  using sum_imbalance balance_sum_zero by linarith

subsection \<open>The free ranges of Pass A\<close>

text \<open>Pass A appends each free edge to the range of its tail resp.\ head (@{const csr_append}),
      starting from empty ranges at the block starts. So the free views are @{locale csr_ranges}
      whose range at a vertex holds exactly its free outgoing resp.\ ingoing edges. The ranges never
      overflow their blocks: a range holds fewer edges than the block, as long as an edge of the
      block is still to come.\<close>

lemma passA_step_fo:
  "fst (snd (snd (passA_step fl e s))) =
     (if classify fl e = InTree then csr_append (fst_list ! e) e (fst (snd (snd s)))
      else fst (snd (snd s)))"
  by (cases s) (simp add: passA_step_def classify_def Let_def)

lemma passA_step_fi:
  "snd (snd (snd (passA_step fl e s))) =
     (if classify fl e = InTree then csr_append (snd_list ! e) e (snd (snd (snd s)))
      else snd (snd (snd s)))"
  by (cases s) (simp add: passA_step_def classify_def Let_def)

lemma passA_fold_fo:
  "fst (snd (snd (fold (passA_step fl) xs s))) =
     fold (\<lambda>e p. if classify fl e = InTree then csr_append (fst_list ! e) e p else p) xs
       (fst (snd (snd s)))"
  by (induction xs arbitrary: s) (simp_all add: passA_step_fo)

lemma passA_fold_fi:
  "snd (snd (snd (fold (passA_step fl) xs s))) =
     fold (\<lambda>e p. if classify fl e = InTree then csr_append (snd_list ! e) e p else p) xs
       (snd (snd (snd s)))"
  by (induction xs arbitrary: s) (simp_all add: passA_step_fi)

lemma ranges_fold:
  fixes B :: "nat list"
  assumes "csr_ranges vcount {..<vcount} B ((!) Hl0) E0" "length Hl0 = vcount"
    "\<And>v c. v < vcount \<Longrightarrow> csr_blocks.csr_abstract B ((!) Hl0) E0 c v = {}"
    "\<And>v. v < vcount \<Longrightarrow> card {e. e < m \<and> ks ! e = v} = B ! Suc v - B ! v"
    "\<And>e. e < m \<Longrightarrow> ks ! e < vcount" "k \<le> m"
  shows "csr_ranges vcount {..<vcount} B ((!) (fst (fold (\<lambda>e p. if P e then csr_append (ks ! e) e p else p) [0..<k] (Hl0, E0))))
           (snd (fold (\<lambda>e p. if P e then csr_append (ks ! e) e p else p) [0..<k] (Hl0, E0))) \<and>
         length (fst (fold (\<lambda>e p. if P e then csr_append (ks ! e) e p else p) [0..<k] (Hl0, E0))) = vcount \<and>
         (\<forall>v c. v < vcount \<longrightarrow>
            csr_blocks.csr_abstract B ((!) (fst (fold (\<lambda>e p. if P e then csr_append (ks ! e) e p else p) [0..<k] (Hl0, E0))))
              (snd (fold (\<lambda>e p. if P e then csr_append (ks ! e) e p else p) [0..<k] (Hl0, E0))) c v =
            {e. e < k \<and> ks ! e = v \<and> P e})"
  using assms(6)
proof(induction k)
  case (Suc k)
  obtain Hl E where FHE: "fold (\<lambda>e p. if P e then csr_append (ks ! e) e p else p) [0..<k] (Hl0, E0) = (Hl, E)"
    by fastforce
  with Suc have R: "csr_ranges vcount {..<vcount} B ((!) Hl) E" "length Hl = vcount"
    "\<And>v c. v < vcount \<Longrightarrow> csr_blocks.csr_abstract B ((!) Hl) E c v = {e. e < k \<and> ks ! e = v \<and> P e}"
    by auto
  show ?case
  proof(cases "P k")
    case True
    obtain Hl' E' where app: "csr_append (ks ! k) k (Hl, E) = (Hl', E')"
      by fastforce
    interpret R: csr_ranges vcount "{..<vcount}" B "(!) Hl" E by (rule R(1))
    have kx: "ks ! k < vcount" using assms(5) Suc.prems by simp
    have "{e. e < k \<and> ks ! e = ks ! k \<and> P e} \<subset> {e. e < m \<and> ks ! e = ks ! k}"
    proof(rule psubsetI)
      have "k \<in> {e. e < m \<and> ks ! e = ks ! k} - {e. e < k \<and> ks ! e = ks ! k \<and> P e}"
        using Suc.prems by simp
      then show "{e. e < k \<and> ks ! e = ks ! k \<and> P e} \<noteq> {e. e < m \<and> ks ! e = ks ! k}"
        by blast
    qed (use Suc.prems in auto)
    then have "card {e. e < k \<and> ks ! e = ks ! k \<and> P e} < card {e. e < m \<and> ks ! e = ks ! k}"
      by (rule psubset_card_mono[rotated]) simp
    then have hlt: "Hl ! (ks ! k) < B ! Suc (ks ! k)"
      using R.csr_card_abstract[OF kx, of undefined] R(3)[OF kx, of undefined] assms(4)[OF kx] by simp
    have notin: "k \<notin> R.csr_abstract c (ks ! k)" for c using R(3)[OF kx] by simp
    have "ks ! k < length Hl" using kx R(2) by simp
    note app_rules = csr_ranges_append[OF R(1) kx this hlt notin app]
    have "csr_blocks.csr_abstract B ((!) Hl') E' c v = {e. e < Suc k \<and> ks ! e = v \<and> P e}" if "v < vcount" for v c
      using app_rules(2)[OF that] R(3)[OF that] True by (auto simp: less_Suc_eq R(3)[OF kx])
    with app_rules(1) R(2) length_csr_append(1)[of "ks ! k" k "(Hl, E)"] show ?thesis
      by (simp add: FHE app True)
  qed (use FHE R in \<open>auto simp: less_Suc_eq\<close>)
qed (use assms in simp)

lemma free_out_eq:
  "free_out fl =
     fold (\<lambda>e p. if classify fl e = InTree then csr_append (fst_list ! e) e p else p) [0..<m]
       (out_lo, out.inp.E_spec)"
  by (simp add: free_out_def passA_def Let_def case_prod_beta passA_fold_fo)

lemma free_in_eq:
  "free_in fl =
     fold (\<lambda>e p. if classify fl e = InTree then csr_append (snd_list ! e) e p else p) [0..<m]
       (in_lo, inc.inp.E_spec)"
  by (simp add: free_in_def passA_def Let_def case_prod_beta passA_fold_fi)

lemma is_free_classify: "e < m \<Longrightarrow> is_free fl e \<longleftrightarrow> classify fl e = InTree"
  by (simp add: is_free_def edge_state_nth)

lemma fst_list_lt: "e < m \<Longrightarrow> fst_list ! e < vcount"
  using fst_list_nth_vertex vs_less_vcount by blast

lemma snd_list_lt: "e < m \<Longrightarrow> snd_list ! e < vcount"
  using snd_list_nth_vertex vs_less_vcount by blast

text \<open>The free ranges after the first @{term k} edges of Pass A.\<close>

lemma out_ranges_fold:
  "k \<le> m \<Longrightarrow>
   csr_ranges vcount {..<vcount} out.inp.B_spec
     ((!) (fst (fold (\<lambda>e p. if classify fl e = InTree then csr_append (fst_list ! e) e p else p) [0..<k] (out_lo, out.inp.E_spec))))
     (snd (fold (\<lambda>e p. if classify fl e = InTree then csr_append (fst_list ! e) e p else p) [0..<k] (out_lo, out.inp.E_spec))) \<and>
   length (fst (fold (\<lambda>e p. if classify fl e = InTree then csr_append (fst_list ! e) e p else p) [0..<k] (out_lo, out.inp.E_spec))) = vcount \<and>
   (\<forall>v c. v < vcount \<longrightarrow>
      csr_blocks.csr_abstract out.inp.B_spec
        ((!) (fst (fold (\<lambda>e p. if classify fl e = InTree then csr_append (fst_list ! e) e p else p) [0..<k] (out_lo, out.inp.E_spec))))
        (snd (fold (\<lambda>e p. if classify fl e = InTree then csr_append (fst_list ! e) e p else p) [0..<k] (out_lo, out.inp.E_spec))) c v =
      {e. e < k \<and> fst_list ! e = v \<and> classify fl e = InTree})"
proof(rule ranges_fold)
  show "csr_ranges vcount {..<vcount} out.inp.B_spec ((!) out_lo) out.inp.E_spec"
    by (rule csr_ranges_start[OF csr_ranges_subset[OF out.graph.csr_ranges_axioms]]) (simp_all add: out_lo_nth)
  then interpret R0: csr_ranges vcount "{..<vcount}" out.inp.B_spec "(!) out_lo" out.inp.E_spec .
  show "csr_blocks.csr_abstract out.inp.B_spec ((!) out_lo) out.inp.E_spec c v = {}" if "v < vcount" for v c
    using that by (simp add: R0.csr_abstract_eq out_lo_nth)
  show "card {e. e < m \<and> fst_list ! e = v} = out.inp.B_spec ! Suc v - out.inp.B_spec ! v" if "v < vcount" for v
    using out.graph.csr_card_abstract[OF that, of undefined] out_block[OF that, of undefined] by simp
qed (simp_all add: length_out_lo fst_list_lt)

lemma in_ranges_fold:
  "k \<le> m \<Longrightarrow>
   csr_ranges vcount {..<vcount} inc.inp.B_spec
     ((!) (fst (fold (\<lambda>e p. if classify fl e = InTree then csr_append (snd_list ! e) e p else p) [0..<k] (in_lo, inc.inp.E_spec))))
     (snd (fold (\<lambda>e p. if classify fl e = InTree then csr_append (snd_list ! e) e p else p) [0..<k] (in_lo, inc.inp.E_spec))) \<and>
   length (fst (fold (\<lambda>e p. if classify fl e = InTree then csr_append (snd_list ! e) e p else p) [0..<k] (in_lo, inc.inp.E_spec))) = vcount \<and>
   (\<forall>v c. v < vcount \<longrightarrow>
      csr_blocks.csr_abstract inc.inp.B_spec
        ((!) (fst (fold (\<lambda>e p. if classify fl e = InTree then csr_append (snd_list ! e) e p else p) [0..<k] (in_lo, inc.inp.E_spec))))
        (snd (fold (\<lambda>e p. if classify fl e = InTree then csr_append (snd_list ! e) e p else p) [0..<k] (in_lo, inc.inp.E_spec))) c v =
      {e. e < k \<and> snd_list ! e = v \<and> classify fl e = InTree})"
proof(rule ranges_fold)
  show "csr_ranges vcount {..<vcount} inc.inp.B_spec ((!) in_lo) inc.inp.E_spec"
    by (rule csr_ranges_start[OF csr_ranges_subset[OF inc.graph.csr_ranges_axioms]]) (simp_all add: in_lo_nth)
  then interpret R0: csr_ranges vcount "{..<vcount}" inc.inp.B_spec "(!) in_lo" inc.inp.E_spec .
  show "csr_blocks.csr_abstract inc.inp.B_spec ((!) in_lo) inc.inp.E_spec c v = {}" if "v < vcount" for v c
    using that by (simp add: R0.csr_abstract_eq in_lo_nth)
  show "card {e. e < m \<and> snd_list ! e = v} = inc.inp.B_spec ! Suc v - inc.inp.B_spec ! v" if "v < vcount" for v
    using inc.graph.csr_card_abstract[OF that, of undefined] in_block[OF that, of undefined] by simp
qed (simp_all add: length_in_lo snd_list_lt)

lemma free_out:
  "csr_ranges vcount {..<vcount} out.inp.B_spec ((!) (fst (free_out fl))) (snd (free_out fl))"
  "v < vcount \<Longrightarrow> csr_blocks.csr_abstract out.inp.B_spec ((!) (fst (free_out fl))) (snd (free_out fl)) c v =
                    {e. e < m \<and> fst_list ! e = v \<and> is_free fl e}"
  using out_ranges_fold[OF order.refl, of fl, folded free_out_eq] by (auto simp: is_free_classify)

lemma free_in:
  "csr_ranges vcount {..<vcount} inc.inp.B_spec ((!) (fst (free_in fl))) (snd (free_in fl))"
  "v < vcount \<Longrightarrow> csr_blocks.csr_abstract inc.inp.B_spec ((!) (fst (free_in fl))) (snd (free_in fl)) c v =
                    {e. e < m \<and> snd_list ! e = v \<and> is_free fl e}"
  using in_ranges_fold[OF order.refl, of fl, folded free_in_eq] by (auto simp: is_free_classify)



section \<open>The free-edge DFS: sizedness and termination\<close>

text \<open>We equip the recursive @{const build_dfs} with the standard call-abstraction scaffold (call
      conditions, per-call state updates, and the derived case / simp / induction / domain-intro
      rules), then use it to show that @{const build_dfs} preserves the vertex-array lengths
      (@{const dfs_sized}) and, under a well-formedness invariant on the iterators, that the
      traversal terminates.\<close>

subsection \<open>Call-abstraction scaffold\<close>

definition "bd_call1_conds fl s \<longleftrightarrow> (case ds_stk s of [] \<Rightarrow> False | v # rest \<Rightarrow>
     csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v)"
definition "bd_upd1 fl s = (case ds_stk s of v # rest \<Rightarrow>
     (let e = csr_blocks.csr_current (snd (free_out fl)) (ds_oc s) v; w = snd_list ! e;
          s1 = s\<lparr>ds_oc := csr_blocks.csr_move ((!) (fst (free_out fl))) (ds_oc s) v\<rparr>
      in if ds_seen s ! w then s1 else dfs_discover s1 v w e))"
definition "bd_call2_conds fl s \<longleftrightarrow> (case ds_stk s of [] \<Rightarrow> False | v # rest \<Rightarrow>
     \<not> csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v \<and>
     csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic s) v)"
definition "bd_upd2 fl s = (case ds_stk s of v # rest \<Rightarrow>
     (let e = csr_blocks.csr_current (snd (free_in fl)) (ds_ic s) v; w = fst_list ! e;
          s1 = s\<lparr>ds_ic := csr_blocks.csr_move ((!) (fst (free_in fl))) (ds_ic s) v\<rparr>
      in if ds_seen s ! w then s1 else dfs_discover s1 v w e))"
definition "bd_call3_conds fl s \<longleftrightarrow> (case ds_stk s of [] \<Rightarrow> False | v # rest \<Rightarrow>
     \<not> csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v \<and>
     \<not> csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic s) v)"
definition "bd_upd3 s = (case ds_stk s of v # rest \<Rightarrow> dfs_finish s v rest)"
definition "bd_ret_conds s \<longleftrightarrow> ds_stk s = []"

lemma bd_cases:
  "\<lbrakk>bd_call1_conds fl s \<Longrightarrow> P; bd_call2_conds fl s \<Longrightarrow> P; bd_call3_conds fl s \<Longrightarrow> P; bd_ret_conds s \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  unfolding bd_call1_conds_def bd_call2_conds_def bd_call3_conds_def bd_ret_conds_def
  by (cases "ds_stk s") auto

lemma bd_simps:
  "\<lbrakk>build_dfs_dom (fl, s); bd_call1_conds fl s\<rbrakk> \<Longrightarrow> build_dfs fl s = build_dfs fl (bd_upd1 fl s)"
  "\<lbrakk>build_dfs_dom (fl, s); bd_call2_conds fl s\<rbrakk> \<Longrightarrow> build_dfs fl s = build_dfs fl (bd_upd2 fl s)"
  "\<lbrakk>build_dfs_dom (fl, s); bd_call3_conds fl s\<rbrakk> \<Longrightarrow> build_dfs fl s = build_dfs fl (bd_upd3 s)"
  "\<lbrakk>build_dfs_dom (fl, s); bd_ret_conds s\<rbrakk> \<Longrightarrow> build_dfs fl s = s"
  by (auto simp: build_dfs_psimps Let_def bd_call1_conds_def bd_upd1_def bd_call2_conds_def bd_upd2_def
      bd_call3_conds_def bd_upd3_def bd_ret_conds_def split: list.splits)

text \<open>The induction rule. @{const build_dfs} hands the two free ranges of Pass A to the range-indexed
      recursion @{const build_dfs_a}, so the raw induction principle ranges over those ranges while @{term P}
      is indexed by the flow. The ranges are constant throughout the descent, so it suffices to carry
      \<open>fo = free_out fl\<close> and \<open>fi = free_in fl\<close> as side conditions through the
      induction.\<close>

lemma bd_induct:
  assumes "build_dfs_dom (fl, s)"
    "\<And>fl s. \<lbrakk>build_dfs_dom (fl, s); bd_call1_conds fl s \<Longrightarrow> P fl (bd_upd1 fl s);
              bd_call2_conds fl s \<Longrightarrow> P fl (bd_upd2 fl s); bd_call3_conds fl s \<Longrightarrow> P fl (bd_upd3 s)\<rbrakk>
            \<Longrightarrow> P fl s"
  shows "P fl s"
proof-
  have "build_dfs_a_dom (fo, fi, t) \<Longrightarrow> fo = free_out fl \<longrightarrow> fi = free_in fl \<longrightarrow> P fl t" for fo fi t
  proof(induction fo fi t rule: build_dfs_a.pinduct)
    case (1 fo fi t)
    show ?case
    proof(intro impI, rule assms(2))
      assume "fo = free_out fl" "fi = free_in fl"
      note IH = 1[unfolded this]
      show "build_dfs_dom (fl, t)" using IH(1) by (simp add: build_dfs_dom_iff)
      show "P fl (bd_upd1 fl t)" if "bd_call1_conds fl t"
      proof-
        obtain v rest where "ds_stk t = v # rest" "csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc t) v"
          using \<open>bd_call1_conds fl t\<close> by (auto simp: bd_call1_conds_def split: list.splits)
        from IH(2)[OF this refl refl refl] this show ?thesis by (simp add: bd_upd1_def Let_def)
      qed
      show "P fl (bd_upd2 fl t)" if "bd_call2_conds fl t"
      proof-
        obtain v rest where "ds_stk t = v # rest" "\<not> csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc t) v"
          "csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic t) v"
          using \<open>bd_call2_conds fl t\<close> by (auto simp: bd_call2_conds_def split: list.splits)
        from IH(3)[OF this refl refl refl] this show ?thesis by (simp add: bd_upd2_def Let_def)
      qed
      show "P fl (bd_upd3 t)" if "bd_call3_conds fl t"
        using that IH(4) by (auto simp: bd_call3_conds_def bd_upd3_def split: list.splits)
    qed
  qed
  then show ?thesis using assms(1) by (simp add: build_dfs_dom_iff)
qed

lemma bd_domintros:
  "\<lbrakk>bd_call1_conds fl s \<Longrightarrow> build_dfs_dom (fl, bd_upd1 fl s);
    bd_call2_conds fl s \<Longrightarrow> build_dfs_dom (fl, bd_upd2 fl s);
    bd_call3_conds fl s \<Longrightarrow> build_dfs_dom (fl, bd_upd3 s)\<rbrakk> \<Longrightarrow> build_dfs_dom (fl, s)"
  unfolding build_dfs_dom_iff bd_call1_conds_def bd_upd1_def bd_call2_conds_def bd_upd2_def
    bd_call3_conds_def bd_upd3_def
  by (rule build_dfs_a.domintros) (auto simp: Let_def split: list.splits if_splits)

subsection \<open>@{const build_dfs} preserves the vertex-array lengths\<close>

lemma bd_upd1_sized: "\<lbrakk>dfs_sized s; bd_call1_conds fl s\<rbrakk> \<Longrightarrow> dfs_sized (bd_upd1 fl s)"
  by (cases "ds_stk s") (simp_all add: bd_upd1_def bd_call1_conds_def dfs_sized_def dfs_discover_def
      dfs_push_def Let_def)

lemma bd_upd2_sized: "\<lbrakk>dfs_sized s; bd_call2_conds fl s\<rbrakk> \<Longrightarrow> dfs_sized (bd_upd2 fl s)"
  by (cases "ds_stk s") (simp_all add: bd_upd2_def bd_call2_conds_def dfs_sized_def dfs_discover_def
      dfs_push_def Let_def)

lemma bd_upd3_sized: "\<lbrakk>dfs_sized s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> dfs_sized (bd_upd3 s)"
  by (cases "ds_stk s") (simp_all add: bd_upd3_def bd_call3_conds_def dfs_sized_def dfs_finish_def Let_def)

subsection \<open>The iterators of the seen vertices\<close>

text \<open>The cursors of a vertex are reset when it is pushed, i.e.\ when it is seen. So the iterators of
      the seen vertices are well-formed (@{const csr_blocks.csr_invar} over the seen vertices), and the
      stack holds seen vertices only. The other cursors are arbitrary.\<close>

definition dfs_seenK :: "'n dfs_state \<Rightarrow> nat set" where
  "dfs_seenK s = {v. v < vcount \<and> ds_seen s ! v}"

definition dfs_wf :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> bool" where
  "dfs_wf fl s \<longleftrightarrow> length (ds_seen s) = Suc vcount \<and> set (ds_stk s) \<subseteq> dfs_seenK s \<and>
     csr_blocks.csr_invar (dfs_seenK s) out.inp.B_spec ((!) (fst (free_out fl))) (ds_oc s) \<and>
     csr_blocks.csr_invar (dfs_seenK s) inc.inp.B_spec ((!) (fst (free_in fl))) (ds_ic s)"

lemma dfs_seenK_sub: "dfs_seenK s \<subseteq> {..<vcount}"
  by (auto simp: dfs_seenK_def)

lemma free_out_K: "K \<subseteq> {..<vcount} \<Longrightarrow>
    csr_ranges vcount K out.inp.B_spec ((!) (fst (free_out fl))) (snd (free_out fl))"
  by (rule csr_ranges_subset[OF free_out(1)])

lemma free_in_K: "K \<subseteq> {..<vcount} \<Longrightarrow>
    csr_ranges vcount K inc.inp.B_spec ((!) (fst (free_in fl))) (snd (free_in fl))"
  by (rule csr_ranges_subset[OF free_in(1)])

lemma dfs_init_wf: "dfs_wf fl dfs_init"
  using csr_invar_empty[OF csr_ranges.axioms(1)[OF free_out(1)]]
    csr_invar_empty[OF csr_ranges.axioms(1)[OF free_in(1)]]
  by (simp add: dfs_wf_def dfs_seenK_def dfs_init_def nth_append del: replicate_Suc cong: conj_cong)

text \<open>Pushing a vertex that has just been marked seen.\<close>

lemma dfs_push_wf:
  assumes "length (ds_seen s) = Suc vcount" "dfs_seenK s = insert w K" "w < vcount"
    "set (ds_stk s) \<subseteq> dfs_seenK s"
    "csr_blocks.csr_invar K out.inp.B_spec ((!) (fst (free_out fl))) (ds_oc s)"
    "csr_blocks.csr_invar K inc.inp.B_spec ((!) (fst (free_in fl))) (ds_ic s)"
  shows "dfs_wf fl (dfs_push s w)"
proof-
  have "K \<subseteq> {..<vcount}" using assms(2) dfs_seenK_sub by blast
  note R = csr_ranges.axioms(1)[OF free_out_K[OF this]] csr_ranges.axioms(1)[OF free_in_K[OF this]]
  have "dfs_seenK (dfs_push s w) = dfs_seenK s" by (simp add: dfs_seenK_def dfs_push_def)
  with assms csr_invar_reset_insert[OF R(1) assms(5,3)] csr_invar_reset_insert[OF R(2) assms(6,3)]
  show ?thesis by (simp add: dfs_wf_def dfs_push_def)
qed

lemma dfs_discover_wf: "\<lbrakk>dfs_wf fl s; w < vcount\<rbrakk> \<Longrightarrow> dfs_wf fl (dfs_discover s v w e)"
  unfolding dfs_discover_def Let_def
  by (rule dfs_push_wf[where K = "dfs_seenK s"]) (auto simp: dfs_wf_def dfs_seenK_def nth_list_update)

text \<open>One step of the iterator of the top vertex: the current edge is a free edge of that vertex, it
      leaves the remaining set, and the other vertices' remaining sets are untouched.\<close>

lemma bd_out_step:
  assumes "dfs_wf fl s" "ds_stk s = v # rest" "csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v"
  defines "e \<equiv> csr_blocks.csr_current (snd (free_out fl)) (ds_oc s) v"
    and "c' \<equiv> csr_blocks.csr_move ((!) (fst (free_out fl))) (ds_oc s) v"
  shows "e < m" "fst_list ! e = v" "is_free fl e" "snd_list ! e < vcount"
    "csr_blocks.csr_invar (dfs_seenK s) out.inp.B_spec ((!) (fst (free_out fl))) c'"
    "e \<in> csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) (ds_oc s) v"
    "csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) c' v =
       csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) (ds_oc s) v - {e}"
    "\<And>j. j \<noteq> v \<Longrightarrow> csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) c' j =
       csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) (ds_oc s) j"
    "finite (csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) (ds_oc s) v)"
proof-
  interpret F: csr_ranges vcount "dfs_seenK s" out.inp.B_spec "(!) (fst (free_out fl))" "snd (free_out fl)"
    by (rule free_out_K) (rule dfs_seenK_sub)
  have inv: "F.csr_invar (ds_oc s)" and vK: "v \<in> dfs_seenK s" using assms(1,2) by (auto simp: dfs_wf_def)
  have ne: "F.csr_remaining (ds_oc s) v \<noteq> {}" using F.csr.idx_has[OF inv vK] assms(3) by simp
  have sub: "F.csr_remaining (ds_oc s) v \<subseteq> {e. e < m \<and> fst_list ! e = v \<and> is_free fl e}"
    using vK F.csr.idx_partition_union[OF inv vK] free_out(2)[of v] by (auto simp: dfs_seenK_def)
  show "e \<in> F.csr_remaining (ds_oc s) v" unfolding e_def using inv vK ne by (rule F.csr.idx_current)
  then show "e < m" "fst_list ! e = v" "is_free fl e" "snd_list ! e < vcount" using sub snd_list_lt by auto
  show "F.csr_invar c'" unfolding c'_def using inv vK by (rule F.csr.idx_move_invar)
  show "F.csr_remaining c' v = F.csr_remaining (ds_oc s) v - {e}"
    unfolding c'_def e_def using inv vK ne by (rule F.csr.idx_move_remaining)
  show "F.csr_remaining c' j = F.csr_remaining (ds_oc s) j" if "j \<noteq> v" for j
    unfolding c'_def using inv vK ne that by (rule F.csr.idx_move_remaining_other)
  show "finite (F.csr_remaining (ds_oc s) v)" using sub by (rule finite_subset) simp
qed

lemma bd_in_step:
  assumes "dfs_wf fl s" "ds_stk s = v # rest" "csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic s) v"
  defines "e \<equiv> csr_blocks.csr_current (snd (free_in fl)) (ds_ic s) v"
    and "c' \<equiv> csr_blocks.csr_move ((!) (fst (free_in fl))) (ds_ic s) v"
  shows "e < m" "snd_list ! e = v" "is_free fl e" "fst_list ! e < vcount"
    "csr_blocks.csr_invar (dfs_seenK s) inc.inp.B_spec ((!) (fst (free_in fl))) c'"
    "e \<in> csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) (ds_ic s) v"
    "csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) c' v =
       csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) (ds_ic s) v - {e}"
    "\<And>j. j \<noteq> v \<Longrightarrow> csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) c' j =
       csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) (ds_ic s) j"
    "finite (csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) (ds_ic s) v)"
proof-
  interpret F: csr_ranges vcount "dfs_seenK s" inc.inp.B_spec "(!) (fst (free_in fl))" "snd (free_in fl)"
    by (rule free_in_K) (rule dfs_seenK_sub)
  have inv: "F.csr_invar (ds_ic s)" and vK: "v \<in> dfs_seenK s" using assms(1,2) by (auto simp: dfs_wf_def)
  have ne: "F.csr_remaining (ds_ic s) v \<noteq> {}" using F.csr.idx_has[OF inv vK] assms(3) by simp
  have sub: "F.csr_remaining (ds_ic s) v \<subseteq> {e. e < m \<and> snd_list ! e = v \<and> is_free fl e}"
    using vK F.csr.idx_partition_union[OF inv vK] free_in(2)[of v] by (auto simp: dfs_seenK_def)
  show "e \<in> F.csr_remaining (ds_ic s) v" unfolding e_def using inv vK ne by (rule F.csr.idx_current)
  then show "e < m" "snd_list ! e = v" "is_free fl e" "fst_list ! e < vcount" using sub fst_list_lt by auto
  show "F.csr_invar c'" unfolding c'_def using inv vK by (rule F.csr.idx_move_invar)
  show "F.csr_remaining c' v = F.csr_remaining (ds_ic s) v - {e}"
    unfolding c'_def e_def using inv vK ne by (rule F.csr.idx_move_remaining)
  show "F.csr_remaining c' j = F.csr_remaining (ds_ic s) j" if "j \<noteq> v" for j
    unfolding c'_def using inv vK ne that by (rule F.csr.idx_move_remaining_other)
  show "finite (F.csr_remaining (ds_ic s) v)" using sub by (rule finite_subset) simp
qed

text \<open>An exhausted vertex has nothing left to iterate.\<close>

lemma bd_finish_empty:
  assumes "dfs_wf fl s" "ds_stk s = v # rest"
    "\<not> csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v"
    "\<not> csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic s) v"
  shows "csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) (ds_oc s) v = {}"
    "csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) (ds_ic s) v = {}"
proof-
  interpret F: csr_ranges vcount "dfs_seenK s" out.inp.B_spec "(!) (fst (free_out fl))" "snd (free_out fl)"
    by (rule free_out_K[OF dfs_seenK_sub])
  interpret G: csr_ranges vcount "dfs_seenK s" inc.inp.B_spec "(!) (fst (free_in fl))" "snd (free_in fl)"
    by (rule free_in_K[OF dfs_seenK_sub])
  have "v \<in> dfs_seenK s" using assms(1,2) by (auto simp: dfs_wf_def)
  then show "F.csr_remaining (ds_oc s) v = {}" "G.csr_remaining (ds_ic s) v = {}"
    using F.csr.idx_has[of "ds_oc s" v] G.csr.idx_has[of "ds_ic s" v] assms by (simp_all add: dfs_wf_def)
qed

subsection \<open>The two scanning calls, packaged\<close>

text \<open>What the invariant proofs below need of a scanning call: the top vertex @{term v}, the scanned
      free edge @{term e} with its far endpoint @{term w} (a real vertex), and the call's result ---
      the state with the moved iterator, or that state with @{term w} discovered.\<close>

lemma bd_upd1_eq:
  assumes "dfs_wf fl s" "bd_call1_conds fl s"
  obtains v rest e w c' where "ds_stk s = v # rest" "e < m" "fst_list ! e = v" "snd_list ! e = w"
    "is_free fl e" "w < vcount"
    "dfs_wf fl (s\<lparr>ds_oc := c'\<rparr>)"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
proof-
  obtain v rest where "ds_stk s = v # rest" "csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v"
    using assms(2) by (auto simp: bd_call1_conds_def split: list.splits)
  note S = bd_out_step[OF assms(1) this]
  from assms(1) S(5) have "dfs_wf fl (s\<lparr>ds_oc := csr_blocks.csr_move ((!) (fst (free_out fl))) (ds_oc s) v\<rparr>)"
    by (simp add: dfs_wf_def dfs_seenK_def)
  with \<open>ds_stk s = v # rest\<close> show ?thesis
    by (intro that[OF _ S(1,2) refl S(3,4)]) (simp_all add: bd_upd1_def Let_def)
qed

lemma bd_upd2_eq:
  assumes "dfs_wf fl s" "bd_call2_conds fl s"
  obtains v rest e w c' where "ds_stk s = v # rest" "e < m" "snd_list ! e = v" "fst_list ! e = w"
    "is_free fl e" "w < vcount"
    "dfs_wf fl (s\<lparr>ds_ic := c'\<rparr>)"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
proof-
  obtain v rest where "ds_stk s = v # rest" "csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic s) v"
    and no: "\<not> csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v"
    using assms(2) by (auto simp: bd_call2_conds_def split: list.splits)
  note S = bd_in_step[OF assms(1) this(1,2)]
  from assms(1) S(5) have "dfs_wf fl (s\<lparr>ds_ic := csr_blocks.csr_move ((!) (fst (free_in fl))) (ds_ic s) v\<rparr>)"
    by (simp add: dfs_wf_def dfs_seenK_def)
  with \<open>ds_stk s = v # rest\<close> no show ?thesis
    by (intro that[OF _ S(1,2) refl S(3,4)]) (simp_all add: bd_upd2_def Let_def)
qed

lemma bd_upd3_eq:
  assumes "bd_call3_conds fl s"
  obtains v rest where "ds_stk s = v # rest" "bd_upd3 s = dfs_finish s v rest"
  using assms by (auto simp: bd_call3_conds_def bd_upd3_def split: list.splits)

subsection \<open>The invariant is maintained\<close>

lemma bd_upd1_wf: "\<lbrakk>dfs_wf fl s; bd_call1_conds fl s\<rbrakk> \<Longrightarrow> dfs_wf fl (bd_upd1 fl s)"
  by (erule bd_upd1_eq) (auto intro: dfs_discover_wf)

lemma bd_upd2_wf: "\<lbrakk>dfs_wf fl s; bd_call2_conds fl s\<rbrakk> \<Longrightarrow> dfs_wf fl (bd_upd2 fl s)"
  by (erule bd_upd2_eq) (auto intro: dfs_discover_wf)

lemma bd_upd3_wf: "\<lbrakk>dfs_wf fl s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> dfs_wf fl (bd_upd3 s)"
  by (auto simp: bd_upd3_def bd_call3_conds_def dfs_wf_def dfs_finish_def dfs_seenK_def Let_def
           split: list.splits)

subsection \<open>Termination\<close>

text \<open>A lexicographic measure decreases along every recursive call: discovering a fresh vertex lowers
      the count of unseen vertices; advancing an iterator without discovery lowers the number of
      edges remaining over the stack; finishing a vertex (nothing remains for it) shortens the
      stack.\<close>

definition dfs_unseen :: "'n dfs_state \<Rightarrow> nat" where
  "dfs_unseen s = card {v. v < Suc vcount \<and> \<not> ds_seen s ! v}"

definition dfs_budget :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> nat" where
  "dfs_budget fl s = (\<Sum>v\<leftarrow>ds_stk s.
     card (csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) (ds_oc s) v) +
     card (csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) (ds_ic s) v))"

definition dfs_stklen :: "'n dfs_state \<Rightarrow> nat" where
  "dfs_stklen s = length (ds_stk s)"

definition dfs_meas :: "'n list \<Rightarrow> ('n dfs_state \<times> 'n dfs_state) set" where
  "dfs_meas fl = measures [dfs_unseen, dfs_budget fl, dfs_stklen]"

lemma dfs_unseen_mark_lt:
  "\<lbrakk>length seen = Suc vcount; w < Suc vcount; \<not> seen ! w\<rbrakk> \<Longrightarrow>
    card {x. x < Suc vcount \<and> \<not> seen[w := True] ! x} < card {x. x < Suc vcount \<and> \<not> seen ! x}"
  by (intro psubset_card_mono) (auto simp: nth_list_update)

lemma dfs_discover_unseen:
  "\<lbrakk>length (ds_seen s) = Suc vcount; w < vcount; \<not> ds_seen s ! w\<rbrakk>
   \<Longrightarrow> dfs_unseen (dfs_discover s v w e) < dfs_unseen s"
  using dfs_unseen_mark_lt[of "ds_seen s" w]
  by (simp add: dfs_unseen_def dfs_discover_def dfs_push_def Let_def)

lemma bd_meas1:
  assumes "dfs_wf fl s" "bd_call1_conds fl s"
  shows "(bd_upd1 fl s, s) \<in> dfs_meas fl"
proof-
  obtain v rest where stk: "ds_stk s = v # rest" "csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v"
    using assms(2) by (auto simp: bd_call1_conds_def split: list.splits)
  note S = bd_out_step[OF assms(1) stk]
  let ?e = "csr_blocks.csr_current (snd (free_out fl)) (ds_oc s) v"
  let ?c' = "csr_blocks.csr_move ((!) (fst (free_out fl))) (ds_oc s) v"
  let ?R = "csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl))"
  let ?I = "csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl)) (ds_ic s)"
  show ?thesis
  proof(cases "ds_seen s ! (snd_list ! ?e)")
    case True
    have "card (?R ?c' v) < card (?R (ds_oc s) v)"
      unfolding S(7) by (rule card_Diff1_less[OF S(9) S(6)])
    moreover from this have "card (?R ?c' y) \<le> card (?R (ds_oc s) y)" for y
      using S(8)[of y] by (cases "y = v") simp_all
    then have "(\<Sum>y\<leftarrow>rest. card (?R ?c' y) + card (?I y)) \<le> (\<Sum>y\<leftarrow>rest. card (?R (ds_oc s) y) + card (?I y))"
      by (intro sum_list_mono) simp
    ultimately show ?thesis
      using stk True by (simp add: bd_upd1_def Let_def dfs_meas_def dfs_budget_def dfs_unseen_def)
  next
    case False
    with assms(1) S(4)
    have "dfs_unseen (dfs_discover (s\<lparr>ds_oc := ?c'\<rparr>) v (snd_list ! ?e) ?e) < dfs_unseen (s\<lparr>ds_oc := ?c'\<rparr>)"
      by (intro dfs_discover_unseen) (simp_all add: dfs_wf_def)
    with stk False show ?thesis by (simp add: bd_upd1_def Let_def dfs_meas_def dfs_unseen_def)
  qed
qed

lemma bd_meas2:
  assumes "dfs_wf fl s" "bd_call2_conds fl s"
  shows "(bd_upd2 fl s, s) \<in> dfs_meas fl"
proof-
  obtain v rest where stk: "ds_stk s = v # rest" "csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic s) v"
    and no: "\<not> csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v"
    using assms(2) by (auto simp: bd_call2_conds_def split: list.splits)
  note S = bd_in_step[OF assms(1) stk]
  let ?e = "csr_blocks.csr_current (snd (free_in fl)) (ds_ic s) v"
  let ?c' = "csr_blocks.csr_move ((!) (fst (free_in fl))) (ds_ic s) v"
  let ?R = "csr_blocks.csr_remaining ((!) (fst (free_in fl))) (snd (free_in fl))"
  let ?O = "csr_blocks.csr_remaining ((!) (fst (free_out fl))) (snd (free_out fl)) (ds_oc s)"
  show ?thesis
  proof(cases "ds_seen s ! (fst_list ! ?e)")
    case True
    have "card (?R ?c' v) < card (?R (ds_ic s) v)"
      unfolding S(7) by (rule card_Diff1_less[OF S(9) S(6)])
    moreover from this have "card (?R ?c' y) \<le> card (?R (ds_ic s) y)" for y
      using S(8)[of y] by (cases "y = v") simp_all
    then have "(\<Sum>y\<leftarrow>rest. card (?O y) + card (?R ?c' y)) \<le> (\<Sum>y\<leftarrow>rest. card (?O y) + card (?R (ds_ic s) y))"
      by (intro sum_list_mono) simp
    ultimately show ?thesis
      using stk no True by (simp add: bd_upd2_def Let_def dfs_meas_def dfs_budget_def dfs_unseen_def)
  next
    case False
    with assms(1) S(4)
    have "dfs_unseen (dfs_discover (s\<lparr>ds_ic := ?c'\<rparr>) v (fst_list ! ?e) ?e) < dfs_unseen (s\<lparr>ds_ic := ?c'\<rparr>)"
      by (intro dfs_discover_unseen) (simp_all add: dfs_wf_def)
    with stk no False show ?thesis by (simp add: bd_upd2_def Let_def dfs_meas_def dfs_unseen_def)
  qed
qed

lemma bd_meas3:
  assumes "dfs_wf fl s" "bd_call3_conds fl s"
  shows "(bd_upd3 s, s) \<in> dfs_meas fl"
proof-
  obtain v rest where "ds_stk s = v # rest" "\<not> csr_blocks.csr_has ((!) (fst (free_out fl))) (ds_oc s) v"
    "\<not> csr_blocks.csr_has ((!) (fst (free_in fl))) (ds_ic s) v"
    using assms(2) by (auto simp: bd_call3_conds_def split: list.splits)
  with bd_finish_empty[OF assms(1) this] show ?thesis
    by (simp add: bd_upd3_def dfs_meas_def dfs_unseen_def dfs_budget_def dfs_stklen_def
        dfs_finish_def Let_def)
qed

text \<open>Well-founded induction on the measure then discharges the domain predicate: the DFS terminates
      on every well-formed state.\<close>

lemma build_dfs_dom_wf: "dfs_wf fl s \<Longrightarrow> build_dfs_dom (fl, s)"
proof(induction s rule: wf_induct_rule[OF wf_measures[of "[dfs_unseen, dfs_budget fl, dfs_stklen]"]])
  case (1 s)
  then show ?case
    by (blast intro: bd_domintros bd_meas1[unfolded dfs_meas_def] bd_meas2[unfolded dfs_meas_def]
        bd_meas3[unfolded dfs_meas_def] bd_upd1_wf bd_upd2_wf bd_upd3_wf)
qed

lemma emit_U_edge_wf: "dfs_wf fl s \<Longrightarrow> dfs_wf fl (emit_U_edge s v)"
  by (simp add: dfs_wf_def dfs_seenK_def emit_U_edge_def Let_def)

section \<open>The structural builder invariant (I1/I2 core)\<close>

text \<open>The first tree-shaped invariant maintained by the whole builder: the artificial root
      @{term vcount} is never marked visited and has no parent, every vertex currently on the DFS stack is visited, and
      every visited real vertex's parent is either the root or another visited vertex. Together with
      the fact that a parent is fixed (when a vertex is first discovered) to a vertex already visited,
      this is the rooted-forest-towards-@{term vcount} skeleton underlying @{term arb_invar} (design
      notes I1/I2). We carry it bundled with @{const dfs_wf} and @{const dfs_sized}, since maintaining
      the parent clause across a discovery needs the discovered vertex to be real and the parent
      array's length.\<close>

definition tree_seen_inv :: "'n dfs_state \<Rightarrow> bool" where
  "tree_seen_inv s \<longleftrightarrow>
     \<not> ds_seen s ! vcount \<and> ds_prnt s ! vcount = 0 \<and>
     (\<forall>v\<in>set (ds_stk s). ds_seen s ! v) \<and>
     (\<forall>w. w < vcount \<longrightarrow> ds_seen s ! w \<longrightarrow>
        ds_prnt s ! w = vcount \<or> (ds_prnt s ! w < vcount \<and> ds_seen s ! (ds_prnt s ! w)))"

subsection \<open>Maintenance across the three recursive calls\<close>

lemma dfs_discover_tsi:
  "\<lbrakk>tree_seen_inv s; length (ds_seen s) = Suc vcount; length (ds_prnt s) = Suc vcount; v < vcount;
    ds_seen s ! v; w < vcount; \<not> ds_seen s ! w\<rbrakk> \<Longrightarrow> tree_seen_inv (dfs_discover s v w e)"
  by (auto simp: tree_seen_inv_def dfs_discover_def dfs_push_def Let_def nth_list_update)

lemma bd_upd1_tsi:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "bd_call1_conds fl s"
  shows "tree_seen_inv (bd_upd1 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF assms(1,4)])
  moreover from this(1) assms(1,3) have "v < vcount" "ds_seen s ! v"
    by (auto simp: dfs_wf_def dfs_seenK_def tree_seen_inv_def)
  moreover have "tree_seen_inv (s\<lparr>ds_oc := c'\<rparr>)" using assms(3) by (simp add: tree_seen_inv_def)
  ultimately show ?thesis
    using dfs_discover_tsi[of "s\<lparr>ds_oc := c'\<rparr>" v w e] assms(1,2) by (simp add: dfs_wf_def dfs_sized_def)
qed

lemma bd_upd2_tsi:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "bd_call2_conds fl s"
  shows "tree_seen_inv (bd_upd2 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF assms(1,4)])
  moreover from this(1) assms(1,3) have "v < vcount" "ds_seen s ! v"
    by (auto simp: dfs_wf_def dfs_seenK_def tree_seen_inv_def)
  moreover have "tree_seen_inv (s\<lparr>ds_ic := c'\<rparr>)" using assms(3) by (simp add: tree_seen_inv_def)
  ultimately show ?thesis
    using dfs_discover_tsi[of "s\<lparr>ds_ic := c'\<rparr>" v w e] assms(1,2) by (simp add: dfs_wf_def dfs_sized_def)
qed

lemma bd_upd3_tsi: "\<lbrakk>tree_seen_inv s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> tree_seen_inv (bd_upd3 s)"
  by (erule bd_upd3_eq) (auto simp: tree_seen_inv_def dfs_finish_def Let_def)

section \<open>The thread invariant (I5)\<close>

text \<open>The builder threads every emitted vertex into a singly-linked list in emission order: at each
      discovery / component-opening it links the fresh vertex \<open>w\<close> after the last emitted vertex
      \<open>ds_prev s\<close> (setting \<open>ds_thrd s ! (ds_prev s)\<close> to \<open>w\<close> and
      \<open>ds_rvth s ! w\<close> to \<open>ds_prev s\<close>) and makes \<open>w\<close> the new last, the
      root @{term vcount} being the first emitted vertex. The following invariant records that
      @{const ds_thrd} and @{const ds_rvth} are \<^emph>\<open>mutual inverses\<close> on the emitted vertices
      (\<open>rvth \<circ> thrd = id\<close> away from the last, \<open>thrd \<circ> rvth = id\<close> away
      from the root), that the last-emitted vertex has no successor and the root no predecessor, that all
      links out of a not-yet-emitted vertex are still the null sentinel \<open>0\<close>, and that vertex
      \<open>0\<close> itself is never emitted (\<open>no_zero_node\<close> makes \<open>0\<close> a pure
      sentinel --- no real vertex collides with it, which is exactly what lets the backward inverse go
      through). A vertex is \<^emph>\<open>emitted\<close> exactly when it is the root or is visited. This is
      design-notes clause I5; it feeds \<open>parent_spec\<close> of the thread and reverse-thread maps and
      the mutual-inverse clauses of \<open>arb_invar\<close>. It touches only the thread fields, so it needs
      neither the free-edge scatter characterisation nor the parent map.\<close>

definition thread_inv :: "'n dfs_state \<Rightarrow> bool" where
  "thread_inv s \<longleftrightarrow>
     ds_prev s < Suc vcount \<and>
     (ds_prev s = vcount \<or> ds_seen s ! (ds_prev s)) \<and>
     ds_thrd s ! (ds_prev s) = 0 \<and>
     ds_rvth s ! vcount = 0 \<and>
     \<not> ds_seen s ! 0 \<and>
     (\<forall>x < Suc vcount. \<not> (x = vcount \<or> ds_seen s ! x) \<longrightarrow> ds_thrd s ! x = 0 \<and> ds_rvth s ! x = 0) \<and>
     (\<forall>x < Suc vcount. (x = vcount \<or> ds_seen s ! x) \<longrightarrow> x \<noteq> ds_prev s \<longrightarrow>
         ds_thrd s ! x < Suc vcount \<and> (ds_thrd s ! x = vcount \<or> ds_seen s ! (ds_thrd s ! x))
         \<and> ds_rvth s ! (ds_thrd s ! x) = x) \<and>
     (\<forall>x < Suc vcount. (x = vcount \<or> ds_seen s ! x) \<longrightarrow> x \<noteq> vcount \<longrightarrow>
         ds_rvth s ! x < Suc vcount \<and> (ds_rvth s ! x = vcount \<or> ds_seen s ! (ds_rvth s ! x))
         \<and> ds_thrd s ! (ds_rvth s ! x) = x)"

text \<open>Small helpers used throughout: writing @{term True} into a boolean array preserves the entries
      already set; and (mirroring \<open>Hout_valid\<close> / \<open>Hin_valid\<close>) a free incident edge's
      other endpoint is a genuine vertex, hence never the reserved sentinel \<open>0\<close> (by
      \<open>no_zero_node\<close>).\<close>

lemma nth_update_True_mono: "xs ! x \<Longrightarrow> (xs[i := True]) ! x"
  by (cases "i = x"; cases "i < length xs") (auto simp: list_update_beyond)

lemma snd_list_nz: "e < m \<Longrightarrow> snd_list ! e \<noteq> 0"
  using snd_list_nth_vertex[of e] no_zero_node by (cases "snd_list ! e = 0") auto

lemma fst_list_nz: "e < m \<Longrightarrow> fst_list ! e \<noteq> 0"
  using fst_list_nth_vertex[of e] no_zero_node by (cases "fst_list ! e = 0") auto

text \<open>The generic maintenance step: any state @{term t} whose four thread-relevant fields are the
      emission update of @{term s} at a fresh real vertex @{term w} (mark @{term w} visited, link it
      after @{term \<open>ds_prev s\<close>}, make it the new last) preserves @{const thread_inv}. Both the
      free-edge discovery @{const dfs_discover} and the component opening @{const open_tree_component}
      are instances.\<close>

lemma thread_inv_upd:
  assumes "thread_inv s" "w < vcount" "w \<noteq> 0" "\<not> ds_seen s ! w" "length (ds_seen s) = Suc vcount"
    "length (ds_thrd s) = Suc vcount" "length (ds_rvth s) = Suc vcount" "ds_prev t = w"
    "ds_seen t = (ds_seen s)[w := True]" "ds_thrd t = (ds_thrd s)[ds_prev s := w]"
    "ds_rvth t = (ds_rvth s)[w := ds_prev s]"
  shows "thread_inv t"
proof-
  define pv where "pv = ds_prev s"
  from assms(1) have pv_lt: "pv < Suc vcount"
    and pv_em: "pv = vcount \<or> ds_seen s ! pv"
    and thrd_pv0: "ds_thrd s ! pv = 0"
    and rvth_r0: "ds_rvth s ! vcount = 0"
    and zunseen: "\<not> ds_seen s ! 0"
    and unem: "\<And>x. \<lbrakk>x < Suc vcount; \<not> (x = vcount \<or> ds_seen s ! x)\<rbrakk> \<Longrightarrow> ds_thrd s ! x = 0 \<and> ds_rvth s ! x = 0"
    and fwd: "\<And>x. \<lbrakk>x < Suc vcount; x = vcount \<or> ds_seen s ! x; x \<noteq> pv\<rbrakk> \<Longrightarrow>
                 ds_thrd s ! x < Suc vcount \<and> (ds_thrd s ! x = vcount \<or> ds_seen s ! (ds_thrd s ! x))
                 \<and> ds_rvth s ! (ds_thrd s ! x) = x"
    and bwd: "\<And>x. \<lbrakk>x < Suc vcount; x = vcount \<or> ds_seen s ! x; x \<noteq> vcount\<rbrakk> \<Longrightarrow>
                 ds_rvth s ! x < Suc vcount \<and> (ds_rvth s ! x = vcount \<or> ds_seen s ! (ds_rvth s ! x))
                 \<and> ds_thrd s ! (ds_rvth s ! x) = x"
    unfolding thread_inv_def pv_def by auto
  have wnv: "w \<noteq> vcount" using assms(2) by auto
  with pv_em assms(4) have pvw: "pv \<noteq> w" by auto
  have wunem: "ds_thrd s ! w = 0 \<and> ds_rvth s ! w = 0"
    using unem[of w] assms(2,4) wnv by auto
  have e_thrd: "ds_thrd t = (ds_thrd s)[pv := w]" and e_rvth: "ds_rvth t = (ds_rvth s)[w := pv]"
    using assms(10,11) pv_def by simp_all
  show ?thesis
    unfolding thread_inv_def
  proof(intro conjI)
    show "ds_prev t < Suc vcount" "ds_prev t = vcount \<or> ds_seen t ! (ds_prev t)"
      "ds_thrd t ! (ds_prev t) = 0" "ds_rvth t ! vcount = 0" "\<not> ds_seen t ! 0"
      using assms(2,3,5,8,9) e_thrd pvw wunem e_rvth wnv rvth_r0 zunseen
      by (simp_all add: nth_list_update)
  next
    show "\<forall>x < Suc vcount. \<not> (x = vcount \<or> ds_seen t ! x) \<longrightarrow> ds_thrd t ! x = 0 \<and> ds_rvth t ! x = 0"
    proof(intro allI impI)
      fix x assume xlt: "x < Suc vcount" and xun: "\<not> (x = vcount \<or> ds_seen t ! x)"
      then have "x \<noteq> w" using assms(2,5,9) by (auto simp: nth_list_update)
      moreover from this have "\<not> (x = vcount \<or> ds_seen s ! x)" using xun assms(9) by (simp add: nth_list_update)
      moreover from this have "x \<noteq> pv" using pv_em by auto
      ultimately show "ds_thrd t ! x = 0 \<and> ds_rvth t ! x = 0"
        using unem[OF xlt] e_thrd e_rvth by (simp add: nth_list_update)
    qed
  next
    show "\<forall>x < Suc vcount. (x = vcount \<or> ds_seen t ! x) \<longrightarrow> x \<noteq> ds_prev t \<longrightarrow>
            ds_thrd t ! x < Suc vcount \<and> (ds_thrd t ! x = vcount \<or> ds_seen t ! (ds_thrd t ! x))
            \<and> ds_rvth t ! (ds_thrd t ! x) = x"
    proof(intro allI impI)
      fix x assume xlt: "x < Suc vcount" and xem: "x = vcount \<or> ds_seen t ! x" and "x \<noteq> ds_prev t"
      then have "x \<noteq> w" using assms(8) by simp
      then have xem': "x = vcount \<or> ds_seen s ! x" using xem assms(9) by (simp add: nth_list_update)
      show "ds_thrd t ! x < Suc vcount \<and> (ds_thrd t ! x = vcount \<or> ds_seen t ! (ds_thrd t ! x))
            \<and> ds_rvth t ! (ds_thrd t ! x) = x"
      proof(cases "x = pv")
        case True
        then show ?thesis using assms(2,5,6,7,9) e_rvth e_thrd pv_lt pv_def
          by (simp add: nth_list_update)
      next
        case False
        with fwd[OF xlt xem'] assms(4) wnv have "ds_thrd s ! x \<noteq> w" by auto
        with fwd[OF xlt xem' False] False e_thrd assms(2,5,9) e_rvth show ?thesis
          by (simp add: nth_list_update)
      qed
    qed
  next
    show "\<forall>x < Suc vcount. (x = vcount \<or> ds_seen t ! x) \<longrightarrow> x \<noteq> vcount \<longrightarrow>
            ds_rvth t ! x < Suc vcount \<and> (ds_rvth t ! x = vcount \<or> ds_seen t ! (ds_rvth t ! x))
            \<and> ds_thrd t ! (ds_rvth t ! x) = x"
    proof(intro allI impI)
      fix x assume xlt: "x < Suc vcount" and "x = vcount \<or> ds_seen t ! x" and xnr: "x \<noteq> vcount"
      then have seenx: "ds_seen t ! x" by auto
      show "ds_rvth t ! x < Suc vcount \<and> (ds_rvth t ! x = vcount \<or> ds_seen t ! (ds_rvth t ! x))
            \<and> ds_thrd t ! (ds_rvth t ! x) = x"
      proof(cases "x = w")
        case True
        then have "ds_rvth t ! x = pv" using e_rvth assms(2,7) by (simp add: nth_list_update)
        with True pv_lt pv_em assms(6,9) e_thrd show ?thesis
          by (auto simp: nth_list_update intro: nth_update_True_mono)
      next
        case False
        then have "ds_seen s ! x" using seenx assms(9) by (simp add: nth_list_update)
        moreover from this bwd[OF xlt _ xnr] have z: "ds_rvth s ! x < Suc vcount"
          "ds_rvth s ! x = vcount \<or> ds_seen s ! (ds_rvth s ! x)" "ds_thrd s ! (ds_rvth s ! x) = x" by auto
        moreover from calculation(1) have "ds_rvth s ! x \<noteq> pv"
          using z(3) thrd_pv0 zunseen by (cases "x = 0") auto
        ultimately show ?thesis
          using False e_rvth assms(9) e_thrd by (auto simp: nth_list_update intro: nth_update_True_mono)
      qed
    qed
  qed
qed

lemma dfs_discover_thi:
  "\<lbrakk>thread_inv s; w < vcount; w \<noteq> 0; \<not> ds_seen s ! w; length (ds_seen s) = Suc vcount;
    length (ds_thrd s) = Suc vcount; length (ds_rvth s) = Suc vcount\<rbrakk>
   \<Longrightarrow> thread_inv (dfs_discover s v w e)"
  by (erule thread_inv_upd) (simp_all add: dfs_discover_def dfs_push_def Let_def)

subsection \<open>Maintenance of @{const thread_inv} across the three recursive calls\<close>

lemma bd_upd1_thi:
  assumes "dfs_wf fl s" "dfs_sized s" "thread_inv s" "bd_call1_conds fl s"
  shows "thread_inv (bd_upd1 fl s)"
proof-
  obtain v e w c' where "e < m" "snd_list ! e = w" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF assms(1,4)])
  moreover have "thread_inv (s\<lparr>ds_oc := c'\<rparr>)" using assms(3) by (simp add: thread_inv_def)
  ultimately show ?thesis
    using dfs_discover_thi[of "s\<lparr>ds_oc := c'\<rparr>" w v e] snd_list_nz[of e] assms(2) by (auto simp: dfs_sized_def)
qed

lemma bd_upd2_thi:
  assumes "dfs_wf fl s" "dfs_sized s" "thread_inv s" "bd_call2_conds fl s"
  shows "thread_inv (bd_upd2 fl s)"
proof-
  obtain v e w c' where "e < m" "fst_list ! e = w" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF assms(1,4)])
  moreover have "thread_inv (s\<lparr>ds_ic := c'\<rparr>)" using assms(3) by (simp add: thread_inv_def)
  ultimately show ?thesis
    using dfs_discover_thi[of "s\<lparr>ds_ic := c'\<rparr>" w v e] fst_list_nz[of e] assms(2) by (auto simp: dfs_sized_def)
qed

lemma bd_upd3_thi: "\<lbrakk>thread_inv s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> thread_inv (bd_upd3 s)"
  by (erule bd_upd3_eq) (simp add: thread_inv_def dfs_finish_def Let_def)

text \<open>The two non-recursive emitters: a saturated @{term U} edge changes no thread field; the initial
      state has the root as sole emitted vertex with all links null.\<close>

lemma emit_U_edge_thi: "thread_inv s \<Longrightarrow> thread_inv (emit_U_edge s v)"
  by (simp add: thread_inv_def emit_U_edge_def Let_def)

lemma dfs_init_thi: "thread_inv dfs_init"
  by (auto simp add: thread_inv_def dfs_init_def simp del: replicate_Suc)

section \<open>The parent-edge invariant (I3)\<close>

text \<open>Design-notes clause I3, for the \<^emph>\<open>interior\<close> tree edges. Every visited non-root
      vertex @{term w} whose parent @{term \<open>ds_prnt s ! w\<close>} is itself a real vertex
      (\<open>< vcount\<close>, i.e.\ @{term w} was discovered inside a component, not opened as a component
      root) has @{term \<open>ds_par s ! w\<close>} equal to the free real edge across which it was
      discovered: that edge is \<open>< m\<close> (real), free, and its endpoints are exactly
      @{term \<open>{w, ds_prnt s ! w}\<close>}, oriented so that
      @{term \<open>ds_dir s ! w = (fst_list ! (ds_par s ! w) = w)\<close>} (\<open>True\<close> iff the edge
      points \<open>w \<rightarrow> parent\<close>, up toward the root). The linchpin is the characterisation
      of the free ranges of Pass A (@{thm free_out(2)} / @{thm free_in(2)}): a vertex discovered in
      @{term v}'s out-scan is joined to @{term v} by an edge whose tail is @{term v}, and dually in-scan by an
      edge whose head is @{term v}. Component roots (\<open>prnt = vcount\<close>) carry an
      \<^emph>\<open>artificial\<close> edge and are excluded here; they are handled by the augmented-array
      assembly. This clause feeds \<open>H1\<close> parent-edge injectivity and the
      \<open>init_tree_corr\<close> orientation obligation.\<close>

definition par_edge_inv :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> bool" where
  "par_edge_inv fl s \<longleftrightarrow>
     (\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_par s ! w < m \<and> is_free fl (ds_par s ! w)
        \<and> ds_dir s ! w = (fst_list ! (ds_par s ! w) = w)
        \<and> fst_list ! (ds_par s ! w) = (if ds_dir s ! w then w else ds_prnt s ! w)
        \<and> snd_list ! (ds_par s ! w) = (if ds_dir s ! w then ds_prnt s ! w else w))"

lemma bd_upd3_pei:
  "\<lbrakk>par_edge_inv fl s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> par_edge_inv fl (bd_upd3 s)"
  by (erule bd_upd3_eq) (auto simp: par_edge_inv_def dfs_finish_def Let_def)

lemma bd_upd1_pei:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "par_edge_inv fl s" "bd_call1_conds fl s"
  shows "par_edge_inv fl (bd_upd1 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "e < m" "fst_list ! e = v" "snd_list ! e = w"
    "is_free fl e" "w < vcount"
    and up: "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF assms(1,5)])
  moreover from this(1) assms(1,3) have "v < vcount" "ds_seen s ! v"
    by (auto simp: dfs_wf_def dfs_seenK_def tree_seen_inv_def)
  ultimately show ?thesis
    using assms(2,4) unfolding par_edge_inv_def
    by (cases "ds_seen s ! w") (auto simp: dfs_sized_def dfs_discover_def dfs_push_def Let_def nth_list_update)
qed

lemma bd_upd2_pei:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "par_edge_inv fl s" "bd_call2_conds fl s"
  shows "par_edge_inv fl (bd_upd2 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "e < m" "snd_list ! e = v" "fst_list ! e = w"
    "is_free fl e" "w < vcount"
    and up: "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF assms(1,5)])
  moreover from this(1) assms(1,3) have "v < vcount" "ds_seen s ! v"
    by (auto simp: dfs_wf_def dfs_seenK_def tree_seen_inv_def)
  ultimately show ?thesis
    using assms(2,4) unfolding par_edge_inv_def
    by (cases "ds_seen s ! w") (auto simp: dfs_sized_def dfs_discover_def dfs_push_def Let_def nth_list_update)
qed

section \<open>The potential invariant (I4)\<close>

text \<open>Design-notes clause I4, at the tagged-pair (\<open>pval\<close>) level for the interior tree
      edges. Every visited non-root vertex @{term w} with an interior parent (\<open>prnt < vcount\<close>)
      has its potential obtained from its parent's by adding an \<open>M_0\<close>-tagged
      \<open>\<plusminus> cost_list ! (ds_par s ! w)\<close>, the sign chosen so the tree edge
      \<open>ds_par s ! w\<close> has zero reduced cost: \<open>+ cost\<close> when @{term w}'s parent is the
      edge's tail, \<open>- cost\<close> otherwise. This is exactly the update @{const dfs_discover} performs
      (its \<open>sgn\<close> formula is syntactically this one, with \<open>v = ds_prnt s ! w\<close> and
      \<open>e = ds_par s ! w\<close>), and potentials are never rewritten, so the equation persists. The
      \<open>pval_abstract\<close>-level zero-reduced-cost \<open>c-pi (ds_par s ! w) = 0\<close> follows once
      the faithful decomposition (\<open>good_pot_val\<close>) is available at \<open>arb_invar\<close>
      assembly. Component roots (\<open>prnt = vcount\<close>) are excluded; their potential is seeded to a
      big-\<open>M\<close> tagged value.\<close>

definition pot_inv :: "'n dfs_state \<Rightarrow> bool" where
  "pot_inv s \<longleftrightarrow>
     (\<forall>w<vcount. ds_seen s ! w \<longrightarrow> ds_prnt s ! w < vcount \<longrightarrow>
        ds_pot s ! w = pval_plus (ds_pot s ! (ds_prnt s ! w))
           (M_0, if ds_prnt s ! w = fst_list ! (ds_par s ! w)
                 then cost_list ! (ds_par s ! w) else - cost_list ! (ds_par s ! w)))"

lemma bd_upd3_pot: "\<lbrakk>pot_inv s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> pot_inv (bd_upd3 s)"
  by (erule bd_upd3_eq) (auto simp: pot_inv_def dfs_finish_def Let_def)

text \<open>The potential invariant survives any update that writes only the fresh, unseen slot @{term c}
      and either leaves it out of the invariant (a component root, whose parent is the root) or makes
      it a child of a seen vertex with exactly the invariant's potential: no earlier vertex has
      @{term c} as parent, so every earlier equation survives.\<close>

lemma pot_inv_fresh:
  assumes "pot_inv s" "tree_seen_inv s" "c < vcount" "\<not> ds_seen s ! c"
    "ds_prnt t ! c < vcount \<Longrightarrow> ds_pot t ! c = pval_plus (ds_pot t ! (ds_prnt t ! c))
       (M_0, if ds_prnt t ! c = fst_list ! (ds_par t ! c) then cost_list ! (ds_par t ! c)
             else - cost_list ! (ds_par t ! c))"
    "\<And>i. i \<noteq> c \<Longrightarrow> ds_seen t ! i = ds_seen s ! i" "\<And>i. i \<noteq> c \<Longrightarrow> ds_prnt t ! i = ds_prnt s ! i"
    "\<And>i. i \<noteq> c \<Longrightarrow> ds_par t ! i = ds_par s ! i" "\<And>i. i \<noteq> c \<Longrightarrow> ds_pot t ! i = ds_pot s ! i"
  shows "pot_inv t"
  unfolding pot_inv_def
proof(intro allI impI)
  fix w assume w: "w < vcount" "ds_seen t ! w" "ds_prnt t ! w < vcount"
  show "ds_pot t ! w = pval_plus (ds_pot t ! (ds_prnt t ! w))
          (M_0, if ds_prnt t ! w = fst_list ! (ds_par t ! w)
                then cost_list ! (ds_par t ! w) else - cost_list ! (ds_par t ! w))"
  proof(cases "w = c")
    case False
    with w assms(6,7) have "ds_seen s ! w" "ds_prnt s ! w < vcount" by simp_all
    moreover from this w(1) assms(2,4) have "ds_prnt s ! w \<noteq> c" by (auto simp: tree_seen_inv_def)
    ultimately show ?thesis using w(1) False assms(1,7-9) by (simp add: pot_inv_def)
  qed (use w assms(5) in simp)
qed

lemma dfs_discover_pot:
  "\<lbrakk>pot_inv s; tree_seen_inv s; dfs_sized s; ds_seen s ! v; w < vcount; \<not> ds_seen s ! w\<rbrakk>
   \<Longrightarrow> pot_inv (dfs_discover s v w e)"
  by (erule pot_inv_fresh, assumption+)
    (auto simp: dfs_sized_def dfs_discover_def dfs_push_def Let_def nth_list_update)

lemma bd_upd1_pot:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "pot_inv s" "bd_call1_conds fl s"
  shows "pot_inv (bd_upd1 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF assms(1,5)])
  moreover from this(1) assms(3) have "ds_seen s ! v" by (auto simp: tree_seen_inv_def)
  moreover have "pot_inv (s\<lparr>ds_oc := c'\<rparr>)" "tree_seen_inv (s\<lparr>ds_oc := c'\<rparr>)" "dfs_sized (s\<lparr>ds_oc := c'\<rparr>)"
    using assms(2-4) by (simp_all add: pot_inv_def tree_seen_inv_def dfs_sized_def)
  ultimately show ?thesis using dfs_discover_pot[of "s\<lparr>ds_oc := c'\<rparr>" v w e] by simp
qed

lemma bd_upd2_pot:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "pot_inv s" "bd_call2_conds fl s"
  shows "pot_inv (bd_upd2 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF assms(1,5)])
  moreover from this(1) assms(3) have "ds_seen s ! v" by (auto simp: tree_seen_inv_def)
  moreover have "pot_inv (s\<lparr>ds_ic := c'\<rparr>)" "tree_seen_inv (s\<lparr>ds_ic := c'\<rparr>)" "dfs_sized (s\<lparr>ds_ic := c'\<rparr>)"
    using assms(2-4) by (simp_all add: pot_inv_def tree_seen_inv_def dfs_sized_def)
  ultimately show ?thesis using dfs_discover_pot[of "s\<lparr>ds_ic := c'\<rparr>" v w e] by simp
qed

text \<open>The potential invariant is preserved by opening a component at an unseen @{term c}: only the
      single fresh slot @{term c} is written (its parent becomes the root, so it is excluded), and no
      previously-emitted vertex's parent is @{term c}, so every earlier equation survives.\<close>

lemma pot_inv_seed:
  "\<lbrakk>pot_inv s; tree_seen_inv s; c < vcount; \<not> ds_seen s ! c; ds_prnt t ! c = vcount;
    \<And>i. i \<noteq> c \<Longrightarrow> ds_seen t ! i = ds_seen s ! i; \<And>i. i \<noteq> c \<Longrightarrow> ds_prnt t ! i = ds_prnt s ! i;
    \<And>i. i \<noteq> c \<Longrightarrow> ds_par t ! i = ds_par s ! i; \<And>i. i \<noteq> c \<Longrightarrow> ds_pot t ! i = ds_pot s ! i\<rbrakk>
   \<Longrightarrow> pot_inv t"
  by (erule pot_inv_fresh) auto

section \<open>The root-potential invariant (I1)\<close>

text \<open>Design-notes clause I1 for the root: @{term \<open>ds_pot s ! vcount = pval_zero\<close>}. The
      root is seeded with zero potential by @{const dfs_init} and every state transformer writes
      @{const ds_pot} only at real vertices (\<open>< vcount\<close>) --- discovery at the fresh child,
      component-opening at the new root @{term c} --- or not at all, so the root potential is never disturbed.
      This discharges the @{term \<open>\<pi> r = 0\<close>} half of \<open>init_pot_fits\<close>.\<close>

definition root_pot_inv :: "'n dfs_state \<Rightarrow> bool" where
  "root_pot_inv s \<longleftrightarrow> ds_pot s ! vcount = pval_zero"

lemma dfs_discover_rpi:
  "\<lbrakk>root_pot_inv s; w < vcount\<rbrakk> \<Longrightarrow> root_pot_inv (dfs_discover s v w e)"
  by (simp add: root_pot_inv_def dfs_discover_def dfs_push_def Let_def nth_list_update)

lemma bd_upd1_rpi:
  "\<lbrakk>dfs_wf fl s; root_pot_inv s; bd_call1_conds fl s\<rbrakk> \<Longrightarrow> root_pot_inv (bd_upd1 fl s)"
  by (erule bd_upd1_eq, assumption) (auto simp: root_pot_inv_def dfs_discover_def dfs_push_def Let_def)

lemma bd_upd2_rpi:
  "\<lbrakk>dfs_wf fl s; root_pot_inv s; bd_call2_conds fl s\<rbrakk> \<Longrightarrow> root_pot_inv (bd_upd2 fl s)"
  by (erule bd_upd2_eq, assumption) (auto simp: root_pot_inv_def dfs_discover_def dfs_push_def Let_def)

lemma bd_upd3_rpi: "\<lbrakk>root_pot_inv s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> root_pot_inv (bd_upd3 s)"
  by (erule bd_upd3_eq) (simp add: root_pot_inv_def dfs_finish_def Let_def)

section \<open>The stack-chain invariant (structural core of I6)\<close>

text \<open>The explicit DFS stack is, read top-to-bottom, exactly a @{const ds_prnt}-chain ending at the
      root: the parent of each frame's vertex is the vertex of the frame below it, and the bottom frame's
      vertex (a component root) has the root @{term vcount} as parent. This is the array-level heart of the
      DFS-preorder step (design-notes I6): when a vertex is discovered from the stack top @{term v} its parent
      is set to @{term v}, and @{term v} is an ancestor of the last-emitted vertex; when a component is opened
      its parent is the root, which every root-path reaches. The full preorder step / clause J then follows at
      \<open>arb_invar\<close> assembly, where the emission order (thread) and the abstract root-path
      (\<open>follow\<close>) are available. The stack is empty at @{const build_tree}, so this invariant is a
      \<^emph>\<open>traversal\<close> invariant (it constrains intermediate states, not the finished tree
      directly).\<close>

fun \<^marker>\<open>provenance ai_human\<close> vchain :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "vchain P [] = True"
| "vchain P [v] = (P ! v = vcount)"
| "vchain P (v # u # rest) = (P ! v = u \<and> vchain P (u # rest))"

lemma vchain_cong:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P ! x = Q ! x) \<Longrightarrow> vchain P xs = vchain Q xs"
  by (induction xs rule: vchain.induct) auto

lemma vchain_tl: "vchain P (v # vs) \<Longrightarrow> vchain P vs"
  by (cases vs) auto

definition stk_prnt_inv :: "'n dfs_state \<Rightarrow> bool" where
  "stk_prnt_inv s \<longleftrightarrow> vchain (ds_prnt s) (ds_stk s)"

lemma bd_upd3_spi: "\<lbrakk>stk_prnt_inv s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> stk_prnt_inv (bd_upd3 s)"
  by (erule bd_upd3_eq) (auto simp: stk_prnt_inv_def dfs_finish_def Let_def dest: vchain_tl)

lemma dfs_discover_spi:
  "\<lbrakk>stk_prnt_inv s; tree_seen_inv s; length (ds_prnt s) = Suc vcount; ds_stk s = v # rest; w < vcount;
    \<not> ds_seen s ! w\<rbrakk> \<Longrightarrow> stk_prnt_inv (dfs_discover s v w e)"
  unfolding stk_prnt_inv_def tree_seen_inv_def dfs_discover_def dfs_push_def Let_def
  by (auto simp: nth_list_update elim!: vchain_cong[THEN iffD1, rotated])

lemma bd_upd1_spi:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "bd_call1_conds fl s"
  shows "stk_prnt_inv (bd_upd1 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF assms(1,5)])
  moreover have "stk_prnt_inv (s\<lparr>ds_oc := c'\<rparr>)" "tree_seen_inv (s\<lparr>ds_oc := c'\<rparr>)"
    using assms(3,4) by (simp_all add: stk_prnt_inv_def tree_seen_inv_def)
  ultimately show ?thesis
    using dfs_discover_spi[of "s\<lparr>ds_oc := c'\<rparr>" v rest w e] assms(2) by (simp add: dfs_sized_def)
qed

lemma bd_upd2_spi:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "bd_call2_conds fl s"
  shows "stk_prnt_inv (bd_upd2 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF assms(1,5)])
  moreover have "stk_prnt_inv (s\<lparr>ds_ic := c'\<rparr>)" "tree_seen_inv (s\<lparr>ds_ic := c'\<rparr>)"
    using assms(3,4) by (simp_all add: stk_prnt_inv_def tree_seen_inv_def)
  ultimately show ?thesis
    using dfs_discover_spi[of "s\<lparr>ds_ic := c'\<rparr>" v rest w e] assms(2) by (simp add: dfs_sized_def)
qed

section \<open>Emission-order invariant (I6, full DFS step)\<close>
text \<open>The full design-notes clause I6 (the preorder DFS step of \<open>preorder_contiguous\<close>): the
      abstract parent of every emitted vertex is an \<^emph>\<open>ancestor\<close> of its thread-predecessor.
      We phrase ancestry via the parent-step relation @{term pstep} --- the child{\isasymrightarrow}parent
      edges of the currently emitted vertices --- whose reflexive-transitive closure is exactly the root-path
      (\<open>follow\<close>) once the abstract tree is assembled. The relation only ever
      \<^emph>\<open>grows\<close> (one edge per emission), so old ancestry facts persist; the emission-order
      pair is discharged at each discovery by the fact that the stack top is an ancestor of the last-emitted
      vertex.

      The bundled invariant @{term emit_ord_inv} carries three clauses: every emitted vertex reaches the root
      @{term vcount} (reaches-root); the stack top is an ancestor of @{const ds_prev} (stack-descends); and
      the target @{term \<open>(ds_rvth s ! w, ds_prnt s ! w) \<in> (pstep s)\<^sup>*\<close>}
      (emission-order). The three are proved together because their maintenance steps feed one another (a
      discovery uses stack-descends for the new pair and reaches-root of the parent for the new reaches-root
      fact).\<close>

definition pstep :: "'n dfs_state \<Rightarrow> (nat \<times> nat) set" where
  "pstep s = {(x, ds_prnt s ! x) |x. x < vcount \<and> ds_seen s ! x}"

lemma pstep_upd:
  "\<lbrakk>ds_prnt t = (ds_prnt s)[w := v]; ds_seen t = (ds_seen s)[w := True]; w < vcount; \<not> ds_seen s ! w;
    length (ds_seen s) = Suc vcount; length (ds_prnt s) = Suc vcount\<rbrakk>
   \<Longrightarrow> pstep t = insert (w, v) (pstep s)"
  by (auto simp: pstep_def nth_list_update split: if_splits)

lemma pstep_cong: "\<lbrakk>ds_prnt s = ds_prnt t; ds_seen s = ds_seen t\<rbrakk> \<Longrightarrow> pstep s = pstep t"
  by (simp add: pstep_def)

definition emit_ord_inv :: "'n dfs_state \<Rightarrow> bool" where
  "emit_ord_inv s \<longleftrightarrow>
     (\<forall>x < vcount. ds_seen s ! x \<longrightarrow> (x, vcount) \<in> (pstep s)\<^sup>*)
   \<and> (ds_stk s \<noteq> [] \<longrightarrow> (ds_prev s, hd (ds_stk s)) \<in> (pstep s)\<^sup>*)
   \<and> (\<forall>w < vcount. ds_seen s ! w \<longrightarrow> (ds_rvth s ! w, ds_prnt s ! w) \<in> (pstep s)\<^sup>*)"

lemma bd_upd3_eoi:
  assumes "dfs_wf fl s" "tree_seen_inv s" "stk_prnt_inv s" "emit_ord_inv s" "bd_call3_conds fl s"
  shows "emit_ord_inv (bd_upd3 s)"
proof-
  obtain v rest where stk: "ds_stk s = v # rest" and up: "bd_upd3 s = dfs_finish s v rest"
    by (rule bd_upd3_eq[OF assms(5)])
  have "pstep (bd_upd3 s) = pstep s" by (simp add: up pstep_def dfs_finish_def Let_def)
  moreover have "(ds_prev s, hd rest) \<in> (pstep s)\<^sup>*" if "rest \<noteq> []"
  proof-
    from stk assms(1,2) have "v < vcount" "ds_seen s ! v" by (auto simp: dfs_wf_def dfs_seenK_def tree_seen_inv_def)
    moreover have "ds_prnt s ! v = hd rest" using that stk assms(3) by (cases rest) (simp_all add: stk_prnt_inv_def)
    ultimately have "(v, hd rest) \<in> pstep s" by (auto simp: pstep_def)
    with stk assms(4) show ?thesis by (auto simp: emit_ord_inv_def pstep_def intro: rtrancl_into_rtrancl)
  qed
  ultimately show ?thesis using assms(4) by (simp add: up emit_ord_inv_def dfs_finish_def Let_def)
qed

text \<open>The generic emission step: a fresh vertex @{term w} is attached below a parent @{term p} that
      reaches the root and is an ancestor of the last-emitted vertex. Both a free-edge discovery
      (\<open>p\<close> the stack top) and a component opening (\<open>p\<close> the root) are instances.\<close>

lemma emit_ord_inv_upd:
  assumes "emit_ord_inv s" "w < vcount" "\<not> ds_seen s ! w" "length (ds_seen s) = Suc vcount"
    "length (ds_prnt s) = Suc vcount" "length (ds_rvth s) = Suc vcount"
    "(p, vcount) \<in> (pstep s)\<^sup>*" "(ds_prev s, p) \<in> (pstep s)\<^sup>*"
    "ds_prnt t = (ds_prnt s)[w := p]" "ds_seen t = (ds_seen s)[w := True]"
    "ds_rvth t = (ds_rvth s)[w := ds_prev s]" "ds_prev t = w" "hd (ds_stk t) = w"
  shows "emit_ord_inv t"
proof-
  have pe: "pstep t = insert (w, p) (pstep s)" by (rule pstep_upd[OF assms(9,10,2-5)])
  then have mono: "(pstep s)\<^sup>* \<subseteq> (pstep t)\<^sup>*" by (intro rtrancl_mono) auto
  with assms mono pe show ?thesis
    unfolding emit_ord_inv_def 
    by (auto intro: converse_rtrancl_into_rtrancl simp: nth_list_update split: if_splits)
qed

lemma dfs_discover_eoi:
  "\<lbrakk>emit_ord_inv s; dfs_sized s; ds_stk s = v # rest; v < vcount; ds_seen s ! v; w < vcount;
    \<not> ds_seen s ! w\<rbrakk> \<Longrightarrow> emit_ord_inv (dfs_discover s v w e)"
  by (rule emit_ord_inv_upd[where w = w and p = v])
    (simp_all add: emit_ord_inv_def dfs_sized_def dfs_discover_def dfs_push_def Let_def)

lemma bd_upd1_eoi:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "emit_ord_inv s" "bd_call1_conds fl s"
  shows "emit_ord_inv (bd_upd1 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF assms(1,5)])
  thus ?thesis 
    using dfs_discover_eoi[of "s\<lparr>ds_oc := c'\<rparr>" v rest w e] assms
    by (auto simp add: dfs_wf_def dfs_seenK_def tree_seen_inv_def emit_ord_inv_def
                       pstep_def dfs_sized_def)
qed

lemma bd_upd2_eoi:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "emit_ord_inv s" "bd_call2_conds fl s"
  shows "emit_ord_inv (bd_upd2 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF assms(1,5)])
  thus ?thesis using dfs_discover_eoi[of "s\<lparr>ds_ic := c'\<rparr>" v rest w e] 
    using assms by (auto simp add: dfs_wf_def dfs_seenK_def 
                         tree_seen_inv_def emit_ord_inv_def pstep_def dfs_sized_def)
qed

lemma emit_ord_inv_seed:
  "\<lbrakk>emit_ord_inv s; thread_inv s; c < vcount; \<not> ds_seen s ! c; length (ds_seen s) = Suc vcount;
    length (ds_prnt s) = Suc vcount; length (ds_rvth s) = Suc vcount; ds_prnt t = (ds_prnt s)[c := vcount];
    ds_seen t = (ds_seen s)[c := True]; ds_rvth t = (ds_rvth s)[c := ds_prev s]; ds_prev t = c;
    ds_stk t = [c]\<rbrakk> \<Longrightarrow> emit_ord_inv t"
  by (rule emit_ord_inv_upd[where w = c and p = vcount])
    (simp_all, (cases "ds_prev s = vcount"; auto simp: thread_inv_def emit_ord_inv_def))

lemma emit_U_edge_eoi: "emit_ord_inv s \<Longrightarrow> emit_ord_inv (emit_U_edge s v)"
  by (auto simp: emit_ord_inv_def pstep_def emit_U_edge_def Let_def)

lemma dfs_init_eoi: "emit_ord_inv dfs_init"
  by (auto simp: emit_ord_inv_def dfs_init_def simp del: replicate_Suc)

section \<open>Subtree bookkeeping (I7): descendant sets and subtree sizes\<close>

text \<open>Design-notes clause I7: when a vertex @{term v} finishes, @{term \<open>ds_snum s ! v\<close>} is
      the size of its subtree and @{term \<open>ds_lsuc s ! v\<close>} its last preorder descendant. We phrase
      the subtree as the set @{term \<open>desc s v\<close>} of emitted @{const pstep}-descendants (the array
      counterpart of the abstract @{text children}). @{const ds_snum} is established
      \<^emph>\<open>at finish\<close>: it is seeded to @{term 1} on discovery and accumulates a child's
      subtree size into its parent when the child pops. The proof threads two facts over the DFS stack: a
      finished vertex's @{const ds_snum} equals its descendant count, and --- telescoping down the stack
      (\<open>snchk\<close>) --- every frame's descendant count equals the running sum of @{const ds_snum}
      over it and the frames above it. A discovery adds the fresh vertex to exactly the descendant sets of the
      current stack vertices (its ancestors), so each frame's count rises by one; a finish reads the top
      frame's count off the telescoping base and credits it upward.\<close>

definition desc :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat set" where
  "desc s v = {u. u < vcount \<and> ds_seen s ! u \<and> (u, v) \<in> (pstep s)\<^sup>*}"

definition dcard :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat" where
  "dcard s v = card (desc s v)"

definition stkverts :: "'n dfs_state \<Rightarrow> nat set" where
  "stkverts s = set ((ds_stk s))"

lemma desc_finite: "finite (desc s v)"
  by (rule finite_subset[of _ "{0..<vcount}"]) (auto simp: desc_def)

lemma desc_sub: "desc s v \<subseteq> {0..<vcount}"
  by (auto simp: desc_def)

lemma pstep_single_valued: "single_valued (pstep s)"
  by (auto simp: single_valued_def pstep_def)

lemma pstep_no_in:
  "\<lbrakk>tree_seen_inv s; w < vcount; \<not> ds_seen s ! w\<rbrakk> \<Longrightarrow> (a, w) \<notin> pstep s"
  by (auto simp: pstep_def tree_seen_inv_def)

lemma pstep_to_w:
  "\<lbrakk>\<And>a. (a, w) \<notin> pstep s; (u, w) \<in> (pstep s)\<^sup>*\<rbrakk> \<Longrightarrow> u = w"
  by (erule rtranclE) auto

lemma pstep_reach_avoid_w:
  "\<lbrakk>\<And>a. (a, w) \<notin> pstep s; P' = insert (w, v0) (pstep s); (u, x) \<in> P'\<^sup>*; u \<noteq> w\<rbrakk> \<Longrightarrow> (u, x) \<in> (pstep s)\<^sup>*"
  by (rotate_tac 2, induction rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl dest: pstep_to_w[rotated])

lemma pstep_from_root: "(vcount, x) \<in> (pstep s)\<^sup>* \<Longrightarrow> x = vcount"
  by (erule converse_rtranclE) (auto simp: pstep_def)

lemma vchain_parent_step:
  "\<lbrakk>vchain P xs; y \<in> set xs\<rbrakk> \<Longrightarrow> P ! y \<in> set xs \<or> P ! y = vcount"
  by (induction P xs rule: vchain.induct) auto

lemma stkverts_parent:
  "\<lbrakk>stk_prnt_inv s; y \<in> stkverts s\<rbrakk> \<Longrightarrow> ds_prnt s ! y \<in> stkverts s \<or> ds_prnt s ! y = vcount"
  by (simp add: stk_prnt_inv_def stkverts_def vchain_parent_step)

lemma pstep_anc_on_stk:
  "\<lbrakk>stk_prnt_inv s; v0 \<in> stkverts s; (v0, x) \<in> (pstep s)\<^sup>*\<rbrakk> \<Longrightarrow> x \<in> stkverts s \<or> x = vcount"
  by (rotate_tac 2, induction rule: rtrancl_induct) (auto simp: pstep_def dest: stkverts_parent)

lemma vchain_hd_reaches:
  "\<lbrakk>vchain (ds_prnt s) (a # xs); \<And>y. y \<in> set (a # xs) \<Longrightarrow> y < vcount \<and> ds_seen s ! y; x \<in> set (a # xs)\<rbrakk>
   \<Longrightarrow> (a, x) \<in> (pstep s)\<^sup>*"
  by(induction xs arbitrary: a)
   (auto intro: converse_rtrancl_into_rtrancl simp: pstep_def)

lemma stkverts_props:
  "\<lbrakk>dfs_wf fl s; y \<in> stkverts s\<rbrakk> \<Longrightarrow> y < vcount \<and> ds_seen s ! y"
  by (auto simp: dfs_wf_def dfs_seenK_def stkverts_def)

lemma stk_top_reaches:
  "\<lbrakk>stk_prnt_inv s; dfs_wf fl s; ds_stk s = v0 # rest; x \<in> stkverts s\<rbrakk> \<Longrightarrow> (v0, x) \<in> (pstep s)\<^sup>*"
  by (rule vchain_hd_reaches) (auto simp: stk_prnt_inv_def stkverts_def dfs_wf_def dfs_seenK_def)

text \<open>How @{const desc} changes on a discovery from stack top @{term v0} to fresh @{term w}: the fresh
      vertex is added to exactly the descendant sets of @{term w}'s ancestors (@{term w} itself and every
      vertex @{term v0} reaches), and nothing else.\<close>

lemma desc_discover:
  assumes "tree_seen_inv s" "w < vcount" "\<not> ds_seen s ! w" "v0 \<noteq> w"
    "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
    "ds_prnt s' = (ds_prnt s)[w := v0]" "ds_seen s' = (ds_seen s)[w := True]"
  shows "desc s' x = (if x = w \<or> (v0, x) \<in> (pstep s)\<^sup>* then insert w (desc s x) else desc s x)"
proof-
  have pe: "pstep s' = insert (w, v0) (pstep s)" 
    by (rule pstep_upd[OF assms(7,8,2,3,5,6)])
  then have mono: "(pstep s)\<^sup>* \<subseteq> (pstep s')\<^sup>*" 
    by (intro rtrancl_mono) auto
  have noin: "\<And>a. (a, w) \<notin> pstep s"
    by (rule pstep_no_in[OF assms(1-3)])
  have "(w, x) \<in> (pstep s')\<^sup>* \<longleftrightarrow> x = w \<or> (v0, x) \<in> (pstep s)\<^sup>*"
  proof
    assume "(w, x) \<in> (pstep s')\<^sup>*"
    then show "x = w \<or> (v0, x) \<in> (pstep s)\<^sup>*"
    proof(cases rule: converse_rtranclE)
      case (step y)
      with pe assms(3)  step pstep_reach_avoid_w[OF noin pe] assms(4) 
      show ?thesis 
        by (auto simp: pstep_def)
    qed simp
  next
    assume "x = w \<or> (v0, x) \<in> (pstep s)\<^sup>*"
    with pe mono show "(w, x) \<in> (pstep s')\<^sup>*" 
      by (auto intro: converse_rtrancl_into_rtrancl)
  qed
  moreover have "w \<notin> desc s x" 
    using assms(3) by (auto simp: desc_def)
  moreover have "u \<in> desc s' x \<longleftrightarrow> (u = w \<and> (w, x) \<in> (pstep s')\<^sup>*) \<or> u \<in> desc s x" for u
    using assms(2,3,5,8) pe pstep_reach_avoid_w[OF noin pe] mono
    by (cases "u = w") (auto simp: desc_def nth_list_update)
  ultimately show ?thesis by (auto simp: set_eq_iff)
qed

lemma desc_fresh_empty:
  "\<lbrakk>tree_seen_inv s; w < vcount; \<not> ds_seen s ! w\<rbrakk> \<Longrightarrow> desc s w = {}"
  by (auto simp: desc_def dest: pstep_to_w[OF pstep_no_in, rotated 3])

fun \<^marker>\<open>provenance ai_human\<close> snchk :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "snchk s acc [] = True"
| "snchk s acc (v # rest) = (dcard s v = ds_snum s ! v + acc \<and> snchk s (dcard s v) rest)"

lemma snchk_cong:
  "(\<And>v. v \<in> set xs \<Longrightarrow> dcard s' v = dcard s v \<and> ds_snum s' ! v = ds_snum s ! v)
   \<Longrightarrow> snchk s' acc xs = snchk s acc xs"
  by (induction xs arbitrary: acc) auto

lemma snchk_incr:
  "(\<And>v. v \<in> set xs \<Longrightarrow> dcard s' v = Suc (dcard s v) \<and> ds_snum s' ! v = ds_snum s ! v)
   \<Longrightarrow> snchk s' (Suc acc) xs = snchk s acc xs"
  by (induction xs arbitrary: acc) auto

definition snum_inv :: "'n dfs_state \<Rightarrow> bool" where
  "snum_inv s \<longleftrightarrow>
     distinct ((ds_stk s))
   \<and> (\<forall>v < vcount. ds_seen s ! v \<longrightarrow> v \<notin> stkverts s \<longrightarrow> ds_snum s ! v = dcard s v)
   \<and> snchk s 0 ((ds_stk s))"

lemma snum_inv_cong:
  "\<lbrakk>ds_prnt t = ds_prnt s; ds_seen t = ds_seen s; ds_snum t = ds_snum s; ds_stk t = ds_stk s; snum_inv s\<rbrakk>
    \<Longrightarrow> snum_inv t"
  using snchk_cong[of "ds_stk s" t s 0] pstep_cong[of t s]
  by (simp add: snum_inv_def stkverts_def dcard_def desc_def)

lemma dfs_discover_sni:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "snum_inv s" "ds_stk s = v # rest"
    "w < vcount" "\<not> ds_seen s ! w"
  shows "snum_inv (dfs_discover s v w e)"
proof-
  let ?t = "dfs_discover s v w e"
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount" "length (ds_snum s) = Suc vcount"
    using assms(2) by (simp_all add: dfs_sized_def)
  have "ds_seen s ! v" using assms(3,6) by (auto simp: tree_seen_inv_def)
  with assms(8) have vne: "v \<noteq> w" by auto
  have wnstk: "w \<notin> stkverts s" using assms(8) stkverts_props[OF assms(1)] by auto
  have ef: "ds_prnt ?t = (ds_prnt s)[w := v]" "ds_seen ?t = (ds_seen s)[w := True]"
    "ds_snum ?t = (ds_snum s)[w := 1]" "ds_stk ?t = w # ds_stk s"
    by (simp_all add: dfs_discover_def dfs_push_def Let_def)
  note DD = desc_discover[OF assms(3,7,8) vne lens(1,2) ef(1,2)]
  have wnd: "w \<notin> desc s x" for x using assms(8) by (auto simp: desc_def)
  have incr: "dcard ?t x = Suc (dcard s x) \<and> ds_snum ?t ! x = ds_snum s ! x" if "x \<in> set (ds_stk s)" for x
    using that wnstk DD[of x] wnd[of x] desc_finite stk_top_reaches[OF assms(4,1,6), of x] ef(3)
    by (cases "x = w") (auto simp: dcard_def stkverts_def)
  show ?thesis
    unfolding snum_inv_def
  proof(intro conjI allI impI)
    show "distinct (ds_stk ?t)" using ef(4) assms(5) wnstk by (simp add: snum_inv_def stkverts_def)
  next
    fix x assume x: "x < vcount" "ds_seen ?t ! x" "x \<notin> stkverts ?t"
    then have "x \<noteq> w" "x \<notin> stkverts s" "ds_seen s ! x"
      using ef(2,4) lens by (auto simp: stkverts_def nth_list_update)
    moreover from this(2) have "(v, x) \<notin> (pstep s)\<^sup>*"
      using pstep_anc_on_stk[OF assms(4), of v x] assms(6) x(1) by (auto simp: stkverts_def)
    ultimately show "ds_snum ?t ! x = dcard ?t x"
      using x(1) assms(5) DD[of x] ef(3) by (auto simp: snum_inv_def dcard_def nth_list_update)
  next
    have "snchk ?t (Suc 0) (ds_stk s)" using assms(5) snchk_incr[OF incr] by (simp add: snum_inv_def)
    moreover have "dcard ?t w = 1" using DD[of w] desc_fresh_empty[OF assms(3,7,8)] by (simp add: dcard_def)
    ultimately show "snchk ?t 0 (ds_stk ?t)" using ef(3,4) assms(7) lens by (simp add: nth_list_update)
  qed
qed

lemma bd_upd1_sni:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "snum_inv s" "bd_call1_conds fl s"
  shows "snum_inv (bd_upd1 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount" "dfs_wf fl (s\<lparr>ds_oc := c'\<rparr>)"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF assms(1,6)])
  moreover have "dfs_sized (s\<lparr>ds_oc := c'\<rparr>)" "tree_seen_inv (s\<lparr>ds_oc := c'\<rparr>)"
    "stk_prnt_inv (s\<lparr>ds_oc := c'\<rparr>)" "snum_inv (s\<lparr>ds_oc := c'\<rparr>)"
    using assms(2-5) snum_inv_cong[of "s\<lparr>ds_oc := c'\<rparr>" s]
    by (simp_all add: dfs_sized_def tree_seen_inv_def stk_prnt_inv_def)
  ultimately show ?thesis using dfs_discover_sni[of fl "s\<lparr>ds_oc := c'\<rparr>" v rest w e] by simp
qed

lemma bd_upd2_sni:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "snum_inv s" "bd_call2_conds fl s"
  shows "snum_inv (bd_upd2 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount" "dfs_wf fl (s\<lparr>ds_ic := c'\<rparr>)"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF assms(1,6)])
  moreover have "dfs_sized (s\<lparr>ds_ic := c'\<rparr>)" "tree_seen_inv (s\<lparr>ds_ic := c'\<rparr>)"
    "stk_prnt_inv (s\<lparr>ds_ic := c'\<rparr>)" "snum_inv (s\<lparr>ds_ic := c'\<rparr>)"
    using assms(2-5) snum_inv_cong[of "s\<lparr>ds_ic := c'\<rparr>" s]
    by (simp_all add: dfs_sized_def tree_seen_inv_def stk_prnt_inv_def)
  ultimately show ?thesis using dfs_discover_sni[of fl "s\<lparr>ds_ic := c'\<rparr>" v rest w e] by simp
qed

lemma bd_upd3_sni:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "snum_inv s" "bd_call3_conds fl s"
  shows "snum_inv (bd_upd3 s)"
proof-
  obtain v rest where stk: "ds_stk s = v # rest" by (rule bd_upd3_eq[OF assms(6)])
  let ?pp = "ds_prnt s ! v" and ?t = "bd_upd3 s"
  have ef: "ds_prnt ?t = ds_prnt s" "ds_seen ?t = ds_seen s"
    "ds_snum ?t = (ds_snum s)[?pp := ds_snum s ! ?pp + ds_snum s ! v]" "ds_stk ?t = rest"
    using stk by (simp_all add: bd_upd3_def dfs_finish_def Let_def)
  have dc: "dcard ?t x = dcard s x" for x using pstep_cong[OF ef(1,2)] by (simp add: dcard_def desc_def ef(2))
  have pp: "?pp = (case rest of [] \<Rightarrow> vcount | g # _ \<Rightarrow> g)"
    using assms(4) stk by (cases rest) (simp_all add: stk_prnt_inv_def)
  from assms(5) stk have dist: "distinct (v # rest)"
    and sn1: "\<forall>x<vcount. ds_seen s ! x \<longrightarrow> x \<notin> stkverts s \<longrightarrow> ds_snum s ! x = dcard s x"
    and snv: "dcard s v = ds_snum s ! v" and tail: "snchk s (ds_snum s ! v) rest"
    by (auto simp: snum_inv_def)
  have "v < vcount" using assms(1) stk by (auto simp: dfs_wf_def dfs_seenK_def)
  show ?thesis
    unfolding snum_inv_def
  proof(intro conjI allI impI)
    show "distinct (ds_stk ?t)" using dist ef(4) by simp
  next
    fix x assume x: "x < vcount" "ds_seen ?t ! x" "x \<notin> stkverts ?t"
    then have xr: "x \<notin> set rest" using ef(4) by (simp add: stkverts_def)
    show "ds_snum ?t ! x = dcard ?t x"
    proof(cases "x = v")
      case True
      with pp dist \<open>v < vcount\<close> have "?pp \<noteq> v" by (cases rest) auto
      with True ef(3) snv dc show ?thesis by simp
    next
      case False
      with xr stk have "x \<notin> stkverts s" by (simp add: stkverts_def)
      moreover have "?pp \<noteq> x" using pp xr x(1) by (cases rest) auto
      ultimately show ?thesis using sn1 x ef(2,3) dc by simp
    qed
  next
    show "snchk ?t 0 (ds_stk ?t)"
    proof(cases rest)
      case (Cons g gs)
      with pp have pg: "?pp = g" by simp
      have "snchk ?t (dcard s g) gs = snchk s (dcard s g) gs"
      proof(rule snchk_cong)
        fix y assume "y \<in> set gs"
        with dist Cons have "y \<noteq> g" by auto
        with pg ef(3) dc show "dcard ?t y = dcard s y \<and> ds_snum ?t ! y = ds_snum s ! y" by simp
      qed
      moreover have "g < length (ds_snum s)"
        using Cons stk stkverts_props[OF assms(1), of g] assms(2) by (simp add: stkverts_def dfs_sized_def)
      ultimately show ?thesis using tail Cons pg ef(3,4) dc by (auto simp: nth_list_update)
    qed (simp add: ef(4))
  qed
qed

lemma emit_U_edge_sni: "snum_inv s \<Longrightarrow> snum_inv (emit_U_edge s v)"
  by (rule snum_inv_cong[where s = s]) (simp_all add: emit_U_edge_def Let_def)

lemma dfs_init_sni: "snum_inv dfs_init"
  by (auto simp: snum_inv_def stkverts_def dfs_init_def simp del: replicate_Suc)

lemma snum_inv_seed:
  assumes "snum_inv s" "tree_seen_inv s" "c < vcount" "\<not> ds_seen s ! c" "ds_stk s = []"
    "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount" "length (ds_snum s) = Suc vcount"
    "ds_prnt t = (ds_prnt s)[c := vcount]" "ds_seen t = (ds_seen s)[c := True]"
    "ds_snum t = (ds_snum s)[c := 1]" "ds_stk t = [c]"
  shows "snum_inv t"
proof-
  have "vcount \<noteq> c" using assms(3) by simp
  note DD = desc_discover[OF assms(2-4) this assms(6,7,9,10)]
  have "dcard t c = 1" using DD[of c] desc_fresh_empty[OF assms(2-4)] by (simp add: dcard_def)
  moreover have "ds_snum t ! v = dcard t v" if "v < vcount" "ds_seen t ! v" "v \<noteq> c" for v
    using that assms(1,5,6,10,11) DD[of v] pstep_from_root[of v]
    by (auto simp: snum_inv_def stkverts_def dcard_def nth_list_update)
  ultimately show ?thesis using assms(3,8,11,12) by (auto simp: snum_inv_def stkverts_def nth_list_update)
qed

lemma snum_inv_lsuc: "snum_inv s \<Longrightarrow> snum_inv (s\<lparr>ds_lsuc := L\<rparr>)"
  by (rule snum_inv_cong[where s = s]) simp_all

text \<open>Design-notes clause I7 for @{const ds_lsuc}: when a vertex @{term v} finishes,
      @{term \<open>ds_lsuc s ! v\<close>} is the \<^emph>\<open>last\<close> vertex emitted inside
      @{term v}'s subtree (the rightmost descendant in the thread --- the block-last for clause J). We phrase
      it at the array level via @{const desc}: for every finished @{term v},
      @{term \<open>ds_lsuc s ! v\<close>} is a descendant of @{term v} whose thread-successor
      \<^emph>\<open>leaves\<close> the subtree. It is set at finish to @{const ds_prev} --- which the
      emission-order stack-descends clause (I6) pins as a descendant of the finishing top, and whose
      thread-successor is @{term 0} (I5) hence outside every subtree. As emission continues, that successor is
      overwritten with a vertex of a sibling subtree --- still outside --- so the property is stable. With
      I6's contiguity (assembly phase) this makes @{term \<open>ds_lsuc s ! v\<close>} exactly the last
      element of @{term v}'s thread-block.\<close>

definition lsuc_inv :: "'n dfs_state \<Rightarrow> bool" where
  "lsuc_inv s \<longleftrightarrow> (\<forall>v < vcount. ds_seen s ! v \<longrightarrow> v \<notin> stkverts s \<longrightarrow>
      ds_lsuc s ! v \<in> desc s v \<and> ds_thrd s ! (ds_lsuc s ! v) \<notin> desc s v)"

lemma bd_upd3_lsi:
  assumes "dfs_wf fl s" "dfs_sized s" "stk_prnt_inv s" "thread_inv s" "emit_ord_inv s" "snum_inv s"
    "lsuc_inv s" "bd_call3_conds fl s"
  shows "lsuc_inv (bd_upd3 s)"
proof-
  obtain v0 rest where stk: "ds_stk s = v0 # rest" by (rule bd_upd3_eq[OF assms(8)])
  let ?t = "bd_upd3 s"
  have ef: "ds_lsuc ?t = (ds_lsuc s)[v0 := ds_prev s]" "ds_thrd ?t = ds_thrd s" "ds_seen ?t = ds_seen s"
    "ds_stk ?t = rest"
    using stk by (simp_all add: bd_upd3_def dfs_finish_def Let_def)
  have dd: "desc ?t x = desc s x" for x
    using stk by (simp add: desc_def pstep_def bd_upd3_def dfs_finish_def Let_def)
  have v0: "v0 < vcount" "length (ds_lsuc s) = Suc vcount"
    using assms(1,2) stk by (auto simp: dfs_wf_def dfs_seenK_def dfs_sized_def)
  have sd: "(ds_prev s, v0) \<in> (pstep s)\<^sup>*" using assms(5) stk by (simp add: emit_ord_inv_def)
  with v0(1) have "ds_prev s \<noteq> vcount" by (auto dest: pstep_from_root)
  with sd assms(4) have prevdesc: "ds_prev s \<in> desc s v0" by (auto simp: thread_inv_def desc_def)
  have zero: "0 \<notin> desc s x" for x using assms(4) by (auto simp: thread_inv_def desc_def)
  show ?thesis
    unfolding lsuc_inv_def
  proof(intro allI impI)
    fix u assume u: "u < vcount" "ds_seen ?t ! u" "u \<notin> stkverts ?t"
    show "ds_lsuc ?t ! u \<in> desc ?t u \<and> ds_thrd ?t ! (ds_lsuc ?t ! u) \<notin> desc ?t u"
    proof(cases "u = v0")
      case True
      with v0 ef(1,2) dd prevdesc zero assms(4) show ?thesis by (simp add: thread_inv_def)
    next
      case False
      with u stk ef(3,4) have "u \<notin> stkverts s" "ds_seen s ! u" by (auto simp: stkverts_def)
      with u(1) False assms(7) ef(1,2) dd show ?thesis by (simp add: lsuc_inv_def)
    qed
  qed
qed

lemma lsuc_inv_cong:
  "\<lbrakk>ds_prnt t = ds_prnt s; ds_seen t = ds_seen s; ds_lsuc t = ds_lsuc s; ds_thrd t = ds_thrd s;
    ds_stk t = ds_stk s; lsuc_inv s\<rbrakk> \<Longrightarrow> lsuc_inv t"
  by (simp add: lsuc_inv_def stkverts_def desc_def pstep_def)

text \<open>The generic emission step for @{const lsuc_inv}: a fresh vertex @{term w} is attached below a
      parent @{term p} that is no ancestor of any finished vertex, and threaded after @{const ds_prev}.\<close>

lemma lsuc_inv_upd:
  assumes "lsuc_inv s" "tree_seen_inv s" "thread_inv s" "w < vcount" "\<not> ds_seen s ! w" "p \<noteq> w"
    "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount" "length (ds_thrd s) = Suc vcount"
    "\<And>u. \<lbrakk>u < vcount; ds_seen s ! u; u \<notin> stkverts s\<rbrakk> \<Longrightarrow> (p, u) \<notin> (pstep s)\<^sup>*"
    "ds_lsuc t = ds_lsuc s" "ds_prnt t = (ds_prnt s)[w := p]" "ds_seen t = (ds_seen s)[w := True]"
    "ds_thrd t = (ds_thrd s)[ds_prev s := w]" "stkverts t = insert w (stkverts s)"
  shows "lsuc_inv t"
proof-
  note DD = desc_discover[OF assms(2,4,5,6,7,8,12,13)]
  have wnd: "w \<notin> desc s x" for x using assms(5) by (auto simp: desc_def)
  have prev: "ds_prev s < Suc vcount" using assms(3) by (simp add: thread_inv_def)
  show ?thesis
    unfolding lsuc_inv_def
  proof(intro allI impI)
    fix u assume u: "u < vcount" "ds_seen t ! u" "u \<notin> stkverts t"
    then have "u \<noteq> w" "u \<notin> stkverts s" "ds_seen s ! u" using assms(7,13,15) by (auto simp: nth_list_update)
    moreover from this have "desc t u = desc s u" using DD[of u] assms(10) u(1) by auto
    ultimately show "ds_lsuc t ! u \<in> desc t u \<and> ds_thrd t ! (ds_lsuc t ! u) \<notin> desc t u"
      using assms(1,9,11,14) u(1) wnd prev
      by (cases "ds_lsuc s ! u = ds_prev s") (auto simp: lsuc_inv_def nth_list_update)
  qed
qed

lemma dfs_discover_lsi:
  assumes "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "thread_inv s" "lsuc_inv s" "ds_stk s = v # rest"
    "w < vcount" "\<not> ds_seen s ! w"
  shows "lsuc_inv (dfs_discover s v w e)"
proof(rule lsuc_inv_upd[OF assms(5,2,4,7,8)])
  show "v \<noteq> w" using assms(2,6,8) by (auto simp: tree_seen_inv_def)
  show "(v, u) \<notin> (pstep s)\<^sup>*" if "u < vcount" "ds_seen s ! u" "u \<notin> stkverts s" for u
    using that pstep_anc_on_stk[OF assms(3), of v u] assms(6) by (auto simp: stkverts_def)
qed (use assms(1,6) in \<open>simp_all add: dfs_sized_def dfs_discover_def dfs_push_def Let_def stkverts_def\<close>)

lemma bd_upd1_lsi:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "thread_inv s" "lsuc_inv s"
    "bd_call1_conds fl s"
  shows "lsuc_inv (bd_upd1 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
      else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF assms(1,7)])
  moreover have "dfs_sized (s\<lparr>ds_oc := c'\<rparr>)" "tree_seen_inv (s\<lparr>ds_oc := c'\<rparr>)"
    "stk_prnt_inv (s\<lparr>ds_oc := c'\<rparr>)" "thread_inv (s\<lparr>ds_oc := c'\<rparr>)" "lsuc_inv (s\<lparr>ds_oc := c'\<rparr>)"
    using assms(2-6) lsuc_inv_cong[of "s\<lparr>ds_oc := c'\<rparr>" s]
    by (simp_all add: dfs_sized_def tree_seen_inv_def stk_prnt_inv_def thread_inv_def)
  ultimately show ?thesis using dfs_discover_lsi[of "s\<lparr>ds_oc := c'\<rparr>" v rest w e] by simp
qed

lemma bd_upd2_lsi:
  assumes "dfs_wf fl s" "dfs_sized s" "tree_seen_inv s" "stk_prnt_inv s" "thread_inv s" "lsuc_inv s"
    "bd_call2_conds fl s"
  shows "lsuc_inv (bd_upd2 fl s)"
proof-
  obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
      else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF assms(1,7)])
  moreover have "dfs_sized (s\<lparr>ds_ic := c'\<rparr>)" "tree_seen_inv (s\<lparr>ds_ic := c'\<rparr>)"
    "stk_prnt_inv (s\<lparr>ds_ic := c'\<rparr>)" "thread_inv (s\<lparr>ds_ic := c'\<rparr>)" "lsuc_inv (s\<lparr>ds_ic := c'\<rparr>)"
    using assms(2-6) lsuc_inv_cong[of "s\<lparr>ds_ic := c'\<rparr>" s]
    by (simp_all add: dfs_sized_def tree_seen_inv_def stk_prnt_inv_def thread_inv_def)
  ultimately show ?thesis using dfs_discover_lsi[of "s\<lparr>ds_ic := c'\<rparr>" v rest w e] by simp
qed

lemma lsuc_inv_seed:
  "\<lbrakk>lsuc_inv s; tree_seen_inv s; thread_inv s; c < vcount; \<not> ds_seen s ! c; ds_stk s = [];
    length (ds_seen s) = Suc vcount; length (ds_prnt s) = Suc vcount; length (ds_thrd s) = Suc vcount;
    ds_lsuc t = ds_lsuc s; ds_prnt t = (ds_prnt s)[c := vcount]; ds_seen t = (ds_seen s)[c := True];
    ds_thrd t = (ds_thrd s)[ds_prev s := c]; ds_stk t = [c]\<rbrakk> \<Longrightarrow> lsuc_inv t"
  by (rule lsuc_inv_upd[where w = c and p = vcount]) (auto simp: stkverts_def dest: pstep_from_root)

lemma emit_U_edge_lsi: "lsuc_inv s \<Longrightarrow> lsuc_inv (emit_U_edge s v)"
  by (rule lsuc_inv_cong[where s = s]) (simp_all add: emit_U_edge_def Let_def)

lemma dfs_init_lsi: "lsuc_inv dfs_init"
  by (auto simp: lsuc_inv_def dfs_init_def simp del: replicate_Suc)

lemma lsuc_inv_root_wrap:
  "lsuc_inv s \<Longrightarrow> lsuc_inv (s\<lparr>ds_lsuc := (ds_lsuc s)[vcount := L]\<rparr>)"
  unfolding lsuc_inv_def stkverts_def by (auto simp: desc_def pstep_def)


definition dfs_inv :: "'n list \<Rightarrow> 'n dfs_state \<Rightarrow> bool" where
  "dfs_inv fl s \<longleftrightarrow> dfs_wf fl s \<and> dfs_sized s \<and> tree_seen_inv s \<and> thread_inv s \<and> par_edge_inv fl s \<and> pot_inv s
     \<and> root_pot_inv s \<and> stk_prnt_inv s \<and> emit_ord_inv s \<and> snum_inv s \<and> lsuc_inv s"

lemma bd_upd1_inv: "\<lbrakk>dfs_inv fl s; bd_call1_conds fl s\<rbrakk> \<Longrightarrow> dfs_inv fl (bd_upd1 fl s)"
  using bd_upd1_wf bd_upd1_sized bd_upd1_tsi bd_upd1_thi bd_upd1_pei bd_upd1_pot bd_upd1_rpi bd_upd1_spi
    bd_upd1_eoi bd_upd1_sni bd_upd1_lsi
  by (auto simp: dfs_inv_def)

lemma bd_upd2_inv: "\<lbrakk>dfs_inv fl s; bd_call2_conds fl s\<rbrakk> \<Longrightarrow> dfs_inv fl (bd_upd2 fl s)"
  using bd_upd2_wf bd_upd2_sized bd_upd2_tsi bd_upd2_thi bd_upd2_pei bd_upd2_pot bd_upd2_rpi bd_upd2_spi
    bd_upd2_eoi bd_upd2_sni bd_upd2_lsi
  by (auto simp: dfs_inv_def)

lemma bd_upd3_inv: "\<lbrakk>dfs_inv fl s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> dfs_inv fl (bd_upd3 s)"
  using bd_upd3_wf bd_upd3_sized bd_upd3_tsi bd_upd3_thi bd_upd3_pei bd_upd3_pot bd_upd3_rpi bd_upd3_spi
    bd_upd3_eoi bd_upd3_sni bd_upd3_lsi
  by (auto simp: dfs_inv_def)

lemma build_dfs_inv: "\<lbrakk>build_dfs_dom (fl, s); dfs_inv fl s\<rbrakk> \<Longrightarrow> dfs_inv fl (build_dfs fl s)"
proof(induct rule: bd_induct[consumes 1])
  case IH: (1 fl s)
  show ?case
    by (rule bd_cases[where s = s and fl = fl])
      (auto intro!: IH(2-4) bd_upd1_inv bd_upd2_inv bd_upd3_inv IH(5) simp: bd_simps[OF IH(1)])
qed

lemma build_dfs_inv': "dfs_inv fl s \<Longrightarrow> dfs_inv fl (build_dfs fl s)"
  by (rule build_dfs_inv) (simp_all add: dfs_inv_def build_dfs_dom_wf)

text \<open>@{const build_dfs} runs until its stack is empty, so every component opened by
      @{const open_tree_component} leaves the stack empty again --- the property that lets the phase folds
      hand each @{const open_tree_component} a between-components state (empty stack), which the subtree
      bookkeeping (I7) needs for its finished-vertex clause.\<close>

lemma build_dfs_stk_empty: "build_dfs_dom (fl, s) \<Longrightarrow> ds_stk (build_dfs fl s) = []"
proof(induct rule: bd_induct[consumes 1])
  case IH: (1 fl s)
  show ?case
    by (rule bd_cases[where s = s and fl = fl]) (auto intro!: IH(2-4) simp: bd_simps[OF IH(1)] bd_ret_conds_def)
qed

lemma open_tree_component_stk_empty:
  "\<lbrakk>dfs_wf fl s; c < vcount\<rbrakk> \<Longrightarrow> ds_stk (open_tree_component fl s c) = []"
  unfolding open_tree_component_def Let_def
  by (intro build_dfs_stk_empty build_dfs_dom_wf dfs_push_wf[where K = "dfs_seenK s"])
    (auto simp: dfs_wf_def dfs_seenK_def nth_list_update)

text \<open>The seed state @{term sd} that @{const open_tree_component} hands to @{const build_dfs}: the
      traversal from it terminates, it satisfies the invariant when @{term c} is a fresh real vertex
      opened between components, and it records @{term c} as a component root together with its
      artificial edge at the cursor.\<close>

lemma open_tree_component_seed:
  assumes "dfs_wf fl s" "dfs_sized s" "c < vcount"
  obtains sd where
    "open_tree_component fl s c = build_dfs fl sd" "build_dfs_dom (fl, sd)"
    "(dfs_inv fl s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv fl sd"
    "ds_stk sd = [c]" "ds_oc sd = ds_oc (dfs_push s c)" "ds_ic sd = ds_ic (dfs_push s c)"
    "ds_nxt sd = Suc (ds_nxt s)"
    "ds_seen sd = (ds_seen s)[c := True]" "ds_prnt sd = (ds_prnt s)[c := vcount]"
    "ds_par sd = (ds_par s)[c := m + ds_nxt s]" "ds_dir sd = (ds_dir s)[c := art_dir c]"
    "ds_pot sd = (ds_pot s)[c := (if art_dir c then pval_negM else pval_M)]"
    "ds_thrd sd = (ds_thrd s)[ds_prev s := c]" "ds_snum sd = (ds_snum s)[c := 1]"
    "ds_afst sd = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
    "ds_asnd sd = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    "ds_acap sd = (ds_acap s)[ds_nxt s := art_tree_cap c]"
    "ds_aflw sd = (ds_aflw s)[ds_nxt s := art_flow c]"
    "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
    "ds_rvth sd = (ds_rvth s)[c := ds_prev s]" "ds_prev sd = c" "ds_lsuc sd = ds_lsuc s"
proof-
  define sd where "sd = dfs_push
             (s\<lparr> ds_afst := (ds_afst s)[ds_nxt s := (if 0 \<le> imbalance ! c then c else vcount)],
                 ds_asnd := (ds_asnd s)[ds_nxt s := (if 0 \<le> imbalance ! c then vcount else c)],
                 ds_acap := (ds_acap s)[ds_nxt s := (if 0 \<le> imbalance ! c then \<bar>imbalance ! c\<bar> + 1 else \<bar>imbalance ! c\<bar>)],
                 ds_aflw := (ds_aflw s)[ds_nxt s := \<bar>imbalance ! c\<bar>],
                 ds_aest := (ds_aest s)[ds_nxt s := InTree],
                 ds_nxt  := Suc (ds_nxt s),
                 ds_seen := (ds_seen s)[c := True],
                 ds_prnt := (ds_prnt s)[c := vcount],
                 ds_par  := (ds_par s)[c := m + ds_nxt s],
                 ds_dir  := (ds_dir s)[c := 0 \<le> imbalance ! c],
                 ds_pot  := (ds_pot s)[c := (if 0 \<le> imbalance ! c then pval_negM else pval_M)],
                 ds_thrd := (ds_thrd s)[ds_prev s := c],
                 ds_rvth := (ds_rvth s)[c := ds_prev s],
                 ds_snum := (ds_snum s)[c := 1],
                 ds_prev := c,
                 ds_stk  := [] \<rparr>) c"
  have opd: "open_tree_component fl s c = build_dfs fl sd"
    by (simp add: open_tree_component_def sd_def Let_def)
  have wf0: "dfs_wf fl sd"
    unfolding sd_def using assms
    by (intro dfs_push_wf[where K = "dfs_seenK s"]) (auto simp: dfs_wf_def dfs_seenK_def dfs_sized_def nth_list_update)
  have invsd: "dfs_inv fl sd"
    if "dfs_inv fl s" "\<not> ds_seen s ! c" "c \<noteq> 0" "ds_stk s = []"
    unfolding dfs_inv_def
    apply(intro conjI)
    subgoal by (rule wf0)
    unfolding sd_def
    subgoal using that assms(3) by (auto simp: dfs_inv_def dfs_sized_def dfs_push_def)
    subgoal using that assms(3) by (auto simp: dfs_inv_def dfs_sized_def tree_seen_inv_def dfs_push_def nth_list_update)
    subgoal
      by (rule thread_inv_upd[where s = s and w = c])
        (use that assms(3) in \<open>auto simp: dfs_inv_def dfs_sized_def dfs_push_def\<close>)
    subgoal using that assms(3) by (auto simp: dfs_inv_def dfs_sized_def par_edge_inv_def dfs_push_def nth_list_update)
    subgoal
      by (rule pot_inv_seed[where s = s and c = c])
        (use that assms(3) in \<open>auto simp: dfs_inv_def dfs_sized_def dfs_push_def nth_list_update\<close>)
    subgoal using that assms(3) by (auto simp: dfs_inv_def dfs_sized_def root_pot_inv_def dfs_push_def nth_list_update)
    subgoal using that assms(3) by (auto simp: dfs_inv_def dfs_sized_def stk_prnt_inv_def dfs_push_def nth_list_update)
    subgoal
      by (rule emit_ord_inv_seed[where s = s and c = c])
        (use that assms(3) in \<open>auto simp: dfs_inv_def dfs_sized_def dfs_push_def\<close>)
    subgoal
      by (rule snum_inv_seed[where s = s and c = c])
        (use that assms(3) in \<open>auto simp: dfs_inv_def dfs_sized_def dfs_push_def\<close>)
    subgoal
      by (rule lsuc_inv_seed[where s = s and c = c])
        (use that assms(3) in \<open>auto simp: dfs_inv_def dfs_sized_def dfs_push_def\<close>)
    done
  show ?thesis
    using invsd
    by (intro that[OF opd build_dfs_dom_wf[OF wf0]])
      (simp_all add: sd_def dfs_push_def art_dir_def art_flow_def art_tree_cap_def)
qed

lemma open_tree_component_inv:
  "\<lbrakk>dfs_inv fl s; c < vcount; \<not> ds_seen s ! c; c \<noteq> 0; ds_stk s = []\<rbrakk> \<Longrightarrow>
    dfs_inv fl (open_tree_component fl s c)"
  by (rule open_tree_component_seed[of fl s c]) (auto simp: dfs_inv_def[of fl s] intro: build_dfs_inv')

lemma emit_U_edge_inv: "dfs_inv fl s \<Longrightarrow> dfs_inv fl (emit_U_edge s v)"
  using emit_U_edge_wf emit_U_edge_sized emit_U_edge_thi emit_U_edge_eoi emit_U_edge_sni emit_U_edge_lsi
  by (simp add: dfs_inv_def tree_seen_inv_def par_edge_inv_def pot_inv_def root_pot_inv_def
      stk_prnt_inv_def emit_U_edge_def Let_def)

lemma phase1_step_inv:
  "\<lbrakk>v \<in> set vs_list; dfs_inv fl s \<and> ds_stk s = []\<rbrakk> \<Longrightarrow>
    dfs_inv fl (phase1_step fl v s) \<and> ds_stk (phase1_step fl v s) = []"
  using no_zero_node vs_less_vcount emit_U_edge_inv[of fl s v] open_tree_component_inv[of fl s v]
    open_tree_component_stk_empty[of fl s v] dfs_inv_def[of fl s]
  by (auto simp: phase1_step_def emit_U_edge_def Let_def)

lemma phase2_step_inv:
  "\<lbrakk>v \<in> set vs_list; dfs_inv fl s \<and> ds_stk s = []\<rbrakk> \<Longrightarrow>
    dfs_inv fl (phase2_step fl v s) \<and> ds_stk (phase2_step fl v s) = []"
  using no_zero_node vs_less_vcount open_tree_component_inv[of fl s v]
    open_tree_component_stk_empty[of fl s v] dfs_inv_def[of fl s]
  by (auto simp: phase2_step_def)

lemma dfs_init_inv: "dfs_inv fl dfs_init"
  using dfs_init_wf dfs_init_sized dfs_init_thi dfs_init_eoi dfs_init_sni dfs_init_lsi
  by (simp add: dfs_inv_def tree_seen_inv_def par_edge_inv_def pot_inv_def root_pot_inv_def stk_prnt_inv_def
      dfs_init_def del: replicate_Suc)

lemma phase1_inv:
  "dfs_inv fl s \<and> ds_stk s = [] \<Longrightarrow> dfs_inv fl (phase1 fl s) \<and> ds_stk (phase1 fl s) = []"
  unfolding phase1_def
  by (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = "\<lambda>s. dfs_inv fl s \<and> ds_stk s = []"])
    (simp_all add: phase1_step_inv)

lemma phase2_inv:
  "dfs_inv fl s \<and> ds_stk s = [] \<Longrightarrow> dfs_inv fl (phase2 fl s) \<and> ds_stk (phase2 fl s) = []"
  unfolding phase2_def
  by (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = "\<lambda>s. dfs_inv fl s \<and> ds_stk s = []"])
    (simp_all add: phase2_step_inv)

lemma build_tree_phases:
  "dfs_inv fl (phase2 fl (phase1 fl dfs_init)) \<and> ds_stk (phase2 fl (phase1 fl dfs_init)) = []"
  using dfs_init_inv by (intro phase2_inv phase1_inv) (simp add: dfs_init_def)

lemma build_tree_inv: "dfs_inv fl (build_tree fl)"
proof-
  let ?s = "phase2 fl (phase1 fl dfs_init)"
  let ?t = "?s\<lparr>ds_lsuc := (ds_lsuc ?s)[vcount := ds_prev ?s]\<rparr>"
  have i: "dfs_inv fl ?s" using build_tree_phases by simp
  show ?thesis
    unfolding build_tree_def Let_def dfs_inv_def
  proof(intro conjI)
    show "dfs_wf fl ?t"  "dfs_sized ?t" using i 
       by (simp add: dfs_inv_def dfs_wf_def dfs_seenK_def dfs_sized_def)+
    show "tree_seen_inv ?t"  "thread_inv ?t"  "par_edge_inv fl ?t" 
         "pot_inv ?t"  "root_pot_inv ?t"  "stk_prnt_inv ?t" 
         "emit_ord_inv ?t"  "snum_inv ?t"  "lsuc_inv ?t" 
      using  i snum_inv_lsuc i lsuc_inv_root_wrap 
      by (auto simp add: par_edge_inv_def pot_inv_def root_pot_inv_def stk_prnt_inv_def
              emit_ord_inv_def pstep_def dfs_inv_def thread_inv_def tree_seen_inv_def)
  qed
qed

text \<open>The two consequences the arborescence proof will consume: the root is outside the visited set,
      and the parent map on the visited vertices is a forest directed towards @{term vcount}.\<close>

lemma build_tree_root_unseen: "\<not> ds_seen (build_tree fl) ! vcount"
  using build_tree_inv by (auto simp: dfs_inv_def tree_seen_inv_def)

lemma build_tree_parent_in_seen:
  "\<lbrakk>w < vcount; ds_seen (build_tree fl) ! w\<rbrakk> \<Longrightarrow>
   ds_prnt (build_tree fl) ! w = vcount
   \<or> (ds_prnt (build_tree fl) ! w < vcount \<and> ds_seen (build_tree fl) ! (ds_prnt (build_tree fl) ! w))"
  using build_tree_inv by (auto simp: dfs_inv_def tree_seen_inv_def)

text \<open>Design-notes I3 for the finished tree: every interior tree vertex's stored parent edge is a real
      free edge realising the link to its parent, with the recorded orientation. (Component roots,
      \<open>prnt = vcount\<close>, are excluded --- their parent edge is the artificial one.)\<close>

lemma build_tree_par_edge:
  "\<lbrakk>w < vcount; ds_seen (build_tree fl) ! w; ds_prnt (build_tree fl) ! w < vcount\<rbrakk> \<Longrightarrow>
   ds_par (build_tree fl) ! w < m \<and> is_free fl (ds_par (build_tree fl) ! w)
   \<and> ds_dir (build_tree fl) ! w = (fst_list ! (ds_par (build_tree fl) ! w) = w)
   \<and> fst_list ! (ds_par (build_tree fl) ! w) = (if ds_dir (build_tree fl) ! w then w else ds_prnt (build_tree fl) ! w)
   \<and> snd_list ! (ds_par (build_tree fl) ! w) = (if ds_dir (build_tree fl) ! w then ds_prnt (build_tree fl) ! w else w)"
  using build_tree_inv by (auto simp: dfs_inv_def par_edge_inv_def)

text \<open>Design-notes I4 for the finished tree: every interior tree vertex's potential is its parent's
      plus the @{term \<open>M_0\<close>}-tagged signed cost of its tree edge --- zero reduced cost on that edge
      (abstract-level once \<open>good_pot_val\<close> is available at assembly).\<close>

lemma build_tree_pot:
  "\<lbrakk>w < vcount; ds_seen (build_tree fl) ! w; ds_prnt (build_tree fl) ! w < vcount\<rbrakk> \<Longrightarrow>
   ds_pot (build_tree fl) ! w = pval_plus (ds_pot (build_tree fl) ! (ds_prnt (build_tree fl) ! w))
     (M_0, if ds_prnt (build_tree fl) ! w = fst_list ! (ds_par (build_tree fl) ! w)
           then cost_list ! (ds_par (build_tree fl) ! w) else - cost_list ! (ds_par (build_tree fl) ! w))"
  using build_tree_inv by (auto simp: dfs_inv_def pot_inv_def)

text \<open>Design-notes I1 for the root: the finished tree gives the artificial root zero potential
      (\<open>\<pi> r = 0\<close>, consumed by \<open>init_pot_fits\<close>).\<close>

lemma build_tree_root_pot: "ds_pot (build_tree fl) ! vcount = pval_zero"
  using build_tree_inv by (simp add: dfs_inv_def root_pot_inv_def)

text \<open>Design-notes I6 for the finished tree (the full preorder DFS step of
      \<open>preorder_contiguous\<close>): the parent of every emitted vertex is an ancestor --- in the
      parent-step closure @{term \<open>(pstep (build_tree fl))\<^sup>*\<close>} --- of its thread-predecessor
      @{const ds_rvth}. Together with the thread mutual-inverse (I5) this is exactly the \<open>dfs\<close>
      premise of \<open>preorder_contiguous\<close>, restated over the arrays; the
      array{\isasymrightarrow}abstract \<open>follow\<close>/\<open>parent_spec\<close> bridge that turns
      @{term pstep} closure into an abstract root-path is set up at \<open>arb_invar\<close> assembly.\<close>

lemma build_tree_emit_order:
  "\<lbrakk>w < vcount; ds_seen (build_tree fl) ! w\<rbrakk> \<Longrightarrow>
   (ds_rvth (build_tree fl) ! w, ds_prnt (build_tree fl) ! w) \<in> (pstep (build_tree fl))\<^sup>*"
  using build_tree_inv by (auto simp: dfs_inv_def emit_ord_inv_def)

text \<open>Every emitted vertex reaches the artificial root through the parent-step closure --- the array
      counterpart of \<open>follow T v\<close> terminating at the root, and the ingredient that makes the abstract
      parent map a genuine forest rooted at @{term vcount}.\<close>

lemma build_tree_reaches_root:
  "\<lbrakk>w < vcount; ds_seen (build_tree fl) ! w\<rbrakk> \<Longrightarrow> (w, vcount) \<in> (pstep (build_tree fl))\<^sup>*"
  using build_tree_inv by (auto simp: dfs_inv_def emit_ord_inv_def)

text \<open>Design-notes I7 for the finished tree: @{term \<open>ds_snum (build_tree fl) ! w\<close>} is the
      size of @{term w}'s subtree --- where the subtree is the array set
      @{term \<open>desc (build_tree fl) w\<close>} of emitted @{const pstep}-descendants, the counterpart of
      the abstract @{text \<open>children (prnt S) w\<close>}. The whole DFS stack is empty at
      @{const build_tree}, so every emitted vertex is finished and the finished-vertex clause of
      @{const snum_inv} applies to all of them.\<close>

lemma build_tree_stk_empty: "ds_stk (build_tree fl) = []"
  using build_tree_phases[of fl] by (simp add: build_tree_def Let_def)

lemma build_tree_snum:
  "\<lbrakk>w < vcount; ds_seen (build_tree fl) ! w\<rbrakk> \<Longrightarrow> ds_snum (build_tree fl) ! w = dcard (build_tree fl) w"
  using build_tree_inv[of fl] build_tree_stk_empty[of fl] by (auto simp: dfs_inv_def snum_inv_def stkverts_def)

text \<open>Design-notes I7 for @{const ds_lsuc} on the finished tree: every tree vertex's stored last-successor
      is a descendant of it whose thread-successor leaves its subtree --- the array form of "\<open>lsuc S v\<close>
      is the last vertex of @{term v}'s subtree block", which with I6's contiguity gives clause J's
      \<open>last pre = lsuc S v\<close> at \<open>arb_invar\<close> assembly.\<close>

lemma build_tree_lsuc:
  "\<lbrakk>w < vcount; ds_seen (build_tree fl) ! w\<rbrakk> \<Longrightarrow>
   ds_lsuc (build_tree fl) ! w \<in> desc (build_tree fl) w
   \<and> ds_thrd (build_tree fl) ! (ds_lsuc (build_tree fl) ! w) \<notin> desc (build_tree fl) w"
  using build_tree_inv[of fl] build_tree_stk_empty[of fl] by (auto simp: dfs_inv_def lsuc_inv_def stkverts_def)

text \<open>The thread consequences (design notes I5): @{const ds_rvth} recovers the @{const ds_thrd}
      source of every emitted, non-last vertex, the root has no thread predecessor, and each thread
      successor of an emitted non-last vertex is itself an emitted vertex --- the raw material for
      \<open>parent_spec\<close> of the thread and reverse-thread maps and the mutual-inverse clauses of
      \<open>arb_invar\<close>.\<close>

lemma build_tree_thread_inv: "thread_inv (build_tree fl)"
  using build_tree_inv by (simp add: dfs_inv_def)

lemma build_tree_root_no_pred: "ds_rvth (build_tree fl) ! vcount = 0"
  using build_tree_thread_inv by (simp add: thread_inv_def)

lemma build_tree_thread_inverse:
  assumes "x < Suc vcount" "x = vcount \<or> ds_seen (build_tree fl) ! x" "x \<noteq> ds_prev (build_tree fl)"
  shows "ds_thrd (build_tree fl) ! x < Suc vcount"
    and "ds_thrd (build_tree fl) ! x = vcount \<or> ds_seen (build_tree fl) ! (ds_thrd (build_tree fl) ! x)"
    and "ds_rvth (build_tree fl) ! (ds_thrd (build_tree fl) ! x) = x"
  using build_tree_thread_inv assms by (auto simp: thread_inv_def)

lemma build_tree_rev_thread_inverse:
  assumes "x < Suc vcount" "x = vcount \<or> ds_seen (build_tree fl) ! x" "x \<noteq> vcount"
  shows "ds_rvth (build_tree fl) ! x < Suc vcount"
    and "ds_rvth (build_tree fl) ! x = vcount \<or> ds_seen (build_tree fl) ! (ds_rvth (build_tree fl) ! x)"
    and "ds_thrd (build_tree fl) ! (ds_rvth (build_tree fl) ! x) = x"
  using build_tree_thread_inv assms by (auto simp: thread_inv_def)

section \<open>Spanning: every vertex is visited by @{const build_tree}\<close>

text \<open>Phase 2 opens every still-unseen vertex, so after the whole build every vertex of @{term vs_list}
      is visited. The proof rests on \<^emph>\<open>monotonicity\<close>: once a vertex is marked, no later
      step unmarks it (@{const dfs_discover} only ever writes @{term True} into @{const ds_seen}, and
      @{const dfs_finish} leaves it untouched). Together with the parent skeleton (design notes I2) this gives
      the L2 ingredient @{term \<open>dom T = V - {r}\<close>}: every real vertex has its parent edge in the
      tree.\<close>

lemma bd_upd1_seen_mono:
  "\<lbrakk>bd_call1_conds fl s; ds_seen s ! x\<rbrakk> \<Longrightarrow> ds_seen (bd_upd1 fl s) ! x"
  by (auto simp: bd_call1_conds_def bd_upd1_def dfs_discover_def dfs_push_def Let_def nth_update_True_mono
      split: list.splits if_splits)

lemma bd_upd2_seen_mono:
  "\<lbrakk>bd_call2_conds fl s; ds_seen s ! x\<rbrakk> \<Longrightarrow> ds_seen (bd_upd2 fl s) ! x"
  by (auto simp: bd_call2_conds_def bd_upd2_def dfs_discover_def dfs_push_def Let_def nth_update_True_mono
      split: list.splits if_splits)

lemma bd_upd3_seen_mono:
  "\<lbrakk>bd_call3_conds fl s; ds_seen s ! x\<rbrakk> \<Longrightarrow> ds_seen (bd_upd3 s) ! x"
  by (auto simp: bd_call3_conds_def bd_upd3_def dfs_finish_def Let_def split: list.splits prod.splits)

lemma build_dfs_seen_mono: "\<lbrakk>build_dfs_dom (fl, s); ds_seen s ! x\<rbrakk> \<Longrightarrow> ds_seen (build_dfs fl s) ! x"
proof(induct rule: bd_induct[consumes 1])
  case IH: (1 fl s)
  show ?case
    by (rule bd_cases[where s = s and fl = fl])
      (auto intro!: IH(2-4) bd_upd1_seen_mono bd_upd2_seen_mono bd_upd3_seen_mono IH(5) simp: bd_simps[OF IH(1)])
qed

lemma open_tree_component_marks:
  "\<lbrakk>dfs_inv fl s; c < vcount\<rbrakk> \<Longrightarrow> ds_seen (open_tree_component fl s c) ! c"
  by (rule open_tree_component_seed[of fl s c])
    (auto simp: dfs_inv_def dfs_sized_def intro!: build_dfs_seen_mono)

lemma open_tree_component_seen_mono:
  "\<lbrakk>dfs_inv fl s; c < vcount; ds_seen s ! x\<rbrakk> \<Longrightarrow> ds_seen (open_tree_component fl s c) ! x"
  by (rule open_tree_component_seed[of fl s c])
    (auto simp: dfs_inv_def intro!: build_dfs_seen_mono nth_update_True_mono)

lemma phase2_step_marks:
  "\<lbrakk>dfs_inv fl s; v < vcount; \<not> is_lonely v\<rbrakk> \<Longrightarrow> ds_seen (phase2_step fl v s) ! v"
  using open_tree_component_marks[of fl s v] by (auto simp: phase2_step_def)

lemma phase2_step_seen_mono:
  "\<lbrakk>dfs_inv fl s; v < vcount; ds_seen s ! x\<rbrakk> \<Longrightarrow> ds_seen (phase2_step fl v s) ! x"
  using open_tree_component_seen_mono[of fl s v x] by (auto simp: phase2_step_def)

lemma fold_phase2_seen_mono:
  "\<lbrakk>set us \<subseteq> set vs_list; dfs_inv fl s \<and> ds_stk s = []; ds_seen s ! x\<rbrakk>
   \<Longrightarrow> ds_seen (fold (phase2_step fl) us s) ! x"
proof(induction us arbitrary: s)
  case (Cons u us)
  then show ?case
    using phase2_step_inv[of u fl s] phase2_step_seen_mono[of fl s u x] vs_less_vcount[of u] by simp
qed simp

lemma fold_phase2_marks:
  "\<lbrakk>set us \<subseteq> set vs_list; dfs_inv fl s \<and> ds_stk s = []; v \<in> set us; \<not> is_lonely v\<rbrakk>
   \<Longrightarrow> ds_seen (fold (phase2_step fl) us s) ! v"
proof(induction us arbitrary: s)
  case (Cons u us)
  then have "u < vcount" "dfs_inv fl (phase2_step fl u s) \<and> ds_stk (phase2_step fl u s) = []"
    using phase2_step_inv[of u fl s] vs_less_vcount[of u] by simp_all
  with Cons show ?case
    using phase2_step_marks[of fl s u] fold_phase2_seen_mono[of us fl "phase2_step fl u s" v] by auto
qed simp

text \<open>The tree spans exactly the \<^emph>\<open>edged\<close> vertices: a lonely name of @{term vs_list}
      is skipped by the guard and so is never marked seen. The non-lonely hypothesis is the one supplied at
      every use site through @{thm edged_not_lonely} / @{const edged_vs_list}.\<close>

lemma build_tree_spans:
  "\<lbrakk>v \<in> set vs_list; \<not> is_lonely v\<rbrakk> \<Longrightarrow> ds_seen (build_tree fl) ! v"
  using fold_phase2_marks[OF subset_refl, of fl "phase1 fl dfs_init" v] phase1_inv[of fl dfs_init] dfs_init_inv
  by (simp add: build_tree_def Let_def phase2_def dfs_init_def)

text \<open>L2 skeleton: every real vertex sits in the parent map with its parent either the root or another
      visited vertex --- i.e.\ @{term \<open>dom T = V - {r}\<close>} together with
      \<open>build_tree_root_unseen\<close>.\<close>

lemma build_tree_vertex_parent:
  "\<lbrakk>v \<in> set vs_list; \<not> is_lonely v\<rbrakk> \<Longrightarrow>
   ds_prnt (build_tree fl) ! v = vcount
   \<or> (ds_prnt (build_tree fl) ! v < vcount \<and> ds_seen (build_tree fl) ! (ds_prnt (build_tree fl) ! v))"
  using build_tree_parent_in_seen vs_less_vcount build_tree_spans by blast

section \<open>Free-edge coverage: every free edge is a tree edge (needs acyclicity)\<close>

text \<open>The tree edges are exactly the free real edges plus the artificial component-root edges. One
      direction --- parent edges are @{term InTree} --- holds unconditionally (design-notes I3 for interior
      vertices, the component-root emission for roots). The converse --- every \<^emph>\<open>free\<close>
      real edge is a parent edge (so @{term \<open>\<E> = T \<union> U \<union> L\<close>} in
      \<open>spanning_tree_partition\<close>) --- is the forest property: an uncovered free edge would be a
      back edge of the depth-first spanning forest, closing a cycle of free arcs, which the acyclicity of
      @{term flow_list} forbids.

      We localise the acyclicity hypothesis to a lightweight @{command context} block rather than burdening
      the outer locale: @{term \<open>original_network.acyclic_flow (h \<circ> nth flow_list)\<close>} is
      precisely what @{thm make_acyclic_correct_unconditional_bflow} delivers on the branch where the
      acyclifying procedure returns @{term Some} (a @{term None} answer means a negative infinite-capacity
      cycle, i.e.\ the instance is unbounded and no tree is built).\<close>

text \<open>The correctness lemmas that need the input flow to be capacity-complying and acyclic live in
      this \<open>fl\<close>-fixing context: the strongly-feasible tree is built from an arbitrary acyclic,
      capacity-complying flow \<open>fl\<close> (the acyclifier's output). The pipeline enters this context with
      \<open>fl\<close> instantiated to that output, discharging the three assumptions from the acyclifier's
      correctness.\<close>

context
  fixes fl :: "'n list"
  assumes fl_nonneg: "\<And>e. e < m \<Longrightarrow> 0 \<le> fl ! e"
      and fl_le_cap: "\<And>e. \<lbrakk>e < m; capacity_list ! e \<noteq> - 1\<rbrakk> \<Longrightarrow> fl ! e \<le> capacity_list ! e"
begin

text \<open>The edge classification reads back exactly the residual bounds. This needs only
      \<open>fl\<close>'s \<^emph>\<open>capacity-compliance\<close>, not its acyclicity --- which is why
      these two live outside the \<open>acyc\<close> context nested below: whether an edge is free is a
      statement about the two residual bounds alone. The initial tree's strong feasibility is a consequence of
      them, so it must not be made to depend on the acyclifier's verdict.\<close>

lemma edge_state_InTree_iff:
  "e < m \<Longrightarrow> edge_state fl ! e = InTree \<longleftrightarrow> 0 < fl ! e \<and> (capacity_list ! e = - 1 \<or> fl ! e < capacity_list ! e)"
  using fl_nonneg[of e] fl_le_cap[of e] by (force simp: edge_state_nth classify_def)

lemma is_free_iff:
  "e < m \<Longrightarrow> is_free fl e \<longleftrightarrow> 0 < fl ! e \<and> (capacity_list ! e = - 1 \<or> fl ! e < capacity_list ! e)"
  by (simp add: is_free_def edge_state_InTree_iff)

context
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth fl)"
begin

text \<open>The concrete consequence used throughout this section: \<open>fl\<close> carries no closed
      residual pre-path of pairwise-distinct free arcs.\<close>

lemma flow_no_free_cycle:
  "\<nexists>C. original_network.prepath C \<and> (\<forall>e\<in>set C. af_arc_free fl (original_network.oedge e))
       \<and> distinct (map original_network.oedge C)
       \<and> original_network.fstv (hd C) = original_network.sndv (last C) \<and> set C \<subseteq> original_network.\<EE>"
  by (rule acyclic_flow_no_free_cycle[OF acyc])

end

end

end

end