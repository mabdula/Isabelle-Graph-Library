theory Matroid_Weighted_Intersection_Path_Loop
  imports Matroid_Intersection_Path_Loop Matroid_Weighted_Intersection
begin

section \<open>Weighted Matroid Intersection as a Loop over an Abstract Tight-Path Search\<close>

text \<open>The primal-dual loop of Frank's weighted matroid intersection algorithm (Korte--Vygen,
  Section 13.7). It is parametrised by a context \<open>tight_ctx X c1 c2\<close>, built once per iteration,
  from which a shortest tight augmenting path (\<open>tight_path\<close>), the reachable set (\<open>reach\<close>) and
  the reweighting amount (\<open>eps\<close>) are read off. How the tight graph is represented and searched is
  invisible here. The context is specified through abstraction functions \<open>ctx_edges\<close>, \<open>ctx_S\<close>
  and \<open>ctx_T\<close>, which are never executed.\<close>

subsection \<open>Facts about One Iteration\<close>

text \<open>ADT-free facts about a fixed common independent set and one reweighting step.\<close>

context double_matroid
begin

text \<open>Local optimality is invariant under a global constant shift.\<close>

lemma local_opt2_shift:
  assumes "X \<subseteq> carrier" "\<forall>z\<in>carrier. c' z = c z + k" "matroid2.local_opt c X"
  shows "matroid2.local_opt c' X"
proof-
  have "x \<in> carrier" if "y \<in> carrier - X" "x \<in> matroid2.the_circuit (insert y X)" for x y
    using matroid2.the_circuit_X_in_X[of "insert y X" carrier] assms(1) that
    by auto
  thus ?thesis
    using assms
    by (auto simp: matroid2.local_opt_def)
qed

text \<open>A common independent set that is locally optimal in both matroids for the split weights has
  maximum original weight among the common independent sets of the same cardinality.\<close>

lemma common_local_opt_max_worig:
  fixes c1 c2 corig :: "'a \<Rightarrow> real"
  assumes "indep1 X'" "indep2 X'" "matroid1.local_opt c1 X'" "matroid2.local_opt c2 X'"
    "\<forall> x \<in> carrier. c1 x + c2 x = corig x"
    "indep1 Y" "indep2 Y" "card Y = card X'"
  shows "sum corig Y \<le> sum corig X'"
proof-
  have "sum c1 Y \<le> sum c1 X'" "sum c2 Y \<le> sum c2 X'"
    using assms matroid1.greedy_optimality[of X' c1] matroid2.greedy_optimality[of X' c2]
    by (auto simp: matroid1.max_weight_card_def matroid2.max_weight_card_def)
  thus ?thesis
    using assms split_weight_sum[of carrier c1 c2 corig] matroid1.indep_subset_carrier
    by (simp add: add_mono)
qed

end

context weighted_intersection_graph
begin

text \<open>The set reachable from \<open>Sbar\<close> in the tight graph, and the weight gaps across its boundary:
  the gaps of the auxiliary arcs leaving it, and the distances of the sources outside it and of
  the targets inside it to the respective maximum.\<close>

definition "Rbar X = {v. \<exists> u \<in> Sbar X. u = v \<or> (\<exists> p. vwalk_bet (Gbar X) u p v)}"

definition "gaps X R =
     {c1 x - c1 y | x y. (x, y) \<in> A1 X \<and> x \<in> R \<and> y \<notin> R}
   \<union> {c2 x - c2 y | x y. (y, x) \<in> A2 X \<and> y \<in> R \<and> x \<notin> R}
   \<union> {Max (c1 ` S X) - c1 y | y. y \<in> S X \<and> y \<notin> R}
   \<union> {Max (c2 ` T X) - c2 y | y. y \<in> T X \<and> y \<in> R}"

lemma gapsE:
  assumes "g \<in> gaps X R"
  obtains (A1) x y where "(x, y) \<in> A1 X" "x \<in> R" "y \<notin> R" "g = c1 x - c1 y"
    | (A2) x y where "(y, x) \<in> A2 X" "y \<in> R" "x \<notin> R" "g = c2 x - c2 y"
    | (S) y where "y \<in> S X" "y \<notin> R" "g = Max (c1 ` S X) - c1 y"
    | (T) y where "y \<in> T X" "y \<in> R" "g = Max (c2 ` T X) - c2 y"
  using assms
  by (unfold gaps_def) blast

lemma gapsI:
  "\<lbrakk>(x, y) \<in> A1 X; x \<in> R; y \<notin> R\<rbrakk> \<Longrightarrow> c1 x - c1 y \<in> gaps X R"
  "\<lbrakk>(y, x) \<in> A2 X; y \<in> R; x \<notin> R\<rbrakk> \<Longrightarrow> c2 x - c2 y \<in> gaps X R"
  "\<lbrakk>y \<in> S X; y \<notin> R\<rbrakk> \<Longrightarrow> Max (c1 ` S X) - c1 y \<in> gaps X R"
  "\<lbrakk>y \<in> T X; y \<in> R\<rbrakk> \<Longrightarrow> Max (c2 ` T X) - c2 y \<in> gaps X R"
  unfolding gaps_def
  by blast+

lemma finite_S: "finite (S X)" and finite_T: "finite (T X)"
  using matroid1.carrier_finite
  by (auto intro: finite_subset simp add: S_def T_def)

lemma Sbar_subset_Rbar: "Sbar X \<subseteq> Rbar X"
  by (auto simp add: Rbar_def)

lemma Sbar_in_Rbar: "\<lbrakk>y \<in> S X; c1 y = Max (c1 ` S X)\<rbrakk> \<Longrightarrow> y \<in> Rbar X"
  by (auto simp: Rbar_def Sbar_def)

lemma Rbar_path:
  "v \<in> Rbar X \<Longrightarrow>
     \<exists> p u. (vwalk_bet (Gbar X) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sbar X"
  by (auto simp: Rbar_def)

lemma Rbar_nopath_Tbar:
  "\<lbrakk>\<nexists> p u v. (vwalk_bet (Gbar X) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sbar X
       \<and> v \<in> Tbar X;
    v \<in> Rbar X\<rbrakk> \<Longrightarrow> v \<notin> Tbar X"
  by (blast dest: Rbar_path)

lemma Rbar_closed:
  assumes "a \<in> Rbar X" "(a, b) \<in> Gbar X"
  shows "b \<in> Rbar X"
proof-
  obtain u where "u \<in> Sbar X" "u = a \<or> (\<exists>p. vwalk_bet (Gbar X) u p a)"
    using assms(1)
    by (auto simp: Rbar_def)
  moreover have "vwalk_bet (Gbar X) a [a, b] b"
    using assms(2)
    by (rule edges_are_vwalk_bet)
  ultimately show ?thesis
    using vwalk_bet_transitive[of "Gbar X" u _ a "[a, b]" b]
    by (auto simp: Rbar_def)
qed

lemma Rbar_subset_carrier:
  "\<lbrakk>indep1 X; indep2 X\<rbrakk> \<Longrightarrow> Rbar X \<subseteq> carrier"
  using Sbar_subset[of X] S_in_carrier[of X] dVs_subset[OF Gbar_subset[of X]] dVs_A1A2_carrier[of X]
  by (auto simp: Rbar_def dest!: vwalk_bet_endpoints(2))

lemma finite_gaps:
  assumes "indep1 X" "indep2 X"
  shows "finite (gaps X R)"
proof-
  have "finite (A1 X \<union> A2 X)"
    by (rule rev_finite_subset[of "carrier \<times> carrier"]; insert matroid1.carrier_finite X_in_carrier[OF assms];
      auto dest: A1_edges[OF assms] A2_edges[OF assms])
  moreover have "gaps X R \<subseteq> (\<lambda>e. c1 (fst e) - c1 (snd e)) ` A1 X
                   \<union> (\<lambda>e. c2 (snd e) - c2 (fst e)) ` A2 X
                   \<union> (\<lambda>y. Max (c1 ` S X) - c1 y) ` S X
                   \<union> (\<lambda>y. Max (c2 ` T X) - c2 y) ` T X"
    by (auto simp: gaps_def intro: rev_image_eqI)
  ultimately show ?thesis
    using finite_S finite_T
    by (simp add: finite_subset)
qed

text \<open>Bounds on the weights of the sources and targets derived from a lower bound on the gaps.\<close>

lemma gaps_S_bound:
  assumes "\<And> g. g \<in> gaps X R \<Longrightarrow> e \<le> g" "y \<in> S X" "y \<notin> R"
  shows "c1 y \<le> Max (c1 ` S X) - e"
  using assms(1)[of "Max (c1 ` S X) - c1 y"] assms(2,3)
  by (auto simp: gaps_def le_diff_eq add.commute)

lemma gaps_T_bound:
  assumes "\<And> g. g \<in> gaps X R \<Longrightarrow> e \<le> g" "y \<in> T X" "y \<in> R"
  shows "c2 y \<le> Max (c2 ` T X) - e"
  using assms(1)[of "Max (c2 ` T X) - c2 y"] assms(2,3)
  by (auto simp: gaps_def le_diff_eq add.commute)

lemma Smax_le:
  "\<lbrakk>matroid1.local_opt c1 X; x \<in> X; y0 \<in> S X\<rbrakk> \<Longrightarrow> Max (c1 ` S X) \<le> c1 x"
  using finite_S[of X]
  by (auto intro!: Max.boundedI simp: matroid1.local_opt_def S_def)

lemma Tmax_le:
  "\<lbrakk>matroid2.local_opt c2 X; x \<in> X; y0 \<in> T X\<rbrakk> \<Longrightarrow> Max (c2 ` T X) \<le> c2 x"
  using finite_T[of X]
  by (auto intro!: Max.boundedI simp: matroid2.local_opt_def T_def)

lemma Sbar_max:
  "\<lbrakk>u \<in> Sbar X; y \<in> carrier - X; indep1 (insert y X)\<rbrakk> \<Longrightarrow> c1 y \<le> c1 u"
  using finite_S[of X]
  by (auto simp: Sbar_def S_def)

lemma Tbar_max:
  "\<lbrakk>v \<in> Tbar X; y \<in> carrier - X; indep2 (insert y X)\<rbrakk> \<Longrightarrow> c2 y \<le> c2 v"
  using finite_T[of X]
  by (auto simp: Tbar_def T_def)

text \<open>Without a tight augmenting path, every gap across the boundary of \<open>Rbar\<close> is positive: it is
  non-negative by local optimality, and a zero gap would be a tight arc leaving \<open>Rbar\<close>, a
  maximum-weight source outside \<open>Rbar\<close> or a maximum-weight target inside it.\<close>

lemma gaps_pos:
  assumes "matroid1.local_opt c1 X" "matroid2.local_opt c2 X"
    "\<nexists> p u v. (vwalk_bet (Gbar X) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sbar X \<and> v \<in>
      Tbar X"
    "g \<in> gaps X (Rbar X)"
  shows "0 < g"
  using assms(4)
proof(cases rule: gapsE)
  case (A1 x y)
  hence "c1 x \<noteq> c1 y"
    using Rbar_closed[of x X y]
    by (auto simp: Gbar_def Abar1_def)
  thus ?thesis
    using A1 assms(1)
    by (auto simp: A1_def matroid1.local_opt_def less_le)
next
  case (A2 x y)
  hence "c2 x \<noteq> c2 y"
    using Rbar_closed[of y X x]
    by (auto simp: Gbar_def Abar2_def)
  thus ?thesis
    using A2 assms(2)
    by (auto simp: A2_def matroid2.local_opt_def less_le)
next
  case (S y)
  hence "c1 y \<le> Max (c1 ` S X)" "c1 y \<noteq> Max (c1 ` S X)"
    using finite_S[of X] Sbar_in_Rbar
    by auto
  thus ?thesis
    using S(3)
    by (simp add: less_le)
next
  case (T y)
  hence "c2 y \<le> Max (c2 ` T X)" "c2 y \<noteq> Max (c2 ` T X)"
    using finite_T[of X] assms(3) Rbar_path[of y X]
    by (auto simp: Tbar_def)
  thus ?thesis
    using T(3)
    by (simp add: less_le)
qed

text \<open>Reweighting by at most the minimum gap preserves both local optima: \<open>c1\<close> decreases on
    \<open>R\<close>,
  and \<open>c2\<close> increases on \<open>R\<close>, which is a decrease on the complement followed by a global
    shift.\<close>

lemma gaps_reweight_local_opt:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X" "matroid2.local_opt c2 X"
    "R \<subseteq> carrier" "0 < e" "\<And> g. g \<in> gaps X R \<Longrightarrow> e \<le> g"
  shows "matroid1.local_opt (\<lambda>z. if z \<in> R then c1 z - e else c1 z) X"
    and "matroid2.local_opt (\<lambda>z. if z \<in> R then c2 z + e else c2 z) X"
proof-
  show "matroid1.local_opt (\<lambda>z. if z \<in> R then c1 z - e else c1 z) X"
  proof(rule matroid1.reweight_preserves_local_opt[OF assms(1,3,5,6)])
    fix y x
    assume "y \<in> carrier - X" "x \<in> matroid1.the_circuit (insert y X) - {y}" "x \<in> R" "y \<notin> R"
    thus "e \<le> c1 x - c1 y"
      by (blast intro: assms(7)[unfolded gaps_def A1_def])
  next
    fix x y
    assume "x \<in> X" "y \<in> carrier - X" "indep1 (insert y X)" "x \<in> R" "y \<notin> R"
    hence "c1 y \<le> Max (c1 ` S X) - e" "Max (c1 ` S X) \<le> c1 x"
      using gaps_S_bound[of X R e, OF assms(7)] Smax_le[OF assms(3)]
      by (auto simp: S_def)
    thus "e \<le> c1 x - c1 y"
      by (simp add: le_diff_eq diff_le_eq add.commute)
  qed
  have "matroid2.local_opt (\<lambda>z. if z \<in> carrier - R then c2 z - e else c2 z) X"
  proof(rule matroid2.reweight_preserves_local_opt[OF assms(2,4) Diff_subset assms(6)])
    fix y x
    assume "y \<in> carrier - X" "x \<in> matroid2.the_circuit (insert y X) - {y}" "x \<in> carrier - R"
      "y \<notin> carrier - R"
    thus "e \<le> c2 x - c2 y"
      by (blast intro: assms(7)[unfolded gaps_def A2_def])
  next
    fix x y
    assume "x \<in> X" "y \<in> carrier - X" "indep2 (insert y X)" "x \<in> carrier - R" "y \<notin> carrier - R"
    hence "c2 y \<le> Max (c2 ` T X) - e" "Max (c2 ` T X) \<le> c2 x"
      using gaps_T_bound[of X R e, OF assms(7)] Tmax_le[OF assms(4)]
      by (auto simp: T_def)
    thus "e \<le> c2 x - c2 y"
      by (simp add: le_diff_eq diff_le_eq add.commute)
  qed
  thus "matroid2.local_opt (\<lambda>z. if z \<in> R then c2 z + e else c2 z) X"
    by (rule local_opt2_shift[where k = e, rotated 2])
       (use assms(2,5) matroid2.indep_subset_carrier in auto)
qed

text \<open>Without gaps, \<open>R\<close> contains \<open>S\<close>, avoids \<open>T\<close> and is closed under the
    auxiliary arcs, so there
  is no augmenting path at all.\<close>

lemma no_gaps_no_augpath:
  assumes "gaps X R = {}"
  shows "\<nexists> p x y. x \<in> S X \<and> y \<in> T X \<and> (vwalk_bet (A1 X \<union> A2 X) x p y \<or> x = y)"
proof-
  have "S X \<subseteq> R" "T X \<inter> R = {}"
    "\<And>a b. \<lbrakk>(a, b) \<in> A1 X \<union> A2 X; a \<in> R\<rbrakk> \<Longrightarrow> b \<in> R"
    using assms gapsI
    by blast+
  thus ?thesis
    using walk_stays_closed[of "A1 X \<union> A2 X" _ _ _ R]
    by blast
qed

text \<open>Reweighting by a positive lower bound of the gaps keeps every vertex of \<open>Rbar\<close> reachable:
  the maximum-weight sources stay maximal, and the tight arcs inside \<open>Rbar\<close> stay tight.\<close>

lemma Rbar_reweight_mono:
  assumes "0 < e" "\<And> g. g \<in> gaps X (Rbar X) \<Longrightarrow> e \<le> g"
  shows "Rbar X \<subseteq> weighted_intersection_graph.Rbar carrier indep1 indep2
           (\<lambda>z. if z \<in> Rbar X then c1 z - e else c1 z) (\<lambda>z. if z \<in> Rbar X then c2 z + e else
             c2 z) X"
proof-
  interpret W': weighted_intersection_graph carrier indep1 indep2
    "\<lambda>z. if z \<in> Rbar X then c1 z - e else c1 z" "\<lambda>z. if z \<in> Rbar X then c2 z + e else c2 z"
    by unfold_locales
  have sb: "Sbar X \<subseteq> W'.Sbar X"
    using argmax_reweight_mono[OF finite_S assms(1) gaps_S_bound[where R = "Rbar X", OF assms(2)] Sbar_in_Rbar]
    by (simp add: Sbar_def W'.Sbar_def)
  have tr: "vwalk_bet (W'.Gbar X) u p v \<or> (p = [u] \<and> u = v)"
    if "vwalk_bet (Gbar X) u p v" "u \<in> Rbar X" for u p v
    by (rule walk_transfer[OF that])
       (blast intro: Rbar_closed Gbar_reweight_tight)+
  show ?thesis
  proof
    fix v
    assume "v \<in> Rbar X"
    then obtain p u where "vwalk_bet (Gbar X) u p v \<or> (p = [u] \<and> u = v)" "u \<in> Sbar X"
      using Rbar_path
      by blast
    thus "v \<in> W'.Rbar X"
      using sb tr[of u p v] Sbar_subset_Rbar[of X]
      by (auto simp: W'.Rbar_def)
  qed
qed

text \<open>Reweighting by the minimum gap makes progress: the gap attaining the minimum closes, so
  either \<open>Rbar\<close> grows strictly, or a tight augmenting path appears.\<close>

lemma Rbar_reweight_progress:
  assumes "\<nexists> p u v. (vwalk_bet (Gbar X) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sbar X \<and> v
    \<in> Tbar X"
    "0 < e" "e \<in> gaps X (Rbar X)" "\<And> g. g \<in> gaps X (Rbar X) \<Longrightarrow> e \<le> g"
  defines "c1' \<equiv> \<lambda>z. if z \<in> Rbar X then c1 z - e else c1 z"
    and "c2' \<equiv> \<lambda>z. if z \<in> Rbar X then c2 z + e else c2 z"
  shows "Rbar X \<subset> weighted_intersection_graph.Rbar carrier indep1 indep2 c1' c2' X
         \<or> (\<exists> p u v. (vwalk_bet (weighted_intersection_graph.Gbar carrier indep1 indep2 c1' c2' X) u p v
                        \<or> (p = [u] \<and> u = v))
                \<and> u \<in> weighted_intersection_graph.Sbar carrier indep1 c1' X
                \<and> v \<in> weighted_intersection_graph.Tbar carrier indep2 c2' X)"
proof-
  interpret W': weighted_intersection_graph carrier indep1 indep2 c1' c2'
    by unfold_locales
  have mono: "Rbar X \<subseteq> W'.Rbar X"
    using Rbar_reweight_mono[OF assms(2,4)]
    by (simp add: c1'_def c2'_def)
  hence strict:
    "\<And>v. \<lbrakk>v \<in> W'.Rbar X; v \<notin> Rbar X\<rbrakk> \<Longrightarrow> Rbar X \<subset> W'.Rbar X"
    by blast
  from assms(3) show ?thesis
  proof(cases rule: gapsE)
    case (A1 x y)
    hence "(x, y) \<in> W'.Gbar X"
      unfolding W'.Gbar_def W'.Abar1_def
      by (simp add: c1'_def)
    thus ?thesis
      using A1(2,3) mono W'.Rbar_closed[of x X y] strict
      by blast
  next
    case (A2 x y)
    hence "(y, x) \<in> W'.Gbar X"
      unfolding W'.Gbar_def W'.Abar2_def
      by (simp add: c2'_def)
    thus ?thesis
      using A2(2,3) mono W'.Rbar_closed[of y X x] strict
      by blast
  next
    case (S y)
    have "Max (c1' ` S X) = Max (c1 ` S X) - e"
      unfolding c1'_def
      using S(1)
      by (intro argmax_reweight_newmax[OF finite_S _ assms(2)
            gaps_S_bound[where R = "Rbar X", OF assms(4)] Sbar_in_Rbar])
         auto
    hence "y \<in> W'.Sbar X"
      using S
      unfolding W'.Sbar_def
      by (simp add: c1'_def)
    thus ?thesis
      using S(2) W'.Sbar_subset_Rbar strict
      by blast
  next
    case (T y)
    have "Max (c2' ` T X) = Max (c2 ` T X)"
      unfolding c2'_def
      using T(1) Rbar_nopath_Tbar[OF assms(1)]
      by (intro argmax_reweight_keepmax[OF finite_T _ assms(2) gaps_T_bound[where R = "Rbar X", OF assms(4)]])
         (auto simp: Tbar_def)
    hence "y \<in> W'.Tbar X"
      using T
      unfolding W'.Tbar_def
      by (simp add: c2'_def)
    thus ?thesis
      using T(2) mono W'.Rbar_path[of y X]
      by blast
  qed
qed

text \<open>Augmenting along a shortest tight walk, or at a single vertex that is a maximum-weight source
  and target, keeps both matroids independent and locally optimal, adds one element, and adds the
  weights of the ends to the two sums.\<close>

lemma augment_single_tight:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X" "matroid2.local_opt c2 X"
    "u \<in> Sbar X" "u \<in> Tbar X"
  shows "indep1 (insert u X)" "indep2 (insert u X)" "card (insert u X) = card X + 1"
    "matroid1.local_opt c1 (insert u X)" "matroid2.local_opt c2 (insert u X)"
    "sum c1 (insert u X) = sum c1 X + c1 u" "sum c2 (insert u X) = sum c2 X + c2 u"
  using assms matroid1.greedy_extension[of X c1 u] matroid2.greedy_extension[of X c2 u] matroid1.indep_finite[of X]
  by (auto simp: Sbar_def Tbar_def S_def T_def add.commute)

lemma augment_tight_walk:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X" "matroid2.local_opt c2 X"
    "vwalk_bet (Gbar X) u p v \<or> (p = [u] \<and> u = v)" "u \<in> Sbar X" "v \<in> Tbar X"
    "\<nexists>q. (vwalk_bet (Gbar X) u q v \<or> (q = [u] \<and> u = v)) \<and> length q < length p"
    "X' = (X \<union> {p ! i | i. i < length p \<and> even i}) - {p ! i | i. i < length p \<and> odd i}"
  shows "set p \<subseteq> carrier \<and> distinct p \<and> hd p = u \<and> last p = v \<and>
    indep1 X' \<and> indep2 X' \<and> card X' = card X + 1 \<and>
    matroid1.local_opt c1 X' \<and> matroid2.local_opt c2 X' \<and> sum c1 X' = sum c1 X + c1 u \<and>
    sum c2 X' = sum c2 X + c2 v"
proof(cases "vwalk_bet (Gbar X) u p v")
  case True
  hence "set p \<subseteq> carrier"
    using assms(1,2) vwalk_bet_in_vertices[of "Gbar X" u p v] dVs_subset[OF Gbar_subset[of X]]
      dVs_A1A2_carrier[of X]
    by blast
  moreover have "\<nexists>q. vwalk_bet (Gbar X) u q v \<and> length q < length p"
    using assms(8)
    by blast
  ultimately show ?thesis
    using augment_tight_path[OF assms(1-4) True assms(6,7) _ assms(9)]
      shortest_vwalk_bet_distinct[of "Gbar X" u p v] True
    by (simp add: vwalk_bet_def)
next
  case False
  hence "p = [u]" "u = v"
    using assms(5)
    by auto
  thus ?thesis
    using assms(1-4,6,7,9) augment_single_tight[of X u] Sbar_subset[of X] S_in_carrier[of X]
    by auto
qed

end

subsection \<open>State and Running Minimum\<close>

text \<open>The state carries the current common independent set \<open>wsol\<close>, the current split
  \<open>wc1\<close>/\<open>wc2\<close> and the fixed original weight \<open>worig\<close>.\<close>

record ('sol, 'cmap) weighted_intersec_state =
  wsol  :: 'sol
  wc1   :: 'cmap
  wc2   :: 'cmap
  worig :: 'cmap

lemma wsol_remove: "wsol (state \<lparr> wsol := new \<rparr>) = new"
  by auto

text \<open>A running minimum (\<^const>\<open>None\<close> = \<open>\<infinity>\<close>), used by the instances to
    compute \<open>eps\<close>.
  \<open>eps_of A a\<close> folds a whole finite set of candidates into the accumulator at once.\<close>

definition "eps_min a v = (case a of None \<Rightarrow> Some v | Some w \<Rightarrow> Some (min w v))"

definition "eps_of A a = (if A = {} then a
   else (case a of None \<Rightarrow> Some (Min A) | Some w \<Rightarrow> Some (min w (Min A))))"

lemma eps_of_empty[simp]: "eps_of {} a = a"
  by (simp add: eps_of_def)

lemma eps_of_None: "eps_of A None = (if A = {} then None else Some (Min A))"
  by (simp add: eps_of_def)

lemma eps_of_single: "eps_min a v = eps_of {v} a"
  by (simp add: eps_of_def eps_min_def split: option.splits)

lemma eps_of_Un:
  fixes A B :: "'b :: linorder set"
  assumes "finite A" "finite B"
  shows "eps_of A (eps_of B a) = eps_of (A \<union> B) a"
  using assms
  by (cases "A = {} \<or> B = {}")
     (auto simp: eps_of_def Min_Un min.assoc min.left_commute min.commute split: option.splits)

lemma foldr_eps_of:
  fixes g :: "'a \<Rightarrow> 'b :: linorder"
  shows "foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) xs a
           = eps_of (g ` {x \<in> set xs. P x}) a"
proof(induction xs)
  case (Cons x xs)
  thus ?case
    by (cases "P x")
       (auto simp: eps_of_single eps_of_Un insert_absorb Collect_disj_eq image_Un
          intro: arg_cong2[where f = eps_of])
qed simp

lemma foldr_eps_of_gen:
  fixes G :: "'a \<Rightarrow> 'b :: linorder set"
  assumes "\<And>y acc. body y acc = eps_of (G y) acc" "\<And>y. finite (G y)"
  shows "foldr body ys a = eps_of (\<Union>y \<in> set ys. G y) a"
  by (induction ys) (simp_all add: assms eps_of_Un)

lemmas [code] = eps_min_def

subsection \<open>The Loop\<close>

text \<open>One iteration builds the context once. With a tight augmenting path it augments if this
  increases the weight, and stops otherwise; without one it reweights by \<open>eps\<close> on the reachable
  set, or stops if \<open>eps\<close> is \<open>\<infinity>\<close>.\<close>

locale weighted_intersection_path_loop_spec =
  intersection_augment_spec set_insert set_delete to_set set_invar set_empty
  for set_insert :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset" and set_delete to_set set_invar set_empty +
  fixes c_shift :: "'rset \<Rightarrow> real \<Rightarrow> 'cmap \<Rightarrow> 'cmap"
    and c_zero :: "'cmap"
    and c_lookup :: "'cmap \<Rightarrow> 'a \<Rightarrow> real"
    and tight_ctx :: "'mset \<Rightarrow> 'cmap \<Rightarrow> 'cmap \<Rightarrow> 'ctx"
    and tight_path :: "'ctx \<Rightarrow> 'a list option"
    and reach :: "'ctx \<Rightarrow> 'rset"
    and eps :: "'ctx \<Rightarrow> real option"
begin

text \<open>Reweighting: \<open>c1\<close> decreases and \<open>c2\<close> increases by \<open>e\<close> on
    \<open>R\<close>.\<close>

definition "reweight R e st =
  st \<lparr> wc1 := c_shift R (- e) (wc1 st), wc2 := c_shift R e (wc2 st) \<rparr>"

text \<open>The weight gain of augmenting along a tight path \<open>p\<close>: the weights of its first element in
  the first and of its last element in the second split.\<close>

definition "path_gain st p = c_lookup (wc1 st) (hd p) + c_lookup (wc2 st) (last p)"

function (domintros) weighted_matroid_intersection ::
  "('mset, 'cmap) weighted_intersec_state \<Rightarrow> ('mset, 'cmap) weighted_intersec_state" where
  "weighted_matroid_intersection st =
     (let X = wsol st; K = tight_ctx X (wc1 st) (wc2 st) in
      case tight_path K of
        Some p \<Rightarrow> (if 0 < path_gain st p
                    then weighted_matroid_intersection (st \<lparr> wsol := augment X p \<rparr>) else st)
      | None \<Rightarrow> (case eps K of
                   None \<Rightarrow> st
                 | Some e \<Rightarrow> weighted_matroid_intersection (reweight (reach K) e st)))"
  by pat_completeness auto

definition "weighted_augment_cond st =
  (let K = tight_ctx (wsol st) (wc1 st) (wc2 st) in
   case tight_path K of Some p \<Rightarrow> 0 < path_gain st p | None \<Rightarrow> False)"

definition "weighted_reweight_cond st =
  (let K = tight_ctx (wsol st) (wc1 st) (wc2 st) in tight_path K = None \<and> eps K \<noteq> None)"

definition "weighted_stop_cond st =
  (let K = tight_ctx (wsol st) (wc1 st) (wc2 st) in
   case tight_path K of Some p \<Rightarrow> \<not> 0 < path_gain st p | None \<Rightarrow> eps K = None)"

definition "weighted_augment_upd st =
  (let X = wsol st; p = the (tight_path (tight_ctx X (wc1 st) (wc2 st)))
   in st \<lparr> wsol := augment X p \<rparr>)"

definition "weighted_reweight_upd st =
  (let K = tight_ctx (wsol st) (wc1 st) (wc2 st) in reweight (reach K) (the (eps K)) st)"

lemmas weighted_loop_defs = weighted_stop_cond_def weighted_augment_cond_def
  weighted_reweight_cond_def weighted_augment_upd_def weighted_reweight_upd_def

lemma P_of_weighted_augmentI:
  "\<lbrakk>weighted_augment_cond st;
    \<And> X K p. \<lbrakk>X = wsol st; K = tight_ctx X (wc1 st) (wc2 st); tight_path K = Some p;
                0 < path_gain st p\<rbrakk> \<Longrightarrow> P (st \<lparr> wsol := augment X p \<rparr>)\<rbrakk>
   \<Longrightarrow> P (weighted_augment_upd st)"
  by (cases "tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st))")
     (auto simp add: weighted_augment_cond_def weighted_augment_upd_def Let_def)

lemma P_of_weighted_reweightI:
  "\<lbrakk>weighted_reweight_cond st;
    \<And> X K e. \<lbrakk>X = wsol st; K = tight_ctx X (wc1 st) (wc2 st); tight_path K = None;
               eps K = Some e\<rbrakk> \<Longrightarrow> P (reweight (reach K) e st)\<rbrakk>
   \<Longrightarrow> P (weighted_reweight_upd st)"
  by (cases "eps (tight_ctx (wsol st) (wc1 st) (wc2 st))")
     (auto simp add: weighted_reweight_cond_def weighted_reweight_upd_def Let_def)

lemma weighted_stop_condE:
  "\<lbrakk>weighted_stop_cond st;
    \<And> X K. \<lbrakk>X = wsol st; K = tight_ctx X (wc1 st) (wc2 st); tight_path K = None; eps K = None\<rbrakk>
       \<Longrightarrow> P;
    \<And> X K p. \<lbrakk>X = wsol st; K = tight_ctx X (wc1 st) (wc2 st); tight_path K = Some p;
       \<not> 0 < path_gain st p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases "tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st))")
     (auto simp add: weighted_stop_cond_def Let_def)

lemma weighted_matroid_intersection_cases:
  "\<lbrakk>weighted_stop_cond st \<Longrightarrow> P; weighted_augment_cond st \<Longrightarrow> P;
    weighted_reweight_cond st \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases "tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st))"; cases "eps (tight_ctx (wsol st) (wc1 st) (wc2 st))")
     (auto simp: weighted_loop_defs Let_def split: if_splits)

lemma weighted_matroid_intersection_simps:
  assumes "weighted_matroid_intersection_dom st"
  shows "weighted_stop_cond st \<Longrightarrow> weighted_matroid_intersection st = st"
    and "weighted_augment_cond st \<Longrightarrow>
           weighted_matroid_intersection st = weighted_matroid_intersection (weighted_augment_upd st)"
    and "weighted_reweight_cond st \<Longrightarrow>
           weighted_matroid_intersection st = weighted_matroid_intersection (weighted_reweight_upd st)"
  by (auto simp: weighted_matroid_intersection.psimps[OF assms] weighted_loop_defs Let_def split: option.split)

lemma weighted_matroid_intersection_induct:
  assumes "weighted_matroid_intersection_dom st"
    "\<And> st. \<lbrakk>weighted_matroid_intersection_dom st;
             weighted_augment_cond st \<Longrightarrow> P (weighted_augment_upd st);
             weighted_reweight_cond st \<Longrightarrow> P (weighted_reweight_upd st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  by (rule weighted_matroid_intersection.pinduct[OF assms(1)], rule assms(2)[simplified weighted_loop_defs Let_def])
     (auto split: option.splits)

lemma weighted_matroid_intersection_domI:
  "\<lbrakk>weighted_augment_cond st \<Longrightarrow> weighted_matroid_intersection_dom (weighted_augment_upd st);
    weighted_reweight_cond st \<Longrightarrow> weighted_matroid_intersection_dom (weighted_reweight_upd st)\<rbrakk>
     \<Longrightarrow> weighted_matroid_intersection_dom st"
  by (rule weighted_matroid_intersection.domintros) (auto simp: weighted_loop_defs Let_def)

partial_function (tailrec) weighted_matroid_intersection_impl ::
  "('mset, 'cmap) weighted_intersec_state \<Rightarrow> ('mset, 'cmap) weighted_intersec_state" where
  "weighted_matroid_intersection_impl st =
     (let X = wsol st; K = tight_ctx X (wc1 st) (wc2 st) in
      case tight_path K of
        Some p \<Rightarrow> (if 0 < path_gain st p
                    then weighted_matroid_intersection_impl (st \<lparr> wsol := augment X p \<rparr>) else st)
      | None \<Rightarrow> (case eps K of
                   None \<Rightarrow> st
                 | Some e \<Rightarrow> weighted_matroid_intersection_impl (reweight (reach K) e st)))"

lemma weighted_implementation_is_same:
  "weighted_matroid_intersection_dom st \<Longrightarrow>
     weighted_matroid_intersection_impl st = weighted_matroid_intersection st"
  by (induction st rule: weighted_matroid_intersection.pinduct)
     (subst weighted_matroid_intersection_impl.simps,
      auto simp: weighted_matroid_intersection.psimps Let_def split: option.splits)

text \<open>Initial state: \<open>X = \<emptyset>\<close> and split \<open>c1 = c\<close>, \<open>c2 =
    0\<close>.\<close>

definition "weighted_initial_state c =
  \<lparr> wsol = set_empty, wc1 = c, wc2 = c_zero, worig = c \<rparr>"

lemmas [code] = weighted_matroid_intersection_impl.simps reweight_def path_gain_def
  weighted_initial_state_def

end

subsection \<open>Correctness\<close>

text \<open>The specification of the weight maps and of the context. A context built for a locally
  optimal common independent set satisfies \<open>ctx_invar\<close>, and its abstraction is the tight graph
  \<open>Gbar\<close> with the endpoints \<open>Sbar\<close> and \<open>Tbar\<close>. The specification of
    \<open>tight_path\<close> is that of the
  unweighted @{term augmenting_path} for this graph; \<open>reach\<close> is the reachable set and \<open>eps\<close>
    the
  minimum gap (\<^const>\<open>None\<close> if there is no gap).\<close>

locale weighted_intersection_path_loop =
  weighted_intersection_path_loop_spec where set_insert = "set_insert :: 'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and c_shift = "c_shift :: 'rset \<Rightarrow> real \<Rightarrow> 'cmap \<Rightarrow> 'cmap"
    and tight_ctx = "tight_ctx :: 'mset \<Rightarrow> 'cmap \<Rightarrow> 'cmap \<Rightarrow> 'ctx"
  + intersection_augment where set_insert = set_insert and carrier = carrier
  + double_matroid where carrier = "carrier :: 'a set"
  for set_insert c_shift tight_ctx carrier +
  fixes c_invar :: "'cmap \<Rightarrow> bool"
    and r_set :: "'rset \<Rightarrow> 'a set"
    and r_invar :: "'rset \<Rightarrow> bool"
    and ctx_invar :: "'mset \<Rightarrow> 'cmap \<Rightarrow> 'cmap \<Rightarrow> 'ctx \<Rightarrow> bool"
    and ctx_edges :: "'ctx \<Rightarrow> ('a \<times> 'a) set"
    and ctx_S :: "'ctx \<Rightarrow> 'a set"
    and ctx_T :: "'ctx \<Rightarrow> 'a set"
  assumes c_zero: "c_invar c_zero" "c_lookup c_zero = (\<lambda> _. 0)"
  assumes c_shift:
    "\<And> R e c. \<lbrakk>c_invar c; r_invar R\<rbrakk> \<Longrightarrow> c_invar (c_shift R e c)"
    "\<And> R e c. \<lbrakk>c_invar c; r_invar R\<rbrakk> \<Longrightarrow>
       c_lookup (c_shift R e c) = (\<lambda> x. if x \<in> r_set R then c_lookup c x + e else c_lookup c x)"
  assumes tight_ctx:
    "\<And> X c1 c2. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep1 (to_set X); indep2 (to_set X);
        c_invar c1; c_invar c2; matroid1.local_opt (c_lookup c1) (to_set X);
        matroid2.local_opt (c_lookup c2) (to_set X)\<rbrakk>
      \<Longrightarrow> ctx_invar X c1 c2 (tight_ctx X c1 c2)"
  assumes ctx_abs:
    "\<And> X c1 c2 K. ctx_invar X c1 c2 K \<Longrightarrow> ctx_edges K =
       weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    "\<And> X c1 c2 K. ctx_invar X c1 c2 K \<Longrightarrow> ctx_S K =
       weighted_intersection_graph.Sbar carrier indep1 (c_lookup c1) (to_set X)"
    "\<And> X c1 c2 K. ctx_invar X c1 c2 K \<Longrightarrow> ctx_T K =
       weighted_intersection_graph.Tbar carrier indep2 (c_lookup c2) (to_set X)"
  assumes tight_path:
    "\<And> X c1 c2 K. ctx_invar X c1 c2 K \<Longrightarrow> tight_path K = None \<longleftrightarrow>
       (\<nexists> p u v. (vwalk_bet (ctx_edges K) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> ctx_S K \<and> v
         \<in> ctx_T K)"
    "\<And> X c1 c2 K p. \<lbrakk>ctx_invar X c1 c2 K; tight_path K = Some p\<rbrakk> \<Longrightarrow>
       \<exists> u v. (vwalk_bet (ctx_edges K) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> ctx_S K \<and> v
         \<in> ctx_T K \<and>
         (\<nexists> p'. (vwalk_bet (ctx_edges K) u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
  assumes reach:
    "\<And> X c1 c2 K. \<lbrakk>ctx_invar X c1 c2 K; tight_path K = None\<rbrakk> \<Longrightarrow> r_invar (reach K)"
    "\<And> X c1 c2 K. \<lbrakk>ctx_invar X c1 c2 K; tight_path K = None\<rbrakk> \<Longrightarrow>
       r_set (reach K) = {v. \<exists> u \<in> ctx_S K. u = v \<or> (\<exists> p. vwalk_bet (ctx_edges K) u p v)}"
  assumes eps:
    "\<And> X c1 c2 K. \<lbrakk>ctx_invar X c1 c2 K; tight_path K = None\<rbrakk> \<Longrightarrow>
       eps K = eps_of (weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1)
                 (c_lookup c2) (to_set X) (weighted_intersection_graph.Rbar carrier indep1 indep2
                 (c_lookup c1) (c_lookup c2) (to_set X))) None"
begin

text \<open>The context specification at a locally optimal common independent set, stated directly in
  terms of the tight graph.\<close>

lemma tight_ctx_props:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "matroid1.local_opt (c_lookup c1) (to_set X)"
    "matroid2.local_opt (c_lookup c2) (to_set X)"
  defines "K \<equiv> tight_ctx X c1 c2"
    and "Gb \<equiv> weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2)
               (to_set X)"
    and "Sb \<equiv> weighted_intersection_graph.Sbar carrier indep1 (c_lookup c1) (to_set X)"
    and "Tb \<equiv> weighted_intersection_graph.Tbar carrier indep2 (c_lookup c2) (to_set X)"
    and "Rb \<equiv> weighted_intersection_graph.Rbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2)
               (to_set X)"
  shows "tight_path K = None \<longleftrightarrow>
           (\<nexists> p u v. (vwalk_bet Gb u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sb \<and> v \<in> Tb)"
    and "tight_path K = Some p \<Longrightarrow>
           \<exists> u v. (vwalk_bet Gb u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sb \<and> v \<in> Tb \<and>
             (\<nexists> p'. (vwalk_bet Gb u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    and "tight_path K = None \<Longrightarrow> r_invar (reach K) \<and> r_set (reach K) = Rb"
    and "tight_path K = None \<Longrightarrow>
           eps K = eps_of (weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1)
                     (c_lookup c2) (to_set X) Rb) None"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have "ctx_invar X c1 c2 K"
    unfolding K_def
    by (rule tight_ctx[OF assms(1-8)])
  thus "tight_path K = None \<longleftrightarrow>
          (\<nexists> p u v. (vwalk_bet Gb u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sb \<and> v \<in> Tb)"
    "tight_path K = Some p \<Longrightarrow>
          \<exists> u v. (vwalk_bet Gb u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sb \<and> v \<in> Tb \<and>
            (\<nexists> p'. (vwalk_bet Gb u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    "tight_path K = None \<Longrightarrow> r_invar (reach K) \<and> r_set (reach K) = Rb"
    "tight_path K = None \<Longrightarrow>
          eps K = eps_of (weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1)
                    (c_lookup c2) (to_set X) Rb) None"
    using tight_path[of X c1 c2 K] reach[of X c1 c2 K] eps[of X c1 c2 K] ctx_abs[of X c1 c2 K]
    by (simp_all add: Gb_def Sb_def Tb_def Rb_def W.Rbar_def)
qed

text \<open>The loop invariant: \<open>wsol\<close> is a common independent set that is locally optimal for the
  split in both matroids, the split sums to the original weight, and \<open>wsol\<close> has maximum weight
  among the common independent sets of cardinality at most \<open>card wsol\<close>.\<close>

definition "w_invar s \<longleftrightarrow>
  set_invar (wsol s) \<and> to_set (wsol s) \<subseteq> carrier
  \<and> indep1 (to_set (wsol s)) \<and> indep2 (to_set (wsol s))
  \<and> c_invar (wc1 s) \<and> c_invar (wc2 s) \<and> c_invar (worig s)
  \<and> (\<forall>x\<in>carrier. c_lookup (wc1 s) x + c_lookup (wc2 s) x = c_lookup (worig s) x)
  \<and> matroid1.local_opt (c_lookup (wc1 s)) (to_set (wsol s))
  \<and> matroid2.local_opt (c_lookup (wc2 s)) (to_set (wsol s))
  \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set (wsol s))
        \<longrightarrow> sum (c_lookup (worig s)) Y \<le> sum (c_lookup (worig s)) (to_set (wsol s)))"


lemma w_invar_initial:
  "c_invar c \<Longrightarrow> w_invar (weighted_initial_state c)"
  using matroid1.greedy_optimality[of "{}" "c_lookup c"]
    matroid2.greedy_optimality[of "{}" "c_lookup c_zero"] set_empty c_zero matroid1.indep_empty
    matroid2.indep_empty matroid1.indep_finite matroid2.indep_finite
  by (auto simp: w_invar_def weighted_initial_state_def matroid1.max_weight_card_def
        matroid2.max_weight_card_def)

text \<open>A tight path found for a state satisfying the invariant is a shortest tight walk, or a single
  tight vertex.\<close>

lemma w_invar_tight_path:
  assumes "w_invar st" "tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st)) = Some p"
  obtains u v where
    "vwalk_bet (weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup (wc1 st))
       (c_lookup (wc2 st)) (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> weighted_intersection_graph.Sbar carrier indep1 (c_lookup (wc1 st)) (to_set (wsol st))"
    "v \<in> weighted_intersection_graph.Tbar carrier indep2 (c_lookup (wc2 st)) (to_set (wsol st))"
    "\<nexists> q. (vwalk_bet (weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup (wc1 st))
       (c_lookup (wc2 st)) (to_set (wsol st))) u q v \<or> (q = [u] \<and> u = v)) \<and> length q < length p"
  using assms tight_ctx_props(2)[of "wsol st" "wc1 st" "wc2 st" p]
  by (auto simp: w_invar_def)

lemma w_invar_no_tight_path:
  "w_invar st \<Longrightarrow> tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st)) = None \<longleftrightarrow>
     (\<nexists> p u v. (vwalk_bet (weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup (wc1 st))
                   (c_lookup (wc2 st)) (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
       \<and> u \<in> weighted_intersection_graph.Sbar carrier indep1 (c_lookup (wc1 st)) (to_set (wsol st))
       \<and> v \<in> weighted_intersection_graph.Tbar carrier indep2 (c_lookup (wc2 st)) (to_set (wsol st)))"
  using tight_ctx_props(1)[of "wsol st" "wc1 st" "wc2 st"]
  by (simp add: w_invar_def)

text \<open>Augment branch: a shortest tight path (or a single tight vertex) keeps both matroids
  independent and locally optimal and adds one element. The original weight grows by the gain of
  the path, which is positive, so the new set is heavier than all smaller common independent
  sets.\<close>

lemma augment_w_invar:
  assumes "w_invar st" "tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st)) = Some p"
    "0 < path_gain st p"
  shows "w_invar (st \<lparr> wsol := augment (wsol st) p \<rparr>)"
    "card (to_set (augment (wsol st) p)) = card (to_set (wsol st)) + 1"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st)"
    "c_lookup (wc2 st)"
    by unfold_locales
  define Xp where "Xp = (to_set (wsol st) \<union> {p ! i | i. i < length p \<and> even i})
                          - {p ! i | i. i < length p \<and> odd i}"
  obtain u v where "vwalk_bet (W.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> W.Sbar (to_set (wsol st))" "v \<in> W.Tbar (to_set (wsol st))"
    "\<nexists>q. (vwalk_bet (W.Gbar (to_set (wsol st))) u q v \<or> (q = [u] \<and> u = v)) \<and> length q < length p"
    by (rule w_invar_tight_path[OF assms(1,2)])
  hence aug: "set p \<subseteq> carrier \<and> distinct p \<and> hd p = u \<and> last p = v \<and> indep1 Xp \<and>
    indep2 Xp \<and> card Xp = card (to_set (wsol st)) + 1 \<and>
    matroid1.local_opt (c_lookup (wc1 st)) Xp \<and> matroid2.local_opt (c_lookup (wc2 st)) Xp \<and>
    sum (c_lookup (wc1 st)) Xp = sum (c_lookup (wc1 st)) (to_set (wsol st)) + c_lookup (wc1 st) u \<and>
    sum (c_lookup (wc2 st)) Xp = sum (c_lookup (wc2 st)) (to_set (wsol st)) + c_lookup (wc2 st) v"
    using W.augment_tight_walk[OF _ _ _ _ _ _ _ _ Xp_def] assms(1)
    by (simp add: w_invar_def)
  hence "set_invar (augment (wsol st) p)" "to_set (augment (wsol st) p) = Xp"
    using assms(1) effect_of_augmentation[of "wsol st" p Xp]
    by (auto simp: w_invar_def Xp_def)
  moreover have "sum (c_lookup (worig st)) (to_set (wsol st)) < sum (c_lookup (worig st)) Xp"
    using aug assms split_weight_sum[of carrier "c_lookup (wc1 st)" "c_lookup (wc2 st)"]
      matroid1.indep_subset_carrier
    by (auto simp: w_invar_def path_gain_def)
  moreover have "sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) Xp"
    if "indep1 Y" "indep2 Y" "card Y \<le> card Xp" for Y
    using that aug assms(1) calculation(3)
      common_local_opt_max_worig[of Xp "c_lookup (wc1 st)" "c_lookup (wc2 st)" "c_lookup (worig st)" Y]
    by (cases "card Y \<le> card (to_set (wsol st))") (force simp: w_invar_def)+
  ultimately show "w_invar (st \<lparr> wsol := augment (wsol st) p \<rparr>)"
    "card (to_set (augment (wsol st) p)) = card (to_set (wsol st)) + 1"
    using aug assms(1) matroid1.indep_subset_carrier
    by (auto simp: w_invar_def)
qed

lemma weighted_augment_props:
  assumes "w_invar st" "weighted_augment_cond st"
  shows "w_invar (weighted_augment_upd st) \<and>
         card (to_set (wsol (weighted_augment_upd st))) = card (to_set (wsol st)) + 1"
  by (rule P_of_weighted_augmentI[OF assms(2)]) (use augment_w_invar[OF assms(1)] in auto)

lemmas w_invar_augment = weighted_augment_props[THEN conjunct1]
lemmas weighted_augment_card = weighted_augment_props[THEN conjunct2]

text \<open>The facts of the reweight branch: the reachable set, the minimum gap and its positivity.\<close>

lemma reweight_facts:
  assumes "w_invar st" "K = tight_ctx (wsol st) (wc1 st) (wc2 st)" "tight_path K = None"
    "eps K = Some e"
  defines "R \<equiv> weighted_intersection_graph.Rbar carrier indep1 indep2 (c_lookup (wc1 st))
                 (c_lookup (wc2 st)) (to_set (wsol st))"
    and "G \<equiv> weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup (wc1 st))
                 (c_lookup (wc2 st)) (to_set (wsol st))
                 (weighted_intersection_graph.Rbar carrier indep1 indep2 (c_lookup (wc1 st))
                    (c_lookup (wc2 st)) (to_set (wsol st)))"
  shows "r_invar (reach K)" "r_set (reach K) = R" "0 < e" "e \<in> G" "\<And> g. g \<in> G \<Longrightarrow> e \<le> g"
    "\<nexists> p u v. (vwalk_bet (weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup (wc1 st))
                 (c_lookup (wc2 st)) (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
       \<and> u \<in> weighted_intersection_graph.Sbar carrier indep1 (c_lookup (wc1 st)) (to_set (wsol st))
       \<and> v \<in> weighted_intersection_graph.Tbar carrier indep2 (c_lookup (wc2 st)) (to_set (wsol st))"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st)"
    "c_lookup (wc2 st)"
    by unfold_locales
  have "r_invar (reach K)" "r_set (reach K) = R" "finite G" "G \<noteq> {}" "e = Min G"
    "\<nexists> p u v. (vwalk_bet (W.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
       \<and> u \<in> W.Sbar (to_set (wsol st)) \<and> v \<in> W.Tbar (to_set (wsol st))"
    using assms(1-4) tight_ctx_props[of "wsol st" "wc1 st" "wc2 st"] W.finite_gaps
    by (auto simp: w_invar_def R_def G_def eps_of_None split: if_splits)
  thus "r_invar (reach K)" "r_set (reach K) = R" "e \<in> G" "\<And> g. g \<in> G \<Longrightarrow> e \<le> g"
    "\<nexists> p u v. (vwalk_bet (W.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
       \<and> u \<in> W.Sbar (to_set (wsol st)) \<and> v \<in> W.Tbar (to_set (wsol st))"
    "0 < e"
    using assms(1) W.gaps_pos[of "to_set (wsol st)" e]
    by (auto simp: w_invar_def G_def)
qed

text \<open>The weights after a reweight step.\<close>

lemma reweight_lookup:
  assumes "w_invar st" "K = tight_ctx (wsol st) (wc1 st) (wc2 st)" "tight_path K = None"
    "eps K = Some e"
  defines "R \<equiv> weighted_intersection_graph.Rbar carrier indep1 indep2 (c_lookup (wc1 st))
                 (c_lookup (wc2 st)) (to_set (wsol st))"
  shows "c_lookup (wc1 (reweight (reach K) e st)) =
           (\<lambda>z. if z \<in> R then c_lookup (wc1 st) z - e else c_lookup (wc1 st) z)"
    "c_lookup (wc2 (reweight (reach K) e st)) =
           (\<lambda>z. if z \<in> R then c_lookup (wc2 st) z + e else c_lookup (wc2 st) z)"
    "c_invar (wc1 (reweight (reach K) e st))" "c_invar (wc2 (reweight (reach K) e st))"
  using assms(1) reweight_facts(1,2)[OF assms(1-4)] c_shift[of "wc1 st" "reach K"]
    c_shift[of "wc2 st" "reach K"]
  by (auto simp: reweight_def R_def w_invar_def fun_eq_iff)

text \<open>Reweight branch: the shift by the minimum gap keeps both local optima, and the split still
  sums to the original weight.\<close>

lemma w_invar_reweight:
  assumes "w_invar st" "weighted_reweight_cond st"
  shows "w_invar (weighted_reweight_upd st)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st)"
    "c_lookup (wc2 st)"
    by unfold_locales
  show ?thesis
  proof(rule P_of_weighted_reweightI[OF assms(2)])
    fix X K e
    assume "X = wsol st" "K = tight_ctx X (wc1 st) (wc2 st)" "tight_path K = None" "eps K = Some e"
    moreover hence
      "matroid1.local_opt (\<lambda>z. if z \<in> W.Rbar (to_set X) then c_lookup (wc1 st) z - e
         else c_lookup (wc1 st) z) (to_set X)"
      "matroid2.local_opt (\<lambda>z. if z \<in> W.Rbar (to_set X) then c_lookup (wc2 st) z + e
         else c_lookup (wc2 st) z) (to_set X)"
      using assms(1) reweight_facts(3,5)[of st K e] W.Rbar_subset_carrier[of "to_set X"]
      by (auto simp: w_invar_def intro!: W.gaps_reweight_local_opt)
    ultimately show "w_invar (reweight (reach K) e st)"
      using assms(1) reweight_lookup[of st K e]
      by (auto simp: w_invar_def reweight_def)
  qed
qed

text \<open>Stop branch: \<open>wsol\<close> is optimal. Without a tight path and without gaps there is no
  augmenting path at all, so \<open>wsol\<close> has maximum cardinality. If a tight path does not increase
  the weight, then no element addable to \<open>wsol\<close> weighs more than its ends, so each element
  beyond \<open>card wsol\<close> adds at most the non-positive gain.\<close>

lemma no_gaps_opt:
  assumes "w_invar st" "tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st)) = None"
    "eps (tight_ctx (wsol st) (wc1 st) (wc2 st)) = None" "indep1 Y" "indep2 Y"
  shows "sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wsol st))"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st)"
    "c_lookup (wc2 st)"
    by unfold_locales
  have "W.gaps (to_set (wsol st)) (W.Rbar (to_set (wsol st))) = {}"
    using assms(1-3) tight_ctx_props(4)[of "wsol st" "wc1 st" "wc2 st"]
    by (auto simp: w_invar_def eps_of_None split: if_splits)
  hence "\<not> card (to_set (wsol st)) < card Y"
    using assms(1,4,5) if_no_augpath_then_maximum(1)[OF _ _ W.no_gaps_no_augpath refl]
    by (auto simp: w_invar_def)
  thus ?thesis
    using assms(1,4,5)
    by (auto simp: w_invar_def not_less)
qed

lemma nonpos_gain_opt:
  assumes "w_invar st" "tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st)) = Some p"
    "\<not> 0 < path_gain st p" "indep1 Y" "indep2 Y"
  shows "sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wsol st))"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st)"
    "c_lookup (wc2 st)"
    by unfold_locales
  obtain u v where uv: "u \<in> W.Sbar (to_set (wsol st))" "v \<in> W.Tbar (to_set (wsol st))"
    "c_lookup (wc1 st) u + c_lookup (wc2 st) v \<le> 0"
    by (rule w_invar_tight_path[OF assms(1,2)]; insert assms(3); auto simp: path_gain_def vwalk_bet_def)
  show ?thesis
  proof(cases "card Y \<le> card (to_set (wsol st))")
    case True
    thus ?thesis
      using assms(1,4,5)
      by (auto simp: w_invar_def)
  next
    case False
    then obtain k where "card Y = card (to_set (wsol st)) + k"
      using le_Suc_ex[of "card (to_set (wsol st))" "card Y"]
      by auto
    hence "sum (c_lookup (wc1 st)) Y
             \<le> sum (c_lookup (wc1 st)) (to_set (wsol st)) + real k * c_lookup (wc1 st) u"
      "sum (c_lookup (wc2 st)) Y
             \<le> sum (c_lookup (wc2 st)) (to_set (wsol st)) + real k * c_lookup (wc2 st) v"
      using assms(1,4,5) uv(1,2) W.Sbar_max W.Tbar_max
        matroid1.local_opt_larger_bound[of _ "c_lookup (wc1 st)" Y k "c_lookup (wc1 st) u"]
        matroid2.local_opt_larger_bound[of _ "c_lookup (wc2 st)" Y k "c_lookup (wc2 st) v"]
      by (auto simp: w_invar_def)
    moreover have "real k * (c_lookup (wc1 st) u + c_lookup (wc2 st) v) \<le> 0"
      using uv(3)
      by (simp add: mult_nonneg_nonpos)
    ultimately show ?thesis
      using assms(1,4) matroid1.indep_subset_carrier
        split_weight_sum[of carrier "c_lookup (wc1 st)" "c_lookup (wc2 st)" "c_lookup (worig st)"]
      by (auto simp: w_invar_def distrib_left)
  qed
qed

lemma w_invar_max_found:
  assumes "w_invar st" "weighted_stop_cond st"
  shows "\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
           sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wsol st))"
  using assms
  by (auto elim!: weighted_stop_condE intro: no_gaps_opt nonpos_gain_opt)

text \<open>Termination: augmentation increases \<open>wsol\<close>, and between two augmentations reweighting
  increases \<open>Rbar\<close> or creates a tight path.\<close>

definition "wmeasure st =
  (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2)
  + 2 * (card carrier - card (weighted_intersection_graph.Rbar carrier indep1 indep2
                               (c_lookup (wc1 st)) (c_lookup (wc2 st)) (to_set (wsol st))))
  + (if tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st)) = None then 1 else 0)"

lemma measure_dec_helper:
  fixes N r r' :: nat
  shows "\<lbrakk>r \<le> r'; r' \<le> N; r < r' \<or> \<not> b'\<rbrakk> \<Longrightarrow>
           A + 2 * (N - r') + (if b' then 1 else 0) < A + 2 * (N - r) + 1"
  by (cases b') auto

lemma measure_aug_helper:
  fixes N c r' x :: nat
  assumes "c + 1 \<le> N" "x \<le> 1"
  shows "(N - (c + 1)) * (2 * N + 2) + 2 * (N - r') + x < (N - c) * (2 * N + 2) + y + z"
proof-
  have "N - c = (N - (c + 1)) + 1"
    using assms(1)
    by simp
  hence "(N - c) * (2 * N + 2) = (N - (c + 1)) * (2 * N + 2) + (2 * N + 2)"
    by simp
  moreover have "N - r' \<le> N"
    by simp
  ultimately show ?thesis
    using assms(2)
    by linarith
qed

lemma wmeasure_reweight_dec:
  assumes "w_invar st" "weighted_reweight_cond st"
  shows "wmeasure (weighted_reweight_upd st) < wmeasure st"
proof-
  define K where "K = tight_ctx (wsol st) (wc1 st) (wc2 st)"
  define st' where "st' = weighted_reweight_upd st"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st)"
    "c_lookup (wc2 st)"
    by unfold_locales
  interpret W': weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st')"
    "c_lookup (wc2 st')"
    by unfold_locales
  obtain e where e: "tight_path K = None" "eps K = Some e" "st' = reweight (reach K) e st"
    using assms(2)
    by (auto simp: weighted_reweight_cond_def weighted_reweight_upd_def st'_def K_def Let_def)
  note rf = reweight_facts[OF assms(1) K_def e(1,2)]
  note cs = reweight_lookup(1,2)[OF assms(1) K_def e(1,2), folded e(3)]
  have state: "wsol st' = wsol st" "w_invar st'"
    using e(3) assms w_invar_reweight[of st]
    by (simp_all add: reweight_def st'_def)
  have "W.Rbar (to_set (wsol st)) \<subseteq> W'.Rbar (to_set (wsol st))"
    using rf(3,5)
    unfolding cs
    by (rule W.Rbar_reweight_mono)
  moreover have "W.Rbar (to_set (wsol st)) \<subset> W'.Rbar (to_set (wsol st))
     \<or> (\<exists> p u v. (vwalk_bet (W'.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
            \<and> u \<in> W'.Sbar (to_set (wsol st)) \<and> v \<in> W'.Tbar (to_set (wsol st)))"
    using rf(6,3,4,5)
    unfolding cs
    by (rule W.Rbar_reweight_progress)
  moreover have "W'.Rbar (to_set (wsol st)) \<subseteq> carrier"
    using assms(1) W'.Rbar_subset_carrier
    by (auto simp: w_invar_def)
  moreover hence "finite (W'.Rbar (to_set (wsol st)))"
    using matroid1.carrier_finite
    by (rule finite_subset)
  ultimately have "card (W.Rbar (to_set (wsol st))) \<le> card (W'.Rbar (to_set (wsol st)))"
    "card (W'.Rbar (to_set (wsol st))) \<le> card carrier"
    "card (W.Rbar (to_set (wsol st))) < card (W'.Rbar (to_set (wsol st)))
     \<or> (\<exists> p u v. (vwalk_bet (W'.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
            \<and> u \<in> W'.Sbar (to_set (wsol st)) \<and> v \<in> W'.Tbar (to_set (wsol st)))"
    using matroid1.carrier_finite
    by (auto intro: card_mono psubset_card_mono)
  thus ?thesis
    using e(1) state w_invar_no_tight_path[of st']
    by (auto simp: wmeasure_def K_def simp flip: st'_def)
qed

lemma wmeasure_augment_dec:
  assumes "w_invar st" "weighted_augment_cond st"
  shows "wmeasure (weighted_augment_upd st) < wmeasure st"
proof-
  have "card (to_set (wsol (weighted_augment_upd st))) = card (to_set (wsol st)) + 1"
    "to_set (wsol (weighted_augment_upd st)) \<subseteq> carrier"
    using weighted_augment_card[OF assms] w_invar_augment[OF assms]
    by (auto simp: w_invar_def)
  moreover hence "card (to_set (wsol st)) + 1 \<le> card carrier"
    using matroid1.carrier_finite card_mono[of carrier "to_set (wsol (weighted_augment_upd st))"]
    by simp
  ultimately show ?thesis
    unfolding wmeasure_def
    by (simp only:) (rule measure_aug_helper; simp)
qed

lemma weighted_matroid_intersection_terminates:
  assumes "w_invar st" "m = wmeasure st"
  shows "weighted_matroid_intersection_dom st"
  using assms
proof(induction m arbitrary: st rule: less_induct)
  case (less m st)
  hence "\<And>st'. \<lbrakk>wmeasure st' < wmeasure st; w_invar st'\<rbrakk> \<Longrightarrow>
           weighted_matroid_intersection_dom st'"
    by blast
  thus ?case
    using less.prems(1) wmeasure_reweight_dec[of st] wmeasure_augment_dec[of st]
      w_invar_reweight[of st] w_invar_augment[of st]
    by (blast intro: weighted_matroid_intersection_domI)
qed

text \<open>Partial correctness: the original weight is never changed, and when the loop stops,
  \<open>wsol\<close> is optimal.\<close>

lemma weighted_worig_preserved:
  "weighted_matroid_intersection_dom st \<Longrightarrow> worig (weighted_matroid_intersection st) = worig st"
  by (induction rule: weighted_matroid_intersection.pinduct)
     (auto simp: weighted_matroid_intersection.psimps reweight_def Let_def split: option.splits)

lemma weighted_correctness_general:
  assumes "weighted_matroid_intersection_dom st" "w_invar st"
  shows "indep1 (to_set (wsol (weighted_matroid_intersection st)))
       \<and> indep2 (to_set (wsol (weighted_matroid_intersection st)))
       \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
            sum (c_lookup (worig (weighted_matroid_intersection st))) Y
              \<le> sum (c_lookup (worig (weighted_matroid_intersection st)))
                     (to_set (wsol (weighted_matroid_intersection st))))"
  using assms(2)
proof(induction st rule: weighted_matroid_intersection_induct)
  case (2 st)
  thus ?case
    using w_invar_max_found[of st] w_invar_augment[of st] w_invar_reweight[of st]
    by (cases st rule: weighted_matroid_intersection_cases)
       (auto simp: weighted_matroid_intersection_simps dest: w_invar_def[THEN iffD1])
qed (rule assms(1))

lemma weighted_matroid_intersection_partial_correct:
  assumes "c_invar c" "weighted_matroid_intersection_dom (weighted_initial_state c)"
  defines "s \<equiv> weighted_matroid_intersection (weighted_initial_state c)"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c) (to_set (wsol s))"
proof-
  interpret WDM: weighted_double_matroid carrier indep1 indep2 "c_lookup c"
    by unfold_locales
  show ?thesis
    using weighted_worig_preserved[OF assms(2)]
      weighted_correctness_general[OF assms(2) w_invar_initial[OF assms(1)]]
    by (simp add: s_def weighted_initial_state_def WDM.is_opt_def)
qed

lemma weighted_matroid_intersection_correct:
  assumes "c_invar c"
  defines "s \<equiv> weighted_matroid_intersection (weighted_initial_state c)"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c) (to_set (wsol s))"
  by (simp add: assms weighted_matroid_intersection_partial_correct weighted_matroid_intersection_terminates
        w_invar_initial)

lemma same_result:
  "c_invar c \<Longrightarrow> weighted_matroid_intersection_impl (weighted_initial_state c)
                   = weighted_matroid_intersection (weighted_initial_state c)"
  by (simp add: weighted_implementation_is_same weighted_matroid_intersection_terminates
        w_invar_initial)

lemma impl_total_correctness:
  assumes "c_invar c"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c)
           (to_set (wsol (weighted_matroid_intersection_impl (weighted_initial_state c))))"
  using assms
  by (simp add: weighted_matroid_intersection_correct same_result)

end

end
