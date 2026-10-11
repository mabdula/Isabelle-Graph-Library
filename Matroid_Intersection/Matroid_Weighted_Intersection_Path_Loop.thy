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

text \<open>A walk stays inside any vertex set closed under its arcs.\<close>

lemma walk_stays_closed:
  assumes "vwalk_bet E x p y" "x \<in> R" "\<And>a b. \<lbrakk>(a, b) \<in> E; a \<in> R\<rbrakk> \<Longrightarrow> b \<in> R"
  shows "y \<in> R"
proof -
  have "x \<in> R \<longrightarrow> y \<in> R" using assms(1)
  proof (induction rule: induct_vwalk_bet)
    case (path1 v) thus ?case by simp
  next
    case (path2 v v' vs b) thus ?case using assms(3) by auto
  qed
  thus ?thesis using assms(2) by simp
qed

text \<open>A walk transfers to another digraph as long as its source lies in a set \<open>R\<close> that is closed
  under the original arcs and whose out-arcs are preserved.\<close>

lemma walk_transfer:
  assumes "vwalk_bet E u p v" "u \<in> R"
    "\<And>a b. \<lbrakk>(a, b) \<in> E; a \<in> R\<rbrakk> \<Longrightarrow> b \<in> R"
    "\<And>a b. \<lbrakk>(a, b) \<in> E; a \<in> R\<rbrakk> \<Longrightarrow> (a, b) \<in> E'"
  shows "vwalk_bet E' u p v \<or> (p = [u] \<and> u = v)"
proof -
  have "u \<in> R \<longrightarrow> vwalk_bet E' u p v \<or> (p = [u] \<and> u = v)" using assms(1)
  proof (induction rule: induct_vwalk_bet)
    case (path1 x) show ?case by auto
  next
    case (path2 x x' xs b)
    show ?case
    proof (rule impI)
      assume xR: "x \<in> R"
      have e': "(x, x') \<in> E'" using path2(1) assms(4) xR by auto
      have x'R: "x' \<in> R" using path2(1) assms(3) xR by auto
      from path2(3) x'R have "vwalk_bet E' x' (x' # xs) b \<or> (x' # xs = [x'] \<and> x' = b)" by simp
      thus "vwalk_bet E' x (x # x' # xs) b \<or> (x # x' # xs = [x] \<and> x = b)"
      proof
        assume "vwalk_bet E' x' (x' # xs) b"
        thus ?thesis using e' by (simp add: vwalk_bet2)
      next
        assume "x' # xs = [x'] \<and> x' = b"
        thus ?thesis using e' edges_are_vwalk_bet by fastforce
      qed
    qed
  qed
  thus ?thesis using assms(2) by simp
qed

context double_matroid
begin

text \<open>Local optimality is invariant under a global constant shift and under agreement on the
  carrier.\<close>

lemma local_opt2_add: "matroid2.local_opt c Y \<Longrightarrow> matroid2.local_opt (\<lambda>z. c z + k) Y"
  by (auto simp add: matroid2.local_opt_def add_right_mono)

lemma local_opt2_cong_imp:
  assumes "X \<subseteq> carrier" "\<forall>z\<in>carrier. c z = c' z" "matroid2.local_opt c X"
  shows "matroid2.local_opt c' X"
  unfolding matroid2.local_opt_def
proof (intro conjI ballI impI)
  fix y x assume yx: "y \<in> carrier - X" "x \<in> matroid2.the_circuit (Set.insert y X) - {y}"
  have "Set.insert y X \<subseteq> carrier" using assms(1) yx(1) by auto
  hence xc: "x \<in> carrier" using yx(2) matroid2.the_circuit_X_in_X[of "Set.insert y X" carrier] by auto
  have "c y \<le> c x" using assms(3) yx by (auto simp add: matroid2.local_opt_def)
  thus "c' y \<le> c' x" using assms(2) xc yx(1) by auto
next
  fix x y assume xy: "x \<in> X" "y \<in> carrier - X" "indep2 (Set.insert y X)"
  have "c y \<le> c x" using assms(3) xy by (auto simp add: matroid2.local_opt_def)
  thus "c' y \<le> c' x" using assms(1,2) xy by auto
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
  have Yc: "Y \<subseteq> carrier" and Xc: "X' \<subseteq> carrier"
    using matroid1.indep_subset_carrier assms(6,1) by auto
  have c1le: "sum c1 Y \<le> sum c1 X'"
    using matroid1.greedy_optimality[OF assms(1), THEN iffD2, OF assms(3)] assms(6,8)
    by (auto simp add: matroid1.max_weight_card_def)
  have c2le: "sum c2 Y \<le> sum c2 X'"
    using matroid2.greedy_optimality[OF assms(2), THEN iffD2, OF assms(4)] assms(7,8)
    by (auto simp add: matroid2.max_weight_card_def)
  have split: "sum corig Z = sum c1 Z + sum c2 Z" if "Z \<subseteq> carrier" for Z
  proof-
    have "sum corig Z = (\<Sum>x\<in>Z. c1 x + c2 x)"
      by (rule sum.cong[OF refl]) (use assms(5) that in auto)
    thus ?thesis by (simp add: sum.distrib)
  qed
  show ?thesis using c1le c2le split[OF Yc] split[OF Xc] by linarith
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

lemma finite_S: "finite (S X)" and finite_T: "finite (T X)"
  using matroid1.carrier_finite by (auto intro: finite_subset simp add: S_def T_def)

lemma Sbar_subset_Rbar: "Sbar X \<subseteq> Rbar X"
  by (auto simp add: Rbar_def)

lemma Rbar_closed:
  assumes "a \<in> Rbar X" "(a, b) \<in> Gbar X"
  shows "b \<in> Rbar X"
proof -
  from assms(1) obtain u where u: "u \<in> Sbar X" "u = a \<or> (\<exists>p. vwalk_bet (Gbar X) u p a)"
    by (auto simp add: Rbar_def)
  have ab: "vwalk_bet (Gbar X) a [a, b] b" using assms(2) by (rule edges_are_vwalk_bet)
  have "\<exists>p. vwalk_bet (Gbar X) u p b"
  proof (cases "u = a")
    case True
    show ?thesis using ab unfolding True by (intro exI)
  next
    case False
    then obtain p where "vwalk_bet (Gbar X) u p a" using u(2) by blast
    from vwalk_bet_transitive[OF this ab] show ?thesis by (intro exI)
  qed
  thus ?thesis using u(1) by (auto simp add: Rbar_def)
qed

lemma Rbar_subset_carrier:
  assumes "indep1 X" "indep2 X"
  shows "Rbar X \<subseteq> carrier"
proof
  fix v assume "v \<in> Rbar X"
  then obtain u where u: "u \<in> Sbar X" "u = v \<or> (\<exists>p. vwalk_bet (Gbar X) u p v)"
    by (auto simp add: Rbar_def)
  show "v \<in> carrier"
  proof (cases "u = v")
    case True thus ?thesis using u(1) Sbar_subset S_in_carrier[OF assms] by auto
  next
    case False
    then obtain p where "vwalk_bet (Gbar X) u p v" using u(2) by auto
    hence "v \<in> dVs (Gbar X)" using vwalk_bet_endpoints by fastforce
    thus ?thesis using dVs_subset[OF Gbar_subset] dVs_A1A2_carrier[OF assms] by (meson subsetD)
  qed
qed

lemma finite_gaps:
  assumes "indep1 X" "indep2 X"
  shows "finite (gaps X R)"
proof-
  have fin: "finite (carrier \<times> carrier)"
    using matroid1.carrier_finite by simp
  have "A1 X \<subseteq> carrier \<times> carrier"
  proof
    fix e assume e: "e \<in> A1 X"
    show "e \<in> carrier \<times> carrier"
      using A1_edges[OF assms e] X_in_carrier[OF assms] by (cases e) auto
  qed
  moreover have "A2 X \<subseteq> carrier \<times> carrier"
  proof
    fix e assume e: "e \<in> A2 X"
    show "e \<in> carrier \<times> carrier"
      using A2_edges[OF assms e] X_in_carrier[OF assms] by (cases e) auto
  qed
  ultimately have fA: "finite (A1 X)" "finite (A2 X)"
    using finite_subset[OF _ fin] by auto
  have "gaps X R \<subseteq> (\<lambda>e. c1 (fst e) - c1 (snd e)) ` A1 X \<union> (\<lambda>e. c2 (snd e) - c2 (fst e)) ` A2 X
                   \<union> (\<lambda>y. Max (c1 ` S X) - c1 y) ` S X \<union> (\<lambda>y. Max (c2 ` T X) - c2 y) ` T X"
    unfolding gaps_def by (auto intro: rev_image_eqI)
  thus ?thesis
    using fA finite_S finite_T by (auto intro: finite_subset)
qed

text \<open>Bounds on the weights of the sources and targets derived from a lower bound on the gaps.\<close>

lemma gaps_S_bound:
  assumes "\<And> g. g \<in> gaps X R \<Longrightarrow> e \<le> g" "y \<in> S X" "y \<notin> R"
  shows "c1 y \<le> Max (c1 ` S X) - e"
proof-
  have "e \<le> Max (c1 ` S X) - c1 y"
    using assms by (auto simp add: gaps_def)
  thus ?thesis by (simp add: le_diff_eq add.commute)
qed

lemma gaps_T_bound:
  assumes "\<And> g. g \<in> gaps X R \<Longrightarrow> e \<le> g" "y \<in> T X" "y \<in> R"
  shows "c2 y \<le> Max (c2 ` T X) - e"
proof-
  have "e \<le> Max (c2 ` T X) - c2 y"
    using assms by (auto simp add: gaps_def)
  thus ?thesis by (simp add: le_diff_eq add.commute)
qed

lemma Smax_le:
  assumes "matroid1.local_opt c1 X" "x \<in> X" "y0 \<in> S X"
  shows "Max (c1 ` S X) \<le> c1 x"
proof -
  have "Max (c1 ` S X) \<in> c1 ` S X"
    using finite_S assms(3) by (intro Max_in) auto
  then obtain z where z: "z \<in> S X" "c1 z = Max (c1 ` S X)" by auto
  have "c1 z \<le> c1 x"
    using assms(1,2) z(1) by (auto simp add: matroid1.local_opt_def S_def)
  thus ?thesis using z(2) by simp
qed

lemma Tmax_le:
  assumes "matroid2.local_opt c2 X" "x \<in> X" "y0 \<in> T X"
  shows "Max (c2 ` T X) \<le> c2 x"
proof -
  have "Max (c2 ` T X) \<in> c2 ` T X"
    using finite_T assms(3) by (intro Max_in) auto
  then obtain z where z: "z \<in> T X" "c2 z = Max (c2 ` T X)" by auto
  have "c2 z \<le> c2 x"
    using assms(1,2) z(1) by (auto simp add: matroid2.local_opt_def T_def)
  thus ?thesis using z(2) by simp
qed

text \<open>Without a tight augmenting path, every gap across the boundary of \<open>Rbar\<close> is positive: it is
  non-negative by local optimality, and a zero gap would be a tight arc leaving \<open>Rbar\<close>, a
  maximum-weight source outside \<open>Rbar\<close> or a maximum-weight target inside it.\<close>

lemma gaps_pos:
  assumes "matroid1.local_opt c1 X" "matroid2.local_opt c2 X"
    and nopath: "\<nexists> p u v. (vwalk_bet (Gbar X) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sbar X \<and> v \<in> Tbar X"
    and "g \<in> gaps X (Rbar X)"
  shows "0 < g"
proof-
  from assms(4) consider
      (A1) x y where "(x, y) \<in> A1 X" "x \<in> Rbar X" "y \<notin> Rbar X" "g = c1 x - c1 y"
    | (A2) x y where "(y, x) \<in> A2 X" "y \<in> Rbar X" "x \<notin> Rbar X" "g = c2 x - c2 y"
    | (S) y where "y \<in> S X" "y \<notin> Rbar X" "g = Max (c1 ` S X) - c1 y"
    | (T) y where "y \<in> T X" "y \<in> Rbar X" "g = Max (c2 ` T X) - c2 y"
    unfolding gaps_def by blast
  thus ?thesis
  proof cases
    case (A1 x y)
    have "c1 y \<le> c1 x"
      using A1(1) assms(1) by (auto simp add: A1_def matroid1.local_opt_def)
    moreover have "c1 x \<noteq> c1 y"
    proof
      assume "c1 x = c1 y"
      hence "(x, y) \<in> Gbar X" using A1(1) by (simp add: Gbar_def Abar1_def)
      thus False using Rbar_closed A1(2,3) by blast
    qed
    ultimately show ?thesis using A1(4) by (auto simp add: less_le)
  next
    case (A2 x y)
    have "c2 y \<le> c2 x"
      using A2(1) assms(2) by (auto simp add: A2_def matroid2.local_opt_def)
    moreover have "c2 x \<noteq> c2 y"
    proof
      assume "c2 x = c2 y"
      hence "(y, x) \<in> Gbar X" using A2(1) by (simp add: Gbar_def Abar2_def)
      thus False using Rbar_closed A2(2,3) by blast
    qed
    ultimately show ?thesis using A2(4) by (auto simp add: less_le)
  next
    case (S y)
    have "c1 y \<le> Max (c1 ` S X)" using finite_S S(1) by simp
    moreover have "c1 y \<noteq> Max (c1 ` S X)"
    proof
      assume "c1 y = Max (c1 ` S X)"
      hence "y \<in> Sbar X" using S(1) by (simp add: Sbar_def)
      thus False using Sbar_subset_Rbar S(2) by blast
    qed
    ultimately show ?thesis using S(3) by (auto simp add: less_le)
  next
    case (T y)
    have "c2 y \<le> Max (c2 ` T X)" using finite_T T(1) by simp
    moreover have "c2 y \<noteq> Max (c2 ` T X)"
    proof
      assume "c2 y = Max (c2 ` T X)"
      hence yT: "y \<in> Tbar X" using T(1) by (simp add: Tbar_def)
      obtain u where u: "u \<in> Sbar X" "u = y \<or> (\<exists>p. vwalk_bet (Gbar X) u p y)"
        using T(2) by (auto simp add: Rbar_def)
      thus False using nopath yT by blast
    qed
    ultimately show ?thesis using T(3) by (auto simp add: less_le)
  qed
qed

text \<open>Reweighting by at most the minimum gap preserves both local optima: \<open>c1\<close> decreases on \<open>R\<close>,
  and \<open>c2\<close> increases on \<open>R\<close>, which is a decrease on the complement followed by a global shift.\<close>

lemma gaps_reweight_local_opt:
  assumes "indep1 X" "indep2 X" "matroid1.local_opt c1 X" "matroid2.local_opt c2 X"
    "R \<subseteq> carrier" "0 < e" "\<And> g. g \<in> gaps X R \<Longrightarrow> e \<le> g"
  shows "matroid1.local_opt (\<lambda>z. if z \<in> R then c1 z - e else c1 z) X"
    and "matroid2.local_opt (\<lambda>z. if z \<in> R then c2 z + e else c2 z) X"
proof-
  show "matroid1.local_opt (\<lambda>z. if z \<in> R then c1 z - e else c1 z) X"
  proof (rule matroid1.reweight_preserves_local_opt[OF assms(1,3,5,6)])
    fix y x assume A: "y \<in> carrier - X" "x \<in> matroid1.the_circuit (insert y X) - {y}"
      "x \<in> R" "y \<notin> R"
    have "c1 x - c1 y \<in> gaps X R" using A unfolding gaps_def A1_def by blast
    thus "e \<le> c1 x - c1 y" by (rule assms(7))
  next
    fix x y assume B: "x \<in> X" "y \<in> carrier - X" "indep1 (insert y X)" "x \<in> R" "y \<notin> R"
    have yS: "y \<in> S X" using B(2,3) by (simp add: S_def)
    have "c1 y \<le> Max (c1 ` S X) - e" by (rule gaps_S_bound[OF assms(7) yS B(5)])
    moreover have "Max (c1 ` S X) \<le> c1 x" by (rule Smax_le[OF assms(3) B(1) yS])
    ultimately show "e \<le> c1 x - c1 y" by (simp add: le_diff_eq diff_le_eq add.commute)
  qed
  have lo_d: "matroid2.local_opt (\<lambda>z. if z \<in> carrier - R then c2 z - e else c2 z) X"
  proof (rule matroid2.reweight_preserves_local_opt[OF assms(2,4) Diff_subset assms(6)])
    fix y x assume A: "y \<in> carrier - X" "x \<in> matroid2.the_circuit (insert y X) - {y}"
      "x \<in> carrier - R" "y \<notin> carrier - R"
    have "c2 x - c2 y \<in> gaps X R" using A unfolding gaps_def A2_def by blast
    thus "e \<le> c2 x - c2 y" by (rule assms(7))
  next
    fix x y assume B: "x \<in> X" "y \<in> carrier - X" "indep2 (insert y X)" "x \<in> carrier - R"
      "y \<notin> carrier - R"
    have yT: "y \<in> T X" using B(2,3) by (simp add: T_def)
    have yR: "y \<in> R" using B(2,5) by simp
    have "c2 y \<le> Max (c2 ` T X) - e" by (rule gaps_T_bound[OF assms(7) yT yR])
    moreover have "Max (c2 ` T X) \<le> c2 x" by (rule Tmax_le[OF assms(4) B(1) yT])
    ultimately show "e \<le> c2 x - c2 y" by (simp add: le_diff_eq diff_le_eq add.commute)
  qed
  have agree: "\<forall>z\<in>carrier. (if z \<in> carrier - R then c2 z - e else c2 z) + e
                      = (if z \<in> R then c2 z + e else c2 z)"
    using assms(5) by auto
  show "matroid2.local_opt (\<lambda>z. if z \<in> R then c2 z + e else c2 z) X"
    using local_opt2_cong_imp[OF matroid2.indep_subset_carrier[OF assms(2)] agree
            local_opt2_add[OF lo_d, of e]] .
qed

text \<open>Without gaps, \<open>R\<close> contains \<open>S\<close>, avoids \<open>T\<close> and is closed under the auxiliary arcs, so there
  is no augmenting path at all.\<close>

lemma no_gaps_no_augpath:
  assumes "gaps X R = {}"
  shows "\<nexists> p x y. x \<in> S X \<and> y \<in> T X \<and> (vwalk_bet (A1 X \<union> A2 X) x p y \<or> x = y)"
proof-
  have SR: "y \<in> R" if y: "y \<in> S X" for y
  proof (rule ccontr)
    assume yR: "y \<notin> R"
    have "Max (c1 ` S X) - c1 y \<in> gaps X R"
      unfolding gaps_def by (rule UnI1, rule UnI2) (use y yR in blast)
    thus False using assms by simp
  qed
  have TR: "y \<notin> R" if y: "y \<in> T X" for y
  proof
    assume yR: "y \<in> R"
    have "Max (c2 ` T X) - c2 y \<in> gaps X R"
      unfolding gaps_def by (rule UnI2) (use y yR in blast)
    thus False using assms by simp
  qed
  have closed: "b \<in> R" if ab: "(a, b) \<in> A1 X \<union> A2 X" and aR: "a \<in> R" for a b
  proof (rule ccontr)
    assume bR: "b \<notin> R"
    from ab have "c1 a - c1 b \<in> gaps X R \<or> c2 b - c2 a \<in> gaps X R"
    proof
      assume ab1: "(a, b) \<in> A1 X"
      have "c1 a - c1 b \<in> gaps X R"
        unfolding gaps_def by (rule UnI1, rule UnI1, rule UnI1) (use ab1 aR bR in blast)
      thus ?thesis ..
    next
      assume ab2: "(a, b) \<in> A2 X"
      have "c2 b - c2 a \<in> gaps X R"
        unfolding gaps_def by (rule UnI1, rule UnI1, rule UnI2) (use ab2 aR bR in blast)
      thus ?thesis ..
    qed
    thus False using assms by simp
  qed
  show ?thesis
  proof (rule notI, elim exE conjE)
    fix p x y assume xy: "x \<in> S X" "y \<in> T X" "vwalk_bet (A1 X \<union> A2 X) x p y \<or> x = y"
    have "y \<in> R"
    proof (cases "x = y")
      case True thus ?thesis using SR[OF xy(1)] by simp
    next
      case False
      hence "vwalk_bet (A1 X \<union> A2 X) x p y" using xy(3) by simp
      thus ?thesis by (rule walk_stays_closed) (use SR[OF xy(1)] closed in auto)
    qed
    thus False using TR[OF xy(2)] by simp
  qed
qed

text \<open>Reweighting by a positive lower bound of the gaps keeps every vertex of \<open>Rbar\<close> reachable:
  the maximum-weight sources stay maximal, and the tight arcs inside \<open>Rbar\<close> stay tight.\<close>

lemma Rbar_reweight_mono:
  assumes "0 < e" "\<And> g. g \<in> gaps X (Rbar X) \<Longrightarrow> e \<le> g"
  shows "Rbar X \<subseteq> weighted_intersection_graph.Rbar carrier indep1 indep2
           (\<lambda>z. if z \<in> Rbar X then c1 z - e else c1 z) (\<lambda>z. if z \<in> Rbar X then c2 z + e else c2 z) X"
proof-
  interpret W': weighted_intersection_graph carrier indep1 indep2
    "\<lambda>z. if z \<in> Rbar X then c1 z - e else c1 z" "\<lambda>z. if z \<in> Rbar X then c2 z + e else c2 z"
    by unfold_locales
  have argR: "\<And>y. \<lbrakk>y \<in> S X; c1 y = Max (c1 ` S X)\<rbrakk> \<Longrightarrow> y \<in> Rbar X"
    using Sbar_subset_Rbar by (auto simp add: Sbar_def)
  have SbarSub: "Sbar X \<subseteq> W'.Sbar X"
    using argmax_reweight_mono[OF finite_S assms(1) gaps_S_bound[OF assms(2)] argR]
    by (simp add: Sbar_def W'.Sbar_def)
  have closed: "\<And>a b. \<lbrakk>(a, b) \<in> Gbar X; a \<in> Rbar X\<rbrakk> \<Longrightarrow> b \<in> Rbar X"
    using Rbar_closed by blast
  have pres: "\<And>a b. \<lbrakk>(a, b) \<in> Gbar X; a \<in> Rbar X\<rbrakk> \<Longrightarrow> (a, b) \<in> W'.Gbar X"
    using Gbar_reweight_tight closed by blast
  show ?thesis
  proof
    fix v assume "v \<in> Rbar X"
    then obtain u where u: "u \<in> Sbar X" "u = v \<or> (\<exists>p. vwalk_bet (Gbar X) u p v)"
      by (auto simp add: Rbar_def)
    have uR: "u \<in> Rbar X" using u(1) Sbar_subset_Rbar by auto
    have "u = v \<or> (\<exists>q. vwalk_bet (W'.Gbar X) u q v)"
    proof (cases "u = v")
      case False
      then obtain p where p: "vwalk_bet (Gbar X) u p v" using u(2) by blast
      have "vwalk_bet (W'.Gbar X) u p v \<or> (p = [u] \<and> u = v)"
        by (rule walk_transfer[OF p uR closed pres])
      thus ?thesis using False by auto
    qed simp
    thus "v \<in> W'.Rbar X" using SbarSub u(1) by (auto simp add: W'.Rbar_def)
  qed
qed

text \<open>Reweighting by the minimum gap makes progress: the gap attaining the minimum closes, so
  either \<open>Rbar\<close> grows strictly, or a tight augmenting path appears.\<close>

lemma Rbar_reweight_progress:
  assumes nopath: "\<nexists> p u v. (vwalk_bet (Gbar X) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sbar X \<and> v \<in> Tbar X"
    and "0 < e" "e \<in> gaps X (Rbar X)" "\<And> g. g \<in> gaps X (Rbar X) \<Longrightarrow> e \<le> g"
  defines "c1' \<equiv> \<lambda>z. if z \<in> Rbar X then c1 z - e else c1 z"
    and "c2' \<equiv> \<lambda>z. if z \<in> Rbar X then c2 z + e else c2 z"
  shows "Rbar X \<subset> weighted_intersection_graph.Rbar carrier indep1 indep2 c1' c2' X
         \<or> (\<exists> p u v. (vwalk_bet (weighted_intersection_graph.Gbar carrier indep1 indep2 c1' c2' X) u p v
                        \<or> (p = [u] \<and> u = v))
                \<and> u \<in> weighted_intersection_graph.Sbar carrier indep1 c1' X
                \<and> v \<in> weighted_intersection_graph.Tbar carrier indep2 c2' X)"
proof-
  interpret W': weighted_intersection_graph carrier indep1 indep2 c1' c2' by unfold_locales
  have mono: "Rbar X \<subseteq> W'.Rbar X"
    using Rbar_reweight_mono[OF assms(2,4)] by (simp add: c1'_def c2'_def)
  have strictI: "\<And>v. \<lbrakk>v \<in> W'.Rbar X; v \<notin> Rbar X\<rbrakk> \<Longrightarrow> Rbar X \<subset> W'.Rbar X"
    using mono by blast
  from assms(3) consider
      (A1) x y where "(x, y) \<in> A1 X" "x \<in> Rbar X" "y \<notin> Rbar X" "e = c1 x - c1 y"
    | (A2) x y where "(y, x) \<in> A2 X" "y \<in> Rbar X" "x \<notin> Rbar X" "e = c2 x - c2 y"
    | (S) y where "y \<in> S X" "y \<notin> Rbar X" "e = Max (c1 ` S X) - c1 y"
    | (T) y where "y \<in> T X" "y \<in> Rbar X" "e = Max (c2 ` T X) - c2 y"
    unfolding gaps_def by blast
  thus ?thesis
  proof cases
    case (A1 x y)
    have "c1' x = c1' y" using A1(2,3,4) by (simp add: c1'_def)
    hence "(x, y) \<in> W'.Gbar X" using A1(1) by (simp add: W'.Gbar_def W'.Abar1_def)
    hence "y \<in> W'.Rbar X" using W'.Rbar_closed mono A1(2) by blast
    thus ?thesis using strictI A1(3) by blast
  next
    case (A2 x y)
    have "c2' y = c2' x" using A2(2,3,4) by (simp add: c2'_def)
    hence "(y, x) \<in> W'.Gbar X" using A2(1) by (simp add: W'.Gbar_def W'.Abar2_def)
    hence "x \<in> W'.Rbar X" using W'.Rbar_closed mono A2(2) by blast
    thus ?thesis using strictI A2(3) by blast
  next
    case (S y)
    have argR: "\<And>y. \<lbrakk>y \<in> S X; c1 y = Max (c1 ` S X)\<rbrakk> \<Longrightarrow> y \<in> Rbar X"
      using Sbar_subset_Rbar by (auto simp add: Sbar_def)
    have "Max (c1' ` S X) = Max (c1 ` S X) - e"
      unfolding c1'_def
      by (rule argmax_reweight_newmax[OF finite_S _ assms(2)
            gaps_S_bound[where R = "Rbar X", OF assms(4)] argR])
        (use S(1) in auto)
    hence "c1' y = Max (c1' ` S X)" using S(2,3) by (simp add: c1'_def)
    hence "y \<in> W'.Rbar X" using S(1) W'.Sbar_subset_Rbar by (auto simp add: W'.Sbar_def)
    thus ?thesis using strictI S(2) by blast
  next
    case (T y)
    have argNR: "\<And>y. \<lbrakk>y \<in> T X; c2 y = Max (c2 ` T X)\<rbrakk> \<Longrightarrow> y \<notin> Rbar X"
    proof
      fix z assume z: "z \<in> T X" "c2 z = Max (c2 ` T X)" "z \<in> Rbar X"
      have zT: "z \<in> Tbar X" using z(1,2) by (simp add: Tbar_def)
      obtain u where "u \<in> Sbar X" "u = z \<or> (\<exists>p. vwalk_bet (Gbar X) u p z)"
        using z(3) by (auto simp add: Rbar_def)
      thus False using nopath zT by blast
    qed
    have "Max (c2' ` T X) = Max (c2 ` T X)"
      unfolding c2'_def
      by (rule argmax_reweight_keepmax[OF finite_T _ assms(2)
            gaps_T_bound[where R = "Rbar X", OF assms(4)] argNR])
        (use T(1) in auto)
    hence "c2' y = Max (c2' ` T X)" using T(2,3) by (simp add: c2'_def)
    hence yT': "y \<in> W'.Tbar X" using T(1) by (simp add: W'.Tbar_def)
    obtain u where "u \<in> W'.Sbar X" "u = y \<or> (\<exists>p. vwalk_bet (W'.Gbar X) u p y)"
      using T(2) mono by (auto simp add: W'.Rbar_def)
    thus ?thesis using yT' by blast
  qed
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

text \<open>A running minimum (\<^const>\<open>None\<close> = \<open>\<infinity>\<close>), used by the instances to compute \<open>eps\<close>.
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
proof (cases "A = {} \<or> B = {}")
  case True thus ?thesis by (auto simp add: Un_commute)
next
  case False
  hence "Min (A \<union> B) = min (Min A) (Min B)" using assms by (simp add: Min_Un)
  thus ?thesis using assms False
    by (auto simp add: eps_of_def min.assoc min.left_commute min.commute split: option.splits)
qed

lemma foldr_eps_of:
  fixes g :: "'a \<Rightarrow> 'b :: linorder"
  shows "foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) xs a
           = eps_of (g ` {x \<in> set xs. P x}) a"
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    have set_eq: "g ` {y \<in> set (x # xs). P y} = Set.insert (g x) (g ` {y \<in> set xs. P y})"
      using True by auto
    have "foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) (x # xs) a
            = eps_min (eps_of (g ` {y \<in> set xs. P y}) a) (g x)"
      using True Cons by simp
    also have "... = eps_of (Set.insert (g x) (g ` {y \<in> set xs. P y})) a"
      by (subst eps_of_single, subst eps_of_Un) auto
    finally show ?thesis by (simp add: set_eq[symmetric])
  next
    case False
    hence "g ` {y \<in> set (x # xs). P y} = g ` {y \<in> set xs. P y}" by auto
    thus ?thesis using False Cons by simp
  qed
qed simp

lemma foldr_eps_of_gen:
  fixes G :: "'a \<Rightarrow> 'b :: linorder set"
  assumes "\<And>y acc. body y acc = eps_of (G y) acc" "\<And>y. finite (G y)"
  shows "foldr body ys a = eps_of (\<Union>y \<in> set ys. G y) a"
proof (induction ys)
  case (Cons y ys)
  have "foldr body (y # ys) a = eps_of (G y) (foldr body ys a)"
    by (simp add: assms(1))
  also have "... = eps_of (G y) (eps_of (\<Union>z \<in> set ys. G z) a)"
    by (simp add: Cons)
  also have "... = eps_of (G y \<union> (\<Union>z \<in> set ys. G z)) a"
    using assms(2) by (subst eps_of_Un) auto
  finally show ?case by simp
qed simp

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

text \<open>Reweighting: \<open>c1\<close> decreases and \<open>c2\<close> increases by \<open>e\<close> on \<open>R\<close>.\<close>

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
  by (cases "tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st))";
      cases "eps (tight_ctx (wsol st) (wc1 st) (wc2 st))")
     (auto simp add: weighted_stop_cond_def weighted_augment_cond_def
        weighted_reweight_cond_def Let_def split: if_splits)

lemma weighted_matroid_intersection_simps:
  assumes "weighted_matroid_intersection_dom st"
  shows "weighted_stop_cond st \<Longrightarrow> weighted_matroid_intersection st = st"
    and "weighted_augment_cond st \<Longrightarrow>
           weighted_matroid_intersection st = weighted_matroid_intersection (weighted_augment_upd st)"
    and "weighted_reweight_cond st \<Longrightarrow>
           weighted_matroid_intersection st = weighted_matroid_intersection (weighted_reweight_upd st)"
  by (auto simp add: weighted_matroid_intersection.psimps[OF assms] weighted_stop_cond_def
        weighted_augment_cond_def weighted_reweight_cond_def weighted_augment_upd_def
        weighted_reweight_upd_def Let_def split: option.split)

lemma weighted_matroid_intersection_induct:
  assumes "weighted_matroid_intersection_dom st"
    "\<And> st. \<lbrakk>weighted_matroid_intersection_dom st;
             weighted_augment_cond st \<Longrightarrow> P (weighted_augment_upd st);
             weighted_reweight_cond st \<Longrightarrow> P (weighted_reweight_upd st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule weighted_matroid_intersection.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified weighted_augment_cond_def weighted_reweight_cond_def
        weighted_augment_upd_def weighted_reweight_upd_def Let_def])
  by (auto split: option.splits)

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
  apply(induction st rule: weighted_matroid_intersection.pinduct)
  apply(subst weighted_matroid_intersection_impl.simps)
  apply(subst weighted_matroid_intersection.psimps, simp)
  by (auto simp add: Let_def split: option.splits)

text \<open>Initial state: \<open>X = \<emptyset>\<close> and split \<open>c1 = c\<close>, \<open>c2 = 0\<close>.\<close>

definition "weighted_initial_state c =
  \<lparr> wsol = set_empty, wc1 = c, wc2 = c_zero, worig = c \<rparr>"

lemmas [code] = weighted_matroid_intersection_impl.simps reweight_def path_gain_def
  weighted_initial_state_def

end

subsection \<open>Correctness\<close>

text \<open>The specification of the weight maps and of the context. A context built for a locally
  optimal common independent set satisfies \<open>ctx_invar\<close>, and its abstraction is the tight graph
  \<open>Gbar\<close> with the endpoints \<open>Sbar\<close> and \<open>Tbar\<close>. The specification of \<open>tight_path\<close> is that of the
  unweighted @{term augmenting_path} for this graph; \<open>reach\<close> is the reachable set and \<open>eps\<close> the
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
       (\<nexists> p u v. (vwalk_bet (ctx_edges K) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> ctx_S K \<and> v \<in> ctx_T K)"
    "\<And> X c1 c2 K p. \<lbrakk>ctx_invar X c1 c2 K; tight_path K = Some p\<rbrakk> \<Longrightarrow>
       \<exists> u v. (vwalk_bet (ctx_edges K) u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> ctx_S K \<and> v \<in> ctx_T K \<and>
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
  have inv: "ctx_invar X c1 c2 K" unfolding K_def by (rule tight_ctx[OF assms(1-8)])
  note abs = ctx_abs[OF inv, folded Gb_def Sb_def Tb_def]
  show "tight_path K = None \<longleftrightarrow>
          (\<nexists> p u v. (vwalk_bet Gb u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sb \<and> v \<in> Tb)"
    using tight_path(1)[OF inv] unfolding abs .
  show "tight_path K = Some p \<Longrightarrow>
          \<exists> u v. (vwalk_bet Gb u p v \<or> (p = [u] \<and> u = v)) \<and> u \<in> Sb \<and> v \<in> Tb \<and>
            (\<nexists> p'. (vwalk_bet Gb u p' v \<or> (p' = [u] \<and> u = v)) \<and> length p' < length p)"
    using tight_path(2)[OF inv] unfolding abs .
  show "tight_path K = None \<Longrightarrow> r_invar (reach K) \<and> r_set (reach K) = Rb"
    using reach[OF inv] unfolding abs
    by (simp add: Rb_def Gb_def Sb_def W.Rbar_def)
  show "tight_path K = None \<Longrightarrow>
          eps K = eps_of (weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1)
                    (c_lookup c2) (to_set X) Rb) None"
    using eps[OF inv] by (simp add: Rb_def)
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
  assumes "c_invar c"
  shows "w_invar (weighted_initial_state c)"
proof-
  have e1: "indep1 {}" and e2: "indep2 {}"
    by (simp_all add: matroid1.indep_empty matroid2.indep_empty)
  have m1: "matroid1.max_weight_card (c_lookup c) {}"
    by (auto simp add: matroid1.max_weight_card_def matroid1.indep_finite card_0_eq)
  have m2: "matroid2.max_weight_card (c_lookup c_zero) {}"
    by (auto simp add: matroid2.max_weight_card_def matroid2.indep_finite card_0_eq)
  note lo1 = matroid1.greedy_optimality[OF e1, THEN iffD1, OF m1]
  note lo2 = matroid2.greedy_optimality[OF e2, THEN iffD1, OF m2]
  show ?thesis
    unfolding w_invar_def weighted_initial_state_def
    using assms e1 e2 lo1 lo2 set_empty c_zero matroid1.indep_finite
    by (auto simp add: c_zero(2) card_0_eq set_empty(2))
qed

text \<open>Augment branch: a shortest tight path (or a single tight vertex) keeps both matroids
  independent and locally optimal and adds one element. The original weight grows by the gain of
  the path, which is positive, so the new set is heavier than all smaller common independent
  sets.\<close>

lemma weighted_augment_props:
  assumes "w_invar st" "weighted_augment_cond st"
  shows "w_invar (weighted_augment_upd st) \<and>
         card (to_set (wsol (weighted_augment_upd st))) = card (to_set (wsol st)) + 1"
proof(rule P_of_weighted_augmentI[OF assms(2)])
  fix X K p
  assume df: "X = wsol st" "K = tight_ctx X (wc1 st) (wc2 st)" "tight_path K = Some p"
    and gain: "0 < path_gain st p"
  define c1 where "c1 = wc1 st"
  define c2 where "c2 = wc2 st"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have facts: "set_invar X" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "c_invar (worig st)"
    "\<forall>x\<in>carrier. c_lookup c1 x + c_lookup c2 x = c_lookup (worig st) x"
    "matroid1.local_opt (c_lookup c1) (to_set X)" "matroid2.local_opt (c_lookup c2) (to_set X)"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set X) \<longrightarrow>
       sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set X)"
    using assms(1) by (simp_all add: w_invar_def df(1) c1_def c2_def)
  have Xcarr: "to_set X \<subseteq> carrier" using matroid1.indep_subset_carrier[OF facts(2)] .
  obtain u v where p_prop:
    "vwalk_bet (W.Gbar (to_set X)) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> W.Sbar (to_set X)" "v \<in> W.Tbar (to_set X)"
    "\<nexists>q. (vwalk_bet (W.Gbar (to_set X)) u q v \<or> (q = [u] \<and> u = v)) \<and> length q < length p"
    using tight_ctx_props(2)[OF facts(1) Xcarr facts(2-5,8,9) df(3)[unfolded df(2), folded c1_def c2_def]]
    by blast
  define Xp where "Xp = (to_set X \<union> {p ! i | i. i < length p \<and> even i})
                          - {p ! i | i. i < length p \<and> odd i}"
  have sh_gbar: "\<nexists>q. vwalk_bet (W.Gbar (to_set X)) u q v \<and> length q < length p"
    using p_prop(4) by blast
  have big: "set p \<subseteq> carrier \<and> distinct p \<and> indep1 Xp \<and> indep2 Xp
           \<and> card Xp = card (to_set X) + 1
           \<and> matroid1.local_opt (c_lookup c1) Xp \<and> matroid2.local_opt (c_lookup c2) Xp
           \<and> sum (c_lookup c1) Xp = sum (c_lookup c1) (to_set X) + c_lookup c1 u
           \<and> sum (c_lookup c2) Xp = sum (c_lookup c2) (to_set X) + c_lookup c2 v
           \<and> hd p = u \<and> last p = v"
  proof(cases "vwalk_bet (W.Gbar (to_set X)) u p v")
    case True
    have "dVs (W.Gbar (to_set X)) \<subseteq> carrier"
      using dVs_subset[OF W.Gbar_subset] dVs_A1A2_carrier[OF facts(2,3)] by blast
    hence pc: "set p \<subseteq> carrier" using vwalk_bet_in_vertices[OF True] by auto
    have dp: "distinct p" using shortest_vwalk_bet_distinct[OF True sh_gbar] .
    note atp = W.augment_tight_path[OF facts(2,3,8,9) True p_prop(2,3) sh_gbar refl]
    show ?thesis using pc dp atp True by (auto simp add: Xp_def vwalk_bet_def)
  next
    case False
    hence su: "p = [u]" "u = v" using p_prop(1) by auto
    have uS: "u \<in> S (to_set X)" using p_prop(2) W.Sbar_subset by auto
    have uT: "u \<in> T (to_set X)" using p_prop(3) su(2) W.Tbar_subset by auto
    have unX: "u \<in> carrier - to_set X" using uS by (auto simp add: S_def)
    have i1u: "indep1 (Set.insert u (to_set X))" using uS by (auto simp add: S_def)
    have i2u: "indep2 (Set.insert u (to_set X))" using uT by (auto simp add: T_def)
    have Xp_is: "Xp = Set.insert u (to_set X)" using su by (auto simp add: Xp_def)
    have mx1: "c_lookup c1 u = Max (c_lookup c1 ` {y \<in> carrier - to_set X. indep1 (Set.insert y (to_set X))})"
      using p_prop(2) by (simp add: W.Sbar_def S_def)
    have mx2: "c_lookup c2 u = Max (c_lookup c2 ` {y \<in> carrier - to_set X. indep2 (Set.insert y (to_set X))})"
      using p_prop(3) su(2) by (simp add: W.Tbar_def T_def)
    have "matroid1.local_opt (c_lookup c1) (Set.insert u (to_set X))"
      using matroid1.greedy_extension[OF facts(2,8) unX i1u mx1] .
    moreover have "matroid2.local_opt (c_lookup c2) (Set.insert u (to_set X))"
      using matroid2.greedy_extension[OF facts(3,9) unX i2u mx2] .
    moreover have "card (Set.insert u (to_set X)) = card (to_set X) + 1"
      using unX matroid1.indep_finite[OF facts(2)] by simp
    moreover have "sum c (Set.insert u (to_set X)) = sum c (to_set X) + c u" for c :: "'a \<Rightarrow> real"
      using unX matroid1.indep_finite[OF facts(2)] by (simp add: add.commute)
    ultimately show ?thesis using i1u i2u Xp_is su unX by auto
  qed
  have pcarr: "set p \<subseteq> carrier" and distinctp: "distinct p"
    and cX1: "indep1 Xp" and cX2: "indep2 Xp" and cXcard: "card Xp = card (to_set X) + 1"
    and cXlo1: "matroid1.local_opt (c_lookup c1) Xp"
    and cXlo2: "matroid2.local_opt (c_lookup c2) Xp"
    and cXs1: "sum (c_lookup c1) Xp = sum (c_lookup c1) (to_set X) + c_lookup c1 u"
    and cXs2: "sum (c_lookup c2) Xp = sum (c_lookup c2) (to_set X) + c_lookup c2 v"
    and uv: "hd p = u" "last p = v"
    using big by auto
  have Xpeq: "to_set (augment X p) = Xp"
    using effect_of_augmentation(2)[OF facts(1) Xcarr pcarr distinctp refl] by (simp add: Xp_def)
  have setinvA: "set_invar (augment X p)"
    using effect_of_augmentation(1)[OF facts(1) Xcarr pcarr distinctp refl] .
  have t2: "to_set (augment X p) \<subseteq> carrier"
    using matroid1.indep_subset_carrier[OF cX1] Xpeq by simp
  have split: "sum (c_lookup (worig st)) Z = sum (c_lookup c1) Z + sum (c_lookup c2) Z"
    if "Z \<subseteq> carrier" for Z
  proof-
    have "sum (c_lookup (worig st)) Z = (\<Sum>x\<in>Z. c_lookup c1 x + c_lookup c2 x)"
      by (rule sum.cong[OF refl]) (use facts(7) that in auto)
    thus ?thesis by (simp add: sum.distrib)
  qed
  have heavier: "sum (c_lookup (worig st)) (to_set X) < sum (c_lookup (worig st)) Xp"
    using split[OF Xcarr] split[OF matroid1.indep_subset_carrier[OF cX1]] cXs1 cXs2 gain uv
    by (simp add: path_gain_def c1_def c2_def)
  have bound: "sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) Xp"
    if Yh: "indep1 Y" "indep2 Y" "card Y \<le> card Xp" for Y
  proof(cases "card Y \<le> card (to_set X)")
    case True
    thus ?thesis using facts(10) Yh(1,2) heavier by fastforce
  next
    case False
    have ceq: "card Y = card Xp" using Yh(3) False cXcard by simp
    show ?thesis
      using common_local_opt_max_worig[OF cX1 cX2 cXlo1 cXlo2 facts(7) Yh(1,2) ceq] .
  qed
  have "w_invar (st\<lparr>wsol := augment X p\<rparr>)"
    unfolding w_invar_def
    using setinvA t2 cX1 cX2 cXlo1 cXlo2 Xpeq facts(4-7) bound
    by (simp add: c1_def c2_def)
  moreover have "card (to_set (wsol (st\<lparr>wsol := augment X p\<rparr>))) = card (to_set (wsol st)) + 1"
    using cXcard Xpeq df(1) by simp
  ultimately show "w_invar (st\<lparr>wsol := augment X p\<rparr>) \<and>
         card (to_set (wsol (st\<lparr>wsol := augment X p\<rparr>))) = card (to_set (wsol st)) + 1" ..
qed

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
    "c_lookup (wc2 st)" by unfold_locales
  have facts: "set_invar (wsol st)" "to_set (wsol st) \<subseteq> carrier"
    "indep1 (to_set (wsol st))" "indep2 (to_set (wsol st))"
    "c_invar (wc1 st)" "c_invar (wc2 st)"
    "matroid1.local_opt (c_lookup (wc1 st)) (to_set (wsol st))"
    "matroid2.local_opt (c_lookup (wc2 st)) (to_set (wsol st))"
    using assms(1) by (simp_all add: w_invar_def)
  note props = tight_ctx_props[OF facts, folded assms(2)]
  show nopath: "\<nexists> p u v. (vwalk_bet (W.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> W.Sbar (to_set (wsol st)) \<and> v \<in> W.Tbar (to_set (wsol st))"
    using props(1) assms(3) by simp
  show "r_invar (reach K)" "r_set (reach K) = R"
    using props(3)[OF assms(3)] by (simp_all add: R_def)
  have eG: "eps_of G None = Some e" using props(4)[OF assms(3)] assms(4) by (simp add: G_def R_def)
  have fin: "finite G" unfolding G_def by (rule W.finite_gaps[OF facts(3,4)])
  have Gne: "G \<noteq> {}" and eMin: "e = Min G" using eG by (auto simp add: eps_of_None split: if_splits)
  show eG': "e \<in> G" using Min_in[OF fin Gne] eMin by simp
  show "\<And> g. g \<in> G \<Longrightarrow> e \<le> g" using Min_le[OF fin] eMin by simp
  show "0 < e"
    by (rule W.gaps_pos[OF facts(7,8) nopath eG'[unfolded G_def R_def]])
qed

text \<open>Reweight branch: the shift by the minimum gap keeps both local optima, and the split still
  sums to the original weight.\<close>

lemma w_invar_reweight:
  assumes "w_invar st" "weighted_reweight_cond st"
  shows "w_invar (weighted_reweight_upd st)"
proof (rule P_of_weighted_reweightI[OF assms(2)])
  fix X K e
  assume df: "X = wsol st" "K = tight_ctx X (wc1 st) (wc2 st)" "tight_path K = None"
    "eps K = Some e"
  define c1 where "c1 = wc1 st"
  define c2 where "c2 = wc2 st"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have facts: "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "c_invar (worig st)"
    "\<forall>z\<in>carrier. c_lookup c1 z + c_lookup c2 z = c_lookup (worig st) z"
    "matroid1.local_opt (c_lookup c1) (to_set X)" "matroid2.local_opt (c_lookup c2) (to_set X)"
    using assms(1) by (simp_all add: w_invar_def df(1) c1_def c2_def)
  note rf = reweight_facts[OF assms(1) df(2)[unfolded df(1)] df(3,4), folded df(1) c1_def c2_def]
  have RC: "W.Rbar (to_set X) \<subseteq> carrier" by (rule W.Rbar_subset_carrier[OF facts(3,4)])
  note lo' = W.gaps_reweight_local_opt[OF facts(3,4,9,10) RC rf(3,5)]
  have cs1: "c_lookup (c_shift (reach K) (- e) c1) =
               (\<lambda>z. if z \<in> W.Rbar (to_set X) then c_lookup c1 z - e else c_lookup c1 z)"
    using c_shift(2)[OF facts(5) rf(1), of "- e"] rf(2) by (simp add: fun_eq_iff)
  have cs2: "c_lookup (c_shift (reach K) e c2) =
               (\<lambda>z. if z \<in> W.Rbar (to_set X) then c_lookup c2 z + e else c_lookup c2 z)"
    using c_shift(2)[OF facts(6) rf(1)] rf(2) by simp
  have split: "\<forall>z\<in>carrier. c_lookup (c_shift (reach K) (- e) c1) z
                 + c_lookup (c_shift (reach K) e c2) z = c_lookup (worig st) z"
    using facts(8) by (simp add: cs1 cs2)
  show "w_invar (reweight (reach K) e st)"
    unfolding w_invar_def reweight_def
    using assms(1) c_shift(1)[OF facts(5) rf(1)] c_shift(1)[OF facts(6) rf(1)] split lo' cs1 cs2
    by (simp add: w_invar_def c1_def c2_def df(1))
qed

text \<open>Stop branch: \<open>wsol\<close> is optimal. Without a tight path and without gaps there is no
  augmenting path at all, so \<open>wsol\<close> has maximum cardinality. If a tight path does not increase
  the weight, then no element addable to \<open>wsol\<close> weighs more than its ends, so each element
  beyond \<open>card wsol\<close> adds at most the non-positive gain.\<close>

lemma w_invar_max_found:
  assumes "w_invar st" "weighted_stop_cond st"
  shows "\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
           sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set (wsol st))"
proof (rule weighted_stop_condE[OF assms(2)])
  fix X K
  assume df: "X = wsol st" "K = tight_ctx X (wc1 st) (wc2 st)" "tight_path K = None"
    "eps K = None"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st)"
    "c_lookup (wc2 st)" by unfold_locales
  have facts: "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar (wc1 st)" "c_invar (wc2 st)"
    "matroid1.local_opt (c_lookup (wc1 st)) (to_set X)"
    "matroid2.local_opt (c_lookup (wc2 st)) (to_set X)"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set X)
       \<longrightarrow> sum (c_lookup (worig st)) Y \<le> sum (c_lookup (worig st)) (to_set X)"
    using assms(1) by (simp_all add: w_invar_def df(1))
  have "eps_of (W.gaps (to_set X) (W.Rbar (to_set X))) None = None"
    using tight_ctx_props(4)[OF facts(1-8) df(3)[unfolded df(2)]] df(4)[unfolded df(2)] by simp
  hence "W.gaps (to_set X) (W.Rbar (to_set X)) = {}"
    by (simp add: eps_of_None split: if_splits)
  hence "\<nexists> Y. indep1 Y \<and> indep2 Y \<and> card (to_set X) < card Y"
    using if_no_augpath_then_maximum(1)[OF facts(3,4) W.no_gaps_no_augpath refl] by blast
  hence "\<And>Y. \<lbrakk>indep1 Y; indep2 Y\<rbrakk> \<Longrightarrow> card Y \<le> card (to_set X)"
    by (meson not_le)
  thus ?thesis using facts(9) df(1) by blast
next
  fix X K p
  assume df: "X = wsol st" "K = tight_ctx X (wc1 st) (wc2 st)" "tight_path K = Some p"
    and gain: "\<not> 0 < path_gain st p"
  define c1 where "c1 = c_lookup (wc1 st)"
  define c2 where "c2 = c_lookup (wc2 st)"
  define c where "c = c_lookup (worig st)"
  interpret W: weighted_intersection_graph carrier indep1 indep2 c1 c2
    by unfold_locales
  have facts: "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar (wc1 st)" "c_invar (wc2 st)"
    "matroid1.local_opt c1 (to_set X)" "matroid2.local_opt c2 (to_set X)"
    "\<forall>Y. indep1 Y \<and> indep2 Y \<and> card Y \<le> card (to_set X) \<longrightarrow> sum c Y \<le> sum c (to_set X)"
    "\<forall>x\<in>carrier. c1 x + c2 x = c x"
    using assms(1) by (simp_all add: w_invar_def df(1) c1_def c2_def c_def)
  obtain u v where p_prop: "vwalk_bet (W.Gbar (to_set X)) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> W.Sbar (to_set X)" "v \<in> W.Tbar (to_set X)"
    using tight_ctx_props(2)[OF facts(1-6) facts(7,8)[unfolded c1_def c2_def]
        df(3)[unfolded df(2)]]
    by (auto simp add: c1_def c2_def)
  have uv: "hd p = u" "last p = v"
    using p_prop(1) by (auto simp add: vwalk_bet_def)
  have nonpos: "c1 u + c2 v \<le> 0"
    using gain uv by (simp add: path_gain_def c1_def c2_def)
  have b1: "c1 y \<le> c1 u" if "y \<in> carrier - to_set X" "indep1 (insert y (to_set X))" for y
  proof-
    have "y \<in> S (to_set X)" using that by (simp add: S_def)
    hence "c1 y \<le> Max (c1 ` S (to_set X))" using W.finite_S by simp
    thus ?thesis using p_prop(2) by (simp add: W.Sbar_def)
  qed
  have b2: "c2 y \<le> c2 v" if "y \<in> carrier - to_set X" "indep2 (insert y (to_set X))" for y
  proof-
    have "y \<in> T (to_set X)" using that by (simp add: T_def)
    hence "c2 y \<le> Max (c2 ` T (to_set X))" using W.finite_T by simp
    thus ?thesis using p_prop(3) by (simp add: W.Tbar_def)
  qed
  have split: "sum c Z = sum c1 Z + sum c2 Z" if "Z \<subseteq> carrier" for Z
  proof-
    have "sum c Z = (\<Sum>x\<in>Z. c1 x + c2 x)"
      by (rule sum.cong[OF refl]) (use facts(10) that in auto)
    thus ?thesis by (simp add: sum.distrib)
  qed
  show ?thesis
    unfolding c_def[symmetric] df(1)[symmetric]
  proof(intro allI impI, elim conjE)
    fix Y assume Y: "indep1 Y" "indep2 Y"
    show "sum c Y \<le> sum c (to_set X)"
    proof(cases "card Y \<le> card (to_set X)")
      case True
      thus ?thesis using facts(9) Y by blast
    next
      case False
      then obtain k where k: "card Y = card (to_set X) + k"
        using le_Suc_ex[of "card (to_set X)" "card Y"] by auto
      have "sum c1 Y \<le> sum c1 (to_set X) + sum (\<lambda> _. c1 u) {..<k}"
        by (rule matroid1.local_opt_larger_bound[OF facts(3,7) Y(1) k b1])
      moreover have "sum c2 Y \<le> sum c2 (to_set X) + sum (\<lambda> _. c2 v) {..<k}"
        by (rule matroid2.local_opt_larger_bound[OF facts(4,8) Y(2) k b2])
      moreover have "real k * (c1 u + c2 v) \<le> 0"
        using nonpos by (simp add: mult_nonneg_nonpos)
      ultimately show ?thesis
        using split[OF matroid1.indep_subset_carrier[OF Y(1)]] split[OF facts(2)]
        by (simp add: distrib_left)
    qed
  qed
qed

text \<open>Termination: augmentation increases \<open>wsol\<close>, and between two augmentations reweighting
  increases \<open>Rbar\<close> or creates a tight path.\<close>

definition "wmeasure st =
  (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2)
  + 2 * (card carrier - card (weighted_intersection_graph.Rbar carrier indep1 indep2
                               (c_lookup (wc1 st)) (c_lookup (wc2 st)) (to_set (wsol st))))
  + (if tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st)) = None then 1 else 0)"

lemma measure_dec_helper:
  fixes N rR rR' :: nat and pn' :: bool
  assumes "rR \<le> rR'" "rR' \<le> N" and "rR < rR' \<or> \<not> pn'"
  shows "2 * (N - rR') + (if pn' then 1 else 0) < 2 * (N - rR) + 1"
  using assms by (cases pn') auto

lemma measure_aug_helper:
  fixes N c A Rp Rp' :: nat
  assumes "c + 1 \<le> N" "A = 2 * N + 2" "Rp' \<le> 2 * N + 1"
  shows "(N - (c + 1)) * A + Rp' < (N - c) * A + Rp"
proof -
  have "N - c = (N - (c + 1)) + 1" using assms(1) by simp
  hence "(N - c) * A = (N - (c + 1)) * A + A" by simp
  thus ?thesis using assms(2,3) by simp
qed

lemma wmeasure_reweight_dec:
  assumes "w_invar st" "weighted_reweight_cond st"
  shows "wmeasure (weighted_reweight_upd st) < wmeasure st"
proof (rule P_of_weighted_reweightI[OF assms(2)])
  fix X K e
  assume df: "X = wsol st" "K = tight_ctx X (wc1 st) (wc2 st)" "tight_path K = None"
    "eps K = Some e"
  define st' where "st' = reweight (reach K) e st"
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st)"
    "c_lookup (wc2 st)" by unfold_locales
  interpret W': weighted_intersection_graph carrier indep1 indep2 "c_lookup (wc1 st')"
    "c_lookup (wc2 st')" by unfold_locales
  note rf = reweight_facts[OF assms(1) df(2)[unfolded df(1)] df(3,4)]
  have upd: "weighted_reweight_upd st = st'"
    using df by (simp add: weighted_reweight_upd_def st'_def Let_def)
  have inv': "w_invar st'" using w_invar_reweight[OF assms] upd by simp
  have facts: "c_invar (wc1 st)" "c_invar (wc2 st)" "indep1 (to_set (wsol st))"
    "indep2 (to_set (wsol st))"
    using assms(1) by (simp_all add: w_invar_def)
  have facts': "set_invar (wsol st')" "to_set (wsol st') \<subseteq> carrier"
    "indep1 (to_set (wsol st'))" "indep2 (to_set (wsol st'))"
    "c_invar (wc1 st')" "c_invar (wc2 st')"
    "matroid1.local_opt (c_lookup (wc1 st')) (to_set (wsol st'))"
    "matroid2.local_opt (c_lookup (wc2 st')) (to_set (wsol st'))"
    using inv' by (simp_all add: w_invar_def)
  have wsol': "wsol st' = wsol st" by (simp add: st'_def reweight_def)
  have cs1: "c_lookup (wc1 st') = (\<lambda>z. if z \<in> W.Rbar (to_set (wsol st))
                                     then c_lookup (wc1 st) z - e else c_lookup (wc1 st) z)"
    using c_shift(2)[OF facts(1) rf(1), of "- e"] rf(2) by (simp add: st'_def reweight_def fun_eq_iff)
  have cs2: "c_lookup (wc2 st') = (\<lambda>z. if z \<in> W.Rbar (to_set (wsol st))
                                     then c_lookup (wc2 st) z + e else c_lookup (wc2 st) z)"
    using c_shift(2)[OF facts(2) rf(1), of e] rf(2) by (simp add: st'_def reweight_def)
  have mono: "W.Rbar (to_set (wsol st)) \<subseteq> W'.Rbar (to_set (wsol st))"
    using W.Rbar_reweight_mono[OF rf(3,5)] by (simp add: cs1 cs2)
  have prog: "W.Rbar (to_set (wsol st)) \<subset> W'.Rbar (to_set (wsol st))
     \<or> (\<exists> p u v. (vwalk_bet (W'.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
            \<and> u \<in> W'.Sbar (to_set (wsol st)) \<and> v \<in> W'.Tbar (to_set (wsol st)))"
    using W.Rbar_reweight_progress[OF rf(6,3,4,5)] by (simp add: cs1 cs2)
  have finC: "finite carrier" by (rule matroid1.carrier_finite)
  have R'C: "W'.Rbar (to_set (wsol st)) \<subseteq> carrier"
    using W'.Rbar_subset_carrier facts(3,4) by blast
  have cardRR': "card (W.Rbar (to_set (wsol st))) \<le> card (W'.Rbar (to_set (wsol st)))"
    using card_mono[OF finite_subset[OF R'C finC] mono] .
  have cardR'N: "card (W'.Rbar (to_set (wsol st))) \<le> card carrier"
    using card_mono[OF finC R'C] .
  have pnone: "tight_path (tight_ctx (wsol st) (wc1 st') (wc2 st')) = None \<longleftrightarrow>
     (\<nexists> p u v. (vwalk_bet (W'.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
            \<and> u \<in> W'.Sbar (to_set (wsol st)) \<and> v \<in> W'.Tbar (to_set (wsol st)))"
    using tight_ctx_props(1)[OF facts'] unfolding wsol' .
  have disj: "card (W.Rbar (to_set (wsol st))) < card (W'.Rbar (to_set (wsol st)))
              \<or> \<not> (tight_path (tight_ctx (wsol st) (wc1 st') (wc2 st')) = None)"
    using prog
  proof
    assume "W.Rbar (to_set (wsol st)) \<subset> W'.Rbar (to_set (wsol st))"
    thus ?thesis using psubset_card_mono[OF finite_subset[OF R'C finC]] by blast
  next
    assume "\<exists> p u v. (vwalk_bet (W'.Gbar (to_set (wsol st))) u p v \<or> (p = [u] \<and> u = v))
            \<and> u \<in> W'.Sbar (to_set (wsol st)) \<and> v \<in> W'.Tbar (to_set (wsol st))"
    thus ?thesis using pnone by blast
  qed
  have e1: "wmeasure st' = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2)
              + (2 * (card carrier - card (W'.Rbar (to_set (wsol st))))
              + (if tight_path (tight_ctx (wsol st) (wc1 st') (wc2 st')) = None then 1 else 0))"
    unfolding wmeasure_def wsol' by simp
  have e2: "wmeasure st = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2)
              + (2 * (card carrier - card (W.Rbar (to_set (wsol st)))) + 1)"
    using df by (simp add: wmeasure_def)
  show "wmeasure (reweight (reach K) e st) < wmeasure st"
    unfolding st'_def[symmetric]
    using measure_dec_helper[OF cardRR' cardR'N disj] e1 e2 by linarith
qed

lemma wmeasure_augment_dec:
  assumes "w_invar st" "weighted_augment_cond st"
  shows "wmeasure (weighted_augment_upd st) < wmeasure st"
proof -
  define st' where "st' = weighted_augment_upd st"
  define Rp' where "Rp' = 2 * (card carrier - card (weighted_intersection_graph.Rbar carrier
      indep1 indep2 (c_lookup (wc1 st')) (c_lookup (wc2 st')) (to_set (wsol st'))))
      + (if tight_path (tight_ctx (wsol st') (wc1 st') (wc2 st')) = None then 1 else 0)"
  have finC: "finite carrier" by (rule matroid1.carrier_finite)
  have card_aug: "card (to_set (wsol st')) = card (to_set (wsol st)) + 1"
    unfolding st'_def by (rule weighted_augment_card[OF assms])
  have "to_set (wsol st') \<subseteq> carrier"
    using w_invar_augment[OF assms] by (simp add: w_invar_def st'_def)
  hence cle: "card (to_set (wsol st)) + 1 \<le> card carrier"
    using card_mono[OF finC] card_aug by metis
  have bnd: "Rp' \<le> 2 * card carrier + 1" unfolding Rp'_def by (rule add_mono) simp_all
  define Rp where "Rp = 2 * (card carrier - card (weighted_intersection_graph.Rbar carrier
      indep1 indep2 (c_lookup (wc1 st)) (c_lookup (wc2 st)) (to_set (wsol st))))
      + (if tight_path (tight_ctx (wsol st) (wc1 st) (wc2 st)) = None then 1 else 0)"
  have "wmeasure st' = (card carrier - (card (to_set (wsol st)) + 1)) * (2 * card carrier + 2) + Rp'"
    unfolding wmeasure_def card_aug Rp'_def by simp
  moreover have "wmeasure st = (card carrier - card (to_set (wsol st))) * (2 * card carrier + 2) + Rp"
    unfolding wmeasure_def Rp_def by simp
  ultimately show ?thesis
    unfolding st'_def[symmetric] using measure_aug_helper[OF cle refl bnd, of Rp] by linarith
qed

lemma weighted_matroid_intersection_terminates:
  assumes "w_invar st" "m = wmeasure st"
  shows "weighted_matroid_intersection_dom st"
  using assms
proof (induction m arbitrary: st rule: less_induct)
  case (less m st)
  show ?case
  proof (rule weighted_matroid_intersection.domintros, goal_cases)
    case (1 e)
    hence cond: "weighted_reweight_cond st" by (simp add: weighted_reweight_cond_def Let_def)
    have upd: "reweight (reach (tight_ctx (wsol st) (wc1 st) (wc2 st))) e st = weighted_reweight_upd st"
      using 1 by (simp add: weighted_reweight_upd_def Let_def)
    show ?case
      unfolding upd
      by (rule less.IH[OF _ w_invar_reweight[OF less.prems(1) cond] refl])
         (use wmeasure_reweight_dec[OF less.prems(1) cond] less.prems(2) in simp)
  next
    case (2 p)
    hence cond: "weighted_augment_cond st" by (simp add: weighted_augment_cond_def Let_def)
    have upd: "st\<lparr>wsol := augment (wsol st) p\<rparr> = weighted_augment_upd st"
      using 2 by (simp add: weighted_augment_upd_def Let_def)
    show ?case
      unfolding upd
      by (rule less.IH[OF _ w_invar_augment[OF less.prems(1) cond] refl])
         (use wmeasure_augment_dec[OF less.prems(1) cond] less.prems(2) in simp)
  qed
qed

text \<open>Partial correctness: the original weight is never changed, and when the loop stops,
  \<open>wsol\<close> is optimal.\<close>

lemma weighted_worig_preserved:
  assumes "weighted_matroid_intersection_dom st"
  shows "worig (weighted_matroid_intersection st) = worig st"
proof (induction st rule: weighted_matroid_intersection_induct)
  case 1
  show ?case by (rule assms)
next
  case (2 st)
  show ?case
  proof (cases st rule: weighted_matroid_intersection_cases)
    case 1
    show ?thesis by (simp add: weighted_matroid_intersection_simps(1)[OF "2.hyps"(1) 1])
  next
    case 2
    have "worig (weighted_augment_upd st) = worig st"
      by (simp add: weighted_augment_upd_def Let_def)
    thus ?thesis
      using "2.IH"(1)[OF 2] by (simp add: weighted_matroid_intersection_simps(2)[OF "2.hyps"(1) 2])
  next
    case 3
    have "worig (weighted_reweight_upd st) = worig st"
      by (simp add: weighted_reweight_upd_def reweight_def Let_def)
    thus ?thesis
      using "2.IH"(2)[OF 3] by (simp add: weighted_matroid_intersection_simps(3)[OF "2.hyps"(1) 3])
  qed
qed

lemma weighted_correctness_general:
  assumes "weighted_matroid_intersection_dom st" "w_invar st"
  shows "indep1 (to_set (wsol (weighted_matroid_intersection st)))
       \<and> indep2 (to_set (wsol (weighted_matroid_intersection st)))
       \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow>
            sum (c_lookup (worig (weighted_matroid_intersection st))) Y
              \<le> sum (c_lookup (worig (weighted_matroid_intersection st)))
                     (to_set (wsol (weighted_matroid_intersection st))))"
  using assms(2)
proof (induction st rule: weighted_matroid_intersection_induct)
  case 1
  show ?case by (rule assms(1))
next
  case (2 st)
  show ?case
  proof (cases st rule: weighted_matroid_intersection_cases)
    case 1
    show ?thesis
      using w_invar_max_found[OF "2.prems" 1] weighted_matroid_intersection_simps(1)[OF "2.hyps"(1) 1]
        "2.prems" by (simp add: w_invar_def)
  next
    case 2
    show ?thesis
      unfolding weighted_matroid_intersection_simps(2)[OF "2.hyps"(1) 2]
      by (rule "2.IH"(1)[OF 2 w_invar_augment[OF "2.prems" 2]])
  next
    case 3
    show ?thesis
      unfolding weighted_matroid_intersection_simps(3)[OF "2.hyps"(1) 3]
      by (rule "2.IH"(2)[OF 3 w_invar_reweight[OF "2.prems" 3]])
  qed
qed

theorem weighted_matroid_intersection_partial_correct:
  assumes "c_invar c" "weighted_matroid_intersection_dom (weighted_initial_state c)"
  defines "s \<equiv> weighted_matroid_intersection (weighted_initial_state c)"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c) (to_set (wsol s))"
proof -
  interpret WDM: weighted_double_matroid carrier indep1 indep2 "c_lookup c" by unfold_locales
  have "worig s = c" using weighted_worig_preserved[OF assms(2)]
    by (simp add: s_def weighted_initial_state_def)
  hence "indep1 (to_set (wsol s)) \<and> indep2 (to_set (wsol s))
       \<and> (\<forall>Y. indep1 Y \<and> indep2 Y \<longrightarrow> sum (c_lookup c) Y \<le> sum (c_lookup c) (to_set (wsol s)))"
    using weighted_correctness_general[OF assms(2) w_invar_initial[OF assms(1)]] by (simp add: s_def)
  thus ?thesis unfolding WDM.is_opt_def by blast
qed

theorem weighted_matroid_intersection_correct:
  assumes "c_invar c"
  defines "s \<equiv> weighted_matroid_intersection (weighted_initial_state c)"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c) (to_set (wsol s))"
proof -
  have dom: "weighted_matroid_intersection_dom (weighted_initial_state c)"
    by (rule weighted_matroid_intersection_terminates[OF w_invar_initial[OF assms(1)] refl])
  show ?thesis unfolding s_def by (rule weighted_matroid_intersection_partial_correct[OF assms(1) dom])
qed

lemma same_result:
  "c_invar c \<Longrightarrow> weighted_matroid_intersection_impl (weighted_initial_state c)
                   = weighted_matroid_intersection (weighted_initial_state c)"
  by (simp add: weighted_implementation_is_same weighted_matroid_intersection_terminates
        w_invar_initial)

theorem impl_total_correctness:
  assumes "c_invar c"
  shows "weighted_double_matroid.is_opt indep1 indep2 (c_lookup c)
           (to_set (wsol (weighted_matroid_intersection_impl (weighted_initial_state c))))"
  using weighted_matroid_intersection_correct[OF assms] same_result[OF assms] by simp

end


end
