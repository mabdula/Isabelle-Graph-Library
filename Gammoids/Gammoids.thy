theory Gammoids
  imports
    Menger_Flows.Menger_Vertex
    Matroids_Greedy.Matroids_Theory
begin

section \<open>Separators and Boundaries\<close>

text \<open>The out-boundary of a vertex set \<open>A\<close> w.r.t.\ sources \<open>S\<close>: all vertices outside \<open>A\<close> that
are sources or out-neighbours of \<open>A\<close>.\<close>

definition out_boundary :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "out_boundary G S A = (S \<union> (\<Union>u \<in> A. neighbourhood G u)) - A"

lemma out_boundaryE[consumes 1, case_names source neighbour]:
  "v \<in> out_boundary G S A \<Longrightarrow>
    (\<lbrakk>v \<in> S; v \<notin> A\<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
    (\<And>u. \<lbrakk>u \<in> A; (u, v) \<in> G; v \<notin> A\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
and out_boundaryI1:
  "\<lbrakk>s \<in> S; s \<notin> A\<rbrakk> \<Longrightarrow> s \<in> out_boundary G S A"
and out_boundaryI2:
  "\<lbrakk>u \<in> A; (u, v) \<in> G; v \<notin> A\<rbrakk> \<Longrightarrow> v \<in> out_boundary G S A"
and out_boundaryD:
  "v \<in> out_boundary G S A \<Longrightarrow> v \<notin> A"
  by (auto simp: out_boundary_def neighbourhood_def)

lemma out_boundary_in_dVs: "S \<subseteq> dVs G \<Longrightarrow> out_boundary G S A \<subseteq> dVs G"
  by (auto elim!: out_boundaryE)

lemma out_boundary_submod:
  assumes "finite (out_boundary G S A)" "finite (out_boundary G S B)"
  shows "card (out_boundary G S (A \<union> B)) + card (out_boundary G S (A \<inter> B))
           \<le> card (out_boundary G S A) + card (out_boundary G S B)"
proof-
  let ?b = "out_boundary G S"
  have sub1: "?b (A \<union> B) \<union> ?b (A \<inter> B) \<subseteq> ?b A \<union> ?b B"
    by (auto simp: out_boundary_def neighbourhood_def)
  have sub2: "?b (A \<union> B) \<inter> ?b (A \<inter> B) \<subseteq> ?b A \<inter> ?b B"
    by (auto simp: out_boundary_def neighbourhood_def)
  have fin: "finite (?b (A \<union> B))" "finite (?b (A \<inter> B))"
    using finite_subset[OF sub1] assms by auto
  have "card (?b (A \<union> B)) + card (?b (A \<inter> B)) =
          card (?b (A \<union> B) \<union> ?b (A \<inter> B)) + card (?b (A \<union> B) \<inter> ?b (A \<inter> B))"
    using fin by (rule card_Un_Int)
  also have "\<dots> \<le> card (?b A \<union> ?b B) + card (?b A \<inter> ?b B)"
    using sub1 sub2 assms by (auto intro!: add_mono card_mono)
  also have "\<dots> = card (?b A) + card (?b B)"
    using assms by (rule card_Un_Int[symmetric])
  finally show ?thesis .
qed

lemma vwalk_bet_leaves_set:
  "\<lbrakk>vwalk_bet G u p v; u \<in> A; v \<notin> A\<rbrakk> \<Longrightarrow>
     \<exists>x y. (x, y) \<in> G \<and> x \<in> A \<and> y \<notin> A \<and> y \<in> set p"
proof(induction rule: induct_vwalk_bet)
  case (path1 v)
  then show ?case
    by simp
next
  case (path2 v v' vs b)
  then show ?case
    by (cases "v' \<in> A") auto
qed

lemma out_boundary_separator:
  assumes "A \<inter> U = {}"
  shows "separator G S U (out_boundary G S A)"
proof(rule separatorI)
  fix s p u
  assume asm: "s \<in> S" "u \<in> U" "vwalk_bet G s p u"
  then have "u \<notin> A"
    using assms by blast
  show "set p \<inter> out_boundary G S A \<noteq> {}"
  proof(cases "s \<in> A")
    case True
    then obtain x y where "(x, y) \<in> G" "x \<in> A" "y \<notin> A" "y \<in> set p"
      using vwalk_bet_leaves_set[OF asm(3) _ \<open>u \<notin> A\<close>] by blast
    then show ?thesis
      by (blast intro: out_boundaryI2)
  next
    case False
    moreover have "s \<in> set p"
      using asm(3) by (rule hd_of_vwalk_bet'')
    ultimately show ?thesis
      using asm(1) by (blast intro: out_boundaryI1)
  qed
qed

lemma separator_out_boundary:
  assumes "separator G S U X" "S \<subseteq> dVs G"
  obtains A where "A \<inter> U = {}" "out_boundary G S A \<subseteq> X"
proof-
  define A where "A = {v. \<exists>u p. u \<in> S \<and> vwalk_bet G u p v \<and> set p \<inter> X = {}}"
  have "A \<inter> U = {}"
    using assms(1) by (auto simp: A_def dest: separatorD)
  moreover have "out_boundary G S A \<subseteq> X"
  proof
    fix v
    assume "v \<in> out_boundary G S A"
    then show "v \<in> X"
    proof(cases rule: out_boundaryE)
      case source
      then have "vwalk_bet G v [v] v"
        using assms(2) by auto
      show ?thesis
      proof(rule ccontr)
        assume "v \<notin> X"
        then have "set [v] \<inter> X = {}"
          by simp
        then have "v \<in> A"
          using source(1) \<open>vwalk_bet G v [v] v\<close> unfolding A_def by blast
        then show False
          using source(2) by simp
      qed
    next
      case (neighbour u)
      from \<open>u \<in> A\<close> obtain s p where s_p: "s \<in> S" "vwalk_bet G s p u" "set p \<inter> X = {}"
        unfolding A_def by blast
      then have "vwalk_bet G s (p @ [v]) v"
        using vwalk_bet_transitive[OF _ edges_are_vwalk_bet[OF \<open>(u, v) \<in> G\<close>]] by simp
      show ?thesis
      proof(rule ccontr)
        assume "v \<notin> X"
        then have "set (p @ [v]) \<inter> X = {}"
          using s_p(3) by simp
        then have "v \<in> A"
          using s_p(1) \<open>vwalk_bet G s (p @ [v]) v\<close> unfolding A_def by blast
        then show False
          using neighbour(3) by simp
      qed
    qed
  qed
  ultimately show ?thesis
    by (rule that)
qed

section \<open>Gammoids\<close>

text \<open>A gammoid is given by a finite digraph \<open>G\<close> and a set of sources \<open>S\<close>. Its ground set are the
vertices \<open>dVs G\<close>, and a set of vertices is independent iff it is linked from \<open>S\<close>.\<close>

locale gammoid =
  fixes G :: "'a dgraph"
    and S :: "'a set"
  assumes G_finite: "finite G"
  assumes S_in_dVs: "S \<subseteq> dVs G"
begin

definition gammoid_indep :: "'a set \<Rightarrow> bool" where
  "gammoid_indep T = linked G S T"

lemma gammoid_indepE:
  "gammoid_indep T \<Longrightarrow> (linked G S T \<Longrightarrow> P) \<Longrightarrow> P"
and gammoid_indepI:
  "linked G S T \<Longrightarrow> gammoid_indep T"
and gammoid_indepD:
  "gammoid_indep T \<Longrightarrow> linked G S T"
  by (auto simp: gammoid_indep_def)

lemma gammoid_indep_system: "indep_system (dVs G) gammoid_indep"
proof(unfold_locales, goal_cases)
  case 1
  then show ?case
    using G_finite by (simp add: finite_vertices_iff)
next
  case (2 X)
  then show ?case
    by (auto dest: gammoid_indepD linked_in_dVs)
next
  case 3
  then show ?case
    using linked_empty by (blast intro: gammoid_indepI)
next
  case (4 X Y)
  then show ?case
    by (auto elim!: gammoid_indepE intro!: gammoid_indepI dest: linked_subset)
qed

lemma dVs_finite: "finite (dVs G)"
  using G_finite by (simp add: finite_vertices_iff)

lemma out_boundary_finite: "finite (out_boundary G S A)"
  using out_boundary_in_dVs[OF S_in_dVs] dVs_finite by (rule finite_subset)

subsection \<open>The Rank Function\<close>

definition gammoid_rank :: "'a set \<Rightarrow> nat" where
  "gammoid_rank U = Max {card T | T. T \<subseteq> U \<and> linked G S T}"

lemma gammoid_rank_set_finite: "finite {card T | T. T \<subseteq> U \<and> linked G S T}"
proof(rule finite_subset)
  show "{card T | T. T \<subseteq> U \<and> linked G S T} \<subseteq> {..card (dVs G)}"
    by (auto intro!: card_mono[OF dVs_finite] dest: linked_in_dVs)
qed simp

lemma gammoid_rank_set_nonempty: "{card T | T. T \<subseteq> U \<and> linked G S T} \<noteq> {}"
proof-
  have "card {} \<in> {card T | T. T \<subseteq> U \<and> linked G S T}"
    using linked_empty by (intro CollectI exI[of _ "{}"]) simp
  then show ?thesis
    by auto
qed

lemma gammoid_rankE:
  obtains T where "T \<subseteq> U" "linked G S T" "card T = gammoid_rank U"
proof-
  have "gammoid_rank U \<in> {card T | T. T \<subseteq> U \<and> linked G S T}"
    unfolding gammoid_rank_def by (rule Max_in[OF gammoid_rank_set_finite gammoid_rank_set_nonempty])
  then obtain T where T: "gammoid_rank U = card T" "T \<subseteq> U" "linked G S T"
    by auto
  show ?thesis
    by (rule that[OF T(2,3) T(1)[symmetric]])
qed

lemma gammoid_rank_maximal:
  assumes "T \<subseteq> U" "linked G S T"
  shows "card T \<le> gammoid_rank U"
proof-
  have "card T \<in> {card T | T. T \<subseteq> U \<and> linked G S T}"
    using assms by (intro CollectI exI[of _ T]) simp
  then show ?thesis
    unfolding gammoid_rank_def by (rule Max_ge[OF gammoid_rank_set_finite])
qed

lemma gammoid_rank_le_card:
  assumes "finite U"
  shows "gammoid_rank U \<le> card U"
proof-
  obtain T where "T \<subseteq> U" "linked G S T" "card T = gammoid_rank U"
    by (rule gammoid_rankE)
  moreover have "card T \<le> card U"
    using assms \<open>T \<subseteq> U\<close> by (rule card_mono)
  ultimately show ?thesis
    by simp
qed

lemma gammoid_rank_mono:
  assumes "U \<subseteq> W"
  shows "gammoid_rank U \<le> gammoid_rank W"
proof-
  obtain T where T: "T \<subseteq> U" "linked G S T" "card T = gammoid_rank U"
    by (rule gammoid_rankE)
  have "T \<subseteq> W"
    using T(1) assms by (rule subset_trans)
  then have "card T \<le> gammoid_rank W"
    using T(2) by (rule gammoid_rank_maximal)
  then show ?thesis
    using T(3) by simp
qed

text \<open>The rank is the minimal size of a boundary. This is the only place where Menger's Theorem
is used.\<close>

lemma gammoid_rank_le_boundary:
  assumes "A \<inter> U = {}"
  shows "gammoid_rank U \<le> card (out_boundary G S A)"
proof-
  obtain T where T: "T \<subseteq> U" "linked G S T" "card T = gammoid_rank U"
    by (rule gammoid_rankE)
  from T(2) obtain p where "linkage G S T p"
    by (rule linkedE)
  then have "card T \<le> card (out_boundary G S A)"
    using out_boundary_separator[OF assms] T(1) out_boundary_finite
    by (rule linkage_card_le_separator)
  then show ?thesis
    using T(3) by simp
qed

lemma gammoid_rank_boundary:
  obtains A where "A \<inter> U = {}" "card (out_boundary G S A) = gammoid_rank U"
proof-
  obtain T X where TX: "T \<subseteq> U" "linked G S T" "separator G S U X" "X \<subseteq> dVs G"
    "card X = card T"
    using menger[OF G_finite, where A = S and B = U] by blast
  obtain A where A: "A \<inter> U = {}" "out_boundary G S A \<subseteq> X"
    by (rule separator_out_boundary[OF TX(3) S_in_dVs])
  have "card (out_boundary G S A) \<le> card X"
    by (rule card_mono[OF finite_subset[OF TX(4) dVs_finite] A(2)])
  also have "\<dots> = card T"
    by (rule TX(5))
  also have "\<dots> \<le> gammoid_rank U"
    using TX(1,2) by (rule gammoid_rank_maximal)
  finally have "card (out_boundary G S A) \<le> gammoid_rank U" .
  moreover have "gammoid_rank U \<le> card (out_boundary G S A)"
    using A(1) by (rule gammoid_rank_le_boundary)
  ultimately have "card (out_boundary G S A) = gammoid_rank U"
    by simp
  with A(1) show ?thesis
    by (rule that)
qed

lemma gammoid_rank_submod:
  "gammoid_rank (U \<union> W) + gammoid_rank (U \<inter> W) \<le> gammoid_rank U + gammoid_rank W"
proof-
  obtain A where A: "A \<inter> U = {}" "card (out_boundary G S A) = gammoid_rank U"
    by (rule gammoid_rank_boundary)
  obtain B where B: "B \<inter> W = {}" "card (out_boundary G S B) = gammoid_rank W"
    by (rule gammoid_rank_boundary)
  have "(A \<inter> B) \<inter> (U \<union> W) = {}"
    using A(1) B(1) by auto
  then have 1: "gammoid_rank (U \<union> W) \<le> card (out_boundary G S (A \<inter> B))"
    by (rule gammoid_rank_le_boundary)
  have "(A \<union> B) \<inter> (U \<inter> W) = {}"
    using A(1) B(1) by auto
  then have 2: "gammoid_rank (U \<inter> W) \<le> card (out_boundary G S (A \<union> B))"
    by (rule gammoid_rank_le_boundary)
  have "card (out_boundary G S (A \<union> B)) + card (out_boundary G S (A \<inter> B))
          \<le> card (out_boundary G S A) + card (out_boundary G S B)"
    by (rule out_boundary_submod[OF out_boundary_finite out_boundary_finite])
  then show ?thesis
    using 1 2 A(2) B(2) by linarith
qed

subsection \<open>Gammoids are Matroids\<close>

lemma gammoid_indep_iff_rank:
  "gammoid_indep T \<longleftrightarrow> T \<subseteq> dVs G \<and> gammoid_rank T = card T"
proof
  assume "gammoid_indep T"
  then have T: "linked G S T"
    by (rule gammoid_indepD)
  then have "T \<subseteq> dVs G"
    by (rule linked_in_dVs)
  moreover have "card T \<le> gammoid_rank T"
    using subset_refl T by (rule gammoid_rank_maximal)
  moreover have "gammoid_rank T \<le> card T"
    using finite_subset[OF \<open>T \<subseteq> dVs G\<close> dVs_finite] by (rule gammoid_rank_le_card)
  ultimately show "T \<subseteq> dVs G \<and> gammoid_rank T = card T"
    by simp
next
  assume asm: "T \<subseteq> dVs G \<and> gammoid_rank T = card T"
  obtain T' where T': "T' \<subseteq> T" "linked G S T'" "card T' = gammoid_rank T"
    by (rule gammoid_rankE)
  have "T' = T"
    by (rule card_subset_eq[OF finite_subset[OF conjunct1[OF asm] dVs_finite] T'(1)])
       (simp add: T'(3) asm)
  then show "gammoid_indep T"
    using T'(2) by (simp add: gammoid_indepI)
qed

theorem gammoid_matroid: "matroid (dVs G) gammoid_indep"
proof-
  have "R1 (dVs G) gammoid_rank"
  proof(intro allI impI)
    fix X
    assume "X \<subseteq> dVs G"
    then show "gammoid_rank X \<le> card X"
      by (intro gammoid_rank_le_card finite_subset[OF _ dVs_finite])
  qed
  moreover have "R2 (dVs G) gammoid_rank"
    by (simp add: gammoid_rank_mono)
  moreover have "R3 (dVs G) gammoid_rank"
    by (simp add: gammoid_rank_submod)
  ultimately have "R1 (dVs G) gammoid_rank \<and> R2 (dVs G) gammoid_rank \<and> R3 (dVs G) gammoid_rank"
    by (intro conjI)
  then have "\<exists>indep. matroid (dVs G) indep \<and>
               (\<forall>X \<subseteq> dVs G. gammoid_rank X = matroid.rank_of indep X)"
    by (rule matroid_iff_rank_axioms1[OF dVs_finite, THEN iffD2])
  then obtain indep where indep: "matroid (dVs G) indep"
    "\<forall>X \<subseteq> dVs G. gammoid_rank X = matroid.rank_of indep X"
    by auto
  have "indep = gammoid_indep"
  proof(rule ext)
    fix X
    have "indep X = (X \<subseteq> dVs G \<and> matroid.rank_of indep X = card X)"
      using fun_cong[OF matroid_indep_expr_rank[OF indep(1)], of X] by simp
    also have "\<dots> = (X \<subseteq> dVs G \<and> gammoid_rank X = card X)"
      using indep(2) by auto
    also have "\<dots> = gammoid_indep X"
      by (rule gammoid_indep_iff_rank[symmetric])
    finally show "indep X = gammoid_indep X" .
  qed
  then show ?thesis
    using indep(1) by simp
qed
end

end
