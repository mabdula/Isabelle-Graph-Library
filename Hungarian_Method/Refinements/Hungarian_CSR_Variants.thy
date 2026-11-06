theory Hungarian_CSR_Variants
  imports
    Hungarian_Method_CSR_Instantiation
    Basic_Matching.Weighted_Matchings_Reductions
    Go.Go_Setup

begin

section \<open>Variants of Weighted Bipartite Matching on Arrays\<close>

text \<open>The variants of  \<open>WBP_Matching_Exec.thy\<close> on top of @{const hungarian_csr_run}: from
      the input arrays, new input arrays of the completed graph of
      @{theory Basic_Matching.Weighted_Matchings_Reductions} are built and passed to the Hungarian
      method, and the matching of the original graph is read off its result.\<close>

subsection \<open>The Completed Graph\<close>

text \<open>The completed graph: the smaller side is padded by new vertices @{term "n + i"}, and the
      left and the right vertices are connected by @{term "k * k"} edges in row-major order. The
      weight of an edge of the original graph is @{term "cf w"} for its original weight @{term w},
      the weight of every other edge is @{term dflt}.\<close>

locale hungarian_csr_completion = hungarian_csr_input h n fs ts ws ls rs
  for h :: "'n::{linordered_idom, heap} \<Rightarrow> real" and n fs ts ws ls rs +
  fixes dflt :: 'n and cf :: "'n \<Rightarrow> 'n"
begin

definition "k = max (length ls) (length rs)"
definition "ls' = ls @ [n..<n + (k - length ls)]"
definition "rs' = rs @ [n..<n + (k - length rs)]"
definition "n' = n + (k - length ls) + (k - length rs)"
definition "posl = foldl (\<lambda>P b. list_update P (rs' ! b) b)
                     (foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k]) [0..<k]"
definition "pos v = posl ! v"
definition "fs' = map (\<lambda>j. ls' ! (j div k)) [0..<k * k]"
definition "ts' = map (\<lambda>j. rs' ! (j mod k)) [0..<k * k]"
definition "eix i = pos (fs ! i) * k + pos (ts ! i)"
definition "ws' = foldl (\<lambda>W i. list_update W (eix i) (cf (ws ! i))) (replicate (k * k) dflt)
                   [0..<length fs]"

lemma length_ls': "length ls' = k" and length_rs': "length rs' = k"
  by (auto simp: ls'_def rs'_def k_def)

lemma one_side_padded: "k - length ls = 0 \<or> k - length rs = 0"
  by (auto simp: k_def)

lemma set_ls': "set ls' = L \<union> {n..<n + (k - length ls)}"
  and set_rs': "set rs' = R \<union> {n..<n + (k - length rs)}"
  by (auto simp: ls'_def rs'_def)

lemma distinct_ls': "distinct ls'" and distinct_rs': "distinct rs'"
  using ls_distinct rs_distinct L_less R_less
  by (fastforce simp: ls'_def rs'_def)+

lemma sides_disjoint': "set ls' \<inter> set rs' = {}"
  using sides_disjoint
  by (auto simp: set_ls' set_rs' k_def dest: L_less R_less)

lemma below_n': "set ls' \<union> set rs' \<subseteq> {..<n'}"
  by (auto simp: set_ls' set_rs' n'_def dest: L_less R_less)

lemma nth_ls'_less: "a < k \<Longrightarrow> ls' ! a < n'" and nth_rs'_less: "a < k \<Longrightarrow> rs' ! a < n'"
  using below_n' length_ls' length_rs' nth_mem[of a ls'] nth_mem[of a rs']
  by (auto simp del: nth_mem)

lemma pos_ls':
  assumes "a < k"
  shows "pos (ls' ! a) = a"
proof-
  have "ls' ! a \<notin> set rs'"
    using assms sides_disjoint' length_ls'
    by (auto simp: disjoint_iff)
  hence "ls' ! a \<notin> (!) rs' ` set [0..<k]"
    using length_rs'
    by (auto)
  moreover have "foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k] ! (ls' ! a) = a"
    by (rule foldl_upd_nth_hit[where f = id, simplified])
       (use assms distinct_ls' length_ls' nth_ls'_less in \<open>auto intro!: inj_on_nth\<close>)
  ultimately show ?thesis
    by (simp add: pos_def posl_def foldl_upd_nth_miss)
qed

lemma pos_rs': "b < k \<Longrightarrow> pos (rs' ! b) = b"
  unfolding pos_def posl_def
  by (rule foldl_upd_nth_hit[where f = id, simplified])
     (use distinct_rs' length_rs' nth_rs'_less in \<open>auto intro!: inj_on_nth\<close>)

lemma pos_less: "v \<in> set ls' \<union> set rs' \<Longrightarrow> pos v < k"
  using pos_ls' pos_rs' length_ls' length_rs'
  by (auto simp: in_set_conv_nth)

lemma ls'_nth_pos: "v \<in> set ls' \<Longrightarrow> ls' ! pos v = v"
  using pos_ls' length_ls'
  by (auto simp: in_set_conv_nth)

lemma rs'_nth_pos: "v \<in> set rs' \<Longrightarrow> rs' ! pos v = v"
  using pos_rs' length_rs'
  by (auto simp: in_set_conv_nth)

lemma pos_eq_ls': "\<lbrakk>pos u = pos v; u \<in> set ls'; v \<in> set ls'\<rbrakk> \<Longrightarrow> u = v"
  using ls'_nth_pos
  by (rule inj_onD[OF inj_on_inverseI])

lemma pos_eq_rs': "\<lbrakk>pos u = pos v; u \<in> set rs'; v \<in> set rs'\<rbrakk> \<Longrightarrow> u = v"
  using rs'_nth_pos
  by (rule inj_onD[OF inj_on_inverseI])

lemma length_fs' [simp]: "length fs' = k * k" and length_ts' [simp]: "length ts' = k * k"
  and length_ws' [simp]: "length ws' = k * k"
  by (simp_all add: fs'_def ts'_def ws'_def)

lemma fs'_nth: "j < k * k \<Longrightarrow> fs' ! j = ls' ! (j div k)"
  and ts'_nth: "j < k * k \<Longrightarrow> ts' ! j = rs' ! (j mod k)"
  by (simp_all add: fs'_def ts'_def)

lemma fs_in_ls': "i < length fs \<Longrightarrow> fs ! i \<in> set ls'"
  and ts_in_rs': "i < length fs \<Longrightarrow> ts ! i \<in> set rs'"
  using fs_L ts_R
  by (simp_all add: set_ls' set_rs')

lemma grid_index:
  assumes "u \<in> set ls'" "v \<in> set rs'"
  shows "pos u * k + pos v < k * k" "fs' ! (pos u * k + pos v) = u" "ts' ! (pos u * k + pos v) = v"
  using assms pos_less[of u] pos_less[of v] mult_add_less[of "pos u" k "pos v"]
  by (simp_all add: fs'_nth ts'_nth ls'_nth_pos rs'_nth_pos)

lemma eix_less: "i < length fs \<Longrightarrow> eix i < k * k"
  by (simp add: eix_def grid_index fs_in_ls' ts_in_rs')

lemma eix_eq_iff:
  assumes "i < length fs" "u \<in> set ls'" "v \<in> set rs'"
  shows "pos u * k + pos v = eix i \<longleftrightarrow> fs ! i = u \<and> ts ! i = v"
  using assms fs_in_ls' ts_in_rs'
  by (auto simp: eix_def mult_add_eq_iff pos_less intro: pos_eq_ls' pos_eq_rs')

lemma eix_inj: "inj_on eix {..<length fs}"
  using eix_eq_iff[of _ "fs ! _" "ts ! _"] fs_in_ls' ts_in_rs' edge_unique
  by (auto simp: inj_on_def eix_def)

lemma ws'_edge: "i < length fs \<Longrightarrow> ws' ! eix i = cf (ws ! i)"
  unfolding ws'_def
  by (rule foldl_upd_nth_hit) (use eix_inj eix_less in \<open>auto simp: atLeast0LessThan\<close>)

lemma ws'_other: "\<lbrakk>j \<notin> eix ` {..<length fs}; j < k * k\<rbrakk> \<Longrightarrow> ws' ! j = dflt"
  unfolding ws'_def
  by (subst foldl_upd_nth_miss) (auto simp: atLeast0LessThan)

lemma set_fs': "set fs' = set ls'"
proof
  show "set fs' \<subseteq> set ls'"
    using length_ls'
    by (auto simp: fs'_def less_mult_imp_div_less)
  show "set ls' \<subseteq> set fs'"
  proof
    fix v
    assume "v \<in> set ls'"
    then obtain a where "a < k" "v = ls' ! a"
      using length_ls'
      by (auto simp: in_set_conv_nth)
    thus "v \<in> set fs'"
      using mult_add_less[of a k 0]
      by (auto simp: fs'_def intro!: image_eqI[where x = "a * k"])
  qed
qed

lemma set_ts': "set ts' = set rs'"
proof
  show "set ts' \<subseteq> set rs'"
    using length_rs'
    by (auto simp: ts'_def div_mod_less_square)
  show "set rs' \<subseteq> set ts'"
  proof
    fix v
    assume "v \<in> set rs'"
    then obtain b where "b < k" "v = rs' ! b"
      using length_rs'
      by (auto simp: in_set_conv_nth)
    thus "v \<in> set ts'"
      using mult_add_less[of 0 k b]
      by (auto simp: ts'_def intro!: image_eqI[where x = b])
  qed
qed

lemma no_parallel': "distinct (zip fs' ts')"
proof(rule distinct_conv_nth[THEN iffD2], intro allI impI)
  fix i j
  assume "i < length (zip fs' ts')" "j < length (zip fs' ts')" "i \<noteq> j"
  thus "zip fs' ts' ! i \<noteq> zip fs' ts' ! j"
    using distinct_ls' distinct_rs' length_ls' length_rs' div_mult_mod_eq[of i k] div_mult_mod_eq[of j k]
    by (auto simp: fs'_nth ts'_nth nth_eq_iff_index_eq div_mod_less_square)
qed

sublocale cp: hungarian_csr_input h n' fs' ts' ws' ls' rs'
  by (intro hungarian_csr_input.intro real_embedding_axioms hungarian_csr_input_axioms.intro)
     (simp_all add: distinct_ls' distinct_rs' set_fs' set_ts' sides_disjoint' no_parallel'
                    below_n'[unfolded Un_subset_iff])

end

subsection \<open>Renaming the Completed Graph of the Reduction\<close>

text \<open>The completed graph @{const bp_perfected_G} of
      @{theory Basic_Matching.Weighted_Matchings_Reductions} is the graph of the instance
      \<open>cp\<close>, up to the renaming of each new vertex @{term "new_vertex i"} to @{term "n + i"}.\<close>

lemma new_vertex_set: "{new_vertex i | i. i < m} = new_vertex ` {..<m}"
  by auto

context hungarian_csr_completion
begin

definition "ren x = (case x of old_vertex v \<Rightarrow> v | new_vertex i \<Rightarrow> n + i)"

lemma ren_simps [simp]: "ren (old_vertex v) = v" "ren (new_vertex i) = n + i"
  by (simp_all add: ren_def)

lemma pad_L: "card R - card L = k - length ls" and pad_R: "card L - card R = k - length rs"
  using ls_distinct rs_distinct
  by (simp_all add: distinct_card k_def max_def)

lemma ren_L': "ren ` bp_perfected_L L R = set ls'"
  by (simp add: bp_perfected_L_def new_vertex_set image_Un image_image image_plus_lessThan
                set_ls' pad_L)

lemma ren_R': "ren ` bp_perfected_R L R = set rs'"
  by (simp add: bp_perfected_R_def new_vertex_set image_Un image_image image_plus_lessThan
                set_rs' pad_R)

lemma grid_edge: "\<lbrakk>u \<in> set ls'; v \<in> set rs'\<rbrakk> \<Longrightarrow> {u, v} \<in> cp.G"
  using cp.G_edge[of "pos u * k + pos v"] grid_index[of u v]
  by simp

lemma cp_G: "cp.G = {{u, v} | u v. u \<in> set ls' \<and> v \<in> set rs'}"
proof
  show "cp.G \<subseteq> {{u, v} | u v. u \<in> set ls' \<and> v \<in> set rs'}"
    by (fastforce simp: cp.G_def set_fs'[symmetric] set_ts'[symmetric])
  show "{{u, v} | u v. u \<in> set ls' \<and> v \<in> set rs'} \<subseteq> cp.G"
    using grid_edge
    by blast
qed

lemma ren_G': "(`) ren ` bp_perfected_G L R = cp.G"
proof
  show "(`) ren ` bp_perfected_G L R \<subseteq> cp.G"
    using ren_L'[symmetric] ren_R'[symmetric]
    by (fastforce simp: bp_perfected_G_def' intro!: grid_edge)
  show "cp.G \<subseteq> (`) ren ` bp_perfected_G L R"
  proof
    fix e
    assume "e \<in> cp.G"
    then obtain x y where "x \<in> bp_perfected_L L R" "y \<in> bp_perfected_R L R" "e = ren ` {x, y}"
      unfolding cp_G ren_L'[symmetric] ren_R'[symmetric]
      by (auto)
    hence "{x, y} \<in> bp_perfected_G L R" "e = ren ` {x, y}"
      by (auto simp: bp_perfected_G_def')
    thus "e \<in> (`) ren ` bp_perfected_G L R"
      by blast
  qed
qed

lemma ren_edge: "e \<in> bp_perfected_G L R \<Longrightarrow> ren ` e \<in> cp.G"
  using ren_G'
  by blast

lemma ren_inj: "inj_on ren (Vs (bp_perfected_G L R))"
  using bp_perfected_Vs_subs[of L R] L_less R_less
  by (auto simp: inj_on_def ren_def bp_perfected_L_def bp_perfected_R_def
                    split: bp_vertex_wrapper.splits)

lemma G_below: "\<lbrakk>e \<in> G; x \<in> e\<rbrakk> \<Longrightarrow> x < n"
  using Vs_G L_less R_less
  by (auto simp: Vs_def)

lemma old_ren: "\<nexists>i. new_vertex i \<in> e \<Longrightarrow> bp_vertex_wrapper.the_vertex ` e = ren ` e"
  by (intro image_cong) (auto simp: ren_def split: bp_vertex_wrapper.splits)

lemma new_ren: "new_vertex i \<in> e \<Longrightarrow> ren ` e \<notin> G"
  using G_below[of "ren ` e" "n + i"]
  by force

lemma perfect_sub: "perfect_matching cp.G Mc \<Longrightarrow> Mc \<subseteq> cp.G"
  by (simp add: perfect_matching_def)

lemma project_preimage:
  assumes "min_weight_perfect_matching cp.G w Mc"
  shows "project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> X \<inter> G = Mc \<inter> G \<inter> X"
proof
  show "project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> X \<inter> G \<subseteq> Mc \<inter> G \<inter> X"
    using old_ren
    by (auto simp: project_to_old_def)
  show "Mc \<inter> G \<inter> X \<subseteq> project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> X \<inter> G"
  proof
    fix ec
    assume "ec \<in> Mc \<inter> G \<inter> X"
    moreover hence "ec \<in> (`) ren ` bp_perfected_G L R"
      using perfect_sub[OF min_weight_perfect_matchingD(1)[OF assms]]
      by (auto simp: ren_G')
    moreover then obtain e where "ec = ren ` e" "e \<in> bp_perfected_G L R"
      by (rule imageE)
    ultimately show "ec \<in> project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> X \<inter> G"
      using new_ren[of _ e] old_ren[of e]
      by (auto simp: project_to_old_def intro!: exI[where x = e])
  qed
qed

lemma G_iff_edge:
  assumes "u \<in> set ls'" "v \<in> set rs'"
  shows "{u, v} \<in> G \<longleftrightarrow> (\<exists>i<length fs. fs ! i = u \<and> ts ! i = v)"
  using assms sides_disjoint' fs_in_ls' ts_in_rs'
  by (auto simp: G_def doubleton_eq_iff)

lemma ws'_at: "\<lbrakk>u \<in> set ls'; v \<in> set rs'\<rbrakk> \<Longrightarrow> h (ws' ! (pos u * k + pos v)) = cp.ecost u v"
  using grid_index cp.ecost_edge[of "pos u * k + pos v"]
  by simp

lemma cp_ecost:
  assumes "u \<in> set ls'" "v \<in> set rs'"
  shows "cp.ecost u v = (if {u, v} \<in> G then h (cf (ws ! eidx u v)) else h dflt)"
proof(cases "{u, v} \<in> G")
  case True
  then obtain i where "i < length fs" "fs ! i = u" "ts ! i = v"
    using assms G_iff_edge
    by blast
  thus ?thesis
    using True assms ws'_at[symmetric, of u v] ws'_edge[of i] eidx_eq[of i] eix_eq_iff[of i u v]
    by simp
next
  case False
  moreover hence "pos u * k + pos v \<notin> eix ` {..<length fs}"
    using assms eix_eq_iff G_iff_edge
    by (auto)
  ultimately show ?thesis
    using assms ws'_at[symmetric, of u v] ws'_other[of "pos u * k + pos v"] grid_index
    by simp
qed

lemma wfun_orig: "\<lbrakk>{u, v} \<in> G; u \<in> L\<rbrakk> \<Longrightarrow> wfun {u, v} = h (ws ! eidx u v)"
  using wfun_eq
  by (simp add: ecost_def)

text \<open>The weights of the completed graph, for a function @{term g} on the reals that @{term cf}
      represents.\<close>

lemma cp_wfun:
  assumes "\<And>a. h (cf a) = g (h a)" "e \<in> cp.G"
  shows "cp.wfun e = (if e \<in> G then g (wfun e) else h dflt)"
proof-
  obtain u v where "u \<in> set ls'" "v \<in> set rs'" "e = {u, v}"
    using assms(2)
    unfolding cp_G
    by blast
  thus ?thesis
    using assms cp_ecost[of u v] cp.wfun_eq[of u v] wfun_orig[of u v] G_below[of e u]
    by (auto simp: set_ls')
qed

text \<open>A minimum weight perfect matching of the completed graph is one of the renamed graph
      @{const bp_perfected_G}.\<close>

lemma completion_transfer:
  assumes "min_weight_perfect_matching cp.G cp.wfun Mc"
  shows "min_weight_perfect_matching (bp_perfected_G L R) (\<lambda>e. cp.wfun (ren ` e))
           {e \<in> bp_perfected_G L R. ren ` e \<in> Mc}"
  using assms ren_inj min_weight_perfect_matching_preimage[of ren "bp_perfected_G L R" cp.wfun Mc]
  by (simp add: ren_G')

lemma wfun_ren:
  assumes "\<And>a. h (cf a) = g (h a)" "e \<in> bp_perfected_G L R"
  shows "cp.wfun (ren ` e) =
           (if (\<exists>i. new_vertex i \<in> e) \<or> bp_vertex_wrapper.the_vertex ` e \<notin> G then h dflt
            else g (wfun (bp_vertex_wrapper.the_vertex ` e)))"
proof(cases "\<exists>i. new_vertex i \<in> e")
  case True
  thus ?thesis
    using assms cp_wfun[of g "ren ` e"] ren_edge new_ren
    by (auto)
next
  case False
  thus ?thesis
    using assms cp_wfun[of g "ren ` e"] ren_edge old_ren[of e]
    by (simp)
qed

text \<open>The weights @{term wred} of a reduction of
      @{theory Basic_Matching.Weighted_Matchings_Reductions} that agree with the weights of the
      completed graph: a minimum weight perfect matching of the completed graph gives one of
      @{const bp_perfected_G} for @{term wred}.\<close>

lemma completion_result:
  assumes "\<And>a. h (cf a) = g (h a)" "min_weight_perfect_matching cp.G cp.wfun Mc"
    and "\<And>e. e \<in> bp_perfected_G L R \<Longrightarrow> wred e =
           (if (\<exists>i. new_vertex i \<in> e) \<or> bp_vertex_wrapper.the_vertex ` e \<notin> G then h dflt
            else g (wfun (bp_vertex_wrapper.the_vertex ` e)))"
  shows "min_weight_perfect_matching (bp_perfected_G L R) wred {e \<in> bp_perfected_G L R. ren ` e \<in> Mc}"
  by (rule min_weight_perfect_matching_cong[where w = "\<lambda>e. cp.wfun (ren ` e)"])
     (use assms completion_transfer wfun_ren in \<open>simp_all\<close>)

lemma G_image: "G = (\<lambda>i. {fs ! i, ts ! i}) ` {..<length fs}"
  by (auto simp: G_def)

lemma finite_G: "finite G"
  by (simp add: G_image)

text \<open>The completed graph has a perfect matching, so the Hungarian method succeeds on it.\<close>

lemma cp_perfect_exists: "\<exists>M. perfect_matching cp.G M"
proof-
  have "finite (bp_perfected_G L R)"
    by (rule finite_G_finite_completion[OF finite_G]) simp_all
  then obtain M where "perfect_matching (bp_perfected_G L R) M"
    using bipartite_G balanced_complete_bipartite_perfected(1)[of G L R]
          perfect_matching_in_balanced_complete_bipartite finite_set[of ls] finite_set[of rs]
    by (blast)
  thus ?thesis
    using perfect_matching_image[of "bp_perfected_G L R" M ren] ren_inj
    by (auto simp: ren_G')
qed

end

subsection \<open>Minimum and Maximum Weight Matchings\<close>

text \<open>The weights are negated for the maximisation.\<close>

definition "sgn_w b w = (if b then - w else w)"

lemma sgn_w_simps [simp]: "sgn_w False w = w" "sgn_w True w = - w"
  by (simp_all add: sgn_w_def)

lemma (in hungarian_csr_completion) h_sgn: "h (sgn_w b a) = sgn_w b (h a)"
  by (cases b) simp_all

text \<open>The weight of an edge of the original graph is @{term "min 0 w"} for its (possibly negated)
      weight @{term w}, the weight of every other edge is @{term 0}.\<close>

locale hungarian_csr_mw =
  hungarian_csr_completion \<theta> cap h n fs ts ws ls rs 0 "\<lambda>w. min 0 (sgn_w neg w)"
  for h :: "'n::{linordered_idom, heap} \<Rightarrow> real" and n fs ts ws ls rs and neg :: bool
  and \<theta> cap :: nat
begin

lemma mw_correct:
  assumes "min_weight_perfect_matching cp.G cp.wfun Mc"
  shows "min_weight_matching G (\<lambda>e. sgn_w neg (wfun e)) (Mc \<inter> G \<inter> {e. sgn_w neg (wfun e) < 0})"
proof-
  have "min_weight_perfect_matching (bp_perfected_G L R)
          (bp_min_costs_to_min_perfect_costs G (\<lambda>e. sgn_w neg (wfun e)))
          {e \<in> bp_perfected_G L R. ren ` e \<in> Mc}"
    by (rule completion_result[where g = "\<lambda>x. min 0 (sgn_w neg x)", OF _ assms])
       (cases neg; simp add: bp_min_costs_to_min_perfect_costs_def)+
  hence "min_weight_matching G (\<lambda>e. sgn_w neg (wfun e))
           (project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter>
            {e |e. sgn_w neg (wfun e) < 0} \<inter> G)"
    by (rule min_weight_perfect_implies_min_weight[OF bipartite_G finite_set finite_set])
  thus ?thesis
    using project_preimage[OF assms]
    by simp
qed

end

subsection \<open>Minimum and Maximum Weight Maximum Cardinality Matchings\<close>

definition "max_abs_weight ws = fold max (map abs ws) (0::'n::linordered_idom)"

text \<open>The weight of an edge of the original graph is its (possibly negated) weight, the weight of
      every other edge is twice the penalty of
      @{theory Basic_Matching.Weighted_Matchings_Reductions}.\<close>

locale hungarian_csr_mwmc = hungarian_csr_completion \<theta> cap h n fs ts ws ls rs
    "2 + of_nat (length ls + length rs) * max_abs_weight ws" "sgn_w neg"
    for h :: "'n::{linordered_idom, heap} \<Rightarrow> real" and n fs ts ws ls rs and neg :: bool
    and \<theta> cap :: nat
begin

lemma h_abs: "h \<bar>a\<bar> = \<bar>h a\<bar>"
  by (cases "a < 0") simp_all

lemma h_of_nat: "h (of_nat m) = of_nat m"
  by (induction m) (simp_all add: h_add)

lemma h_two: "h 2 = 2"
  using h_add[of 1 1]
  by simp

lemma h_fold_max: "h (fold max (map abs xs) a) = fold max (map (\<lambda>x. \<bar>h x\<bar>) xs) (h a)"
  by (induction xs arbitrary: a) (simp_all add: h_abs)

lemma wfun_edge: "i < length fs \<Longrightarrow> wfun {fs ! i, ts ! i} = h (ws ! i)"
  using wfun_eq[of "fs ! i" "ts ! i"] ecost_edge[of i]
  by (auto simp: G_def)

lemma wfun_set: "{\<bar>wfun e\<bar> | e. e \<in> G} = (\<lambda>x. \<bar>h x\<bar>) ` set ws"
proof-
  have "{\<bar>wfun e\<bar> | e. e \<in> G} = (\<lambda>i. \<bar>h (ws ! i)\<bar>) ` {..<length fs}"
    by (auto simp: Setcompr_eq_image G_image image_image wfun_edge intro!: image_cong)
  moreover have "set ws = (!) ws ` {..<length fs}"
    using ws_length
    by (simp add: lessThan_atLeast0 nth_image)
  ultimately show ?thesis
    by (simp add: image_image)
qed

lemma card_Vs_G: "card (Vs G) = length ls + length rs"
  using Vs_G sides_disjoint ls_distinct rs_distinct
  by (simp add: card_Un_disjoint distinct_card)

lemma h_dflt: "h (2 + of_nat (length ls + length rs) * max_abs_weight ws) =
                 2 * penalty G (\<lambda>e. sgn_w neg (wfun e))"
proof-
  have "h (max_abs_weight ws) = Max (insert 0 {\<bar>wfun e\<bar> | e. e \<in> G})"
    using Max_insert_fold[of 0 "map (\<lambda>x. \<bar>h x\<bar>) ws"]
    by (simp add: max_abs_weight_def h_fold_max wfun_set)
  moreover have "penalty G (\<lambda>e. sgn_w neg (wfun e)) = penalty G wfun"
    by (cases neg) (simp_all add: penalty_def)
  ultimately show ?thesis
    by (simp add: penalty_def card_Vs_G h_add h_mult h_of_nat h_two field_simps)
qed

lemma mwmc_correct:
  assumes "min_weight_perfect_matching cp.G cp.wfun Mc"
  shows "min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e)) (Mc \<inter> G)"
proof-
  have "min_weight_perfect_matching (bp_perfected_G L R)
          (bp_min_max_card_costs_to_min_perfect_costs G (\<lambda>e. sgn_w neg (wfun e)))
          {e \<in> bp_perfected_G L R. ren ` e \<in> Mc}"
    by (rule completion_result[where g = "sgn_w neg"])
       (use assms in \<open>simp_all add: h_sgn bp_min_max_card_costs_to_min_perfect_costs_def h_dflt[simplified]\<close>)
  hence "min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e))
           (project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> G)"
    by (rule min_weight_perfect_gives_min_weight_max_card_matching[OF bipartite_G finite_set finite_set])
  thus ?thesis
    using project_preimage[OF assms, of UNIV]
    by simp
qed

end

subsection \<open>Reading off the Matching of the Original Graph\<close>

text \<open>The matching of the original graph is read off a matching of the completed graph by one
      pass over the left vertices: a matched pair is kept if the test @{term kp} accepts the
      weight of its edge in the completed graph.\<close>

context hungarian_csr_completion
begin

definition "extract_step kp Mb Mo u = (case Mb u of None \<Rightarrow> Mo
   | Some v \<Rightarrow> if kp (ws' ! (pos u * k + pos v)) then Mo(u \<mapsto> v, v \<mapsto> u) else Mo)"

definition "extract kp Mb = foldl (extract_step kp Mb) Map.empty ls"

lemma extract_step_simps:
  "Mb u = None \<Longrightarrow> extract_step kp Mb Mo u = Mo"
  "Mb u = Some v \<Longrightarrow>
   extract_step kp Mb Mo u = (if kp (ws' ! (pos u * k + pos v)) then Mo(u \<mapsto> v, v \<mapsto> u) else Mo)"
  by (simp_all add: extract_step_def)

lemma L_ls': "L \<subseteq> set ls'"
  by (simp add: set_ls')

lemma cp_G_right: "\<lbrakk>{u, v} \<in> cp.G; u \<in> set ls'\<rbrakk> \<Longrightarrow> v \<in> set rs'"
  using sides_disjoint'
  unfolding cp_G
  by (auto simp: doubleton_eq_iff)

lemma G_sides: "\<lbrakk>{u, v} \<in> G; u \<notin> L\<rbrakk> \<Longrightarrow> v \<in> L"
  by (erule G_edgeE) (auto dest: fs_L)

lemma extract_inv:
  assumes "\<And>u v. Mb u = Some v \<Longrightarrow> Mb v = Some u" "\<And>u v. Mb u = Some v \<Longrightarrow> {u, v} \<in> cp.G"
    and "\<And>u v. \<lbrakk>u \<in> L; v \<in> set rs'\<rbrakk> \<Longrightarrow> kp (ws' ! (pos u * k + pos v)) \<longleftrightarrow> Q {u, v}"
    and "distinct xs" "set xs \<subseteq> L"
  shows "foldl (extract_step kp Mb) Map.empty xs =
           (\<lambda>x. if x \<in> set xs \<or> (\<exists>u\<in>set xs. Mb u = Some x)
                then (case Mb x of None \<Rightarrow> None | Some y \<Rightarrow> if Q {x, y} then Some y else None)
                else None)"
  using assms(4,5)
proof(induction xs rule: rev_induct)
  case (snoc u xs)
  have u: "u \<in> L" "u \<notin> set xs" "set xs \<subseteq> L"
    using snoc.prems
    by auto
  have IH: "foldl (extract_step kp Mb) Map.empty xs =
             (\<lambda>x. if x \<in> set xs \<or> (\<exists>u\<in>set xs. Mb u = Some x)
                  then (case Mb x of None \<Rightarrow> None | Some y \<Rightarrow> if Q {x, y} then Some y else None)
                  else None)"
    using snoc
    by simp
  have right: "w \<in> set rs'" if "Mb u' = Some w" "u' \<in> L" for u' w
    using that assms(2) cp_G_right L_ls'
    by blast
  have nu: "\<not> (\<exists>u'\<in>set xs. Mb u' = Some u)"
    using right[OF assms(1)] u L_ls' sides_disjoint'
    by (blast)
  show ?case
  proof(cases "Mb u")
    case None
    show ?thesis
      apply (rule ext)
      subgoal for x
        using IH None nu
        by (cases "x = u") (simp_all add: extract_step_simps)
      done
  next
    case (Some v)
    have v: "v \<in> set rs'" "Mb v = Some u" "v \<notin> set xs" "v \<noteq> u"
      using right[OF Some u(1)] assms(1)[OF Some] u L_ls' sides_disjoint'
      by auto
    have nv: "\<not> (\<exists>u'\<in>set xs. Mb u' = Some v)"
      using v(2) u(2)
      by (auto dest: assms(1))
    show ?thesis
      apply (rule ext)
      subgoal for x
        using IH Some v nv nu u(2) assms(3)[OF u(1) v(1)]
        by (cases "x = u"; cases "x = v") (simp_all add: extract_step_simps insert_commute)
      done
  qed
qed simp

lemma extract_correct:
  assumes "\<And>u v. Mb u = Some v \<Longrightarrow> Mb v = Some u" "\<And>u v. Mb u = Some v \<Longrightarrow> {u, v} \<in> cp.G"
    and "\<And>u v. \<lbrakk>u \<in> L; v \<in> set rs'\<rbrakk> \<Longrightarrow> kp (ws' ! (pos u * k + pos v)) \<longleftrightarrow> Q {u, v}"
    and "\<And>e. Q e \<Longrightarrow> e \<in> G"
  shows "{{u, v} | u v. extract kp Mb u = Some v} = {e \<in> {{u, v} | u v. Mb u = Some v}. Q e}"
proof-
  note inv = extract_inv[where kp = kp and Q = Q and Mb = Mb and xs = ls, OF assms(1-3) ls_distinct order_refl]
  have ex: "extract kp Mb x = (case Mb x of None \<Rightarrow> None | Some y \<Rightarrow> if Q {x, y} then Some y else None)" for x
  proof(cases "Mb x")
    case (Some y)
    show ?thesis
    proof(cases "Q {x, y}")
      case True
      hence "x \<in> L \<or> (\<exists>u\<in>L. Mb u = Some x)"
        using G_sides[OF assms(4)[OF True]] assms(1)[OF Some]
        by auto
      thus ?thesis
        using inv
        by (simp add: extract_def)
    qed (simp add: inv extract_def Some)
  qed (simp add: inv extract_def)
  show ?thesis
    unfolding ex
    by (auto split: option.splits if_splits)
qed

end



section \<open>The Imperative Programs\<close>

subsection \<open>Loops\<close>

text \<open>A loop over @{term "[i..<m]"} that threads a state through the iterations.\<close>

partial_function (heap) fold_imp :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's Heap) \<Rightarrow> 's \<Rightarrow> 's Heap" where
  "fold_imp i m f s = (if i < m then do { s' \<leftarrow> f i s; fold_imp (Suc i) m f s' } else return s)"

declare fold_imp.simps[code]

lemma fold_imp_rule:
  assumes "i \<le> m" "\<And>j s. \<lbrakk>i \<le> j; j < m\<rbrakk> \<Longrightarrow> <P j s> f j s <P (Suc j)>"
  shows "<P i s> fold_imp i m f s <P m>"
  using assms
proof(induction "m - i" arbitrary: i s)
  case 0
  thus ?case
    by (subst fold_imp.simps) sep_auto
next
  case (Suc d)
  have f: "<P i s> f i s <P (Suc i)>"
    using Suc
    by simp
  have r: "<P (Suc i) s'> fold_imp (Suc i) m f s' <P m>" for s'
    by (rule Suc.hyps(1)) (use Suc in auto)
  show ?case
    using Suc
    by (subst fold_imp.simps) (sep_auto heap: f r)
qed

subsection \<open>Building the Arrays of the Completed Graph\<close>

text \<open>Copying a side and padding it by new vertices @{term "n + i"}.\<close>

definition pad_step :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit \<Rightarrow> unit Heap" where
  "pad_step S l nv A a u = do {
     x \<leftarrow> (if a < l then Array.nth S a else return (nv + (a - l)));
     _ \<leftarrow> Array.upd a x A;
     return () }"

lemma pad_loop_rule:
  assumes "length xs = K" "length src \<le> K"
  shows "<A \<mapsto>\<^sub>a xs * S \<mapsto>\<^sub>a src> fold_imp 0 K (pad_step S (length src) nv A) ()
         <\<lambda>_. A \<mapsto>\<^sub>a (src @ [nv..<nv + (K - length src)]) * S \<mapsto>\<^sub>a src>"
proof-
  define ys where "ys = src @ [nv..<nv + (K - length src)]"
  have len: "length ys = K"
    using assms
    by (simp add: ys_def)
  have v: "ys ! j = (if j < length src then src ! j else nv + (j - length src))" if "j < K" for j
    using that assms
    by (simp add: ys_def nth_append)
  have "<A \<mapsto>\<^sub>a (take 0 ys @ drop 0 xs) * S \<mapsto>\<^sub>a src> fold_imp 0 K (pad_step S (length src) nv A) ()
        <\<lambda>_. A \<mapsto>\<^sub>a (take K ys @ drop K xs) * S \<mapsto>\<^sub>a src>"
  proof(rule fold_imp_rule[where P = "\<lambda>j _. A \<mapsto>\<^sub>a (take j ys @ drop j xs) * S \<mapsto>\<^sub>a src"])
    fix j s assume j: "0 \<le> j" "j < K"
    have u: "list_update (take j ys @ drop j xs) j (ys ! j) = take (Suc j) ys @ drop (Suc j) xs"
      using j len assms
      by (simp add: take_drop_upd)
    show "<A \<mapsto>\<^sub>a (take j ys @ drop j xs) * S \<mapsto>\<^sub>a src> pad_step S (length src) nv A j s
          <\<lambda>_. A \<mapsto>\<^sub>a (take (Suc j) ys @ drop (Suc j) xs) * S \<mapsto>\<^sub>a src>"
      unfolding pad_step_def
      using j assms len u v[OF j(2)]
      by sep_auto
  qed simp
  thus ?thesis
    using len assms(1)
    by (simp add: ys_def)
qed

text \<open>The positions of the vertices in their side.\<close>

definition pos_step :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit \<Rightarrow> unit Heap" where
  "pos_step S P a u = do { x \<leftarrow> Array.nth S a; _ \<leftarrow> Array.upd x a P; return () }"

lemma pos_loop_rule:
  assumes "length ys = K" "\<forall>x\<in>set ys. x < length P0"
  shows "<Pa \<mapsto>\<^sub>a P0 * S \<mapsto>\<^sub>a ys> fold_imp 0 K (pos_step S Pa) ()
         <\<lambda>_. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<K] * S \<mapsto>\<^sub>a ys>"
proof-
  have "<Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<0] * S \<mapsto>\<^sub>a ys>
        fold_imp 0 K (pos_step S Pa) ()
        <\<lambda>_. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<K] * S \<mapsto>\<^sub>a ys>"
  proof(rule fold_imp_rule[where P = "\<lambda>j _. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<j] *
                                         S \<mapsto>\<^sub>a ys"])
    fix j s assume j: "0 \<le> j" "j < K"
    have "ys ! j < length P0"
      using assms j nth_mem[of j ys]
      by auto
    thus "<Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<j] * S \<mapsto>\<^sub>a ys> pos_step S Pa j s
          <\<lambda>_. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<Suc j] * S \<mapsto>\<^sub>a ys>"
      unfolding pos_step_def
      using j assms(1)
      by sep_auto
  qed simp
  thus ?thesis
    by simp
qed

text \<open>The endpoints of the edges of the completed graph, in row-major order.\<close>

definition grid_step :: "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow>
                          unit \<Rightarrow> unit Heap" where
  "grid_step k As Bs Fa Ta j u = do {
     x \<leftarrow> Array.nth As (j div k);
     y \<leftarrow> Array.nth Bs (j mod k);
     _ \<leftarrow> Array.upd j x Fa;
     _ \<leftarrow> Array.upd j y Ta;
     return () }"

lemma grid_loop_rule:
  assumes "length as = k" "length bs = k" "length xs = k * k" "length ys = k * k"
  shows "<As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a xs * Ta \<mapsto>\<^sub>a ys> fold_imp 0 (k * k) (grid_step k As Bs Fa Ta) ()
         <\<lambda>_. As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a map (\<lambda>j. as ! (j div k)) [0..<k * k] *
             Ta \<mapsto>\<^sub>a map (\<lambda>j. bs ! (j mod k)) [0..<k * k]>"
proof-
  define F where "F = map (\<lambda>j. as ! (j div k)) [0..<k * k]"
  define T where "T = map (\<lambda>j. bs ! (j mod k)) [0..<k * k]"
  have lF: "length F = k * k" "length T = k * k"
    by (simp_all add: F_def T_def)
  have "<As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take 0 F @ drop 0 xs) * Ta \<mapsto>\<^sub>a (take 0 T @ drop 0 ys)>
        fold_imp 0 (k * k) (grid_step k As Bs Fa Ta) ()
        <\<lambda>_. As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take (k * k) F @ drop (k * k) xs) *
            Ta \<mapsto>\<^sub>a (take (k * k) T @ drop (k * k) ys)>"
  proof(rule fold_imp_rule[where P = "\<lambda>j _. As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take j F @ drop j xs) *
                                         Ta \<mapsto>\<^sub>a (take j T @ drop j ys)"])
    fix j s assume j: "0 \<le> j" "j < k * k"
    have u: "list_update (take j F @ drop j xs) j (as ! (j div k)) = take (Suc j) F @ drop (Suc j) xs"
            "list_update (take j T @ drop j ys) j (bs ! (j mod k)) = take (Suc j) T @ drop (Suc j) ys"
      using j assms
      by (simp_all add: F_def T_def take_drop_upd)
    show "<As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take j F @ drop j xs) * Ta \<mapsto>\<^sub>a (take j T @ drop j ys)>
          grid_step k As Bs Fa Ta j s
          <\<lambda>_. As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take (Suc j) F @ drop (Suc j) xs) *
              Ta \<mapsto>\<^sub>a (take (Suc j) T @ drop (Suc j) ys)>"
      unfolding grid_step_def
      using j assms lF div_mod_less_square[of j k]
      by (sep_auto simp: u)
  qed simp
  thus ?thesis
    using assms lF
    by (simp add: F_def T_def)
qed

text \<open>The weights of the completed graph: the default weight everywhere, and @{term "cf w"} at the
      edge of the completed graph for an original edge of weight @{term w}.\<close>

definition wgt_step :: "('n \<Rightarrow> 'n) \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::heap array \<Rightarrow> nat array \<Rightarrow>
                         'n array \<Rightarrow> nat \<Rightarrow> unit \<Rightarrow> unit Heap" where
  "wgt_step cf k Fa Ta Wa Pa Wc i u = do {
     x \<leftarrow> Array.nth Fa i;
     y \<leftarrow> Array.nth Ta i;
     px \<leftarrow> Array.nth Pa x;
     py \<leftarrow> Array.nth Pa y;
     w \<leftarrow> Array.nth Wa i;
     _ \<leftarrow> Array.upd (px * k + py) (cf w) Wc;
     return () }"

text \<open>The arrays of the completed graph, together with the position array and the numbers of
      vertices and of vertices per side.\<close>

definition hungarian_csr_complete ::
  "'n::heap \<Rightarrow> ('n \<Rightarrow> 'n) \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow>
   (nat array \<times> nat array \<times> 'n array \<times> nat array \<times> nat array \<times> nat array \<times> nat \<times> nat) Heap" where
  "hungarian_csr_complete dflt cf n Fa Ta Wa La Rv = do {
     l \<leftarrow> Array.len La;
     r \<leftarrow> Array.len Rv;
     m \<leftarrow> Array.len Fa;
     let k = max l r;
     let n' = n + (k - l) + (k - r);
     La' \<leftarrow> Array.new k 0;
     fold_imp 0 k (pad_step La l n La') ();
     Rv' \<leftarrow> Array.new k 0;
     fold_imp 0 k (pad_step Rv r n Rv') ();
     Pa \<leftarrow> Array.new n' 0;
     fold_imp 0 k (pos_step La' Pa) ();
     fold_imp 0 k (pos_step Rv' Pa) ();
     Fa' \<leftarrow> Array.new (k * k) 0;
     Ta' \<leftarrow> Array.new (k * k) 0;
     fold_imp 0 (k * k) (grid_step k La' Rv' Fa' Ta') ();
     Wa' \<leftarrow> Array.new (k * k) dflt;
     fold_imp 0 m (wgt_step cf k Fa Ta Wa Pa Wa') ();
     return (Fa', Ta', Wa', La', Rv', Pa, n', k) }"

subsection \<open>Reading off the Matching\<close>

text \<open>The buddies of the completed graph are read from the array @{term Mi}, with @{term n'} for a
      free vertex. The kept pairs are written into the array @{term Mo} of size @{term n}, in
      place.\<close>

definition extract_imp_step :: "('n::heap \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow>
                                'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit \<Rightarrow> unit Heap" where
  "extract_imp_step kp n' k La Pa Wc Mi Mo a s = do {
     u \<leftarrow> Array.nth La a;
     v \<leftarrow> array_fun_lookup_imp Mi u;
     (if v = n' then return ()
      else do {
        pv \<leftarrow> Array.nth Pa v;
        w \<leftarrow> Array.nth Wc (a * k + pv);
        if kp w then do { array_fun_upd_imp Mo u v; array_fun_upd_imp Mo v u } else return () }) }"

definition extract_imp :: "('n::heap \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow>
                           nat array \<Rightarrow> nat array \<Rightarrow> unit Heap" where
  "extract_imp kp n' k La Pa Wc Mi Mo = do {
     l \<leftarrow> Array.len La;
     fold_imp 0 l (extract_imp_step kp n' k La Pa Wc Mi Mo) () }"

subsection \<open>The Reduction\<close>

text \<open>The array of the result is allocated, the arrays of the completed graph are built, the
      Hungarian method of \<open>Hungarian_Method_CSR_Instantiation\<close> runs on them, and the matching of
      the original graph is read off. The result is the array of buddies, with @{term n} for a
      free vertex.\<close>

definition hungarian_csr_reduced_run ::
  "'n::{linordered_idom, heap} \<Rightarrow> ('n \<Rightarrow> 'n) \<Rightarrow> ('n \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array Heap" where
  "hungarian_csr_reduced_run dflt cf kp n \<theta> cap Fa Ta Wa La Rv = do {
     Mo \<leftarrow> Array.new n n;
     (Fa', Ta', Wa', La', Rv', Pa, n', k) \<leftarrow> hungarian_csr_complete dflt cf n Fa Ta Wa La Rv;
     (r, Mi, Pti) \<leftarrow> hungarian_csr_run n' \<theta> cap Fa' Ta' Wa' La' Rv';
     extract_imp kp n' k La Pa Wa' Mi Mo;
     return Mo }"

context hungarian_csr_completion
begin

lemma length_posl [simp]: "length posl = n'"
  by (simp add: posl_def)

lemma edge_bounds':
  "j < length fs \<Longrightarrow> fs ! j < n' \<and> ts ! j < n' \<and> j < length ts \<and> j < length ws \<and> eix j < k * k"
  using fs_in_ls'[of j] ts_in_rs'[of j] below_n' ts_length ws_length eix_less[of j]
  by auto

lemma eix_posl: "posl ! (fs ! j) * k + posl ! (ts ! j) = eix j"
  by (simp add: eix_def pos_def)

lemma wgt_loop_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a replicate (k * k) dflt>
   fold_imp 0 (length fs) (wgt_step cf k Fa Ta Wa Pa Wc) ()
   <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws'>"
proof-
  let ?W = "\<lambda>j. foldl (\<lambda>W i. list_update W (eix i) (cf (ws ! i))) (replicate (k * k) dflt) [0..<j]"
  have "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ?W 0>
        fold_imp 0 (length fs) (wgt_step cf k Fa Ta Wa Pa Wc) ()
        <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ?W (length fs)>"
  proof(rule fold_imp_rule[where P = "\<lambda>j _. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl *
                                         Wc \<mapsto>\<^sub>a ?W j"])
    fix j s assume j: "0 \<le> j" "j < length fs"
    show "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ?W j>
          wgt_step cf k Fa Ta Wa Pa Wc j s
          <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ?W (Suc j)>"
      unfolding wgt_step_def
      using j edge_bounds'[of j]
      by (sep_auto simp: eix_posl)
  qed simp
  thus ?thesis
    by (simp add: ws'_def)
qed

lemma pad_ls'_rule:
  "<A \<mapsto>\<^sub>a replicate k 0 * La \<mapsto>\<^sub>a ls> fold_imp 0 k (pad_step La (length ls) n A) ()
   <\<lambda>_. A \<mapsto>\<^sub>a ls' * La \<mapsto>\<^sub>a ls>"
  using pad_loop_rule[of "replicate k 0" k ls]
  by (simp add: ls'_def k_def)

lemma pad_rs'_rule:
  "<A \<mapsto>\<^sub>a replicate k 0 * Rv \<mapsto>\<^sub>a rs> fold_imp 0 k (pad_step Rv (length rs) n A) ()
   <\<lambda>_. A \<mapsto>\<^sub>a rs' * Rv \<mapsto>\<^sub>a rs>"
  using pad_loop_rule[of "replicate k 0" k rs]
  by (simp add: rs'_def k_def)

lemma pos_ls'_rule:
  "<Pa \<mapsto>\<^sub>a replicate n' 0 * S \<mapsto>\<^sub>a ls'> fold_imp 0 k (pos_step S Pa) ()
   <\<lambda>_. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k] * S \<mapsto>\<^sub>a ls'>"
  using pos_loop_rule[of ls' k "replicate n' 0"] length_ls' below_n'
  by auto

lemma pos_rs'_rule:
  "<Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k] * S \<mapsto>\<^sub>a rs'>
   fold_imp 0 k (pos_step S Pa) () <\<lambda>_. Pa \<mapsto>\<^sub>a posl * S \<mapsto>\<^sub>a rs'>"
  using pos_loop_rule[of rs' k "foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k]"]
        length_rs' below_n'
  by (auto simp: posl_def)

lemma grid'_rule:
  "<As \<mapsto>\<^sub>a ls' * Bs \<mapsto>\<^sub>a rs' * Fb \<mapsto>\<^sub>a replicate (k * k) 0 * Tb \<mapsto>\<^sub>a replicate (k * k) 0>
   fold_imp 0 (k * k) (grid_step k As Bs Fb Tb) ()
   <\<lambda>_. As \<mapsto>\<^sub>a ls' * Bs \<mapsto>\<^sub>a rs' * Fb \<mapsto>\<^sub>a fs' * Tb \<mapsto>\<^sub>a ts'>"
  using grid_loop_rule[of ls' k rs' "replicate (k * k) 0" "replicate (k * k) 0"] length_ls' length_rs'
  by (simp add: fs'_def ts'_def)

lemma complete_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_complete dflt cf n Fa Ta Wa La Rv
   <\<lambda>(Fa', Ta', Wa', La', Rv', Pa, n'', k'). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      Fa' \<mapsto>\<^sub>a fs' * Ta' \<mapsto>\<^sub>a ts' * Wa' \<mapsto>\<^sub>a ws' * La' \<mapsto>\<^sub>a ls' * Rv' \<mapsto>\<^sub>a rs' * Pa \<mapsto>\<^sub>a posl *
      \<up>(n'' = n' \<and> k' = k)>"
  unfolding hungarian_csr_complete_def
  by (sep_auto heap: pad_ls'_rule pad_rs'_rule pos_ls'_rule pos_rs'_rule grid'_rule wgt_loop_rule
               simp: k_def[symmetric] n'_def[symmetric])

lemma ls_nth_props:
  assumes "a < length ls"
  shows "a < k" "ls ! a \<in> set ls'" "posl ! (ls ! a) = a" "ls ! a \<in> L" "ls ! a < n" "ls ! a < n'"
  using assms pos_ls'[of a] L_less below_n' nth_mem[of a ls]
  by (auto simp: k_def ls'_def nth_append pos_def simp del: nth_mem)

lemma rs'_posl: "v \<in> set rs' \<Longrightarrow> posl ! v < k \<and> v < n'"
  using pos_less below_n'
  by (auto simp: pos_def)

lemma buddy_lookup_upd:
  "\<lbrakk>u < m; v < m\<rbrakk> \<Longrightarrow>
   aug_csr.buddy_lookup m (Mt(u := v, v := u)) = (aug_csr.buddy_lookup m Mt)(u \<mapsto> v, v \<mapsto> u)"
  by (auto simp: aug_csr.buddy_lookup_def array_fun_lookup_def)

text \<open>The matching of the completed graph is the total map @{term Mb} with @{term n'} for a free
      vertex; it is read through @{term "aug_csr.buddy_lookup n'"}. A kept pair belongs to the
      original graph, hence its vertices are below @{term n}.\<close>

lemma extract_imp_rule:
  assumes "\<And>u v. aug_csr.buddy_lookup n' Mb u = Some v \<Longrightarrow> {u, v} \<in> cp.G"
    and "\<And>u v. \<lbrakk>u \<in> L; v \<in> set rs'; kp (ws' ! (pos u * k + pos v))\<rbrakk> \<Longrightarrow> v < n"
  shows "<La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * Mo \<mapsto>\<^sub>a replicate n n>
         extract_imp kp n' k La Pa Wc Mi Mo
         <\<lambda>_. \<exists>\<^sub>AMt. La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi *
              array_fun_assn n Mt Mo *
              \<up>(aug_csr.buddy_lookup n Mt = extract kp (aug_csr.buddy_lookup n' Mb))>"
proof-
  let ?B = "aug_csr.buddy_lookup n' Mb"
  let ?E = "\<lambda>a. foldl (extract_step kp ?B) Map.empty (take a ls)"
  let ?P = "\<lambda>a (s::unit). \<exists>\<^sub>AMt. La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi *
                               array_fun_assn n Mt Mo * \<up>(aug_csr.buddy_lookup n Mt = ?E a)"
  have step: "<?P a s> extract_imp_step kp n' k La Pa Wc Mi Mo a s <?P (Suc a)>"
    if "a < length ls" for a s
  proof(cases "Mb (ls ! a) = n'")
    case True
    hence "?B (ls ! a) = None"
      by (simp add: aug_csr.buddy_lookup_def array_fun_lookup_def)
    thus ?thesis
      unfolding extract_imp_step_def array_fun_lookup_imp_def
      using that True ls_nth_props[of a]
      by (sep_auto heap: array_fun_lookup_rule simp: take_Suc_conv_app_nth extract_step_def)
  next
    case False
    define v where "v = Mb (ls ! a)"
    have B: "?B (ls ! a) = Some v"
      using False
      by (simp add: aug_csr.buddy_lookup_def array_fun_lookup_def v_def)
    have v: "v \<in> set rs'"
      using that assms(1)[OF B] ls_nth_props[of a]
      by (auto intro: cp_G_right)
    have w: "ws' ! (pos (ls ! a) * k + pos v) = ws' ! (a * k + posl ! v)"
      using that ls_nth_props[of a]
      by (simp add: pos_def)
    show ?thesis
    proof(cases "kp (ws' ! (a * k + posl ! v))")
      case True
      have vn: "v < n"
        using that True v w assms(2)[of "ls ! a" v] ls_nth_props[of a]
        by simp
      show ?thesis
        apply (rule ht_exEI, rule norm_pre_extractI(5))
        subgoal premises Mt for Mt
        proof-
          have c: "<La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * array_fun_assn n Mt Mo>
                   extract_imp_step kp n' k La Pa Wc Mi Mo a s
                   <\<lambda>_. La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi *
                        array_fun_assn n (Mt(ls ! a := v, v := ls ! a)) Mo>"
            unfolding extract_imp_step_def array_fun_lookup_imp_def array_fun_upd_imp_def
            using that False True vn ls_nth_props[of a] rs'_posl[OF v] mult_add_less[of a k "posl ! v"]
            by (sep_auto heap: array_fun_lookup_rule array_fun_upd_rule simp: v_def[symmetric])
          have e: "aug_csr.buddy_lookup n (Mt(ls ! a := v, v := ls ! a)) = ?E (Suc a)"
            using that Mt True vn ls_nth_props[of a]
            by (simp add: take_Suc_conv_app_nth extract_step_def B w buddy_lookup_upd)
          show ?thesis
            by (rule ht_cons_post[OF c]) (sep_auto simp: e)
        qed
        done
    next
      case False
      show ?thesis
        apply (rule ht_exEI, rule norm_pre_extractI(5))
        subgoal premises Mt for Mt
        proof-
          have c: "<La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * array_fun_assn n Mt Mo>
                   extract_imp_step kp n' k La Pa Wc Mi Mo a s
                   <\<lambda>_. La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * array_fun_assn n Mt Mo>"
            unfolding extract_imp_step_def array_fun_lookup_imp_def
            using that \<open>Mb (ls ! a) \<noteq> n'\<close> False ls_nth_props[of a] rs'_posl[OF v] mult_add_less[of a k "posl ! v"]
            by (sep_auto heap: array_fun_lookup_rule simp: v_def[symmetric])
          have e: "aug_csr.buddy_lookup n Mt = ?E (Suc a)"
            using that Mt False
            by (simp add: take_Suc_conv_app_nth extract_step_def B w)
          show ?thesis
            by (rule ht_cons_post[OF c]) (sep_auto simp: e)
        qed
        done
    qed
  qed
  have loop: "<?P 0 ()> fold_imp 0 (length ls) (extract_imp_step kp n' k La Pa Wc Mi Mo) ()
              <?P (length ls)>"
    by (rule fold_imp_rule[where P = ?P]) (simp_all add: step)
  have init: "La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * Mo \<mapsto>\<^sub>a replicate n n
              \<Longrightarrow>\<^sub>A ?P 0 ()"
    unfolding array_fun_assn_replicate[symmetric]
    by (rule ent_ex_postI[where x = "\<lambda>_. n"])
       (sep_auto simp: aug_csr.buddy_lookup_def array_fun_lookup_def)
  have loop': "<La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * Mo \<mapsto>\<^sub>a replicate n n>
               fold_imp 0 (length ls) (extract_imp_step kp n' k La Pa Wc Mi Mo) () <?P (length ls)>"
    by (rule ht_cons_pre[OF init loop])
  show ?thesis
    unfolding extract_imp_def
    by (sep_auto heap: loop' simp: extract_def)
qed

text \<open>The Hungarian method succeeds on the completed graph, and its matching is symmetric, consists
      of edges of the completed graph and is a perfect matching of minimum weight.\<close>

lemma cp_hungarian_some: "\<exists>Mb. cp.hl.hungarian = Some Mb"
proof(cases cp.hl.hungarian)
  case None
  hence "\<nexists>M. perfect_matching cp.G M"
    by (rule cp.hl.hungarian_correctness(1))
  thus ?thesis
    using cp_perfect_exists
    by simp
qed simp

lemma cp_result:
  assumes "cp.hl.hungarian = Some Mb"
  shows "\<And>u v. aug_csr.buddy_lookup n' Mb u = Some v \<Longrightarrow> aug_csr.buddy_lookup n' Mb v = Some u"
    and "\<And>u v. aug_csr.buddy_lookup n' Mb u = Some v \<Longrightarrow> {u, v} \<in> cp.G"
    and "min_weight_perfect_matching cp.G cp.wfun
           {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v}"
  using cp.hl.hungarian_final_invar[OF assms] cp.hl.hungarian_correctness(2)[OF assms]
  by (auto simp: aug_csr.invar_matching_def aug_csr.symmetric_buddies_def aug_csr.\<M>_def')
     (blast)

lemma reduced_run_rule:
  assumes "\<And>u v. \<lbrakk>u \<in> L; v \<in> set rs'; kp (ws' ! (pos u * k + pos v))\<rbrakk> \<Longrightarrow> v < n"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_reduced_run dflt cf kp n theta cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AMb Mt. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n Mt Mo * true *
         \<up>(cp.hl.hungarian = Some Mb \<and>
           aug_csr.buddy_lookup n Mt = extract kp (aug_csr.buddy_lookup n' Mb))>"
proof-
  obtain Mb where Mb: "cp.hl.hungarian = Some Mb"
    using cp_hungarian_some
    by blast
  note ex = extract_imp_rule[OF cp_result(2)[OF Mb] assms]
  show ?thesis
    unfolding hungarian_csr_reduced_run_def
    by (sep_auto heap: complete_rule cp.hungarian_csr_run_rule ex simp: Mb)
qed

end

subsection \<open>Correctness of the Variants\<close>

context hungarian_csr_mw
begin

lemma mw_keep:
  assumes "u \<in> L" "v \<in> set rs'"
  shows "ws' ! (pos u * k + pos v) < 0 \<longleftrightarrow> {u, v} \<in> G \<and> sgn_w neg (wfun {u, v}) < 0"
proof-
  have "ws' ! (pos u * k + pos v) < 0 \<longleftrightarrow> cp.ecost u v < 0"
    using assms L_ls' ws'_at[of u v, symmetric]
    by auto
  thus ?thesis
    using assms L_ls' cp_ecost[of u v] wfun_orig[of u v]
    by (cases "{u, v} \<in> G") (auto simp: h_sgn)
qed

lemma mw_extract:
  assumes "cp.hl.hungarian = Some Mb"
  shows "min_weight_matching G (\<lambda>e. sgn_w neg (wfun e))
           {{u, v} | u v. extract (\<lambda>w. w < 0) (aug_csr.buddy_lookup n' Mb) u = Some v}"
proof-
  have "{{u, v} | u v. extract (\<lambda>w. w < 0) (aug_csr.buddy_lookup n' Mb) u = Some v} =
        {e \<in> {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v}. e \<in> G \<and> sgn_w neg (wfun e) < 0}"
    by (rule extract_correct[OF cp_result(1,2)[OF assms]]) (simp_all add: mw_keep)
  also have "\<dots> = {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v} \<inter> G \<inter>
                   {e. sgn_w neg (wfun e) < 0}"
    by auto
  finally show ?thesis
    using mw_correct[OF cp_result(3)[OF assms]]
    by simp
qed

lemma mw_kept: "\<lbrakk>u \<in> L; v \<in> set rs'; ws' ! (pos u * k + pos v) < 0\<rbrakk> \<Longrightarrow> v < n"
  using mw_keep G_below[of "{u, v}" v]
  by simp

lemma mw_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_reduced_run 0 (\<lambda>w. min 0 (sgn_w neg w)) (\<lambda>w. w < 0) n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n M))>"
  apply (rule ht_cons_post_prec[OF reduced_run_rule])
  subgoal
    by (rule mw_kept)
  apply (intro ent_ex_preI)
  subgoal for Mo Mb Mt
  proof(cases "cp.hl.hungarian = Some Mb \<and>
                aug_csr.buddy_lookup n Mt = extract (\<lambda>w. w < 0) (aug_csr.buddy_lookup n' Mb)")
    case True
    show ?thesis
      by (rule ent_ex_postI[where x = Mt]) (use True mw_extract[of Mb] in \<open>sep_auto simp: aug_csr.\<M>_def'\<close>)
  next
    case False
    then show ?thesis
      by (simp only: ent_pure_pre_iff) blast
  qed
  done

end

context hungarian_csr_mwmc
begin

lemma mwmc_keep:
  assumes "u \<in> L" "v \<in> set rs'"
  shows "ws' ! (pos u * k + pos v) < 2 + of_nat (length ls + length rs) * max_abs_weight ws
           \<longleftrightarrow> {u, v} \<in> G"
proof-
  have "ws' ! (pos u * k + pos v) < 2 + of_nat (length ls + length rs) * max_abs_weight ws \<longleftrightarrow>
          cp.ecost u v < 2 * penalty G (\<lambda>e. sgn_w neg (wfun e))"
    using assms L_ls' ws'_at[of u v, symmetric] h_dflt[symmetric]
    by (auto)
  moreover have "sgn_w neg (wfun {u, v}) < 2 * penalty G (\<lambda>e. sgn_w neg (wfun e))" if "{u, v} \<in> G"
    using that penalty_gtr_0[OF finite_G, of "\<lambda>e. sgn_w neg (wfun e)"]
          edge_weight_less_thatn_penalty[OF graph_invarG[OF bipartite_G finite_set finite_set] that,
                                         of "\<lambda>e. sgn_w neg (wfun e)"]
    by linarith
  ultimately show ?thesis
    using assms L_ls' cp_ecost[of u v] wfun_orig[of u v] h_dflt
    by (cases "{u, v} \<in> G") (auto simp: h_sgn)
qed

lemma mwmc_extract:
  assumes "cp.hl.hungarian = Some Mb"
  shows "min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e))
           {{u, v} | u v. extract (\<lambda>w. w < 2 + of_nat (length ls + length rs) * max_abs_weight ws)
                            (aug_csr.buddy_lookup n' Mb) u = Some v}"
proof-
  have "{{u, v} | u v. extract (\<lambda>w. w < 2 + of_nat (length ls + length rs) * max_abs_weight ws)
                         (aug_csr.buddy_lookup n' Mb) u = Some v} =
        {e \<in> {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v}. e \<in> G}"
    by (rule extract_correct[OF cp_result(1,2)[OF assms]]) (simp_all only: mwmc_keep)
  also have "\<dots> = {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v} \<inter> G"
    by auto
  finally show ?thesis
    using mwmc_correct[OF cp_result(3)[OF assms]]
    by simp
qed

lemma mwmc_kept:
  "\<lbrakk>u \<in> L; v \<in> set rs';
    ws' ! (pos u * k + pos v) < 2 + of_nat (length ls + length rs) * max_abs_weight ws\<rbrakk>
   \<Longrightarrow> v < n"
  using mwmc_keep G_below[of "{u, v}" v]
  by simp

lemma mwmc_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_reduced_run (2 + of_nat (length ls + length rs) * max_abs_weight ws) (sgn_w neg)
     (\<lambda>w. w < 2 + of_nat (length ls + length rs) * max_abs_weight ws) n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n M))>"
  apply (rule ht_cons_post_prec[OF reduced_run_rule])
  subgoal
    by (rule mwmc_kept)
  apply (intro ent_ex_preI)
  subgoal for Mo Mb Mt
  proof(cases "cp.hl.hungarian = Some Mb \<and>
                aug_csr.buddy_lookup n Mt =
                  extract (\<lambda>w. w < 2 + of_nat (length ls + length rs) * max_abs_weight ws)
                    (aug_csr.buddy_lookup n' Mb)")
    case True
    show ?thesis
      by (rule ent_ex_postI[where x = Mt]) (use True mwmc_extract[of Mb] in \<open>sep_auto simp: aug_csr.\<M>_def'\<close>)
  next
    case False
    then show ?thesis
      by (simp only: ent_pure_pre_iff) blast
  qed
  done

end

subsection \<open>The Programs for the Variants\<close>

text \<open>Minimum and maximum weight matchings.\<close>

definition "hungarian_csr_mw_run neg = hungarian_csr_reduced_run 0 (\<lambda>w. min 0 (sgn_w neg w)) (\<lambda>w. w < 0)"

text \<open>Minimum and maximum weight maximum cardinality matchings. The penalty is computed from the
      largest absolute weight.\<close>

definition max_abs_step :: "'n::{linordered_idom, heap} array \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n Heap" where
  "max_abs_step Wa i s = do { w \<leftarrow> Array.nth Wa i; return (max \<bar>w\<bar> s) }"

lemma max_abs_loop_rule:
  "<Wa \<mapsto>\<^sub>a ws> fold_imp 0 (length ws) (max_abs_step Wa) 0
   <\<lambda>s. Wa \<mapsto>\<^sub>a ws * \<up>(s = max_abs_weight ws)>"
proof-
  have "<Wa \<mapsto>\<^sub>a ws * \<up>(0 = fold max (map abs (take 0 ws)) 0)> fold_imp 0 (length ws) (max_abs_step Wa) 0
        <\<lambda>s. Wa \<mapsto>\<^sub>a ws * \<up>(s = fold max (map abs (take (length ws) ws)) 0)>"
  proof(rule fold_imp_rule[where P = "\<lambda>j s. Wa \<mapsto>\<^sub>a ws * \<up>(s = fold max (map abs (take j ws)) 0)"])
    fix j s assume j: "0 \<le> j" "j < length ws"
    show "<Wa \<mapsto>\<^sub>a ws * \<up>(s = fold max (map abs (take j ws)) 0)> max_abs_step Wa j s
          <\<lambda>s. Wa \<mapsto>\<^sub>a ws * \<up>(s = fold max (map abs (take (Suc j) ws)) 0)>"
      unfolding max_abs_step_def
      using j
      by (sep_auto simp: take_Suc_conv_app_nth)
  qed simp
  thus ?thesis
    by (simp add: max_abs_weight_def)
qed

definition hungarian_csr_mwmc_run ::
  "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array 
   \<Rightarrow> nat array \<Rightarrow>
   nat array \<Rightarrow> nat array Heap" where
  "hungarian_csr_mwmc_run neg n \<theta> cap Fa Ta Wa La Rv = do {
     m \<leftarrow> Array.len Wa;
     l \<leftarrow> Array.len La;
     r \<leftarrow> Array.len Rv;
     mx \<leftarrow> fold_imp 0 m (max_abs_step Wa) 0;
     hungarian_csr_reduced_run (2 + of_nat (l + r) * mx) (sgn_w neg)
       (\<lambda>w. w < 2 + of_nat (l + r) * mx) n \<theta> cap Fa Ta Wa La Rv }"

text \<open>Maximum weight perfect matchings, on the negated weights.\<close>

definition neg_step :: "'n::{uminus, heap} array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> unit \<Rightarrow> unit Heap" where
  "neg_step Wa Wn i u = do { w \<leftarrow> Array.nth Wa i; _ \<leftarrow> Array.upd i (- w) Wn; return () }"

lemma neg_loop_rule:
  "<Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a replicate (length ws) 0> fold_imp 0 (length ws) (neg_step Wa Wn) ()
   <\<lambda>_. Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a map uminus ws>"
proof-
  define ys where "ys = map uminus ws"
  have "<Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a (take 0 ys @ drop 0 (replicate (length ws) 0))>
        fold_imp 0 (length ws) (neg_step Wa Wn) ()
        <\<lambda>_. Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a (take (length ws) ys @ drop (length ws) (replicate (length ws) 0))>"
  proof(rule fold_imp_rule[where P = "\<lambda>j _. Wa \<mapsto>\<^sub>a ws *
                                         Wn \<mapsto>\<^sub>a (take j ys @ drop j (replicate (length ws) 0))"])
    fix j s assume j: "0 \<le> j" "j < length ws"
    have u: "list_update (take j ys @ drop j (replicate (length ws) 0)) j (- ws ! j) =
             take (Suc j) ys @ drop (Suc j) (replicate (length ws) 0)"
      by (rule take_drop_upd) (use j in \<open>simp_all add: ys_def\<close>)
    show "<Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a (take j ys @ drop j (replicate (length ws) 0))> neg_step Wa Wn j s
          <\<lambda>_. Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a (take (Suc j) ys @ drop (Suc j) (replicate (length ws) 0))>"
      unfolding neg_step_def
      using j u
      by (sep_auto simp: ys_def)
  qed simp
  thus ?thesis
    by (simp add: ys_def)
qed

definition "hungarian_csr_max_perfect_run n \<theta> cap Fa Ta Wa La Rv = do {
     m \<leftarrow> Array.len Wa;
     Wn \<leftarrow> Array.new m 0;
     fold_imp 0 m (neg_step Wa Wn) ();
     hungarian_csr_run n \<theta> cap Fa Ta Wn La Rv }"

subsection \<open>Correctness of the Programs\<close>

context hungarian_csr_input
begin

lemma hungarian_csr_mw_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mw_run neg n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n M))>"
proof-
  interpret mw: hungarian_csr_mw h n fs ts ws ls rs neg
    by unfold_locales
  show ?thesis
    unfolding hungarian_csr_mw_run_def
    by (rule mw.mw_run_rule)
qed

lemma min_weight_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mw_run False n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true * \<up>(min_weight_matching G wfun (aug_csr.\<M> n M))>"
  using hungarian_csr_mw_run_rule[of _ _ _ _ _ False]
  by simp

lemma max_weight_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mw_run True n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true * \<up>(max_weight_matching G wfun (aug_csr.\<M> n M))>"
  using hungarian_csr_mw_run_rule[of _ _ _ _ _ True]
  by (simp add: neg_min_weight_matching)

lemma hungarian_csr_mwmc_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mwmc_run neg n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n M))>"
proof-
  interpret mwmc: hungarian_csr_mwmc h n fs ts ws ls rs neg
    by unfold_locales
  show ?thesis
    unfolding hungarian_csr_mwmc_run_def
    by (sep_auto heap: max_abs_loop_rule mwmc.mwmc_run_rule)
qed

lemma min_weight_max_card_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mwmc_run False n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_max_card_matching G wfun (aug_csr.\<M> n M))>"
  using hungarian_csr_mwmc_run_rule[of _ _ _ _ _ False]
  by simp

lemma max_weight_max_card_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mwmc_run True n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(max_weight_max_card_matching G wfun (aug_csr.\<M> n M))>"
  using hungarian_csr_mwmc_run_rule[of _ _ _ _ _ True]
  by (simp add: neg_min_weight_max_card_matching)

lemma neg_input: "hungarian_csr_input h n fs ts (map uminus ws) ls rs"
  by (intro hungarian_csr_input.intro real_embedding_axioms hungarian_csr_input_axioms.intro)
     (simp_all add: ts_length ws_length ls_distinct rs_distinct fs_ls ts_rs sides_disjoint
                    verts_below[unfolded Un_subset_iff] no_parallel)

lemma max_weight_perfect_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_max_perfect_run n theta cap Fa Ta Wa La Rv
   <\<lambda>(r, Mi, Pti). \<exists>\<^sub>AM \<pi>. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      array_fun_assn n M Mi * array_fun_val_assn h n \<pi> Pti * true *
      \<up>((r = result.success \<and> max_weight_perfect_matching G wfun (aug_csr.\<M> n M)) \<or>
        (r = result.failure \<and> (\<nexists>M'. perfect_matching G M')))>"
proof-
  interpret ng: hungarian_csr_input h n fs ts "map uminus ws" ls rs
    by (rule neg_input)
  have w: "ng.wfun e = - wfun e" if "e \<in> G" for e
  proof-
    obtain i where "i < length fs" "e = {fs ! i, ts ! i}"
      using \<open>e \<in> G\<close>
      by (auto simp: G_def)
    thus ?thesis
      using \<open>e \<in> G\<close> ng.wfun_eq[of "fs ! i" "ts ! i"] ng.ecost_edge[of i] wfun_eq[of "fs ! i" "ts ! i"]
            ecost_edge[of i] ws_length
      by simp
  qed
  have conv: "max_weight_perfect_matching G wfun X" if "min_weight_perfect_matching G ng.wfun X" for X
  proof-
    have "min_weight_perfect_matching G (\<lambda>e. - wfun e) X"
      by (rule min_weight_perfect_matching_cong[OF that w])
    thus ?thesis
      by (simp add: neg_min_weight_perfect_matching)
  qed
  have run: "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_max_perfect_run n theta cap Fa Ta Wa La Rv
   <\<lambda>(r, Mi, Pti). \<exists>\<^sub>AM \<pi>. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      array_fun_assn n M Mi * array_fun_val_assn h n \<pi> Pti * true *
      \<up>((r = result.success \<and> min_weight_perfect_matching G ng.wfun (aug_csr.\<M> n M)) \<or>
        (r = result.failure \<and> (\<nexists>M'. perfect_matching G M')))>"
    unfolding hungarian_csr_max_perfect_run_def
    by (sep_auto heap: neg_loop_rule ng.hungarian_csr_run_correct)
  show ?thesis
    apply (rule ht_cons_post_prec[OF run])
    apply (clarsimp split: prod.splits)
    apply (intro ent_ex_preI)
    apply (rule ent_ex_postI, rule ent_ex_postI)
    by (sep_auto dest: conv)
qed

end

definition hungarian_csr_mw_run_int :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow>
    nat array \<Rightarrow> nat array \<Rightarrow> nat array Heap" where
  "hungarian_csr_mw_run_int = hungarian_csr_mw_run"

definition hungarian_csr_mwmc_run_int :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow>
    nat array \<Rightarrow> nat array \<Rightarrow> nat array Heap" where
  "hungarian_csr_mwmc_run_int = hungarian_csr_mwmc_run"

definition hungarian_csr_max_perfect_run_int :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow>
    nat array \<Rightarrow> nat array \<Rightarrow> (result \<times> nat array \<times> int array) Heap" where
  "hungarian_csr_max_perfect_run_int = hungarian_csr_max_perfect_run"


export_code hungarian_csr_mw_run_int hungarian_csr_mwmc_run_int hungarian_csr_max_perfect_run_int
  checking SML_imp

export_code
  (*min weight perfect matching*)
  hungarian_csr_run_int
  (*max weight perfect matching*)
  hungarian_csr_max_perfect_run_int
  (*min/max weight matching*)
  hungarian_csr_mw_run_int
  (*min/max weight max cardinality matching*)
  hungarian_csr_mwmc_run_int
  (*conversions*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int
  in SML_imp module_name Hungarian_CSR_Variants file_prefix Hungarian_CSR_Variants_imperative
end
