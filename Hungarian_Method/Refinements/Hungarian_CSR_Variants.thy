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

subsection \<open>Renaming Vertices\<close>

text \<open>Perfect matchings of minimum weight are preserved under a renaming of the vertices that is
      injective on the vertices of the graph.\<close>


lemma Vs_image_image: "Vs ((`) f ` E) = f ` Vs E"
  by (auto simp: Vs_def)

lemma inj_on_image_edges:
  assumes "inj_on f (Vs E)" "M \<subseteq> E"
  shows "inj_on ((`) f) M"
proof (rule inj_onI)
  fix x y assume xy: "x \<in> M" "y \<in> M" "f ` x = f ` y"
  hence "x \<subseteq> Vs E" "y \<subseteq> Vs E" using assms(2) by (auto simp: Vs_def)
  thus "x = y" using xy(3) inj_on_image_eq_iff[OF assms(1)] by blast
qed

text \<open>From the branch \<open>weighted_blossom\<close>, theory \<open>Matching.thy\<close>.\<close>

lemma matching_image_rev:
  assumes "matching ((image f) ` M)" "inj_on f (Vs M)"
  shows   "matching M"
proof(rule matchingI, rule ccontr, goal_cases)
  case (1 e1 e2)
  hence f: "f ` e1 \<inter> f ` e2 \<noteq> {}" "f ` e1 \<in> (image f) ` M" "f ` e2 \<in> (image f) ` M"
        "f ` e1 \<noteq> f ` e2"
    using "1"(1,2,3) assms(2) Vs_def[of M] Union_upper[of e2 M]
      Union_upper[of e1 M] inj_on_image_eq_iff[of f "Vs M" e1 e2]
    by auto
  have "f ` e1 \<inter> f ` e2 = {}"
    by (rule matching_def[THEN iffD1, OF assms(1), rule_format, OF f(2,3,4)])
  thus ?case using f(1) by simp
qed

lemma perfect_matching_image:
  assumes "perfect_matching E M" "inj_on f (Vs E)"
  shows "perfect_matching ((`) f ` E) ((`) f ` M)"
proof -
  have "Vs M \<subseteq> Vs E" using assms(1) by (auto simp: perfect_matching_def Vs_def)
  hence "inj_on f (Vs M)" using assms(2) inj_on_subset by blast
  hence "matching ((`) f ` M)" using assms(1) matching_image by (auto simp: perfect_matching_def)
  thus ?thesis using assms(1) by (auto simp: perfect_matching_def Vs_image_image)
qed

lemma perfect_matching_preimage:
  assumes "perfect_matching ((`) f ` E) Mc" "inj_on f (Vs E)"
  shows "perfect_matching E {e \<in> E. f ` e \<in> Mc}" "(`) f ` {e \<in> E. f ` e \<in> Mc} = Mc"
proof -
  have Mc: "Mc \<subseteq> (`) f ` E" "matching Mc" "Vs Mc = f ` Vs E"
    using assms(1) by (auto simp: perfect_matching_def Vs_image_image)
  show img: "(`) f ` {e \<in> E. f ` e \<in> Mc} = Mc" using Mc(1) by blast
  have sub: "e \<subseteq> Vs E" if "e \<in> E" for e using that by (auto simp: Vs_def)
  have "Vs {e \<in> E. f ` e \<in> Mc} \<subseteq> Vs E" by (auto simp: Vs_def)
  hence inj: "inj_on f (Vs {e \<in> E. f ` e \<in> Mc})" using assms(2) inj_on_subset by blast
  have "matching {e \<in> E. f ` e \<in> Mc}"
    by (rule matching_image_rev[OF _ inj]) (simp add: img Mc(2))
  moreover have "Vs E \<subseteq> Vs {e \<in> E. f ` e \<in> Mc}"
  proof
    fix v assume v: "v \<in> Vs E"
    hence "f v \<in> Vs Mc" using Mc(3) by simp
    then obtain ec where ec: "ec \<in> Mc" "f v \<in> ec" by (auto simp: Vs_def)
    from Mc(1) ec(1) obtain e where e: "e \<in> E" "ec = f ` e" by auto
    hence "v \<in> e" using ec(2) v sub assms(2) by (auto simp: inj_on_def)
    thus "v \<in> Vs {e \<in> E. f ` e \<in> Mc}" using e ec(1) by (auto simp: Vs_def)
  qed
  ultimately show "perfect_matching E {e \<in> E. f ` e \<in> Mc}"
    by (auto simp: perfect_matching_def Vs_def)
qed

lemma sum_image_edges:
  "\<lbrakk>inj_on f (Vs E); M \<subseteq> E\<rbrakk> \<Longrightarrow> sum w ((`) f ` M) = sum (\<lambda>e. w (f ` e)) M"
  using sum.reindex[OF inj_on_image_edges, of f E M w] by (simp add: comp_def)

lemma min_weight_perfect_matching_preimage:
  assumes "min_weight_perfect_matching ((`) f ` E) w Mc" "inj_on f (Vs E)"
  shows "min_weight_perfect_matching E (\<lambda>e. w (f ` e)) {e \<in> E. f ` e \<in> Mc}"
proof (rule min_weight_perfect_matchingI)
  have pm: "perfect_matching ((`) f ` E) Mc" by (rule min_weight_perfect_matchingD(1)[OF assms(1)])
  show "perfect_matching E {e \<in> E. f ` e \<in> Mc}" by (rule perfect_matching_preimage(1)[OF pm assms(2)])
  fix M2 assume M2: "perfect_matching E M2"
  have "sum (\<lambda>e. w (f ` e)) {e \<in> E. f ` e \<in> Mc} = sum w Mc"
    using sum_image_edges[OF assms(2), of "{e \<in> E. f ` e \<in> Mc}" w]
          perfect_matching_preimage(2)[OF pm assms(2)] by simp
  also have "\<dots> \<le> sum w ((`) f ` M2)"
    by (rule min_weight_perfect_matchingD(2)[OF assms(1) perfect_matching_image[OF M2 assms(2)]])
  also have "\<dots> = sum (\<lambda>e. w (f ` e)) M2"
    using M2 by (intro sum_image_edges[OF assms(2)]) (simp add: perfect_matching_def)
  finally show "sum (\<lambda>e. w (f ` e)) {e \<in> E. f ` e \<in> Mc} \<le> sum (\<lambda>e. w (f ` e)) M2" .
qed

lemma min_weight_perfect_matching_cong:
  assumes "min_weight_perfect_matching E w M" "\<And>e. e \<in> E \<Longrightarrow> w e = w2 e"
  shows "min_weight_perfect_matching E w2 M"
proof (rule min_weight_perfect_matchingI)
  have eq: "sum w M2 = sum w2 M2" if "perfect_matching E M2" for M2
    using that assms(2) by (intro sum.cong) (auto simp: perfect_matching_def)
  show pm: "perfect_matching E M" by (rule min_weight_perfect_matchingD(1)[OF assms(1)])
  fix M2 assume M2: "perfect_matching E M2"
  show "sum w2 M \<le> sum w2 M2"
    using min_weight_perfect_matchingD(2)[OF assms(1) M2] eq[OF pm] eq[OF M2] by simp
qed

subsection \<open>The Completed Graph\<close>


lemma mult_add_less: assumes "a < k" "b < k" shows "a * k + b < k * (k::nat)"
proof -
  have "a * k + b < Suc a * k" using assms(2) by simp
  also have "\<dots> \<le> k * k" using assms(1) by (intro mult_le_mono1) simp
  finally show ?thesis .
qed

lemma mult_add_div_mod: "b < k \<Longrightarrow> (a * k + b) div k = a" "b < k \<Longrightarrow> (a * k + b) mod (k::nat) = b"
  by simp_all

lemma mult_add_eq:
  assumes "b < k" "b' < k" "a * k + b = a' * k + (b'::nat)"
  shows "a = a'" "b = b'"
proof -
  have "(a * k + b) div k = (a' * k + b') div k" "(a * k + b) mod k = (a' * k + b') mod k"
    by (simp_all only: assms(3))
  thus "a = a'" "b = b'" using assms(1,2) by simp_all
qed
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
  using ls_distinct rs_distinct L_less R_less by (fastforce simp: ls'_def rs'_def)+

lemma sides_disjoint': "set ls' \<inter> set rs' = {}"
  using sides_disjoint by (auto simp: set_ls' set_rs' k_def dest: L_less R_less)

lemma below_n': "set ls' \<union> set rs' \<subseteq> {..<n'}"
  by (auto simp: set_ls' set_rs' n'_def dest: L_less R_less)
lemma nth_ls'_less: assumes "a < k" shows "ls' ! a < n'"
proof -
  have "ls' ! a \<in> set ls'" using assms length_ls' by simp
  thus ?thesis using below_n' by auto
qed

lemma nth_rs'_less: assumes "a < k" shows "rs' ! a < n'"
proof -
  have "rs' ! a \<in> set rs'" using assms length_rs' by simp
  thus ?thesis using below_n' by auto
qed

lemma img_rs': "(!) rs' ` set [0..<k] = set rs'"
  by (metis length_rs' map_nth set_map)

lemma pos_ls': "a < k \<Longrightarrow> pos (ls' ! a) = a"
proof -
  assume a: "a < k"
  have "ls' ! a \<in> set ls'" using a length_ls' by simp
  hence "ls' ! a \<notin> (!) rs' ` set [0..<k]" using sides_disjoint' img_rs' by blast
  moreover have "foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k] ! (ls' ! a) = a"
    by (rule foldl_upd_nth_hit[where f = id, simplified])
       (use a distinct_ls' length_ls' nth_ls'_less in \<open>auto intro!: inj_on_nth\<close>)
  ultimately show ?thesis by (simp add: pos_def posl_def foldl_upd_nth_miss)
qed

lemma pos_rs': "b < k \<Longrightarrow> pos (rs' ! b) = b"
  unfolding pos_def posl_def
  by (rule foldl_upd_nth_hit[where f = id, simplified])
     (use distinct_rs' length_rs' nth_rs'_less in \<open>auto intro!: inj_on_nth\<close>)

lemma pos_less: "v \<in> set ls' \<union> set rs' \<Longrightarrow> pos v < k"
  using pos_ls' pos_rs' length_ls' length_rs' by (auto simp: in_set_conv_nth)

lemma ls'_nth_pos: "v \<in> set ls' \<Longrightarrow> ls' ! pos v = v"
  using pos_ls' length_ls' by (auto simp: in_set_conv_nth)

lemma rs'_nth_pos: "v \<in> set rs' \<Longrightarrow> rs' ! pos v = v"
  using pos_rs' length_rs' by (auto simp: in_set_conv_nth)

lemma length_fs' [simp]: "length fs' = k * k" and length_ts' [simp]: "length ts' = k * k"
  and length_ws' [simp]: "length ws' = k * k"
  by (simp_all add: fs'_def ts'_def ws'_def)

lemma fs'_nth: "j < k * k \<Longrightarrow> fs' ! j = ls' ! (j div k)"
  and ts'_nth: "j < k * k \<Longrightarrow> ts' ! j = rs' ! (j mod k)"
  by (simp_all add: fs'_def ts'_def)

lemma fs_in_ls': "i < length fs \<Longrightarrow> fs ! i \<in> set ls'"
  and ts_in_rs': "i < length fs \<Longrightarrow> ts ! i \<in> set rs'"
  using fs_L ts_R by (simp_all add: set_ls' set_rs')

lemma eix_less: "i < length fs \<Longrightarrow> eix i < k * k"
  by (simp add: eix_def mult_add_less pos_less fs_in_ls' ts_in_rs')

lemma eix_inj: "inj_on eix {..<length fs}"
proof (rule inj_onI)
  fix i j assume ij: "i \<in> {..<length fs}" "j \<in> {..<length fs}" "eix i = eix j"
  have p: "pos (ts ! i) < k" "pos (ts ! j) < k" using ij(1,2) pos_less ts_in_rs' by auto
  have "pos (fs ! i) = pos (fs ! j)"
    using mult_add_div_mod(1)[OF p(1), of "pos (fs ! i)"] mult_add_div_mod(1)[OF p(2), of "pos (fs ! j)"]
          ij(3) by (simp add: eix_def)
  moreover have "pos (ts ! i) = pos (ts ! j)"
    using arg_cong[OF ij(3)[unfolded eix_def], of "\<lambda>x. x mod k"] p by simp
  ultimately have "fs ! i = fs ! j" "ts ! i = ts ! j"
    using ls'_nth_pos rs'_nth_pos fs_in_ls' ts_in_rs' ij(1,2) by (metis lessThan_iff)+
  thus "i = j" using edge_unique ij(1,2) by simp
qed

lemma ws'_edge: "i < length fs \<Longrightarrow> ws' ! eix i = cf (ws ! i)"
  unfolding ws'_def
  by (rule foldl_upd_nth_hit) (use eix_inj eix_less in \<open>auto simp: atLeast0LessThan\<close>)

lemma ws'_other: "j \<notin> eix ` {..<length fs} \<Longrightarrow> j < k * k \<Longrightarrow> ws' ! j = dflt"
  unfolding ws'_def by (subst foldl_upd_nth_miss) (auto simp: atLeast0LessThan)

lemma set_fs': "set fs' = set ls'"
proof
  show "set fs' \<subseteq> set ls'"
    using length_ls' by (auto simp: fs'_def less_mult_imp_div_less)
  show "set ls' \<subseteq> set fs'"
  proof
    fix v assume "v \<in> set ls'"
    then obtain a where a: "a < k" "v = ls' ! a" using length_ls' by (auto simp: in_set_conv_nth)
    hence "a * k < k * k" "fs' ! (a * k) = v" using mult_add_less[OF a(1), of 0] by (simp_all add: fs'_nth)
    thus "v \<in> set fs'" by (metis length_fs' nth_mem)
  qed
qed

lemma set_ts': "set ts' = set rs'"
proof
  show "set ts' \<subseteq> set rs'"
  proof
    fix v assume "v \<in> set ts'"
    then obtain j where j: "j < k * k" "v = ts' ! j" by (auto simp: in_set_conv_nth)
    hence "0 < k" by (cases k) auto
    hence "j mod k < k" by simp
    thus "v \<in> set rs'" using j length_rs' by (simp add: ts'_nth)
  qed
  show "set rs' \<subseteq> set ts'"
  proof
    fix v assume "v \<in> set rs'"
    then obtain b where b: "b < k" "v = rs' ! b" using length_rs' by (auto simp: in_set_conv_nth)
    hence "b < k * k" "ts' ! b = v" using mult_add_less[OF b(1) b(1)] by (simp_all add: ts'_nth)
    thus "v \<in> set ts'" by (metis length_ts' nth_mem)
  qed
qed

lemma no_parallel': "distinct (zip fs' ts')"
proof (rule distinct_conv_nth[THEN iffD2], intro allI impI)
  fix i j assume ij: "i < length (zip fs' ts')" "j < length (zip fs' ts')" "i \<noteq> j"
  hence l: "i < k * k" "j < k * k" by simp_all
  hence k0: "0 < k" by (cases k) auto
  have d: "i div k < k" "j div k < k" "i mod k < k" "j mod k < k"
    using l k0 by (simp_all add: less_mult_imp_div_less)
  show "zip fs' ts' ! i \<noteq> zip fs' ts' ! j"
  proof
    assume "zip fs' ts' ! i = zip fs' ts' ! j"
    hence "ls' ! (i div k) = ls' ! (j div k)" "rs' ! (i mod k) = rs' ! (j mod k)"
      using l by (simp_all add: fs'_nth ts'_nth)
    hence "i div k = j div k" "i mod k = j mod k"
      using d distinct_ls' distinct_rs' length_ls' length_rs' by (simp_all add: nth_eq_iff_index_eq)
    hence "i = j" by (metis div_mult_mod_eq)
    thus False using ij(3) by simp
  qed
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

lemma image_plus_lessThan: "(\<lambda>i. n + i) ` {..<m} = {n..<n + (m::nat)}"
proof
  show "(\<lambda>i. n + i) ` {..<m} \<subseteq> {n..<n + m}" by auto
  show "{n..<n + m} \<subseteq> (\<lambda>i. n + i) ` {..<m}"
  proof
    fix x assume "x \<in> {n..<n + m}"
    thus "x \<in> (\<lambda>i. n + i) ` {..<m}" by (intro rev_image_eqI[of "x - n"]) auto
  qed
qed

lemma new_vertex_set: "{new_vertex i | i. i < m} = new_vertex ` {..<m}"
  by auto

context hungarian_csr_completion
begin

definition "ren x = (case x of old_vertex v \<Rightarrow> v | new_vertex i \<Rightarrow> n + i)"

lemma ren_simps [simp]: "ren (old_vertex v) = v" "ren (new_vertex i) = n + i"
  by (simp_all add: ren_def)

lemma pad_L: "card R - card L = k - length ls" and pad_R: "card L - card R = k - length rs"
  using ls_distinct rs_distinct by (simp_all add: distinct_card k_def max_def)

lemma ren_L': "ren ` bp_perfected_L L R = set ls'"
  by (simp add: bp_perfected_L_def new_vertex_set image_Un image_image image_plus_lessThan
                set_ls' pad_L)

lemma ren_R': "ren ` bp_perfected_R L R = set rs'"
  by (simp add: bp_perfected_R_def new_vertex_set image_Un image_image image_plus_lessThan
                set_rs' pad_R)

lemma cp_G: "cp.G = {{u, v} | u v. u \<in> set ls' \<and> v \<in> set rs'}"
proof
  show "cp.G \<subseteq> {{u, v} | u v. u \<in> set ls' \<and> v \<in> set rs'}"
  proof
    fix e assume "e \<in> cp.G"
    then obtain j where j: "j < k * k" "e = {fs' ! j, ts' ! j}" by (auto simp: cp.G_def)
    hence "fs' ! j \<in> set ls'" "ts' ! j \<in> set rs'"
      using set_fs' set_ts' by (metis length_fs' length_ts' nth_mem)+
    thus "e \<in> {{u, v} | u v. u \<in> set ls' \<and> v \<in> set rs'}" using j(2) by blast
  qed
  show "{{u, v} | u v. u \<in> set ls' \<and> v \<in> set rs'} \<subseteq> cp.G"
  proof
    fix e assume "e \<in> {{u, v} | u v. u \<in> set ls' \<and> v \<in> set rs'}"
    then obtain u v where uv: "u \<in> set ls'" "v \<in> set rs'" "e = {u, v}" by blast
    have p: "pos u < k" "pos v < k" using uv(1,2) pos_less by simp_all
    have j: "pos u * k + pos v < k * k" by (rule mult_add_less[OF p])
    have "fs' ! (pos u * k + pos v) = u" "ts' ! (pos u * k + pos v) = v"
      using j p(2) uv(1,2) by (simp_all add: fs'_nth ts'_nth ls'_nth_pos rs'_nth_pos)
    thus "e \<in> cp.G" using j uv(3) unfolding cp.G_def by (metis (mono_tags, lifting) length_fs' mem_Collect_eq)
  qed
qed

lemma ren_G': "(`) ren ` bp_perfected_G L R = cp.G"
proof
  show "(`) ren ` bp_perfected_G L R \<subseteq> cp.G"
  proof
    fix e assume "e \<in> (`) ren ` bp_perfected_G L R"
    then obtain x y where "x \<in> bp_perfected_L L R" "y \<in> bp_perfected_R L R" "e = {ren x, ren y}"
      by (auto simp: bp_perfected_G_def')
    thus "e \<in> cp.G" using ren_L' ren_R' unfolding cp_G by blast
  qed
  show "cp.G \<subseteq> (`) ren ` bp_perfected_G L R"
  proof
    fix e assume "e \<in> cp.G"
    then obtain u v where uv: "u \<in> set ls'" "v \<in> set rs'" "e = {u, v}" unfolding cp_G by blast
    then obtain x y where "x \<in> bp_perfected_L L R" "y \<in> bp_perfected_R L R" "u = ren x" "v = ren y"
      using ren_L' ren_R' by (metis imageE)
    hence "{x, y} \<in> bp_perfected_G L R" "e = ren ` {x, y}" using uv(3) by (auto simp: bp_perfected_G_def')
    thus "e \<in> (`) ren ` bp_perfected_G L R" by blast
  qed
qed

lemma ren_inj: "inj_on ren (Vs (bp_perfected_G L R))"
proof -
  have s: "Vs (bp_perfected_G L R) \<subseteq> {x. \<forall>v. x = old_vertex v \<longrightarrow> v < n}"
  proof
    fix x assume "x \<in> Vs (bp_perfected_G L R)"
    hence "x \<in> bp_perfected_L L R \<union> bp_perfected_R L R" by (rule subsetD[OF bp_perfected_Vs_subs])
    thus "x \<in> {x. \<forall>v. x = old_vertex v \<longrightarrow> v < n}"
      by (auto simp: bp_perfected_L_def bp_perfected_R_def dest: L_less R_less)
  qed
  have i: "inj_on ren {x. \<forall>v. x = old_vertex v \<longrightarrow> v < n}"
    by (rule inj_onI) (auto simp: ren_def split: bp_vertex_wrapper.splits)
  show ?thesis by (rule inj_on_subset[OF i s])
qed

lemma G_below: assumes "e \<in> G" "x \<in> e" shows "x < n"
proof -
  have "x \<in> Vs G" using assms by (auto simp: Vs_def)
  thus ?thesis using Vs_G L_less R_less by auto
qed

lemma old_ren: "\<nexists>i. new_vertex i \<in> e \<Longrightarrow> bp_vertex_wrapper.the_vertex ` e = ren ` e"
proof (rule image_cong[OF refl])
  fix x assume "\<nexists>i. new_vertex i \<in> e" "x \<in> e"
  thus "bp_vertex_wrapper.the_vertex x = ren x" by (cases x) auto
qed

lemma new_ren: "new_vertex i \<in> e \<Longrightarrow> ren ` e \<notin> G"
  using G_below[of "ren ` e" "n + i"] by force

lemma project_preimage:
  assumes "Mc \<subseteq> cp.G"
  shows "project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> G = Mc \<inter> G"
proof
  show "project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> G \<subseteq> Mc \<inter> G"
  proof
    fix ec assume "ec \<in> project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> G"
    then obtain e where "ren ` e \<in> Mc" "\<nexists>i. new_vertex i \<in> e"
        "ec = bp_vertex_wrapper.the_vertex ` e" "ec \<in> G"
      by (auto simp: project_to_old_def)
    thus "ec \<in> Mc \<inter> G" using old_ren by simp
  qed
  show "Mc \<inter> G \<subseteq> project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> G"
  proof
    fix ec assume ec: "ec \<in> Mc \<inter> G"
    hence "ec \<in> (`) ren ` bp_perfected_G L R" using assms ren_G' by auto
    then obtain e where e: "ec = ren ` e" "e \<in> bp_perfected_G L R" by (rule imageE)
    have nn: "\<nexists>i. new_vertex i \<in> e"
    proof
      assume "\<exists>i. new_vertex i \<in> e"
      then obtain i where "new_vertex i \<in> e" ..
      hence "ren ` e \<notin> G" by (rule new_ren)
      thus False using e(1) ec by simp
    qed
    hence the: "ec = bp_vertex_wrapper.the_vertex ` e" using old_ren e(1) by simp
    have "ec \<in> project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc}"
      unfolding project_to_old_def
      by (rule CollectI, rule exI[of _ e]) (use e ec nn the in simp)
    thus "ec \<in> project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> G" using ec by simp
  qed
qed

lemma G_iff_edge:
  assumes "u \<in> set ls'" "v \<in> set rs'"
  shows "{u, v} \<in> G \<longleftrightarrow> (\<exists>i<length fs. fs ! i = u \<and> ts ! i = v)"
proof
  assume "{u, v} \<in> G"
  thus "\<exists>i<length fs. fs ! i = u \<and> ts ! i = v"
  proof (cases rule: G_edgeE)
    case (2 i)
    hence "u \<in> R" using ts_R by simp
    hence "u < n" "u \<notin> L" using R_less sides_disjoint by auto
    thus ?thesis using assms(1) by (simp add: set_ls')
  qed auto
qed (auto simp: G_def)

lemma cp_ecost:
  assumes "u \<in> set ls'" "v \<in> set rs'"
  shows "cp.ecost u v = (if {u, v} \<in> G then h (cf (ws ! eidx u v)) else h dflt)"
proof -
  have p: "pos u < k" "pos v < k" using assms pos_less by simp_all
  have j: "pos u * k + pos v < k * k" by (rule mult_add_less[OF p])
  have "fs' ! (pos u * k + pos v) = u" "ts' ! (pos u * k + pos v) = v"
    using j p(2) assms by (simp_all add: fs'_nth ts'_nth ls'_nth_pos rs'_nth_pos)
  hence ec: "cp.ecost u v = h (ws' ! (pos u * k + pos v))"
    using cp.ecost_edge[of "pos u * k + pos v"] j by simp
  show ?thesis
  proof (cases "{u, v} \<in> G")
    case True
    then obtain i where i: "i < length fs" "fs ! i = u" "ts ! i = v"
      using G_iff_edge[OF assms] by auto
    hence "eix i = pos u * k + pos v" "eidx u v = i" using eidx_eq[OF i(1)] by (simp_all add: eix_def)
    thus ?thesis using True ec ws'_edge[OF i(1)] by simp
  next
    case False
    have "pos u * k + pos v \<notin> eix ` {..<length fs}"
    proof (rule notI, erule imageE)
      fix i assume j: "pos u * k + pos v = eix i" "i \<in> {..<length fs}"
      have i: "i < length fs" using j(2) by simp
      have pt: "pos (ts ! i) < k" using pos_less ts_in_rs'[OF i] by simp
      have "pos (fs ! i) * k + pos (ts ! i) = pos u * k + pos v" using j(1) by (simp add: eix_def)
      note eq = mult_add_eq[OF pt p(2) this]
      have "fs ! i = ls' ! pos (fs ! i)" using ls'_nth_pos[OF fs_in_ls'[OF i]] by simp
      also have "\<dots> = u" using eq(1) ls'_nth_pos[OF assms(1)] by simp
      finally have fi: "fs ! i = u" .
      have "ts ! i = rs' ! pos (ts ! i)" using rs'_nth_pos[OF ts_in_rs'[OF i]] by simp
      also have "\<dots> = v" using eq(2) rs'_nth_pos[OF assms(2)] by simp
      finally have ti: "ts ! i = v" .
      show False using False G_iff_edge[OF assms] i fi ti by auto
    qed
    thus ?thesis using False ec ws'_other j by simp
  qed
qed

text \<open>The weights of the completed graph, for a function @{term g} on the reals that @{term cf}
      represents.\<close>

lemma cp_wfun:
  assumes "\<And>a. h (cf a) = g (h a)" "e \<in> cp.G"
  shows "cp.wfun e = (if e \<in> G then g (wfun e) else h dflt)"
proof -
  obtain u v where uv: "u \<in> set ls'" "v \<in> set rs'" "e = {u, v}" using assms(2) unfolding cp_G by blast
  have "cp.wfun e = cp.ecost u v" using cp.wfun_eq assms(2) uv(3) by simp
  moreover have "wfun e = h (ws ! eidx u v)" if "e \<in> G"
  proof -
    have "u < n" using G_below that uv(3) by simp
    hence "u \<in> L" using uv(1) by (simp add: set_ls')
    thus ?thesis using wfun_eq that uv(3) by (simp add: ecost_def)
  qed
  ultimately show ?thesis using cp_ecost[OF uv(1,2)] assms(1) uv(3) by auto
qed

text \<open>A minimum weight perfect matching of the completed graph is one of the renamed graph
      @{const bp_perfected_G}.\<close>

lemma completion_transfer:
  assumes "min_weight_perfect_matching cp.G cp.wfun Mc"
  shows "min_weight_perfect_matching (bp_perfected_G L R) (\<lambda>e. cp.wfun (ren ` e))
           {e \<in> bp_perfected_G L R. ren ` e \<in> Mc}"
  using min_weight_perfect_matching_preimage[OF assms[folded ren_G'] ren_inj] .

end

context hungarian_csr_completion
begin

lemma wfun_ren:
  assumes "\<And>a. h (cf a) = g (h a)" "e \<in> bp_perfected_G L R"
  shows "cp.wfun (ren ` e) =
           (if (\<exists>i. new_vertex i \<in> e) \<or> bp_vertex_wrapper.the_vertex ` e \<notin> G then h dflt
            else g (wfun (bp_vertex_wrapper.the_vertex ` e)))"
proof -
  have "ren ` e \<in> (`) ren ` bp_perfected_G L R" by (rule imageI[OF assms(2)])
  hence w: "cp.wfun (ren ` e) = (if ren ` e \<in> G then g (wfun (ren ` e)) else h dflt)"
    unfolding ren_G' by (rule cp_wfun[OF assms(1)])
  show ?thesis
  proof (cases "\<exists>i. new_vertex i \<in> e")
    case True
    then obtain i where "new_vertex i \<in> e" ..
    hence "ren ` e \<notin> G" by (rule new_ren)
    thus ?thesis using w True by simp
  next
    case False
    thus ?thesis using w old_ren[OF False] by simp
  qed
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
  by (rule min_weight_perfect_matching_cong[OF completion_transfer[OF assms(2)]])
     (simp add: wfun_ren[OF assms(1)] assms(3))

lemma finite_G: "finite G"
proof -
  have "G = (\<lambda>i. {fs ! i, ts ! i}) ` {..<length fs}" by (auto simp: G_def)
  thus ?thesis by simp
qed

text \<open>The completed graph has a perfect matching, so the Hungarian method succeeds on it.\<close>

lemma cp_perfect_exists: "\<exists>M. perfect_matching cp.G M"
proof -
  have fin: "finite (bp_perfected_G L R)"
    by (rule finite_G_finite_completion[OF finite_G]) simp_all
  obtain M where M: "perfect_matching (bp_perfected_G L R) M"
    using perfect_matching_in_balanced_complete_bipartite[OF
            balanced_complete_bipartite_perfected(1)[OF bipartite_G finite_set finite_set] fin]
    by blast
  have "perfect_matching cp.G ((`) ren ` M)"
    using perfect_matching_image[OF M ren_inj] by (simp only: ren_G')
  thus ?thesis ..
qed

lemma perfect_sub: "perfect_matching cp.G Mc \<Longrightarrow> Mc \<subseteq> cp.G"
  by (simp add: perfect_matching_def)

end

subsection \<open>Minimum and Maximum Weight Matchings\<close>

text \<open>The weights are negated for the maximisation.\<close>

definition "sgn_w b w = (if b then - w else w)"

lemma sgn_w_simps [simp]: "sgn_w False w = w" "sgn_w True w = - w"
  by (simp_all add: sgn_w_def)

text \<open>The weight of an edge of the original graph is @{term "min 0 w"} for its (possibly negated)
      weight @{term w}, the weight of every other edge is @{term 0}.\<close>

locale hungarian_csr_mw =
  hungarian_csr_completion \<theta> cap h n fs ts ws ls rs 0 "\<lambda>w. min 0 (sgn_w neg w)"
  for h :: "'n::{linordered_idom, heap} \<Rightarrow> real" and n fs ts ws ls rs and neg :: bool
  and \<theta> cap :: nat
begin

theorem mw_correct:
  assumes "min_weight_perfect_matching cp.G cp.wfun Mc"
  shows "min_weight_matching G (\<lambda>e. sgn_w neg (wfun e)) (Mc \<inter> G \<inter> {e. sgn_w neg (wfun e) < 0})"
proof -
  have "min_weight_perfect_matching (bp_perfected_G L R)
          (bp_min_costs_to_min_perfect_costs G (\<lambda>e. sgn_w neg (wfun e)))
          {e \<in> bp_perfected_G L R. ren ` e \<in> Mc}"
    by (rule completion_result[where g = "\<lambda>x. min 0 (sgn_w neg x)", OF _ assms])
       (cases neg; simp add: bp_min_costs_to_min_perfect_costs_def)+
  hence "min_weight_matching G (\<lambda>e. sgn_w neg (wfun e))
           (project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter>
            {e |e. sgn_w neg (wfun e) < 0} \<inter> G)"
    by (rule min_weight_perfect_implies_min_weight[OF bipartite_G finite_set finite_set])
  moreover have "project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter>
                   {e |e. sgn_w neg (wfun e) < 0} \<inter> G = Mc \<inter> G \<inter> {e. sgn_w neg (wfun e) < 0}"
  proof -
    have "project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> G = Mc \<inter> G"
      by (rule project_preimage[OF perfect_sub[OF min_weight_perfect_matchingD(1)[OF assms]]])
    thus ?thesis by auto
  qed
  ultimately show ?thesis by simp
qed

end

subsection \<open>Minimum and Maximum Weight Maximum Cardinality Matchings\<close>

lemma Max_insert_fold: "Max (insert a (set xs)) = fold max xs (a::'a::linorder)"
proof (induction xs arbitrary: a)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "Max (insert a (set (x # xs))) = Max (insert (max x a) (set xs))"
    by (cases "xs = []") (simp_all add: max.commute max.left_commute)
  thus ?case using Cons.IH by simp
qed

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
  using h_add[of 1 1] by simp

lemma h_fold_max: "h (fold max (map abs xs) a) = fold max (map (\<lambda>x. \<bar>h x\<bar>) xs) (h a)"
  by (induction xs arbitrary: a) (simp_all add: h_abs)

lemma wfun_edge: "i < length fs \<Longrightarrow> wfun {fs ! i, ts ! i} = h (ws ! i)"
  using wfun_eq[of "fs ! i" "ts ! i"] ecost_edge[of i] by (auto simp: G_def)

lemma wfun_set: "{\<bar>wfun e\<bar> | e. e \<in> G} = (\<lambda>x. \<bar>h x\<bar>) ` set ws"
proof
  show "{\<bar>wfun e\<bar> | e. e \<in> G} \<subseteq> (\<lambda>x. \<bar>h x\<bar>) ` set ws"
  proof
    fix x assume "x \<in> {\<bar>wfun e\<bar> | e. e \<in> G}"
    then obtain i where i: "i < length fs" "x = \<bar>wfun {fs ! i, ts ! i}\<bar>" by (auto simp: G_def)
    hence "x = \<bar>h (ws ! i)\<bar>" "ws ! i \<in> set ws" using wfun_edge ws_length by simp_all
    thus "x \<in> (\<lambda>x. \<bar>h x\<bar>) ` set ws" by simp
  qed
  show "(\<lambda>x. \<bar>h x\<bar>) ` set ws \<subseteq> {\<bar>wfun e\<bar> | e. e \<in> G}"
  proof
    fix x assume "x \<in> (\<lambda>x. \<bar>h x\<bar>) ` set ws"
    then obtain i where i: "i < length fs" "x = \<bar>h (ws ! i)\<bar>"
      using ws_length by (auto simp: in_set_conv_nth)
    hence "x = \<bar>wfun {fs ! i, ts ! i}\<bar>" "{fs ! i, ts ! i} \<in> G"
      using wfun_edge by (auto simp: G_def)
    thus "x \<in> {\<bar>wfun e\<bar> | e. e \<in> G}" by blast
  qed
qed

lemma card_Vs_G: "card (Vs G) = length ls + length rs"
  using Vs_G sides_disjoint ls_distinct rs_distinct by (simp add: card_Un_disjoint distinct_card)

lemma h_dflt: "h (2 + of_nat (length ls + length rs) * max_abs_weight ws) =
                 2 * penalty G (\<lambda>e. sgn_w neg (wfun e))"
proof -
  have "h (max_abs_weight ws) = fold max (map (\<lambda>x. \<bar>h x\<bar>) ws) 0"
    by (simp add: max_abs_weight_def h_fold_max)
  also have "\<dots> = Max (insert 0 (set (map (\<lambda>x. \<bar>h x\<bar>) ws)))" by (rule Max_insert_fold[symmetric])
  also have "\<dots> = Max (insert 0 {\<bar>wfun e\<bar> | e. e \<in> G})" by (simp only: set_map wfun_set)
  finally have m: "h (max_abs_weight ws) = Max (insert 0 {\<bar>wfun e\<bar> | e. e \<in> G})" .
  have "penalty G (\<lambda>e. sgn_w neg (wfun e)) = penalty G wfun"
    by (cases neg) (simp_all add: penalty_def)
  thus ?thesis using m by (simp add: penalty_def card_Vs_G h_add h_mult h_of_nat h_two field_simps)
qed

theorem mwmc_correct:
  assumes "min_weight_perfect_matching cp.G cp.wfun Mc"
  shows "min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e)) (Mc \<inter> G)"
proof -
  have "min_weight_perfect_matching (bp_perfected_G L R)
          (bp_min_max_card_costs_to_min_perfect_costs G (\<lambda>e. sgn_w neg (wfun e)))
          {e \<in> bp_perfected_G L R. ren ` e \<in> Mc}"
  proof (rule completion_result[where g = "sgn_w neg", OF _ assms])
    show "h (sgn_w neg a) = sgn_w neg (h a)" for a by (simp add: sgn_w_def)
    show "bp_min_max_card_costs_to_min_perfect_costs G (\<lambda>e. sgn_w neg (wfun e)) e =
            (if (\<exists>i. new_vertex i \<in> e) \<or> bp_vertex_wrapper.the_vertex ` e \<notin> G
             then h (2 + of_nat (length ls + length rs) * max_abs_weight ws)
             else sgn_w neg (wfun (bp_vertex_wrapper.the_vertex ` e)))" for e
      by (simp only: bp_min_max_card_costs_to_min_perfect_costs_def h_dflt) simp
  qed
  hence "min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e))
           (project_to_old {e \<in> bp_perfected_G L R. ren ` e \<in> Mc} \<inter> G)"
    by (rule min_weight_perfect_gives_min_weight_max_card_matching[OF bipartite_G finite_set finite_set])
  thus ?thesis
    using project_preimage[OF perfect_sub[OF min_weight_perfect_matchingD(1)[OF assms]]] by simp
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

lemma L_ls': "L \<subseteq> set ls'"
  by (simp add: set_ls')

lemma cp_G_right: "\<lbrakk>{u, v} \<in> cp.G; u \<in> set ls'\<rbrakk> \<Longrightarrow> v \<in> set rs'"
  using sides_disjoint' unfolding cp_G by (auto simp: doubleton_eq_iff)

lemma G_sides: "\<lbrakk>{u, v} \<in> G; u \<notin> L\<rbrakk> \<Longrightarrow> v \<in> L"
  by (erule G_edgeE) (auto dest: fs_L)

lemma extract_inv:
  assumes sym: "\<And>u v. Mb u = Some v \<Longrightarrow> Mb v = Some u"
    and edges: "\<And>u v. Mb u = Some v \<Longrightarrow> {u, v} \<in> cp.G"
    and kp: "\<And>u v. \<lbrakk>u \<in> L; v \<in> set rs'\<rbrakk> \<Longrightarrow> kp (ws' ! (pos u * k + pos v)) \<longleftrightarrow> Q {u, v}"
    and xs: "distinct xs" "set xs \<subseteq> L"
  shows "foldl (extract_step kp Mb) Map.empty xs =
           (\<lambda>x. if x \<in> set xs \<or> (\<exists>u\<in>set xs. Mb u = Some x)
                then (case Mb x of None \<Rightarrow> None | Some y \<Rightarrow> if Q {x, y} then Some y else None)
                else None)"
  using xs
proof (induction xs rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc u xs)
  have u: "u \<in> L" "u \<notin> set xs" "set xs \<subseteq> L" using snoc.prems by auto
  have IH: "foldl (extract_step kp Mb) Map.empty xs =
             (\<lambda>x. if x \<in> set xs \<or> (\<exists>u\<in>set xs. Mb u = Some x)
                  then (case Mb x of None \<Rightarrow> None | Some y \<Rightarrow> if Q {x, y} then Some y else None)
                  else None)"
    using snoc by simp
  have right: "w \<in> set rs'" if "Mb u' = Some w" "u' \<in> L" for u' w
    using cp_G_right[OF edges[OF that(1)]] that(2) L_ls' by blast
  have nu: "\<not> (\<exists>u'\<in>set xs. Mb u' = Some u)"
  proof
    assume "\<exists>u'\<in>set xs. Mb u' = Some u"
    then obtain u' where u': "u' \<in> set xs" "Mb u' = Some u" ..
    hence "u' \<in> set rs'" using right[OF sym[OF u'(2)] u(1)] by simp
    moreover have "u' \<in> set ls'" using u' u(3) L_ls' by auto
    ultimately show False using sides_disjoint' by auto
  qed
  show ?case
  proof (cases "Mb u")
    case None
    show ?thesis
    proof (rule ext)
      fix x show "foldl (extract_step kp Mb) Map.empty (xs @ [u]) x =
        (if x \<in> set (xs @ [u]) \<or> (\<exists>u\<in>set (xs @ [u]). Mb u = Some x)
         then (case Mb x of None \<Rightarrow> None | Some y \<Rightarrow> if Q {x, y} then Some y else None) else None)"
        using IH None nu by (cases "x = u") (simp_all add: extract_step_def)
    qed
  next
    case (Some v)
    have v: "v \<in> set rs'" by (rule right[OF Some u(1)])
    have vu: "Mb v = Some u" by (rule sym[OF Some])
    have vxs: "v \<notin> set xs" using v u(3) L_ls' sides_disjoint' by auto
    have nv: "\<not> (\<exists>u'\<in>set xs. Mb u' = Some v)"
    proof
      assume "\<exists>u'\<in>set xs. Mb u' = Some v"
      then obtain u' where u': "u' \<in> set xs" "Mb u' = Some v" ..
      hence "u' = u" using sym[OF u'(2)] vu by simp
      thus False using u' u(2) by simp
    qed
    have vneq: "v \<noteq> u" using v u(1) L_ls' sides_disjoint' by auto
    have kq: "kp (ws' ! (pos u * k + pos v)) \<longleftrightarrow> Q {u, v}" by (rule kp[OF u(1) v])
    have qs: "Q {v, u} = Q {u, v}" by (simp add: insert_commute)
    show ?thesis
    proof (rule ext)
      fix x show "foldl (extract_step kp Mb) Map.empty (xs @ [u]) x =
        (if x \<in> set (xs @ [u]) \<or> (\<exists>u\<in>set (xs @ [u]). Mb u = Some x)
         then (case Mb x of None \<Rightarrow> None | Some y \<Rightarrow> if Q {x, y} then Some y else None) else None)"
      proof (cases "x = u")
        case True thus ?thesis using IH Some kq u(2) nu by (simp add: extract_step_def)
      next
        case False
        show ?thesis
        proof (cases "x = v")
          case True thus ?thesis using IH Some vu kq qs vxs nv vneq by (simp add: extract_step_def)
        next
          case False
          thus ?thesis using IH Some \<open>x \<noteq> u\<close> by (simp add: extract_step_def)
        qed
      qed
    qed
  qed
qed

lemma extract_correct:
  assumes sym: "\<And>u v. Mb u = Some v \<Longrightarrow> Mb v = Some u"
    and edges: "\<And>u v. Mb u = Some v \<Longrightarrow> {u, v} \<in> cp.G"
    and kp: "\<And>u v. \<lbrakk>u \<in> L; v \<in> set rs'\<rbrakk> \<Longrightarrow> kp (ws' ! (pos u * k + pos v)) \<longleftrightarrow> Q {u, v}"
    and QG: "\<And>e. Q e \<Longrightarrow> e \<in> G"
  shows "{{u, v} | u v. extract kp Mb u = Some v} = {e \<in> {{u, v} | u v. Mb u = Some v}. Q e}"
proof -
  note inv = extract_inv[where kp = kp and Q = Q and Mb = Mb and xs = ls,
                         OF sym edges kp ls_distinct order_refl]
  have ex: "extract kp Mb x = (case Mb x of None \<Rightarrow> None | Some y \<Rightarrow> if Q {x, y} then Some y else None)"
    for x
  proof (cases "Mb x")
    case (Some y)
    show ?thesis
    proof (cases "Q {x, y}")
      case True
      hence "x \<in> L \<or> (\<exists>u\<in>L. Mb u = Some x)"
        using G_sides[OF QG[OF True]] sym[OF Some] by auto
      thus ?thesis using inv by (simp add: extract_def)
    qed (simp add: inv extract_def Some)
  qed (simp add: inv extract_def)
  show ?thesis
    unfolding ex by (auto split: option.splits if_splits)
qed

lemma h_sgn: "h (sgn_w b a) = sgn_w b (h a)"
  by (cases b) simp_all

lemma ws'_at:
  assumes "u \<in> set ls'" "v \<in> set rs'"
  shows "h (ws' ! (pos u * k + pos v)) = cp.ecost u v"
proof -
  have p: "pos u < k" "pos v < k" using assms pos_less by simp_all
  have j: "pos u * k + pos v < k * k" by (rule mult_add_less[OF p])
  have "fs' ! (pos u * k + pos v) = u" "ts' ! (pos u * k + pos v) = v"
    using j p(2) assms by (simp_all add: fs'_nth ts'_nth ls'_nth_pos rs'_nth_pos)
  thus ?thesis using cp.ecost_edge[of "pos u * k + pos v"] j by simp
qed

lemma wfun_orig: "\<lbrakk>{u, v} \<in> G; u \<in> L\<rbrakk> \<Longrightarrow> wfun {u, v} = h (ws ! eidx u v)"
  using wfun_eq by (simp add: ecost_def)

end

context hungarian_csr_mw
begin

lemma mw_keep:
  assumes "u \<in> L" "v \<in> set rs'"
  shows "ws' ! (pos u * k + pos v) < 0 \<longleftrightarrow> {u, v} \<in> G \<and> sgn_w neg (wfun {u, v}) < 0"
proof -
  have ul: "u \<in> set ls'" using assms(1) by (simp add: set_ls')
  have "ws' ! (pos u * k + pos v) < 0 \<longleftrightarrow> h (ws' ! (pos u * k + pos v)) < 0" by simp
  also have "\<dots> \<longleftrightarrow> cp.ecost u v < 0" by (simp only: ws'_at[OF ul assms(2)])
  also have "\<dots> \<longleftrightarrow> {u, v} \<in> G \<and> sgn_w neg (wfun {u, v}) < 0"
    by (cases "{u, v} \<in> G") (simp_all add: cp_ecost[OF ul assms(2)] h_sgn wfun_orig[OF _ assms(1)])
  finally show ?thesis .
qed

end

context hungarian_csr_mwmc
begin

lemma mwmc_keep:
  assumes "u \<in> L" "v \<in> set rs'"
  shows "ws' ! (pos u * k + pos v) < 2 + of_nat (length ls + length rs) * max_abs_weight ws
           \<longleftrightarrow> {u, v} \<in> G"
proof -
  let ?D = "2 + of_nat (length ls + length rs) * max_abs_weight ws"
  let ?w = "\<lambda>e. sgn_w neg (wfun e)"
  have ul: "u \<in> set ls'" using assms(1) by (simp add: set_ls')
  have "ws' ! (pos u * k + pos v) < ?D \<longleftrightarrow> h (ws' ! (pos u * k + pos v)) < h ?D" by simp
  also have "\<dots> \<longleftrightarrow> cp.ecost u v < 2 * penalty G ?w" by (simp only: ws'_at[OF ul assms(2)] h_dflt)
  also have "\<dots> \<longleftrightarrow> {u, v} \<in> G"
  proof (cases "{u, v} \<in> G")
    case True
    have "?w {u, v} < penalty G ?w"
      by (rule edge_weight_less_thatn_penalty[OF graph_invarG[OF bipartite_G finite_set finite_set] True])
    moreover have "0 < penalty G ?w" by (rule penalty_gtr_0[OF finite_G])
    ultimately have lt: "?w {u, v} < 2 * penalty G ?w" by linarith
    have "cp.ecost u v = ?w {u, v}"
      by (simp only: cp_ecost[OF ul assms(2)] if_P[OF True] h_sgn wfun_orig[OF True assms(1)])
    thus ?thesis using lt True by simp
  next
    case False
    have "cp.ecost u v = 2 * penalty G ?w"
      by (simp only: cp_ecost[OF ul assms(2)] if_not_P[OF False] h_dflt)
    thus ?thesis using False by simp
  qed
  finally show ?thesis .
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
proof (induction "m - i" arbitrary: i s)
  case 0
  hence "i = m" by simp
  thus ?case by (subst fold_imp.simps) sep_auto
next
  case (Suc d)
  hence i: "i < m" by simp
  have f: "<P i s> f i s <P (Suc i)>" using Suc.prems(2) i by simp
  have r: "<P (Suc i) s'> fold_imp (Suc i) m f s' <P m>" for s'
    by (rule Suc.hyps(1)) (use Suc i in auto)
  show ?case using i by (subst fold_imp.simps) (sep_auto heap: f r)
qed

lemma take_drop_upd:
  "\<lbrakk>a < length ys; length xs = length ys; y = ys ! a\<rbrakk> \<Longrightarrow>
   list_update (take a ys @ drop a xs) a y = take (Suc a) ys @ drop (Suc a) xs"
  by (simp add: list_update_append take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric])

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
proof -
  define ys where "ys = src @ [nv..<nv + (K - length src)]"
  have len: "length ys = K" using assms by (simp add: ys_def)
  have v: "ys ! j = (if j < length src then src ! j else nv + (j - length src))" if "j < K" for j
    using that assms by (simp add: ys_def nth_append)
  have "<A \<mapsto>\<^sub>a (take 0 ys @ drop 0 xs) * S \<mapsto>\<^sub>a src> fold_imp 0 K (pad_step S (length src) nv A) ()
        <\<lambda>_. A \<mapsto>\<^sub>a (take K ys @ drop K xs) * S \<mapsto>\<^sub>a src>"
  proof (rule fold_imp_rule[where P = "\<lambda>j _. A \<mapsto>\<^sub>a (take j ys @ drop j xs) * S \<mapsto>\<^sub>a src"])
    fix j s assume j: "0 \<le> j" "j < K"
    have u: "list_update (take j ys @ drop j xs) j (ys ! j) = take (Suc j) ys @ drop (Suc j) xs"
      using j len assms by (simp add: take_drop_upd)
    show "<A \<mapsto>\<^sub>a (take j ys @ drop j xs) * S \<mapsto>\<^sub>a src> pad_step S (length src) nv A j s
          <\<lambda>_. A \<mapsto>\<^sub>a (take (Suc j) ys @ drop (Suc j) xs) * S \<mapsto>\<^sub>a src>"
      unfolding pad_step_def using j assms len u v[OF j(2)] by sep_auto
  qed simp
  thus ?thesis using len assms(1) by (simp add: ys_def)
qed

text \<open>The positions of the vertices in their side.\<close>

definition pos_step :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit \<Rightarrow> unit Heap" where
  "pos_step S P a u = do { x \<leftarrow> Array.nth S a; _ \<leftarrow> Array.upd x a P; return () }"

lemma pos_loop_rule:
  assumes "length ys = K" "\<forall>x\<in>set ys. x < length P0"
  shows "<Pa \<mapsto>\<^sub>a P0 * S \<mapsto>\<^sub>a ys> fold_imp 0 K (pos_step S Pa) ()
         <\<lambda>_. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<K] * S \<mapsto>\<^sub>a ys>"
proof -
  have "<Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<0] * S \<mapsto>\<^sub>a ys>
        fold_imp 0 K (pos_step S Pa) ()
        <\<lambda>_. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<K] * S \<mapsto>\<^sub>a ys>"
  proof (rule fold_imp_rule[where P = "\<lambda>j _. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<j] *
                                         S \<mapsto>\<^sub>a ys"])
    fix j s assume j: "0 \<le> j" "j < K"
    have "ys ! j < length P0" using assms j nth_mem[of j ys] by auto
    thus "<Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<j] * S \<mapsto>\<^sub>a ys> pos_step S Pa j s
          <\<lambda>_. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ys ! a) a) P0 [0..<Suc j] * S \<mapsto>\<^sub>a ys>"
      unfolding pos_step_def using j assms(1) by sep_auto
  qed simp
  thus ?thesis by simp
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
proof -
  define F where "F = map (\<lambda>j. as ! (j div k)) [0..<k * k]"
  define T where "T = map (\<lambda>j. bs ! (j mod k)) [0..<k * k]"
  have lF: "length F = k * k" and lT: "length T = k * k" by (simp_all add: F_def T_def)
  have "<As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take 0 F @ drop 0 xs) * Ta \<mapsto>\<^sub>a (take 0 T @ drop 0 ys)>
        fold_imp 0 (k * k) (grid_step k As Bs Fa Ta) ()
        <\<lambda>_. As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take (k * k) F @ drop (k * k) xs) *
            Ta \<mapsto>\<^sub>a (take (k * k) T @ drop (k * k) ys)>"
  proof (rule fold_imp_rule[where P = "\<lambda>j _. As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take j F @ drop j xs) *
                                         Ta \<mapsto>\<^sub>a (take j T @ drop j ys)"])
    fix j s assume j: "0 \<le> j" "j < k * k"
    hence k0: "0 < k" by (cases k) auto
    have d: "j div k < k" "j mod k < k" using j k0 by (simp_all add: less_mult_imp_div_less)
    have v: "F ! j = as ! (j div k)" "T ! j = bs ! (j mod k)" using j by (simp_all add: F_def T_def)
    have u: "list_update (take j F @ drop j xs) j (as ! (j div k)) = take (Suc j) F @ drop (Suc j) xs"
            "list_update (take j T @ drop j ys) j (bs ! (j mod k)) = take (Suc j) T @ drop (Suc j) ys"
      using j lF lT assms v by (simp_all add: take_drop_upd)
    show "<As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take j F @ drop j xs) * Ta \<mapsto>\<^sub>a (take j T @ drop j ys)>
          grid_step k As Bs Fa Ta j s
          <\<lambda>_. As \<mapsto>\<^sub>a as * Bs \<mapsto>\<^sub>a bs * Fa \<mapsto>\<^sub>a (take (Suc j) F @ drop (Suc j) xs) *
              Ta \<mapsto>\<^sub>a (take (Suc j) T @ drop (Suc j) ys)>"
      unfolding grid_step_def using j d assms lF lT by (sep_auto simp: u)
  qed simp
  thus ?thesis using assms lF lT by (simp add: F_def T_def)
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

lemma wgt_loop_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a replicate (k * k) dflt>
   fold_imp 0 (length fs) (wgt_step cf k Fa Ta Wa Pa Wc) ()
   <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws'>"
proof -
  let ?W = "\<lambda>j. foldl (\<lambda>W i. list_update W (eix i) (cf (ws ! i))) (replicate (k * k) dflt) [0..<j]"
  have "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ?W 0>
        fold_imp 0 (length fs) (wgt_step cf k Fa Ta Wa Pa Wc) ()
        <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ?W (length fs)>"
  proof (rule fold_imp_rule[where P = "\<lambda>j _. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl *
                                         Wc \<mapsto>\<^sub>a ?W j"])
    fix j s assume j: "0 \<le> j" "j < length fs"
    have b: "fs ! j < n'" "ts ! j < n'" "j < length ts" "j < length ws" "eix j < k * k"
      using j fs_in_ls'[of j] ts_in_rs'[of j] below_n' ts_length ws_length eix_less[of j] by auto
    have e: "posl ! (fs ! j) * k + posl ! (ts ! j) = eix j" by (simp add: eix_def pos_def)
    show "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ?W j>
          wgt_step cf k Fa Ta Wa Pa Wc j s
          <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ?W (Suc j)>"
      unfolding wgt_step_def using j b by (sep_auto simp: e)
  qed simp
  thus ?thesis by (simp add: ws'_def)
qed

lemma complete_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_complete dflt cf n Fa Ta Wa La Rv
   <\<lambda>(Fa', Ta', Wa', La', Rv', Pa, n'', k'). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      Fa' \<mapsto>\<^sub>a fs' * Ta' \<mapsto>\<^sub>a ts' * Wa' \<mapsto>\<^sub>a ws' * La' \<mapsto>\<^sub>a ls' * Rv' \<mapsto>\<^sub>a rs' * Pa \<mapsto>\<^sub>a posl *
      \<up>(n'' = n' \<and> k' = k)>"
proof -
  have kl: "length ls \<le> k" "length rs \<le> k" by (simp_all add: k_def)
  have r1: "<A \<mapsto>\<^sub>a replicate k 0 * La \<mapsto>\<^sub>a ls> fold_imp 0 k (pad_step La (length ls) n A) ()
            <\<lambda>_. A \<mapsto>\<^sub>a ls' * La \<mapsto>\<^sub>a ls>" for A
    using pad_loop_rule[of "replicate k 0" k ls] kl by (simp add: ls'_def)
  have r2: "<A \<mapsto>\<^sub>a replicate k 0 * Rv \<mapsto>\<^sub>a rs> fold_imp 0 k (pad_step Rv (length rs) n A) ()
            <\<lambda>_. A \<mapsto>\<^sub>a rs' * Rv \<mapsto>\<^sub>a rs>" for A
    using pad_loop_rule[of "replicate k 0" k rs] kl by (simp add: rs'_def)
  have r3: "<Pa \<mapsto>\<^sub>a replicate n' 0 * S \<mapsto>\<^sub>a ls'> fold_imp 0 k (pos_step S Pa) ()
            <\<lambda>_. Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k] * S \<mapsto>\<^sub>a ls'>"
    for Pa S
    using pos_loop_rule[of ls' k "replicate n' 0"] length_ls' below_n' by auto
  have r4: "<Pa \<mapsto>\<^sub>a foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k] * S \<mapsto>\<^sub>a rs'>
            fold_imp 0 k (pos_step S Pa) () <\<lambda>_. Pa \<mapsto>\<^sub>a posl * S \<mapsto>\<^sub>a rs'>" for Pa S
    using pos_loop_rule[of rs' k "foldl (\<lambda>P a. list_update P (ls' ! a) a) (replicate n' 0) [0..<k]"]
          length_rs' below_n' by (auto simp: posl_def)
  have r5: "<As \<mapsto>\<^sub>a ls' * Bs \<mapsto>\<^sub>a rs' * Fb \<mapsto>\<^sub>a replicate (k * k) 0 * Tb \<mapsto>\<^sub>a replicate (k * k) 0>
            fold_imp 0 (k * k) (grid_step k As Bs Fb Tb) ()
            <\<lambda>_. As \<mapsto>\<^sub>a ls' * Bs \<mapsto>\<^sub>a rs' * Fb \<mapsto>\<^sub>a fs' * Tb \<mapsto>\<^sub>a ts'>" for As Bs Fb Tb
    using grid_loop_rule[of ls' k rs' "replicate (k * k) 0" "replicate (k * k) 0"] length_ls' length_rs'
    by (simp add: fs'_def ts'_def)
  show ?thesis
    unfolding hungarian_csr_complete_def
    by (sep_auto heap: r1 r2 r3 r4 r5 wgt_loop_rule simp: k_def[symmetric] n'_def[symmetric])
qed

text \<open>The matching of the completed graph is the total map @{term Mb} with @{term n'} for a free
      vertex; it is read through @{term "aug_csr.buddy_lookup n'"}. A kept pair belongs to the
      original graph, hence its vertices are below @{term n}.\<close>

lemma extract_imp_rule:
  assumes edges: "\<And>u v. aug_csr.buddy_lookup n' Mb u = Some v \<Longrightarrow> {u, v} \<in> cp.G"
    and kept: "\<And>u v. \<lbrakk>u \<in> L; v \<in> set rs'; kp (ws' ! (pos u * k + pos v))\<rbrakk> \<Longrightarrow> v < n"
  shows "<La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * Mo \<mapsto>\<^sub>a replicate n n>
         extract_imp kp n' k La Pa Wc Mi Mo
         <\<lambda>_. \<exists>\<^sub>AMt. La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi *
              array_fun_assn n Mt Mo *
              \<up>(aug_csr.buddy_lookup n Mt = extract kp (aug_csr.buddy_lookup n' Mb))>"
proof -
  let ?B = "aug_csr.buddy_lookup n' Mb"
  let ?E = "\<lambda>a. foldl (extract_step kp ?B) Map.empty (take a ls)"
  let ?P = "\<lambda>a (s::unit). \<exists>\<^sub>AMt. La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi *
                               array_fun_assn n Mt Mo * \<up>(aug_csr.buddy_lookup n Mt = ?E a)"
  have step: "<?P a s> extract_imp_step kp n' k La Pa Wc Mi Mo a s <?P (Suc a)>"
    if a: "a < length ls" for a s
  proof -
    have ak: "a < k" using a by (simp add: k_def)
    have lsa: "ls' ! a = ls ! a" using a by (simp add: ls'_def nth_append)
    have u: "ls ! a \<in> set ls'" "posl ! (ls ! a) = a"
      using pos_ls'[OF ak] lsa a by (simp_all add: set_ls' pos_def)
    have uL: "ls ! a \<in> L" using a by simp
    have un: "ls ! a < n" "ls ! a < n'" using uL L_less u(1) below_n' by auto
    have E: "?E (Suc a) = extract_step kp ?B (?E a) (ls ! a)"
      using a by (simp add: take_Suc_conv_app_nth)
    show ?thesis
    proof (cases "Mb (ls ! a) = n'")
      case True
      hence B: "?B (ls ! a) = None" by (simp add: aug_csr.buddy_lookup_def array_fun_lookup_def)
      show ?thesis unfolding extract_imp_step_def array_fun_lookup_imp_def using a un True
        by (sep_auto heap: array_fun_lookup_rule simp: E extract_step_def B)
    next
      case False
      define v where "v = Mb (ls ! a)"
      have B: "?B (ls ! a) = Some v" using False by (simp add: aug_csr.buddy_lookup_def array_fun_lookup_def v_def)
      have v: "v \<in> set rs'" by (rule cp_G_right[OF edges[OF B] u(1)])
      have pv: "posl ! v < k" "v < n'" using v pos_less below_n' by (auto simp: pos_def)
      have idx: "a * k + posl ! v < k * k" by (rule mult_add_less[OF ak pv(1)])
      have w: "ws' ! (pos (ls ! a) * k + pos v) = ws' ! (a * k + posl ! v)"
        by (simp add: pos_def u(2))
      have nv: "Mb (ls ! a) \<noteq> n'" by (rule False)
      have vv: "Mb (ls ! a) = v" by (simp add: v_def)
      show ?thesis
      proof (cases "kp (ws' ! (a * k + posl ! v))")
        case True
        have vn: "v < n" using kept[OF uL v] True w by simp
        have upd: "aug_csr.buddy_lookup n (Mt(ls ! a := v, v := ls ! a)) =
                   (aug_csr.buddy_lookup n Mt)(ls ! a \<mapsto> v, v \<mapsto> ls ! a)" for Mt
          using un vn by (auto simp: aug_csr.buddy_lookup_def array_fun_lookup_def)
        show ?thesis
          apply (rule ht_exEI, rule norm_pre_extractI(5))
          subgoal premises Mt for Mt
          proof -
            have c: "<La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * array_fun_assn n Mt Mo>
                     extract_imp_step kp n' k La Pa Wc Mi Mo a s
                     <\<lambda>_. La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi *
                          array_fun_assn n (Mt(ls ! a := v, v := ls ! a)) Mo>"
              unfolding extract_imp_step_def array_fun_lookup_imp_def array_fun_upd_imp_def
              using a un nv pv idx True vn
              by (sep_auto heap: array_fun_lookup_rule array_fun_upd_rule simp: vv)
            have e: "aug_csr.buddy_lookup n (Mt(ls ! a := v, v := ls ! a)) = ?E (Suc a)"
              using Mt True by (simp add: E extract_step_def B w upd)
            show ?thesis by (rule ht_cons_post[OF c]) (sep_auto simp: e)
          qed
          done
      next
        case False
        show ?thesis
          apply (rule ht_exEI, rule norm_pre_extractI(5))
          subgoal premises Mt for Mt
          proof -
            have c: "<La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * array_fun_assn n Mt Mo>
                     extract_imp_step kp n' k La Pa Wc Mi Mo a s
                     <\<lambda>_. La \<mapsto>\<^sub>a ls * Pa \<mapsto>\<^sub>a posl * Wc \<mapsto>\<^sub>a ws' * array_fun_assn n' Mb Mi * array_fun_assn n Mt Mo>"
              unfolding extract_imp_step_def array_fun_lookup_imp_def
              using a un nv pv idx False
              by (sep_auto heap: array_fun_lookup_rule simp: vv)
            have e: "aug_csr.buddy_lookup n Mt = ?E (Suc a)"
              using Mt False by (simp add: E extract_step_def B w)
            show ?thesis by (rule ht_cons_post[OF c]) (sep_auto simp: e)
          qed
          done
      qed
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
    unfolding extract_imp_def by (sep_auto heap: loop' simp: extract_def)
qed

text \<open>The Hungarian method succeeds on the completed graph, and its matching is symmetric, consists
      of edges of the completed graph and is a perfect matching of minimum weight.\<close>

lemma cp_hungarian_some: "\<exists>Mb. cp.hl.hungarian = Some Mb"
proof (cases cp.hl.hungarian)
  case None
  hence "\<nexists>M. perfect_matching cp.G M" by (rule cp.hl.hungarian_correctness(1))
  thus ?thesis using cp_perfect_exists by simp
qed simp

lemma cp_result:
  assumes "cp.hl.hungarian = Some Mb"
  shows "\<And>u v. aug_csr.buddy_lookup n' Mb u = Some v \<Longrightarrow> aug_csr.buddy_lookup n' Mb v = Some u"
    and "\<And>u v. aug_csr.buddy_lookup n' Mb u = Some v \<Longrightarrow> {u, v} \<in> cp.G"
    and "min_weight_perfect_matching cp.G cp.wfun
           {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v}"
proof -
  have inv: "aug_csr.invar_matching n' cp.G Mb" by (rule cp.hl.hungarian_final_invar[OF assms])
  have M: "aug_csr.\<M> n' Mb = {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v}"
    by (simp add: aug_csr.\<M>_def')
  show "aug_csr.buddy_lookup n' Mb v = Some u" if "aug_csr.buddy_lookup n' Mb u = Some v" for u v
    using inv that by (auto simp: aug_csr.invar_matching_def aug_csr.symmetric_buddies_def)
  show "{u, v} \<in> cp.G" if "aug_csr.buddy_lookup n' Mb u = Some v" for u v
  proof -
    have "{u, v} \<in> aug_csr.\<M> n' Mb" using that M by blast
    thus ?thesis using inv by (auto simp: aug_csr.invar_matching_def)
  qed
  show "min_weight_perfect_matching cp.G cp.wfun
          {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v}"
    using cp.hl.hungarian_correctness(2)[OF assms] M by simp
qed

theorem reduced_run_rule:
  assumes kept: "\<And>u v. \<lbrakk>u \<in> L; v \<in> set rs'; kp (ws' ! (pos u * k + pos v))\<rbrakk> \<Longrightarrow> v < n"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_reduced_run dflt cf kp n theta cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AMb Mt. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n Mt Mo * true *
         \<up>(cp.hl.hungarian = Some Mb \<and>
           aug_csr.buddy_lookup n Mt = extract kp (aug_csr.buddy_lookup n' Mb))>"
proof -
  obtain Mb where Mb: "cp.hl.hungarian = Some Mb" using cp_hungarian_some by blast
  note ex = extract_imp_rule[OF cp_result(2)[OF Mb] kept]
  show ?thesis unfolding hungarian_csr_reduced_run_def
    by (sep_auto heap: complete_rule cp.hungarian_csr_run_rule ex simp: Mb)
qed
end

subsection \<open>Correctness of the Variants\<close>

context hungarian_csr_mw
begin

lemma mw_extract:
  assumes "cp.hl.hungarian = Some Mb"
  shows "min_weight_matching G (\<lambda>e. sgn_w neg (wfun e))
           {{u, v} | u v. extract (\<lambda>w. w < 0) (aug_csr.buddy_lookup n' Mb) u = Some v}"
proof -
  have "{{u, v} | u v. extract (\<lambda>w. w < 0) (aug_csr.buddy_lookup n' Mb) u = Some v} =
        {e \<in> {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v}. e \<in> G \<and> sgn_w neg (wfun e) < 0}"
    by (rule extract_correct[OF cp_result(1,2)[OF assms]]) (simp_all add: mw_keep)
  also have "\<dots> = {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v} \<inter> G \<inter>
                   {e. sgn_w neg (wfun e) < 0}" by auto
  finally show ?thesis using mw_correct[OF cp_result(3)[OF assms]] by simp
qed

lemma mw_kept: "\<lbrakk>u \<in> L; v \<in> set rs'; ws' ! (pos u * k + pos v) < 0\<rbrakk> \<Longrightarrow> v < n"
  using mw_keep G_below[of "{u, v}" v] by simp

theorem mw_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_reduced_run 0 (\<lambda>w. min 0 (sgn_w neg w)) (\<lambda>w. w < 0) n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n M))>"
  apply (rule ht_cons_post_prec[OF reduced_run_rule])
  subgoal by (rule mw_kept)
  apply (intro ent_ex_preI)
  subgoal for Mo Mb Mt
  proof (cases "cp.hl.hungarian = Some Mb \<and>
                aug_csr.buddy_lookup n Mt = extract (\<lambda>w. w < 0) (aug_csr.buddy_lookup n' Mb)")
    case True
    have key: "min_weight_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n Mt)"
      using mw_extract[OF conjunct1[OF True]] by (simp add: aug_csr.\<M>_def' conjunct2[OF True])
    show ?thesis by (rule ent_ex_postI[where x = Mt]) (use key in sep_auto)
  next
    case False
    then show ?thesis by (simp only: ent_pure_pre_iff) blast
  qed
  done

end

context hungarian_csr_mwmc
begin

lemma mwmc_extract:
  assumes "cp.hl.hungarian = Some Mb"
  shows "min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e))
           {{u, v} | u v. extract (\<lambda>w. w < 2 + of_nat (length ls + length rs) * max_abs_weight ws)
                            (aug_csr.buddy_lookup n' Mb) u = Some v}"
proof -
  have "{{u, v} | u v. extract (\<lambda>w. w < 2 + of_nat (length ls + length rs) * max_abs_weight ws)
                         (aug_csr.buddy_lookup n' Mb) u = Some v} =
        {e \<in> {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v}. e \<in> G}"
    by (rule extract_correct[OF cp_result(1,2)[OF assms]]) (simp_all only: mwmc_keep)
  also have "\<dots> = {{u, v} | u v. aug_csr.buddy_lookup n' Mb u = Some v} \<inter> G" by auto
  finally show ?thesis using mwmc_correct[OF cp_result(3)[OF assms]] by simp
qed

lemma mwmc_kept:
  "\<lbrakk>u \<in> L; v \<in> set rs';
    ws' ! (pos u * k + pos v) < 2 + of_nat (length ls + length rs) * max_abs_weight ws\<rbrakk>
   \<Longrightarrow> v < n"
  using mwmc_keep G_below[of "{u, v}" v] by simp

theorem mwmc_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_reduced_run (2 + of_nat (length ls + length rs) * max_abs_weight ws) (sgn_w neg)
     (\<lambda>w. w < 2 + of_nat (length ls + length rs) * max_abs_weight ws) n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n M))>"
  apply (rule ht_cons_post_prec[OF reduced_run_rule])
  subgoal by (rule mwmc_kept)
  apply (intro ent_ex_preI)
  subgoal for Mo Mb Mt
  proof (cases "cp.hl.hungarian = Some Mb \<and>
                aug_csr.buddy_lookup n Mt =
                  extract (\<lambda>w. w < 2 + of_nat (length ls + length rs) * max_abs_weight ws)
                    (aug_csr.buddy_lookup n' Mb)")
    case True
    have key: "min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n Mt)"
      using mwmc_extract[OF conjunct1[OF True]] by (simp add: aug_csr.\<M>_def' conjunct2[OF True])
    show ?thesis by (rule ent_ex_postI[where x = Mt]) (use key in sep_auto)
  next
    case False
    then show ?thesis by (simp only: ent_pure_pre_iff) blast
  qed
  done

end

subsection \<open>The Programs for the Variants\<close>

lemma neg_min_weight_matching:
  "min_weight_matching G (\<lambda>e. - w e) M \<longleftrightarrow> max_weight_matching G w M"
  by (auto simp: min_weight_matching_def max_weight_matching_def sum_negf)

lemma neg_min_weight_max_card_matching:
  "min_weight_max_card_matching G (\<lambda>e. - w e) M \<longleftrightarrow> max_weight_max_card_matching G w M"
  by (auto simp: min_weight_max_card_matching_def max_weight_max_card_matching_def sum_negf)

lemma neg_min_weight_perfect_matching:
  "min_weight_perfect_matching G (\<lambda>e. - w e) M \<longleftrightarrow> max_weight_perfect_matching G w M"
  by (auto simp: min_weight_perfect_matching_def max_weight_perfect_matching_def sum_negf)

text \<open>Minimum and maximum weight matchings.\<close>

definition "hungarian_csr_mw_run neg = hungarian_csr_reduced_run 0 (\<lambda>w. min 0 (sgn_w neg w)) (\<lambda>w. w < 0)"

text \<open>Minimum and maximum weight maximum cardinality matchings. The penalty is computed from the
      largest absolute weight.\<close>

definition max_abs_step :: "'n::{linordered_idom, heap} array \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n Heap" where
  "max_abs_step Wa i s = do { w \<leftarrow> Array.nth Wa i; return (max \<bar>w\<bar> s) }"

lemma max_abs_loop_rule:
  "<Wa \<mapsto>\<^sub>a ws> fold_imp 0 (length ws) (max_abs_step Wa) 0
   <\<lambda>s. Wa \<mapsto>\<^sub>a ws * \<up>(s = max_abs_weight ws)>"
proof -
  have "<Wa \<mapsto>\<^sub>a ws * \<up>(0 = fold max (map abs (take 0 ws)) 0)> fold_imp 0 (length ws) (max_abs_step Wa) 0
        <\<lambda>s. Wa \<mapsto>\<^sub>a ws * \<up>(s = fold max (map abs (take (length ws) ws)) 0)>"
  proof (rule fold_imp_rule[where P = "\<lambda>j s. Wa \<mapsto>\<^sub>a ws * \<up>(s = fold max (map abs (take j ws)) 0)"])
    fix j s assume j: "0 \<le> j" "j < length ws"
    show "<Wa \<mapsto>\<^sub>a ws * \<up>(s = fold max (map abs (take j ws)) 0)> max_abs_step Wa j s
          <\<lambda>s. Wa \<mapsto>\<^sub>a ws * \<up>(s = fold max (map abs (take (Suc j) ws)) 0)>"
      unfolding max_abs_step_def using j by (sep_auto simp: take_Suc_conv_app_nth)
  qed simp
  thus ?thesis by (simp add: max_abs_weight_def)
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
proof -
  define ys where "ys = map uminus ws"
  have len: "length ys = length ws" by (simp add: ys_def)
  have "<Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a (take 0 ys @ drop 0 (replicate (length ws) 0))>
        fold_imp 0 (length ws) (neg_step Wa Wn) ()
        <\<lambda>_. Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a (take (length ws) ys @ drop (length ws) (replicate (length ws) 0))>"
  proof (rule fold_imp_rule[where P = "\<lambda>j _. Wa \<mapsto>\<^sub>a ws *
                                         Wn \<mapsto>\<^sub>a (take j ys @ drop j (replicate (length ws) 0))"])
    fix j s assume j: "0 \<le> j" "j < length ws"
    have u: "list_update (take j ys @ drop j (replicate (length ws) 0)) j (- ws ! j) =
             take (Suc j) ys @ drop (Suc j) (replicate (length ws) 0)"
      by (rule take_drop_upd) (use j len in \<open>simp_all add: ys_def\<close>)
    show "<Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a (take j ys @ drop j (replicate (length ws) 0))> neg_step Wa Wn j s
          <\<lambda>_. Wa \<mapsto>\<^sub>a ws * Wn \<mapsto>\<^sub>a (take (Suc j) ys @ drop (Suc j) (replicate (length ws) 0))>"
      unfolding neg_step_def using j len u by sep_auto
  qed simp
  thus ?thesis using len by (simp add: ys_def)
qed

definition "hungarian_csr_max_perfect_run n \<theta> cap Fa Ta Wa La Rv = do {
     m \<leftarrow> Array.len Wa;
     Wn \<leftarrow> Array.new m 0;
     fold_imp 0 m (neg_step Wa Wn) ();
     hungarian_csr_run n \<theta> cap Fa Ta Wn La Rv }"

subsection \<open>Correctness of the Programs\<close>

context hungarian_csr_input
begin

theorem hungarian_csr_mw_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mw_run neg n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n M))>"
proof -
  interpret mw: hungarian_csr_mw h n fs ts ws ls rs neg by unfold_locales
  show ?thesis unfolding hungarian_csr_mw_run_def by (rule mw.mw_run_rule)
qed

corollary min_weight_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mw_run False n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true * \<up>(min_weight_matching G wfun (aug_csr.\<M> n M))>"
  using hungarian_csr_mw_run_rule[of _ _ _ _ _ False] by simp

corollary max_weight_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mw_run True n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true * \<up>(max_weight_matching G wfun (aug_csr.\<M> n M))>"
  using hungarian_csr_mw_run_rule[of _ _ _ _ _ True] by (simp add: neg_min_weight_matching)

theorem hungarian_csr_mwmc_run_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mwmc_run neg n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_max_card_matching G (\<lambda>e. sgn_w neg (wfun e)) (aug_csr.\<M> n M))>"
proof -
  interpret mwmc: hungarian_csr_mwmc h n fs ts ws ls rs neg by unfold_locales
  show ?thesis unfolding hungarian_csr_mwmc_run_def
    by (sep_auto heap: max_abs_loop_rule mwmc.mwmc_run_rule)
qed

corollary min_weight_max_card_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mwmc_run False n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(min_weight_max_card_matching G wfun (aug_csr.\<M> n M))>"
  using hungarian_csr_mwmc_run_rule[of _ _ _ _ _ False] by simp

corollary max_weight_max_card_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_mwmc_run True n \<theta> cap Fa Ta Wa La Rv
   <\<lambda>Mo. \<exists>\<^sub>AM. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
         array_fun_assn n M Mo * true *
         \<up>(max_weight_max_card_matching G wfun (aug_csr.\<M> n M))>"
  using hungarian_csr_mwmc_run_rule[of _ _ _ _ _ True] by (simp add: neg_min_weight_max_card_matching)

lemma neg_input: "hungarian_csr_input h n fs ts (map uminus ws) ls rs"
  by (intro hungarian_csr_input.intro real_embedding_axioms hungarian_csr_input_axioms.intro)
     (simp_all add: ts_length ws_length ls_distinct rs_distinct fs_ls ts_rs sides_disjoint
                    verts_below[unfolded Un_subset_iff] no_parallel)

theorem max_weight_perfect_matching_run:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_max_perfect_run n theta cap Fa Ta Wa La Rv
   <\<lambda>(r, Mi, Pti). \<exists>\<^sub>AM \<pi>. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      array_fun_assn n M Mi * array_fun_val_assn h n \<pi> Pti * true *
      \<up>((r = result.success \<and> max_weight_perfect_matching G wfun (aug_csr.\<M> n M)) \<or>
        (r = result.failure \<and> (\<nexists>M'. perfect_matching G M')))>"
proof -
  interpret ng: hungarian_csr_input h n fs ts "map uminus ws" ls rs by (rule neg_input)
  have w: "ng.wfun e = - wfun e" if e: "e \<in> G" for e
  proof -
    obtain i where i: "i < length fs" "e = {fs ! i, ts ! i}" using e by (auto simp: G_def)
    have "ng.wfun e = ng.ecost (fs ! i) (ts ! i)" using ng.wfun_eq[of "fs ! i" "ts ! i"] e i(2) by simp
    also have "\<dots> = h (map uminus ws ! i)" by (rule ng.ecost_edge[OF i(1)])
    also have "\<dots> = - wfun e"
      using wfun_eq[of "fs ! i" "ts ! i"] ecost_edge[OF i(1)] e i ws_length by simp
    finally show ?thesis .
  qed
  have conv: "max_weight_perfect_matching G wfun X" if "min_weight_perfect_matching G ng.wfun X" for X
  proof -
    have "min_weight_perfect_matching G (\<lambda>e. - wfun e) X"
      by (rule min_weight_perfect_matching_cong[OF that w])
    thus ?thesis by (simp add: neg_min_weight_perfect_matching)
  qed
  have run: "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
   hungarian_csr_max_perfect_run n theta cap Fa Ta Wa La Rv
   <\<lambda>(r, Mi, Pti). \<exists>\<^sub>AM \<pi>. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
      array_fun_assn n M Mi * array_fun_val_assn h n \<pi> Pti * true *
      \<up>((r = result.success \<and> min_weight_perfect_matching G ng.wfun (aug_csr.\<M> n M)) \<or>
        (r = result.failure \<and> (\<nexists>M'. perfect_matching G M')))>"
    unfolding hungarian_csr_max_perfect_run_def
    by(sep_auto heap: neg_loop_rule ng.hungarian_csr_run_correct)
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

