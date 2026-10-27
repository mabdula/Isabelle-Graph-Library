theory Bipartite_Arrays
  imports Partition_Oracle_Imp Basic_Matching.Matching
begin

section \<open>Bipartite Graphs Given by Two Arrays\<close>

text \<open>The graph is the set of the doubletons \<open>{fs ! i, ts ! i}\<close>. It is bipartite with the left
  endpoints on one side and the right endpoints on the other, and no edge is listed twice. A
  set of positions represents the set of its doubletons.\<close>

definition "bm_setup_imp nv Fa Ta k = do {
   m \<leftarrow> Array.len Fa;
   H1 \<leftarrow> part_handle_imp m nv Fa;
   H2 \<leftarrow> part_handle_imp m nv Ta;
   Xi \<leftarrow> Array.new m False;
   C1 \<leftarrow> Array.new nv 0;
   C2 \<leftarrow> Array.new nv 0;
   k m H1 H2 Xi C1 C2 }"

locale bipartite_matching_imp =
  fixes nv :: nat
    and fs ts :: "nat list"
  assumes lengths: "length ts = length fs"
    and bip: "bipartite ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (set fs) (set ts)"
    and simple: "inj_on (\<lambda> i. (fs ! i, ts ! i)) {0..<length fs}"
    and verts: "set fs \<union> set ts \<subseteq> {..<nv}"
begin

lemma sides: "set fs \<inter> set ts = {}"
  using bip
  by (rule bipartite_disjointD)

lemma ends: "i < length fs \<Longrightarrow> fs ! i \<in> set fs \<and> ts ! i \<in> set ts"
  using lengths
  by simp

lemma left_right: "\<lbrakk>i < length fs; j < length fs\<rbrakk> \<Longrightarrow> fs ! i \<noteq> ts ! j"
  using sides ends[of i] ends[of j]
  by (fastforce)

lemma dbltn_inj: "inj_on (\<lambda> i. {fs ! i, ts ! i}) {0..<length fs}"
  using simple
  by (auto simp: inj_on_def doubleton_eq_iff left_right)

lemma ends_bound:
  "i < length fs \<Longrightarrow> fs ! i < nv \<and> ts ! i < nv"
  using verts ends[of i]
  by (fastforce)

lemma blocks_in: "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts = blocks_assn (length fs) nv fs Fa * blocks_assn
    (length fs) nv ts Ta"
  by (simp add: blocks_assn_def lengths ends_bound)

text \<open>The allocation prologue shared by the programs on such graphs: the partner handles of the
  two partition oracles, the empty solution array and the two block counters. It is followed by
  the continuation \<open>k\<close>.\<close>

lemma bm_len_rule:
  "<F * (blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta)> Array.len Fa
    <\<lambda> r. F * (blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta) *
      \<up>(r = length fs)>"
  by (sep_auto simp: blocks_assn_def)

lemma bm_setup_rule:
  assumes "\<And> H1 H2 Xi C1 C2.
    <F * part_pst (length fs) fs H1 * part_pst (length fs) ts H2 * bool_array_set_assn (length fs) {} Xi *
       cnt_assn nv fs {} C1 * cnt_assn nv ts {} C2 *
       blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta * true>
      k (length fs) H1 H2 Xi C1 C2 <Q>"
  shows "<F * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> bm_setup_imp nv Fa Ta k <Q>"
proof-
  let ?B = "blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta"
  note len = bm_len_rule[where F = F and Fa = Fa and Ta = Ta]
  have h1: "<F * ?B> part_handle_imp (length fs) nv Fa <\<lambda> H1. F * ?B * part_pst (length fs) fs H1 * true>"
    by (rule ht_frame_ac[OF part_handle_rule[where bl = fs], where R = "F * blocks_assn (length fs) nv ts Ta"])
       (simp only: star_aci, rule ent_refl)+
  have h2: "<F * ?B * part_pst (length fs) fs H1 * true> part_handle_imp (length fs) nv Ta
            <\<lambda> H2. F * ?B * part_pst (length fs) fs H1 * part_pst (length fs) ts H2 * true>" for H1
    by (rule ht_frame_ac[OF part_handle_rule[where bl = ts], where R = "F * blocks_assn (length fs) nv fs Fa *
          part_pst (length fs) fs H1 * true"])
       (simp only: star_aci, rule ent_refl)+
  show ?thesis
    unfolding bm_setup_imp_def mult.assoc blocks_in
    by (rule ht_bind[OF len], rule ht_pure_pre, simp only:,
        rule ht_bind[OF h1], rule ht_bind[OF h2],
        rule alloc_bind[OF bool_array_set_assn_new], rule alloc_bind[OF cnt_assn_new[of _ fs]],
        rule alloc_bind[OF cnt_assn_new[of _ ts]], rule ht_cons_pre[OF _ assms])
       (simp only: star_aci, rule ent_refl)
qed

end

subsection \<open>Edge Weights\<close>

text \<open>A further list of the same length holds the edge weights, read in the reals through \<open>h\<close>.
  Since no edge is listed twice, this defines a weight function on the edges.\<close>

locale weighted_bipartite_arrays = bipartite_matching_imp nv fs ts
  for nv fs ts +
  fixes h :: "'n \<Rightarrow> real" and ws :: "'n list"
  assumes ws_length: "length ws = length fs"
begin

definition "edge_weight e = h (ws ! (THE i. i < length fs \<and> {fs ! i, ts ! i} = e))"

lemma edge_weight: "i < length fs \<Longrightarrow> edge_weight {fs ! i, ts ! i} = h (ws ! i)"
  unfolding edge_weight_def
  by (rule arg_cong[where f = "\<lambda> i. h (ws ! i)"], rule the_equality)
     (auto dest: inj_onD[OF dbltn_inj])

lemma sum_img:
  assumes "X \<subseteq> {0..<length fs}"
  shows "sum edge_weight ((\<lambda> i. {fs ! i, ts ! i}) ` X) = sum (\<lambda> i. h (ws ! i)) X"
  using assms
  by (subst sum.reindex) (auto intro: inj_on_subset[OF dbltn_inj] simp: edge_weight intro!: sum.cong)

end

end
