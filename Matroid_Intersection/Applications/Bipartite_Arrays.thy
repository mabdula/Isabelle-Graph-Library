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
  using bip by (rule bipartite_disjointD)

lemma ends: "i < length fs \<Longrightarrow> fs ! i \<in> set fs \<and> ts ! i \<in> set ts"
  using lengths by simp

lemma left_right: "\<lbrakk>i < length fs; j < length fs\<rbrakk> \<Longrightarrow> fs ! i \<noteq> ts ! j"
proof
  assume ij: "i < length fs" "j < length fs" and eq: "fs ! i = ts ! j"
  have "fs ! i \<in> set fs" "fs ! i \<in> set ts"
    using ends[OF ij(1)] ends[OF ij(2)] unfolding eq by simp_all
  then show False
    using sides by blast
qed

lemma dbltn_inj: "inj_on (\<lambda> i. {fs ! i, ts ! i}) {0..<length fs}"
proof(rule inj_onI)
  fix i j
  assume i: "i \<in> {0..<length fs}" and j: "j \<in> {0..<length fs}" 
    and eq: "{fs ! i, ts ! i} = {fs ! j, ts ! j}"
  have "fs ! i \<in> {fs ! j, ts ! j}" "ts ! i \<in> {fs ! j, ts ! j}"
    unfolding eq[symmetric] by simp_all
  then have "fs ! i = fs ! j" "ts ! i = ts ! j"
    using left_right[of i j] left_right[of j i] i j by auto
  then show "i = j"
    using simple i j by (intro inj_onD[OF simple]) simp_all
qed

lemma blocks_in: "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts = blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta"
proof-
  have "fs ! i < nv" "ts ! i < nv" if "i < length fs" for i
    using ends[OF that] verts by auto
  then have "\<forall> i < length fs. fs ! i < nv" "\<forall> i < length fs. ts ! i < nv"
    by simp_all
  then show ?thesis
    unfolding blocks_assn_def using lengths by simp
qed

text \<open>The allocation prologue shared by the programs on such graphs: the partner handles of the
  two partition oracles, the empty solution array and the two block counters. It is followed by
  the continuation \<open>k\<close>.\<close>

lemma bm_setup_rule:
  assumes k: "\<And> H1 H2 Xi C1 C2.
    <F * part_pst (length fs) fs H1 * part_pst (length fs) ts H2 * bool_array_set_assn (length fs) {} Xi *
       cnt_assn nv fs {} C1 * cnt_assn nv ts {} C2 *
       blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta * true>
      k (length fs) H1 H2 Xi C1 C2 <Q>"
  shows "<F * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> bm_setup_imp nv Fa Ta k <Q>"
proof-
  let ?B = "blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta"
  have pre: "F * Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts = F * ?B"
    by (simp only: mult.assoc blocks_in)
  have len: "<F * ?B> Array.len Fa <\<lambda> r. F * ?B * \<up>(r = length fs)>"
    by (sep_auto simp: blocks_assn_def)
  have h1: "<F * ?B> part_handle_imp (length fs) nv Fa <\<lambda> H1. F * ?B * part_pst (length fs) fs H1 * true>"
    by (rule ht_frame_ac[OF part_handle_rule[where bl = fs], where R = "F * blocks_assn (length fs) nv ts Ta"])
       (simp only: star_aci, rule ent_refl)+
  have h2: "<F * ?B * part_pst (length fs) fs H1 * true> part_handle_imp (length fs) nv Ta
            <\<lambda> H2. F * ?B * part_pst (length fs) fs H1 * part_pst (length fs) ts H2 * true>" for H1
    by (rule ht_frame_ac[OF part_handle_rule[where bl = ts], where R = "F * blocks_assn (length fs) nv fs Fa *
          part_pst (length fs) fs H1 * true"])
       (simp only: star_aci, rule ent_refl)+
  show ?thesis
    unfolding bm_setup_imp_def pre
    apply (rule ht_bind[OF len], rule ht_pure_pre, simp only:)
    apply (rule ht_bind[OF h1], rule ht_bind[OF h2])
    apply (rule alloc_bind[OF bool_array_set_assn_new], rule alloc_bind[OF cnt_assn_new[of _ fs]],
           rule alloc_bind[OF cnt_assn_new[of _ ts]])
    apply (rule ht_cons_pre[OF _ k], simp only: star_aci, rule ent_refl)
    done
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
proof-
  assume i: "i < length fs"
  have "(THE j. j < length fs \<and> {fs ! j, ts ! j} = {fs ! i, ts ! i}) = i"
  proof(rule the_equality)
    show "i < length fs \<and> {fs ! i, ts ! i} = {fs ! i, ts ! i}"
      using i by simp
  next
    fix j
    assume "j < length fs \<and> {fs ! j, ts ! j} = {fs ! i, ts ! i}"
    then show "j = i"
      using i by (intro inj_onD[OF dbltn_inj]) simp_all
  qed
  then show ?thesis
    unfolding edge_weight_def by simp
qed

lemma sum_img:
  assumes X: "X \<subseteq> {0..<length fs}"
  shows "sum edge_weight ((\<lambda> i. {fs ! i, ts ! i}) ` X) = sum (\<lambda> i. h (ws ! i)) X"
proof-
  have "sum edge_weight ((\<lambda> i. {fs ! i, ts ! i}) ` X) = sum (edge_weight \<circ> (\<lambda> i. {fs ! i, ts ! i})) X"
    by (rule sum.reindex[OF inj_on_subset[OF dbltn_inj X]])
  also have "\<dots> = sum (\<lambda> i. h (ws ! i)) X"
    using X by (intro sum.cong) (auto simp: edge_weight)
  finally show ?thesis .
qed

end

end