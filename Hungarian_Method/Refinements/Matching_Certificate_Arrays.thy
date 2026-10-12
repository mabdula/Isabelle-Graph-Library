theory Matching_Certificate_Arrays
  imports
    Matching_Certificate_Imperative
    Data_Structures.Imp_Bool_Set
begin

section \<open>Certificate Checkers for Extremal Bipartite Matchings on Arrays\<close>

text \<open>The instance is given by the arrays of the left endpoints, the right endpoints and the
      weights of the edges, and by the arrays of the left and the right vertices. The edges are
      named by their positions. The candidate matching is an array of edge names, the potential
      an array with one entry per vertex, and the Hall violator an array of left vertices. Mark
      sets are Boolean arrays of length @{term n}.\<close>

subsection \<open>Read-Only Arrays\<close>

lemma array_rlist: "imp_rlist (\<lambda>xs a. a \<mapsto>\<^sub>a xs) Array.len Array.nth"
  by unfold_locales sep_auto+

subsection \<open>The Edges as an Iterable Set of Positions\<close>

type_synonym 'n edge_arrays = "nat array \<times> nat array \<times> 'n array"

definition arr_es_assn ::
  "nat set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> 'n::heap) \<Rightarrow> 'n edge_arrays \<Rightarrow> assn" where
  "arr_es_assn D F T W = (\<lambda>(Fa, Ta, Wa).
     Fa \<mapsto>\<^sub>a map F [0..<card D] * Ta \<mapsto>\<^sub>a map T [0..<card D] * Wa \<mapsto>\<^sub>a map W [0..<card D] *
     \<up>(\<exists>m. D = {0..<m}))"

definition "arr_elst D = [0..<card D]"

definition "arr_it_assn xs it = \<up>(xs = [fst it..<snd it])"

definition arr_memb :: "'n::heap edge_arrays \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "arr_memb = (\<lambda>(Fa, Ta, Wa) e. do { m \<leftarrow> Array.len Fa; return (e < m) })"

definition arr_fst :: "'n::heap edge_arrays \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "arr_fst = (\<lambda>(Fa, Ta, Wa) e. Array.nth Fa e)"

definition arr_snd :: "'n::heap edge_arrays \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "arr_snd = (\<lambda>(Fa, Ta, Wa) e. Array.nth Ta e)"

definition arr_w :: "'n::heap edge_arrays \<Rightarrow> nat \<Rightarrow> 'n Heap" where
  "arr_w = (\<lambda>(Fa, Ta, Wa) e. Array.nth Wa e)"

definition arr_it_init :: "'n::heap edge_arrays \<Rightarrow> (nat \<times> nat) Heap" where
  "arr_it_init = (\<lambda>(Fa, Ta, Wa). do { m \<leftarrow> Array.len Fa; return (0, m) })"

definition arr_it_has_next :: "'n::heap edge_arrays \<Rightarrow> nat \<times> nat \<Rightarrow> bool Heap" where
  "arr_it_has_next p it = return (fst it < snd it)"

definition arr_it_next :: "'n::heap edge_arrays \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat \<times> nat) Heap" where
  "arr_it_next p it = return (fst it, Suc (fst it), snd it)"

lemma Cons_eq_upt_conv: "(x # xs = [i..<j]) = (i < j \<and> x = i \<and> xs = [Suc i..<j])"
  by (subst eq_commute) (auto simp: upt_eq_Cons_conv)

lemma arr_edge_set:
  "imp_edge_set arr_es_assn arr_elst arr_it_assn arr_memb arr_fst arr_snd arr_w
     arr_it_init arr_it_has_next arr_it_next"
  by (unfold_locales; unfold split_paired_all;
      sep_auto simp: arr_es_assn_def arr_elst_def arr_it_assn_def arr_memb_def arr_fst_def
                     arr_snd_def arr_w_def arr_it_init_def arr_it_has_next_def arr_it_next_def
                     Cons_eq_upt_conv)

subsection \<open>The Programs\<close>

global_interpretation cert_arr: matching_cert_imp_code
  arr_memb arr_fst arr_snd arr_w arr_it_init arr_it_has_next arr_it_next
  Array.len Array.nth Array.len Array.nth Array.len Array.nth bool_array_set_isin_imp bool_array_set_insert_imp
  defines cert_arr_feas_loop = cert_arr.feas_loop
    and cert_arr_match_loop = cert_arr.match_loop
    and cert_arr_vert_loop = cert_arr.vert_loop
    and cert_arr_certify_sh = cert_arr.certify_sh_imp
    and cert_arr_certify = cert_arr.certify_imp
    and cert_arr_insert_loop = cert_arr.insert_loop
    and cert_arr_hall_S_loop = cert_arr.hall_S_loop
    and cert_arr_hall_N_loop = cert_arr.hall_N_loop
    and cert_arr_hall = cert_arr.hall_imp
    and cert_arr_certify_mc = cert_arr.certify_mc_imp
  done

declare cert_arr.feas_loop.simps[code] cert_arr.match_loop.simps[code]
  cert_arr.vert_loop.simps[code] cert_arr.insert_loop.simps[code]
  cert_arr.hall_S_loop.simps[code] cert_arr.hall_N_loop.simps[code]

text \<open>The top-level programs allocate the mark sets and run the checks.\<close>

definition certify_arrays ::
  "bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> bool Heap" where
  "certify_arrays neg perfect n Fa Ta Wa La Rv Ma Ya = do {
     Ui \<leftarrow> Array.new n False;
     cert_arr_certify neg perfect n (Fa, Ta, Wa) La Rv Ma Ya Ui }"

definition hall_arrays ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> bool Heap" where
  "hall_arrays n Fa Ta Wa La Rv Sa = do {
     Li \<leftarrow> Array.new n False;
     Si \<leftarrow> Array.new n False;
     Ni \<leftarrow> Array.new n False;
     cert_arr_hall n (Fa, Ta, Wa) La Rv Sa Li Si Ni }"

definition certify_mc_arrays ::
  "bool \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n \<Rightarrow> nat array \<Rightarrow> bool Heap" where
  "certify_mc_arrays neg n Fa Ta Wa La Rv Ma Ya t Sa = do {
     Ui \<leftarrow> Array.new n False;
     Li \<leftarrow> Array.new n False;
     Si \<leftarrow> Array.new n False;
     Ni \<leftarrow> Array.new n False;
     cert_arr_certify_mc neg n (Fa, Ta, Wa) La Rv Ma Ya t Sa Ui Li Si Ni }"

subsection \<open>Correctness\<close>

text \<open>The assumptions on the instance.\<close>

locale bp_cert_input = real_embedding h
  for h :: "'n::{linordered_idom, heap} \<Rightarrow> real" +
  fixes n :: nat
    and fs :: "nat list"
    and ts :: "nat list"
    and ws :: "'n list"
    and ls :: "nat list"
    and rs :: "nat list"
  assumes ts_length: "length ts = length fs"
    and ws_length: "length ws = length fs"
    and ls_distinct: "distinct ls"
    and rs_distinct: "distinct rs"
    and fs_ls: "set fs = set ls"
    and ts_rs: "set ts = set rs"
    and sides_disjoint: "set ls \<inter> set rs = {}"
    and verts_below: "set ls \<union> set rs \<subseteq> {..<n}"
    and no_parallel: "distinct (zip fs ts)"
begin

definition "G = {{fs ! i, ts ! i} | i. i < length fs}"

lemma cert_mc:
  "matching_cert {0..<length fs} [0..<length fs] ((!) fs) ((!) ts) n ls rs h"
proof (intro matching_cert.intro real_embedding_axioms matching_cert_axioms.intro)
  show "set [0..<length fs] = {0..<length fs}" by simp
  show "(!) fs ` {0..<length fs} = set ls" using fs_ls nth_image[of "length fs" fs] by simp
  show "(!) ts ` {0..<length fs} = set rs" using ts_rs ts_length nth_image[of "length ts" ts] by simp
  show "distinct ls" "distinct rs" "set ls \<inter> set rs = {}" "set ls \<union> set rs \<subseteq> {..<n}"
    by (rule ls_distinct rs_distinct sides_disjoint verts_below)+
  show "inj_on (\<lambda>i. (fs ! i, ts ! i)) {0..<length fs}"
  proof (rule inj_onI)
    fix i j assume ij: "i \<in> {0..<length fs}" "j \<in> {0..<length fs}" "(fs ! i, ts ! i) = (fs ! j, ts ! j)"
    hence "zip fs ts ! i = zip fs ts ! j" using ts_length by simp
    thus "i = j" using nth_eq_iff_index_eq[OF no_parallel] ij(1,2) ts_length by simp
  qed
qed

sublocale cert: matching_cert_imp "{0..<length fs}" "[0..<length fs]" "(!) fs" "(!) ts" "(!) ws"
  n ls rs h arr_es_assn arr_elst arr_it_assn arr_memb arr_fst arr_snd arr_w
  arr_it_init arr_it_has_next arr_it_next
  "\<lambda>xs a. a \<mapsto>\<^sub>a xs" Array.len Array.nth "\<lambda>xs a. a \<mapsto>\<^sub>a xs" Array.len Array.nth
  "\<lambda>xs a. a \<mapsto>\<^sub>a xs" Array.len Array.nth
  "{..<n}" "\<lambda>X. X \<subseteq> {..<n}" id "{}" insert "\<lambda>x X. X - {x}" "\<lambda>X x. x \<in> X" "bool_array_set_assn n"
  "Array.new n False" bool_array_set_insert_imp bool_array_set_delete_imp bool_array_set_isin_imp
  by (rule matching_cert_imp.intro[OF cert_mc arr_edge_set array_rlist array_rlist array_rlist
             bool_array_set_fixed_univ_set_imp])
     (unfold_locales; simp add: arr_elst_def)

lemma G_eq: "cert.G = G"
  by (auto simp: cert.G_def cert.cedge_def G_def)

lemma Mat_eq: "cert.Mat ms = {{fs ! i, ts ! i} | i. i \<in> set ms}"
  by (auto simp: cert.Mat_def cert.cedge_def)

text \<open>The weight of an edge is the weight at its position.\<close>

lemma wG_eq: "i < length fs \<Longrightarrow> cert.wG {fs ! i, ts ! i} = h (ws ! i)"
  using cert.wG_edge[of i] by (simp add: cert.cedge_def)

lemma es_assn_eq: "cert.EA (Fa, Ta, Wa) = Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws"
proof -
  have "map ((!) ts) [0..<length fs] = ts" "map ((!) ws) [0..<length fs] = ws"
    using ts_length ws_length map_nth[of ts] map_nth[of ws] by simp_all
  moreover have "\<exists>m. {0..<length fs} = {0..<m}" by blast
  ultimately show ?thesis by (simp add: arr_es_assn_def map_nth)
qed

theorem certify_arrays_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys>
   certify_arrays neg perfect n Fa Ta Wa La Rv Ma Ya
   <\<lambda>r. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys *
        true * \<up>(r = cert.certify neg perfect ms ys)>"
  unfolding certify_arrays_def cert_arr_certify_def
  by (sep_auto heap: cert.mark_empty_rule cert.certify_imp_rule[where p = "(Fa, Ta, Wa)", unfolded es_assn_eq])

theorem hall_arrays_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs * Sa \<mapsto>\<^sub>a S>
   hall_arrays n Fa Ta Wa La Rv Sa
   <\<lambda>r. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs * Sa \<mapsto>\<^sub>a S *
        true * \<up>(r = cert.hall_check S)>"
  unfolding hall_arrays_def cert_arr_hall_def
  by (sep_auto heap: cert.mark_empty_rule cert.hall_imp_rule[where p = "(Fa, Ta, Wa)", unfolded es_assn_eq])

theorem certify_mc_arrays_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys * Sa \<mapsto>\<^sub>a S>
   certify_mc_arrays neg n Fa Ta Wa La Rv Ma Ya t Sa
   <\<lambda>r. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys *
        Sa \<mapsto>\<^sub>a S * true * \<up>(r = cert.certify_mc neg ms ys t S)>"
  unfolding certify_mc_arrays_def cert_arr_certify_mc_def
  by (sep_auto heap: cert.mark_empty_rule cert.certify_mc_imp_rule[where p = "(Fa, Ta, Wa)", unfolded es_assn_eq])

subsection \<open>The Certified Properties\<close>

text \<open>If the checkers accept, the candidate @{term "{{fs ! i, ts ! i} | i. i \<in> set ms}"} is a minimum
      or maximum weight (perfect) matching of @{const G} for the weights @{const cert.wG}
      (lemma @{thm [source] wG_eq}), or there is no perfect matching.\<close>

abbreviation "arrays_assn Fa Ta Wa La Rv \<equiv>
  Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs"

lemma certify_arrays_post:
  assumes "cert.certify neg perfect ms ys \<Longrightarrow> P"
  shows "<arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys>
         certify_arrays neg perfect n Fa Ta Wa La Rv Ma Ya
         <\<lambda>r. arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys * true * \<up>(r \<longrightarrow> P)>"
  by (rule ht_cons_post_prec[OF certify_arrays_rule]) (sep_auto intro: assms)

corollary min_weight_perfect_matching_arrays:
  "<arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys>
   certify_arrays False True n Fa Ta Wa La Rv Ma Ya
   <\<lambda>r. arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys * true *
        \<up>(r \<longrightarrow> min_weight_perfect_matching G cert.wG {{fs ! i, ts ! i} | i. i \<in> set ms})>"
  by (rule certify_arrays_post) (use cert.min_weight_perfect_certified in \<open>simp add: G_eq Mat_eq\<close>)

corollary max_weight_perfect_matching_arrays:
  "<arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys>
   certify_arrays True True n Fa Ta Wa La Rv Ma Ya
   <\<lambda>r. arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys * true *
        \<up>(r \<longrightarrow> max_weight_perfect_matching G cert.wG {{fs ! i, ts ! i} | i. i \<in> set ms})>"
  by (rule certify_arrays_post) (use cert.max_weight_perfect_certified in \<open>simp add: G_eq Mat_eq\<close>)

corollary min_weight_matching_arrays:
  "<arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys>
   certify_arrays False False n Fa Ta Wa La Rv Ma Ya
   <\<lambda>r. arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys * true *
        \<up>(r \<longrightarrow> min_weight_matching G cert.wG {{fs ! i, ts ! i} | i. i \<in> set ms})>"
  by (rule certify_arrays_post) (use cert.min_weight_matching_certified in \<open>simp add: G_eq Mat_eq\<close>)

corollary max_weight_matching_arrays:
  "<arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys>
   certify_arrays True False n Fa Ta Wa La Rv Ma Ya
   <\<lambda>r. arrays_assn Fa Ta Wa La Rv * Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys * true *
        \<up>(r \<longrightarrow> max_weight_matching G cert.wG {{fs ! i, ts ! i} | i. i \<in> set ms})>"
  by (rule certify_arrays_post) (use cert.max_weight_matching_certified in \<open>simp add: G_eq Mat_eq\<close>)

corollary no_perfect_matching_arrays:
  "<arrays_assn Fa Ta Wa La Rv * Sa \<mapsto>\<^sub>a S>
   hall_arrays n Fa Ta Wa La Rv Sa
   <\<lambda>r. arrays_assn Fa Ta Wa La Rv * Sa \<mapsto>\<^sub>a S * true * \<up>(r \<longrightarrow> (\<nexists>M. perfect_matching G M))>"
  by (rule ht_cons_post_prec[OF hall_arrays_rule]) (sep_auto dest: cert.hall_sound simp: G_eq)

end

end
