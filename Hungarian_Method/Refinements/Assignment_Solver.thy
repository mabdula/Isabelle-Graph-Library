theory Assignment_Solver
  imports
    Hungarian_CSR_Variants
    Matching_Certificate_Arrays
begin

provenance ai


section \<open>A Certifying Solver for the Assignment Problem\<close>

text \<open>The top level of a solver for minimum weight perfect matchings in bipartite graphs (the
      DIMACS assignment problem), in the pattern of the DIMACS min-cost flow solver: an untrusted
      oracle proposes an answer with a certificate, the certifier of
      \<open>Matching_Certificate_Arrays.thy\<close> checks it, and if the check fails, the Hungarian method
      of \<open>Hungarian_Method_CSR_Instantiation.thy\<close> solves the instance. The Hungarian method
      always starts from scratch: it has no warm start, so it ignores the oracle's answer.

      The input is given by the arrays of the left endpoints, the right endpoints and the weights
      of the edges, and by the arrays of the left and the right vertices. The answer is a flag
      and the set of the selected edges as a Boolean array over the edge positions.\<close>

subsection \<open>The Oracle's Answer\<close>

text \<open>An optimal matching (as edge positions) with a dual, a Hall violator, or nothing.\<close>

datatype 'n asn_answer = Asn_opt "nat array" "'n array" | Asn_infeas "nat array" | Asn_unknown

fun asn_answer_assn :: "'n::heap asn_answer \<Rightarrow> assn" where
  "asn_answer_assn (Asn_opt Ma Ya) = (\<exists>\<^sub>Ams ys. Ma \<mapsto>\<^sub>a ms * Ya \<mapsto>\<^sub>a ys)"
| "asn_answer_assn (Asn_infeas Sa) = (\<exists>\<^sub>AS. Sa \<mapsto>\<^sub>a S)"
| "asn_answer_assn Asn_unknown = emp"

subsection \<open>The Program\<close>

text \<open>Whether all elements of an array are in a set.\<close>

definition all_in_step :: "nat array \<Rightarrow> bool array \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool Heap" where
  "all_in_step La Cv i b = do { v \<leftarrow> Array.nth La i; c \<leftarrow> Array.nth Cv v; return (b \<and> c) }"

text \<open>Selecting the edges of a matching given by buddies.\<close>

definition sel_step :: "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> bool array \<Rightarrow> nat \<Rightarrow> unit \<Rightarrow>
    unit Heap" where
  "sel_step Fa Ta Mi Sel i _ = do {
     u \<leftarrow> Array.nth Fa i;
     v \<leftarrow> Array.nth Ta i;
     bu \<leftarrow> Array.nth Mi u;
     bv \<leftarrow> Array.nth Mi v;
     if bu = v \<or> bv = u then bool_array_set_insert_imp i Sel else return () }"

text \<open>Checking the oracle's answer.\<close>

definition asn_check ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> nat array \<Rightarrow>
   nat array \<Rightarrow> 'n asn_answer \<Rightarrow> bool Heap" where
  "asn_check n Fa Ta Wa La Rv a = (case a of
     Asn_opt Ma Ya \<Rightarrow> certify_arrays False True n Fa Ta Wa La Rv Ma Ya
   | Asn_infeas Sa \<Rightarrow> hall_arrays n Fa Ta Wa La Rv Sa
   | Asn_unknown \<Rightarrow> return False)"

text \<open>Reporting an accepted answer.\<close>

definition asn_accept :: "'n::heap asn_answer \<Rightarrow> bool array \<Rightarrow> (bool \<times> bool array) Heap" where
  "asn_accept a Sel = (case a of
     Asn_opt Ma Ya \<Rightarrow> do { k \<leftarrow> Array.len Ma; bool_array_set_insert_all Ma 0 k Sel; return (True, Sel) }
   | _ \<Rightarrow> return (False, Sel))"

text \<open>Reporting the result of the Hungarian method.\<close>

definition asn_select :: "result \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> bool array \<Rightarrow>
    (bool \<times> bool array) Heap" where
  "asn_select r Fa Ta Mi Sel = (if r = result.success then do {
       m \<leftarrow> Array.len Fa;
       fold_imp 0 m (sel_step Fa Ta Mi Sel) ();
       return (True, Sel) }
     else return (False, Sel))"

text \<open>The cleanup: the Hungarian method with the shortcut on until the end (the threshold is the
      number of left vertices) and at most two rematches per chain.\<close>

definition asn_cleanup ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> nat array \<Rightarrow>
   nat array \<Rightarrow> bool array \<Rightarrow> (bool \<times> bool array) Heap" where
  "asn_cleanup n Fa Ta Wa La Rv Sel = do {
     cL \<leftarrow> Array.len La;
     (r, Mi, _) \<leftarrow> hungarian_csr_run n cL 2 Fa Ta Wa La Rv;
     asn_select r Fa Ta Mi Sel }"

text \<open>Checking the oracle's answer and falling back on the Hungarian method.\<close>

definition asn_finish ::
  "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> nat array \<Rightarrow>
   nat array \<Rightarrow> 'n asn_answer \<Rightarrow> bool array \<Rightarrow> (bool \<times> bool array) Heap" where
  "asn_finish n Fa Ta Wa La Rv a Sel = do {
     c \<leftarrow> asn_check n Fa Ta Wa La Rv a;
     if c then asn_accept a Sel else asn_cleanup n Fa Ta Wa La Rv Sel }"

text \<open>Whether every vertex is on an edge.\<close>

definition asn_covered :: "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> bool Heap" where
  "asn_covered n Fa Ta La Rv = do {
     m \<leftarrow> Array.len Fa;
     cL \<leftarrow> Array.len La;
     cR \<leftarrow> Array.len Rv;
     Cv \<leftarrow> Array.new n False;
     bool_array_set_insert_all Fa 0 m Cv;
     bool_array_set_insert_all Ta 0 m Cv;
     okL \<leftarrow> fold_imp 0 cL (all_in_step La Cv) True;
     okR \<leftarrow> fold_imp 0 cR (all_in_step Rv Cv) True;
     return (okL \<and> okR) }"

text \<open>The whole program. Every vertex must be on an edge; otherwise there is no perfect matching
      and the oracle is not asked.\<close>

definition asn_solve ::
  "(nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n asn_answer Heap) \<Rightarrow>
   nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n::{linordered_idom, heap} array \<Rightarrow> nat array \<Rightarrow>
   nat array \<Rightarrow> (bool \<times> bool array) Heap" where
  "asn_solve orc n Fa Ta Wa La Rv = do {
     ok \<leftarrow> asn_covered n Fa Ta La Rv;
     m \<leftarrow> Array.len Fa;
     Sel \<leftarrow> Array.new m False;
     if ok then do {
       a \<leftarrow> orc n Fa Ta Wa La Rv;
       asn_finish n Fa Ta Wa La Rv a Sel }
     else return (False, Sel) }"

subsection \<open>The Loops\<close>

lemma all_in_step_rule:
  "\<lbrakk>set xs \<subseteq> {..<n}; j < length xs\<rbrakk> \<Longrightarrow>
   <La \<mapsto>\<^sub>a xs * bool_array_set_assn n S Cv * \<up>(b \<longleftrightarrow> set (take j xs) \<subseteq> S)>
   all_in_step La Cv j b
   <\<lambda>b. La \<mapsto>\<^sub>a xs * bool_array_set_assn n S Cv * \<up>(b \<longleftrightarrow> set (take (Suc j) xs) \<subseteq> S)>"
  unfolding all_in_step_def
  by (sep_auto heap: bool_array_set_memb_rule simp: take_Suc_conv_app_nth nth_below)

lemma all_in_rule:
  "set xs \<subseteq> {..<n} \<Longrightarrow>
   <La \<mapsto>\<^sub>a xs * bool_array_set_assn n S Cv> fold_imp 0 (length xs) (all_in_step La Cv) True
   <\<lambda>b. La \<mapsto>\<^sub>a xs * bool_array_set_assn n S Cv * \<up>(b \<longleftrightarrow> set xs \<subseteq> S)>"
  using fold_imp_rule[of 0 "length xs"
          "\<lambda>j b. La \<mapsto>\<^sub>a xs * bool_array_set_assn n S Cv * \<up>(b \<longleftrightarrow> set (take j xs) \<subseteq> S)"
          "all_in_step La Cv" True]
        all_in_step_rule
  by simp

lemma sel_step_rule:
  "\<lbrakk>set fs \<subseteq> {..<n}; set ts \<subseteq> {..<n}; length ts = length fs; j < length fs\<rbrakk> \<Longrightarrow>
   <Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * array_fun_assn n M Mi *
    bool_array_set_assn (length fs) {i. i < j \<and> (M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i)} Sel>
   sel_step Fa Ta Mi Sel j u
   <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * array_fun_assn n M Mi *
        bool_array_set_assn (length fs)
          {i. i < Suc j \<and> (M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i)} Sel>"
  unfolding sel_step_def bool_array_set_insert_imp_def
  by (sep_auto heap: array_fun_lookup_rule bool_array_set_upd_rule simp: Collect_less_Suc nth_below)

lemma sel_rule:
  "\<lbrakk>set fs \<subseteq> {..<n}; set ts \<subseteq> {..<n}; length ts = length fs\<rbrakk> \<Longrightarrow>
   <Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * array_fun_assn n M Mi * bool_array_set_assn (length fs) {} Sel>
   fold_imp 0 (length fs) (sel_step Fa Ta Mi Sel) ()
   <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * array_fun_assn n M Mi *
        bool_array_set_assn (length fs)
          {i. i < length fs \<and> (M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i)} Sel>"
  using fold_imp_rule[of 0 "length fs"
          "\<lambda>j _. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * array_fun_assn n M Mi *
                 bool_array_set_assn (length fs)
                   {i. i < j \<and> (M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i)} Sel"
          "sel_step Fa Ta Mi Sel" "()"]
        sel_step_rule
  by simp

lemma insert_all_rule:
  "\<lbrakk>set xs \<subseteq> {..<n}; S \<subseteq> {..<n}; m = length xs\<rbrakk> \<Longrightarrow>
   <Xa \<mapsto>\<^sub>a xs * bool_array_set_assn n S Cv> bool_array_set_insert_all Xa 0 m Cv
   <\<lambda>_. Xa \<mapsto>\<^sub>a xs * bool_array_set_assn n (S \<union> set xs) Cv>"
  using bool_array_set_insert_all_rule[of 0 xs n S Xa Cv]
  by simp

subsection \<open>The Input\<close>

text \<open>What the parser guarantees: the endpoints of the edges are left and right vertices, the
      sides are disjoint and below @{term n}, and there are no parallel edges. Unlike in
      @{locale bp_cert_input} and @{locale hungarian_csr_input}, a vertex need not be on an edge:
      that is what the program checks first.\<close>

locale asn_input = real_embedding h
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
    and fs_ls: "set fs \<subseteq> set ls"
    and ts_rs: "set ts \<subseteq> set rs"
    and sides_disjoint: "set ls \<inter> set rs = {}"
    and verts_below: "set ls \<union> set rs \<subseteq> {..<n}"
    and no_parallel: "distinct (zip fs ts)"
begin

text \<open>The graph, its weights, the matching of a set of edge positions, and the specification of
      the result.\<close>

abbreviation "Gi \<equiv> {{fs ! i, ts ! i} | i. i < length fs}"

abbreviation "wi \<equiv> \<lambda>d. h (ws ! (THE i. i < length fs \<and> {fs ! i, ts ! i} = d))"

abbreviation "Msel S \<equiv> {{fs ! i, ts ! i} | i. i \<in> S}"

abbreviation "covered \<equiv> set ls \<subseteq> set fs \<union> set ts \<and> set rs \<subseteq> set fs \<union> set ts"

definition "asn_post b S =
  ((b \<longleftrightarrow> Vs Gi = set ls \<union> set rs \<and> (\<exists>M. perfect_matching Gi M)) \<and>
   (b \<longrightarrow> min_weight_perfect_matching Gi wi (Msel S)))"

abbreviation "arrays_assn Fa Ta Wa La Rv \<equiv>
  Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs"

lemma fs_below: "set fs \<subseteq> {..<n}" and ts_below: "set ts \<subseteq> {..<n}"
  and ls_below: "set ls \<subseteq> {..<n}" and rs_below: "set rs \<subseteq> {..<n}"
  using fs_ls ts_rs verts_below
  by auto

lemma edge_below: "i < length fs \<Longrightarrow> fs ! i < n" "i < length fs \<Longrightarrow> ts ! i < n"
  using fs_below ts_below ts_length
  by (simp_all add: nth_below)

lemma Vs_Gi: "Vs Gi = set fs \<union> set ts"
  unfolding Vs_def
  using ts_length
  by (auto simp: in_set_conv_nth; blast)

lemma covered_iff: "covered \<longleftrightarrow> Vs Gi = set ls \<union> set rs"
  using fs_ls ts_rs
  by (auto simp: Vs_Gi)

lemma covered_rule:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs> asn_covered n Fa Ta La Rv
   <\<lambda>b. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs * true * \<up>(b \<longleftrightarrow> covered)>"
  unfolding asn_covered_def
  using fs_below ts_below ts_length
  by (sep_auto heap: bool_array_set_insert_all_new[OF fs_below] insert_all_rule
                     all_in_rule[OF ls_below] all_in_rule[OF rs_below])

end

text \<open>If every vertex is on an edge, the input is one of the certifier and of the Hungarian
      method.\<close>

locale asn_cov = asn_input +
  assumes cov: "set ls \<subseteq> set fs \<union> set ts \<and> set rs \<subseteq> set fs \<union> set ts"
begin

lemma fs_eq: "set fs = set ls" and ts_eq: "set ts = set rs"
  using cov fs_ls ts_rs sides_disjoint
  by auto

sublocale bp: bp_cert_input h n fs ts ws ls rs
  by (intro bp_cert_input.intro real_embedding_axioms bp_cert_input_axioms.intro)
     (simp_all add: ts_length ws_length ls_distinct rs_distinct fs_eq ts_eq sides_disjoint
                    verts_below[unfolded Un_subset_iff] no_parallel)

sublocale hi: hungarian_csr_input h n fs ts ws ls rs "length ls" 2
  by (intro hungarian_csr_input.intro real_embedding_axioms hungarian_csr_input_axioms.intro)
     (simp_all add: ts_length ws_length ls_distinct rs_distinct fs_eq ts_eq sides_disjoint
                    verts_below[unfolded Un_subset_iff] no_parallel)

lemma bp_G: "bp.G = Gi" and hi_G: "hi.G = Gi"
  by (simp_all add: bp.G_def hi.G_def)

lemma bp_wG: "bp.cert.wG = wi"
  by (simp add: fun_eq_iff bp.cert.wG_def bp.cert.cedge_def)

lemma wi_edge: "i < length fs \<Longrightarrow> wi {fs ! i, ts ! i} = h (ws ! i)"
  using bp.wG_eq[of i]
  by (simp add: bp_wG)

lemma hi_G_edge: "i < length fs \<Longrightarrow> {fs ! i, ts ! i} \<in> hi.G"
  by (auto simp: hi_G)

lemma hi_wfun: "e \<in> Gi \<Longrightarrow> hi.wfun e = wi e"
  by (auto simp: hi.wfun_eq hi_G_edge hi.ecost_edge wi_edge)

end

context asn_cov
begin

subsection \<open>The Cleanup\<close>

text \<open>The edges selected from the buddies of the Hungarian method are its matching.\<close>

lemma aug_M_eq: "aug_csr.\<M> n M = {{x, M x} | x. M x \<noteq> n}"
  by (auto simp: aug_csr.\<M>_def aug_csr.buddy_lookup_def array_fun_lookup_def upairs_of_map_def
           split: if_splits)

lemma aug_M_memI: "M x \<noteq> n \<Longrightarrow> {x, M x} \<in> aug_csr.\<M> n M"
  by (auto simp: aug_M_eq)

lemma buddy_sel:
  assumes "aug_csr.\<M> n M \<subseteq> Gi"
  shows "{{fs ! i, ts ! i} | i. i < length fs \<and> (M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i)} =
         aug_csr.\<M> n M"
proof(intro equalityI subsetI)
  fix e
  assume "e \<in> {{fs ! i, ts ! i} | i. i < length fs \<and> (M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i)}"
  then obtain i
    where "i < length fs" "e = {fs ! i, ts ! i}" "M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i"
    by blast
  thus "e \<in> aug_csr.\<M> n M"
    using aug_M_memI[of M "fs ! i"] aug_M_memI[of M "ts ! i"] edge_below[of i]
    by (auto simp: insert_commute)
next
  fix e
  assume "e \<in> aug_csr.\<M> n M"
  moreover obtain i where "i < length fs" "e = {fs ! i, ts ! i}"
    using assms calculation
    by blast
  ultimately show
    "e \<in> {{fs ! i, ts ! i} | i. i < length fs \<and> (M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i)}"
    by (auto simp: aug_M_eq doubleton_eq_iff)
qed

lemma hungarian_post:
  assumes "min_weight_perfect_matching hi.G hi.wfun (aug_csr.\<M> n M)"
  shows "asn_post True {i. i < length fs \<and> (M (fs ! i) = ts ! i \<or> M (ts ! i) = fs ! i)}"
proof-
  have "min_weight_perfect_matching Gi wi (aug_csr.\<M> n M)"
    using assms[unfolded hi_G]
    by (rule min_weight_perfect_matching_cong) (rule hi_wfun)
  moreover have "aug_csr.\<M> n M \<subseteq> Gi"
    using calculation
    by (simp add: min_weight_perfect_matching_def perfect_matching_def)
  ultimately show ?thesis
    using cov covered_iff
    by (auto simp: asn_post_def buddy_sel min_weight_perfect_matching_def)
qed

lemma failure_post: "\<nexists>M. perfect_matching hi.G M \<Longrightarrow> asn_post False S"
  by (simp add: asn_post_def hi_G)

lemma select_rule:
  "min_weight_perfect_matching hi.G hi.wfun (aug_csr.\<M> n M) \<Longrightarrow>
   <Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * array_fun_assn n M Mi * bool_array_set_assn (length fs) {} Sel>
   fold_imp 0 (length fs) (sel_step Fa Ta Mi Sel) ()
   <\<lambda>_. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * array_fun_assn n M Mi *
        (\<exists>\<^sub>AS. bool_array_set_assn (length fs) S Sel * \<up>(asn_post True S))>"
  using fs_below ts_below ts_length
  by (sep_auto heap: sel_rule simp: hungarian_post)

lemma asn_select_rule:
  assumes "(r = result.success \<and> min_weight_perfect_matching hi.G hi.wfun (aug_csr.\<M> n M)) \<or>
           (r = result.failure \<and> (\<nexists>M'. perfect_matching hi.G M'))"
  shows "<arrays_assn Fa Ta Wa La Rv * array_fun_assn n M Mi *
          bool_array_set_assn (length fs) {} Sel>
         asn_select r Fa Ta Mi Sel
         <\<lambda>(b, Sel'). arrays_assn Fa Ta Wa La Rv *
           (\<exists>\<^sub>AS. bool_array_set_assn (length fs) S Sel' * \<up>(asn_post b S)) * true>"
proof(cases "r = result.success")
  case True
  thus ?thesis
    using assms
    unfolding asn_select_def
    by (sep_auto heap: select_rule)
next
  case False
  thus ?thesis
    using assms
    unfolding asn_select_def
    by (sep_auto simp: failure_post)
qed

lemma cleanup_rule:
  "<arrays_assn Fa Ta Wa La Rv * bool_array_set_assn (length fs) {} Sel>
   asn_cleanup n Fa Ta Wa La Rv Sel
   <\<lambda>(b, Sel'). arrays_assn Fa Ta Wa La Rv *
     (\<exists>\<^sub>AS. bool_array_set_assn (length fs) S Sel' * \<up>(asn_post b S)) * true>"
  unfolding asn_cleanup_def
  by (sep_auto heap: hi.hungarian_csr_run_correct asn_select_rule)

subsection \<open>Checking the Oracle's Answer\<close>

lemma certified_below: "bp.cert.certify False True ms ys \<Longrightarrow> set ms \<subseteq> {..<length fs}"
  by (auto simp: bp.cert.certify_def bp.cert.certify_sh_def split: prod.splits
           dest!: bp.cert.match_list_props)

lemma certified_post: "bp.cert.certify False True ms ys \<Longrightarrow> asn_post True (set ms)"
  using bp.cert.min_weight_perfect_certified[of ms ys] cov covered_iff
  by (auto simp: asn_post_def bp.G_eq bp.Mat_eq bp_G bp_wG min_weight_perfect_matching_def)

lemma hall_post: "bp.cert.hall_check S \<Longrightarrow> asn_post False S'"
  using bp.cert.hall_sound[of S]
  by (simp add: asn_post_def bp.G_eq bp_G)

lemma finish_rule:
  "<arrays_assn Fa Ta Wa La Rv * asn_answer_assn a * bool_array_set_assn (length fs) {} Sel>
   asn_finish n Fa Ta Wa La Rv a Sel
   <\<lambda>(b, Sel'). arrays_assn Fa Ta Wa La Rv *
     (\<exists>\<^sub>AS. bool_array_set_assn (length fs) S Sel' * \<up>(asn_post b S)) * true>"
proof(cases a)
  case (Asn_opt Ma Ya)
  show ?thesis
    unfolding Asn_opt asn_finish_def asn_check_def asn_accept_def
    by (sep_auto heap: bp.certify_arrays_rule cleanup_rule insert_all_rule
                 dest: certified_below certified_post)
next
  case (Asn_infeas Sa)
  show ?thesis
    unfolding Asn_infeas asn_finish_def asn_check_def asn_accept_def
    by (sep_auto heap: bp.hall_arrays_rule cleanup_rule dest: hall_post)
next
  case Asn_unknown
  show ?thesis
    unfolding Asn_unknown asn_finish_def asn_check_def asn_accept_def
    by (sep_auto heap: cleanup_rule)
qed

end

subsection \<open>Correctness\<close>

context asn_input
begin

text \<open>The only assumption on the oracle: it leaves the input alone and returns fresh arrays.\<close>

lemma asn_solve_rule:
  assumes "<arrays_assn Fa Ta Wa La Rv> orc n Fa Ta Wa La Rv
           <\<lambda>a. arrays_assn Fa Ta Wa La Rv * asn_answer_assn a>"
  shows "<arrays_assn Fa Ta Wa La Rv> asn_solve orc n Fa Ta Wa La Rv
         <\<lambda>(b, Sel). arrays_assn Fa Ta Wa La Rv *
           (\<exists>\<^sub>AS. bool_array_set_assn (length fs) S Sel * \<up>(asn_post b S)) * true>"
proof(cases covered)
  case True
  interpret c: asn_cov h n fs ts ws ls rs
    by unfold_locales (rule True)
  show ?thesis
    unfolding asn_solve_def
    by (sep_auto heap: covered_rule assms c.finish_rule[unfolded bool_array_set_assn_replicate]
                 simp: True)
next
  case False
  hence "asn_post False {}"
    unfolding asn_post_def covered_iff[symmetric]
    by blast
  thus ?thesis
    unfolding asn_solve_def
    by (sep_auto heap: covered_rule simp: False bool_array_set_assn_replicate[symmetric])
qed

text \<open>The selected edges as read from the array.\<close>

lemma Msel_map:
  "S \<subseteq> {..<length fs} \<Longrightarrow>
   {{fs ! i, ts ! i} | i. i < length fs \<and> map (\<lambda>i. i \<in> S) [0..<length fs] ! i} = Msel S"
  by (auto 4 4)

end

subsection \<open>The Program on Integers\<close>

text \<open>The program with integer weights, as exported. Its correctness is stated without any
      locale: the assumptions on the input are the ones the DIMACS parser establishes, and the
      only assumption on the oracle is that it leaves the input alone. On \<open>True\<close>, the
      selected edges are a minimum weight perfect matching; the flag is \<open>False\<close> exactly when
      some vertex has no perfect partner, i.e. when a vertex is on no edge or there is no perfect
      matching.\<close>

definition asn_solve_int ::
  "(nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int asn_answer Heap) \<Rightarrow>
   nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow>
   (bool \<times> bool array) Heap" where
  "asn_solve_int = asn_solve"

lemma asn_solve_int_correct:
  fixes ws :: "int list" and fs ts ls rs :: "nat list"
  defines "G \<equiv> {{fs ! i, ts ! i} | i. i < length fs}"
    and "w \<equiv> \<lambda>d. real_of_int (ws ! (THE i. i < length fs \<and> {fs ! i, ts ! i} = d))"
  assumes "length ts = length fs" "length ws = length fs" "distinct ls" "distinct rs"
    and "set fs \<subseteq> set ls" "set ts \<subseteq> set rs" "set ls \<inter> set rs = {}"
    and "set ls \<union> set rs \<subseteq> {..<n}" "distinct (zip fs ts)"
    and "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
          orc n Fa Ta Wa La Rv
         <\<lambda>a. Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
             asn_answer_assn a>"
  shows "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs>
          asn_solve_int orc n Fa Ta Wa La Rv
         <\<lambda>(b, Sel). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Wa \<mapsto>\<^sub>a ws * La \<mapsto>\<^sub>a ls * Rv \<mapsto>\<^sub>a rs *
           (\<exists>\<^sub>Asel. Sel \<mapsto>\<^sub>a sel * \<up>(length sel = length fs \<and>
              (b \<longleftrightarrow> Vs G = set ls \<union> set rs \<and> (\<exists>M. perfect_matching G M)) \<and>
              (b \<longrightarrow> min_weight_perfect_matching G w
                       {{fs ! i, ts ! i} | i. i < length fs \<and> sel ! i}))) * true>"
proof-
  interpret asn_input "of_int :: int \<Rightarrow> real" n fs ts ws ls rs
    by (intro asn_input.intro asn_input_axioms.intro real_embedding.intro) (use assms in simp_all)
  show ?thesis
    unfolding asn_solve_int_def
    by (sep_auto heap: asn_solve_rule[of Fa Ta Wa La Rv orc, OF assms(12)]
                 simp: bool_array_set_assn_def asn_post_def Msel_map G_def w_def)
qed

end
