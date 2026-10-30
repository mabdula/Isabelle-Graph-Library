theory Matching_Certificate_Example
  imports Matching_Certificate_Arrays
begin

provenance ai


section \<open>Examples for the Certificate Checkers\<close>

text \<open>The checkers with integer weights. They do not depend on any solver: the candidate
      solutions and the certificates below are given by hand.\<close>

definition \<^marker>\<open>provenance ai_human\<close> certify_arrays_int :: "bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow>
    nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> bool Heap" where
  "certify_arrays_int = certify_arrays"

definition \<^marker>\<open>provenance ai_human\<close> hall_arrays_int :: "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow>
    nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> bool Heap" where
  "hall_arrays_int = hall_arrays"

text \<open>Programs that build the arrays from lists and run the checkers.\<close>

definition \<^marker>\<open>provenance ai_human\<close> run_certify :: "bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow> bool Heap" where
  "run_certify neg perfect n fs ts ws ls rs ms ys = do {
     Fa \<leftarrow> Array.of_list fs;
     Ta \<leftarrow> Array.of_list ts;
     Wa \<leftarrow> Array.of_list ws;
     La \<leftarrow> Array.of_list ls;
     Rv \<leftarrow> Array.of_list rs;
     Ma \<leftarrow> Array.of_list ms;
     Ya \<leftarrow> Array.of_list ys;
     certify_arrays_int neg perfect n Fa Ta Wa La Rv Ma Ya }"

definition \<^marker>\<open>provenance ai_human\<close> run_hall :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool Heap" where
  "run_hall n fs ts ws ls rs S = do {
     Fa \<leftarrow> Array.of_list fs;
     Ta \<leftarrow> Array.of_list ts;
     Wa \<leftarrow> Array.of_list ws;
     La \<leftarrow> Array.of_list ls;
     Rv \<leftarrow> Array.of_list rs;
     Sa \<leftarrow> Array.of_list S;
     hall_arrays_int n Fa Ta Wa La Rv Sa }"

definition "check_cert neg perfect n fs ts ws ls rs ms ys = do {
   r \<leftarrow> run_certify neg perfect n fs ts ws ls rs ms ys;
   return (ms, ys, r) }"

definition "check_hall n fs ts ws ls rs S = do {
   r \<leftarrow> run_hall n fs ts ws ls rs S;
   return (S, r) }"

subsection \<open>A Graph with a Perfect Matching\<close>

text \<open>Left vertices @{text "0, 2, 4"}, right vertices @{text "1, 3, 5"}, and the edges
      @{text "0: (0, 1, 4), 1: (0, 3, -1), 2: (2, 1, -2), 3: (2, 5, 6), 4: (4, 3, 3)"} and
      @{text "5: (4, 5, -5)"}. The perfect matchings are @{text "{0, 3, 4}"} (weight @{text 13}) and
      @{text "{1, 2, 5}"} (weight @{text "-8"}). The latter is also the minimum weight matching, the
      former the maximum weight matching.\<close>

definition "fsA = [0::nat, 0, 2, 2, 4, 4]"
definition "tsA = [1::nat, 3, 1, 5, 3, 5]"
definition "wsA = [4::int, -1, -2, 6, 3, -5]"
definition "lsA = [0::nat, 2, 4]"
definition "rsA = [1::nat, 3, 5]"

text \<open>The certificates. A candidate is a list of edge names, a dual a list with one potential per
      vertex @{text "0, ..., 5"}. For the minimum: @{text "y u + y v \<le> w"} on all edges, with
      equality on the matching @{text "{1, 2, 5}"}. For the maximum: the same for the negated
      weights and the matching @{text "{0, 3, 4}"}. Both duals are non-positive and all vertices are
      matched, so they also certify the minimum and the maximum weight matching.\<close>

definition "msA_min = [1::nat, 2, 5]"
definition "ysA_min = [0::int, -2, 0, -1, 0, -5]"
definition "msA_max = [0::nat, 3, 4]"
definition "ysA_max = [0::int, -4, 0, -3, 0, -6]"

text \<open>Wrong certificates: a perturbed dual (edge @{text 5} is violated), a repeated edge name, an
      edge name out of range.\<close>

definition "ysA_bad = [0::int, -2, 0, -1, 0, -4]"
definition "msA_dup = [1::nat, 1, 2]"
definition "msA_range = [1::nat, 2, 9]"

definition "certA_check neg perfect ms ys = check_cert neg perfect 6 fsA tsA wsA lsA rsA ms ys"

text \<open>The programs return the candidate and the certificate together with the verdict.\<close>

definition \<^marker>\<open>provenance ai_human\<close> exA :: "(nat list \<times> int list \<times> bool) list Heap" where
  "exA = do {
     a \<leftarrow> certA_check False True msA_min ysA_min;
     b \<leftarrow> certA_check True True msA_max ysA_max;
     c \<leftarrow> certA_check False False msA_min ysA_min;
     d \<leftarrow> certA_check True False msA_max ysA_max;
     return [a, b, c, d] }"

text \<open>Rejected: the wrong certificates, and a maximum weight perfect matching claimed to be of
      minimum weight.\<close>

definition \<^marker>\<open>provenance ai_human\<close> exA_neg :: "(nat list \<times> int list \<times> bool) list Heap" where
  "exA_neg = do {
     a \<leftarrow> certA_check False True msA_min ysA_bad;
     b \<leftarrow> certA_check False True msA_dup ysA_min;
     c \<leftarrow> certA_check False True msA_range ysA_min;
     d \<leftarrow> certA_check False True msA_max ysA_max;
     return [a, b, c, d] }"

ML_val \<open>@{code exA} ()\<close>
ML_val \<open>@{code exA_neg} ()\<close>

subsection \<open>A Graph without a Perfect Matching\<close>

text \<open>Left vertices @{text "0, 2, 4"}, right vertices @{text "1, 3, 5"}, and the edges
      @{text "0: (0, 1, 1), 1: (2, 1, 3), 2: (4, 3, 2), 3: (4, 5, 1)"}. The left vertices
      @{text "0, 2"} have the single neighbour @{text 1}, which violates Hall's condition. The
      maximum weight matching is @{text "{1, 2}"} (weight @{text 5}); the vertices @{text 0} and
      @{text 5} stay unmatched and get the potential @{text 0}.\<close>

definition "fsB = [0::nat, 2, 4, 4]"
definition "tsB = [1::nat, 1, 3, 5]"
definition "wsB = [1::int, 3, 2, 1]"
definition "lsB = [0::nat, 2, 4]"
definition "rsB = [1::nat, 3, 5]"

text \<open>The certificates. A Hall violator is a list of left vertices; repetitions are allowed.\<close>

definition "hallB = [0::nat, 2]"
definition "hallB_dup = [0::nat, 2, 0]"

text \<open>The maximum weight matching @{text "{1, 2}"} and its dual for the negated weights:
      non-positive, @{text "y u + y v \<le> - w"} on all edges, tight on the matching, and zero on the
      unmatched vertices @{text 0} and @{text 5}.\<close>

definition "msB_max = [1::nat, 2]"
definition "ysB_max = [0::int, -1, -2, -1, -1, 0]"

text \<open>Rejected: sets satisfying Hall's condition (@{text "N({0}) = {1}"},
      @{text "N({0, 4}) = {1, 3, 5}"}).\<close>

definition "hallB_bad1 = [0::nat]"
definition "hallB_bad2 = [0::nat, 4]"

definition "hallB_check S = check_hall 6 fsB tsB wsB lsB rsB S"
definition "certB_check neg perfect ms ys = check_cert neg perfect 6 fsB tsB wsB lsB rsB ms ys"

definition \<^marker>\<open>provenance ai_human\<close> exB_hall :: "(nat list \<times> bool) list Heap" where
  "exB_hall = do {
     a \<leftarrow> hallB_check hallB;
     b \<leftarrow> hallB_check hallB_dup;
     c \<leftarrow> hallB_check hallB_bad1;
     d \<leftarrow> hallB_check hallB_bad2;
     return [a, b, c, d] }"

text \<open>The maximum weight matching is accepted, but not as a maximum weight perfect matching.\<close>

definition \<^marker>\<open>provenance ai_human\<close> exB_max :: "(nat list \<times> int list \<times> bool) list Heap" where
  "exB_max = do {
     a \<leftarrow> certB_check True False msB_max ysB_max;
     b \<leftarrow> certB_check True True msB_max ysB_max;
     return [a, b] }"

text \<open>An unbalanced graph has no perfect matching; the empty violator suffices.\<close>

definition "hallC = ([] :: nat list)"

definition \<^marker>\<open>provenance ai_human\<close> exC :: "(nat list \<times> bool) Heap" where
  "exC = check_hall 3 [0, 2] [1, 1] [1, 1] [0, 2] [1] hallC"

ML_val \<open>@{code exB_hall} ()\<close>
ML_val \<open>@{code exB_max} ()\<close>
ML_val \<open>@{code exC} ()\<close>

subsection \<open>Extremal Weight Maximum Cardinality Matchings\<close>

definition \<^marker>\<open>provenance ai_human\<close> certify_mc_arrays_int :: "bool \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow>
    nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int \<Rightarrow> nat array \<Rightarrow> bool Heap" where
  "certify_mc_arrays_int = certify_mc_arrays"

definition \<^marker>\<open>provenance ai_human\<close> run_certify_mc :: "bool \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> nat list \<Rightarrow> bool Heap" where
  "run_certify_mc neg n fs ts ws ls rs ms ys t S = do {
     Fa \<leftarrow> Array.of_list fs;
     Ta \<leftarrow> Array.of_list ts;
     Wa \<leftarrow> Array.of_list ws;
     La \<leftarrow> Array.of_list ls;
     Rv \<leftarrow> Array.of_list rs;
     Ma \<leftarrow> Array.of_list ms;
     Ya \<leftarrow> Array.of_list ys;
     Sa \<leftarrow> Array.of_list S;
     certify_mc_arrays_int neg n Fa Ta Wa La Rv Ma Ya t Sa }"

definition "check_mc neg n fs ts ws ls rs ms ys t S = do {
   r \<leftarrow> run_certify_mc neg n fs ts ws ls rs ms ys t S;
   return (ms, ys, t, S, r) }"

text \<open>The certificate is a dual for the weights shifted by @{text "- t"} (non-positive, zero on
      unmatched vertices) and a set @{text S} of left vertices with
      @{text "|L| - |S| + |N(S)| \<le> |ms|"}. On graph B, the matchings of maximum cardinality have two
      edges; @{text "{0, 3}"} (weight @{text 2}) is of minimum and @{text "{1, 2}"} (weight
      @{text 5}) of maximum weight among them. The set @{text "S = {0, 2}"} has the single neighbour
      @{text 1}. For the minimum, @{text "t = 1"} and the dual is zero; for the maximum (negated
      weights), @{text "t = -2"} and the dual is @{text "-1"} at vertex @{text 1}.\<close>

definition "msB_mc_min = [0::nat, 3]"
definition "ysB_mc_min = [0::int, 0, 0, 0, 0, 0]"
definition "msB_mc_max = [1::nat, 2]"
definition "ysB_mc_max = [0::int, -1, 0, 0, 0, 0]"
definition "defB = [0::nat, 2]"

definition "mcA_check neg ms ys t S = check_mc neg 6 fsA tsA wsA lsA rsA ms ys t S"
definition "mcB_check neg ms ys t S = check_mc neg 6 fsB tsB wsB lsB rsB ms ys t S"

text \<open>Accepted: the two certificates on graph B, and on graph A (perfect) the certificates of
      the perfect matchings with @{text "t = 0"} and @{text "S = {}"}.\<close>

definition \<^marker>\<open>provenance ai_human\<close> exB_mc :: "(nat list \<times> int list \<times> int \<times> nat list \<times> bool) list Heap" where
  "exB_mc = do {
     a \<leftarrow> mcB_check False msB_mc_min ysB_mc_min 1 defB;
     b \<leftarrow> mcB_check True msB_mc_max ysB_mc_max (-2) defB;
     c \<leftarrow> mcA_check False msA_min ysA_min 0 [];
     d \<leftarrow> mcA_check True msA_max ysA_max 0 [];
     return [a, b, c, d] }"

text \<open>Rejected: a set @{text S} that does not certify the cardinality, the unshifted dual (edge
      @{text 0} is not tight), a matching that is not of maximum cardinality, and the minimum
      claimed to be the maximum.\<close>

definition \<^marker>\<open>provenance ai_human\<close> exB_mc_neg :: "(nat list \<times> int list \<times> int \<times> nat list \<times> bool) list Heap" where
  "exB_mc_neg = do {
     a \<leftarrow> mcB_check False msB_mc_min ysB_mc_min 1 [0];
     b \<leftarrow> mcB_check False msB_mc_min ysB_mc_min 0 defB;
     c \<leftarrow> mcB_check False [0] ysB_mc_min 1 defB;
     d \<leftarrow> mcB_check True msB_mc_min ysB_mc_max (-2) defB;
     return [a, b, c, d] }"

ML_val \<open>@{code exB_mc} ()\<close>
ML_val \<open>@{code exB_mc_neg} ()\<close>

subsection \<open>Exported SML Code\<close>

export_code
  certify_arrays_int hall_arrays_int run_certify run_hall check_cert check_hall
  exA exA_neg exB_hall exB_max exC
  certify_mc_arrays_int run_certify_mc check_mc exB_mc exB_mc_neg
  nat_of_integer integer_of_nat int_of_integer integer_of_int
  in SML_imp module_name Matching_Certificate file_prefix Matching_Certificate_imperative

subsection \<open>Correctness\<close>

interpretation int_embedding: real_embedding "of_int :: int \<Rightarrow> real"
  by unfold_locales (simp_all add: of_int_less_iff)

interpretation A: bp_cert_input "of_int :: int \<Rightarrow> real" 6 fsA tsA wsA lsA rsA
  by (intro bp_cert_input.intro int_embedding.real_embedding_axioms bp_cert_input_axioms.intro)
     (auto simp: fsA_def tsA_def wsA_def lsA_def rsA_def)

interpretation B: bp_cert_input "of_int :: int \<Rightarrow> real" 6 fsB tsB wsB lsB rsB
  by (intro bp_cert_input.intro int_embedding.real_embedding_axioms bp_cert_input_axioms.intro)
     (auto simp: fsB_def tsB_def wsB_def lsB_def rsB_def)

text \<open>Hence, whenever the checkers accept on these instances, the candidates are optimal, or there
      is no perfect matching.\<close>

thm A.min_weight_perfect_matching_arrays A.max_weight_perfect_matching_arrays
    A.min_weight_matching_arrays A.max_weight_matching_arrays B.no_perfect_matching_arrays

end
