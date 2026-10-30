theory Hungarian_CSR_Example
  imports
    Hungarian_CSR_Variants
begin

provenance ai


section \<open>The Example of  \<open>Hungarian_Example.thy\<close> with Integer Weights\<close>

text \<open>The graph of  \<open>Hungarian_Example.thy\<close>, with the weights multiplied by 1000 and
      rounded. The CSR instantiation does not admit parallel edges, so of the two copies of the
      edge \<open>(2, 9)\<close> only the one that the example's map keeps (weight \<open>100\<close>) is taken.\<close>

definition "edges_and_costs_int = [(0::nat, 1::nat, 1000::int), (0, 3, -10000),
  (0, 5, 667), (0, 7, 11), (2, 5, -12000), (2, 9, 100000), (2, 1, 2500), (4, 5, 2143),
  (4, 3, -1300), (4, 7, 2400),
  (6, 1, 1911), (6, 9, 200000), (8, 9, 10000000), (8, 1, 6200), (0, 9, -100000),
  (2, 7, -100000), (2, 3, -40000), (4, 9, -100000)]"

definition "fs_ex = map fst edges_and_costs_int"
definition "ts_ex = map (fst o snd) edges_and_costs_int"
definition "ws_ex = map (snd o snd) edges_and_costs_int"
definition "ls_ex = [0::nat, 2, 4, 6, 8]"
definition "rs_ex = [1::nat, 3, 5, 7, 9]"
definition "n_ex = (10::nat)"
definition "\<theta> = 10"
definition "cap_ex = (3::nat)"

subsection \<open>Perfect Matchings\<close>

text \<open>The program allocates the input arrays, runs the Hungarian method and reads off the matched
      pairs \<open>(l, r)\<close> with \<open>l\<close> left, and the potential of every vertex.\<close>

definition hungarian_csr_example :: "(result \<times> (nat \<times> nat) list \<times> int list) Heap" where
  "hungarian_csr_example = do {
     Fa \<leftarrow> Array.of_list fs_ex;
     Ta \<leftarrow> Array.of_list ts_ex;
     Wa \<leftarrow> Array.of_list ws_ex;
     La \<leftarrow> Array.of_list ls_ex;
     Rv \<leftarrow> Array.of_list rs_ex;
     (r, Mi, Pti) \<leftarrow> hungarian_csr_run_int n_ex \<theta> cap_ex Fa Ta Wa La Rv;
     M \<leftarrow> Array.freeze Mi;
     P \<leftarrow> Array.freeze Pti;
     return (r, [(u, M ! u). u \<leftarrow> ls_ex, M ! u \<noteq> n_ex], P) }"

definition hungarian_csr_max_perfect_example :: "(result \<times> (nat \<times> nat) list) Heap" where
  "hungarian_csr_max_perfect_example = do {
     Fa \<leftarrow> Array.of_list fs_ex;
     Ta \<leftarrow> Array.of_list ts_ex;
     Wa \<leftarrow> Array.of_list ws_ex;
     La \<leftarrow> Array.of_list ls_ex;
     Rv \<leftarrow> Array.of_list rs_ex;
     (r, Mi, Pti) \<leftarrow> hungarian_csr_max_perfect_run_int n_ex \<theta> cap_ex Fa Ta Wa La Rv;
     M \<leftarrow> Array.freeze Mi;
     return (r, [(u, M ! u). u \<leftarrow> ls_ex, M ! u \<noteq> n_ex]) }"

text \<open>Minimum weight perfect matching, and maximum weight perfect matching.\<close>

ML_val \<open>@{code hungarian_csr_example} ()\<close>
ML_val \<open>@{code hungarian_csr_max_perfect_example} ()\<close>

subsection \<open>The Other Variants\<close>

definition run_matching_example ::
  "(nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat array Heap) \<Rightarrow>
   (nat \<times> nat) list Heap" where
  "run_matching_example prog = do {
     Fa \<leftarrow> Array.of_list fs_ex;
     Ta \<leftarrow> Array.of_list ts_ex;
     Wa \<leftarrow> Array.of_list ws_ex;
     La \<leftarrow> Array.of_list ls_ex;
     Rv \<leftarrow> Array.of_list rs_ex;
     Mo \<leftarrow> prog n_ex Fa Ta Wa La Rv;
     M \<leftarrow> Array.freeze Mo;
     return [(u, M ! u). u \<leftarrow> ls_ex, M ! u \<noteq> n_ex] }"

definition "ex_min_matching = run_matching_example (hungarian_csr_mw_run_int False \<theta> cap_ex)"
definition "ex_max_matching = run_matching_example (hungarian_csr_mw_run_int True \<theta> cap_ex)"
definition "ex_min_max_card_matching =
  run_matching_example (hungarian_csr_mwmc_run_int False \<theta> cap_ex)"
definition "ex_max_max_card_matching =
  run_matching_example (hungarian_csr_mwmc_run_int True \<theta> cap_ex)"

text \<open>Minimum and maximum weight matchings, and minimum and maximum weight matchings among the
      matchings of maximum cardinality.\<close>

ML_val \<open>@{code ex_min_matching} ()\<close>
ML_val \<open>@{code ex_max_matching} ()\<close>
ML_val \<open>@{code ex_min_max_card_matching} ()\<close>
ML_val \<open>@{code ex_max_max_card_matching} ()\<close>

subsection \<open>Exported SML Code\<close>

text \<open>The imperative programs, written to an SML file among the exports of this theory: the six
      variants on arrays, the example programs running them, and the conversions between
      @{typ nat}/@{typ int} and the target language's integers that a driver needs in order to
      build the input arrays.\<close>

export_code
  (*the six variants*)
  hungarian_csr_run_int hungarian_csr_max_perfect_run_int
  hungarian_csr_mw_run_int hungarian_csr_mwmc_run_int
  (*the example*)
  hungarian_csr_example hungarian_csr_max_perfect_example
  ex_min_matching ex_max_matching ex_min_max_card_matching ex_max_max_card_matching
  (*conversions*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int
  in SML_imp module_name Hungarian_CSR file_prefix Hungarian_CSR_imperative

section \<open>Correctness\<close>

interpretation int_embedding: real_embedding "of_int :: int \<Rightarrow> real"
  by unfold_locales (simp_all add: of_int_less_iff)

text \<open>The input satisfies the assumptions of @{locale hungarian_csr_input}.\<close>

interpretation ex: hungarian_csr_input "of_int :: int \<Rightarrow> real" n_ex fs_ex ts_ex ws_ex ls_ex rs_ex \<theta>
  cap_ex
  by (intro hungarian_csr_input.intro int_embedding.real_embedding_axioms
            hungarian_csr_input_axioms.intro)
     (simp_all add: fs_ex_def ts_ex_def ws_ex_def ls_ex_def rs_ex_def n_ex_def
                    edges_and_costs_int_def, auto)

text \<open>Hence the programs are correct on the example: the perfect matchings are of minimum and of
      maximum weight (on success; on failure, there is no perfect matching), and the matchings of
      the other variants are of minimum and maximum weight, among all matchings and among the
      matchings of maximum cardinality.\<close>

thm ex.hungarian_csr_run_correct ex.max_weight_perfect_matching_run
    ex.min_weight_matching_run ex.max_weight_matching_run
    ex.min_weight_max_card_matching_run ex.max_weight_max_card_matching_run

end
