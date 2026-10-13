theory DIMACS_Solver
  imports Mincost_Oracle_Certificates_Pluggable_Refinement Mincost_Solver_Reduction_Refinement
    Network_Simplex_Instantiation_Refinement 
    Use_Network_Simplex.Network_Simplex_Int
    Code_Target_Nat_Machine
begin

section \<open>The DIMACS solver, assembled\<close>

text \<open>The three theories before this one each solve one part of the problem and stop there.
      \<open>Mincost_Solver_Reduction\<close> turns a parsed DIMACS instance into the standard shape the library
      reasons about, and says what each of the three possible answers about the reduced instance
      means for the original one.  \<open>Mincost_Oracle_Certificates\<close> takes an instance in that shape,
      hands it to an untrusted solver, checks the certificate that comes back, and --- if the check
      fails --- defers to a verified procedure.  \<open>Network_Simplex_Int\<close> \<^emph>\<open>is\<close> such a verified
      procedure.  This theory puts the three together.

      Two things are worth saying about what is assumed here.

      \<^item> \<^emph>\<open>The functional locale assumes exactly what the reduction assumes.\<close>  The reduction is the
        first step, so its well-formedness conditions on the parsed lists are unavoidable; nothing
        else is.  In particular the oracle is a plain parameter with no assumption whatever, and the
        cleanup is \<^emph>\<open>not\<close> a parameter at all --- it is the network simplex, and the obligation
        \<open>cleanup_correct\<close> of @{locale mcf_oracle_cleanup} is discharged, not assumed.

      \<^item> \<^emph>\<open>The numbers are integers.\<close>  A DIMACS instance is integral by definition, so the numeric
        type is @{typ int} and the embedding into the reals of @{locale real_embedding} is
        @{const of_int} --- the genuine one.  Nothing in the pipeline is left generic, and code
        generation emits arbitrary-precision integer arithmetic.\<close>


subsection \<open>An integer square root\<close>

text \<open>The pivot rule is tuned by three counts, and the sizes that work well in practice are all
      \<^emph>\<open>square-root shaped\<close>.  Newton's iteration on @{typ nat} gives one: it halves the error each
      step, so the fuel below is never exhausted in practice and is there only to make the recursion
      structural.

      \<^emph>\<open>Nothing is proved about this function and nothing needs to be.\<close>  The pivot rule enters the
      correctness proof only through @{term \<open>0 < block_size\<close>} and two conditions like it, and those
      are secured by the @{const max} in the definitions further down, whatever this returns.  A bad
      answer here would cost time, never soundness --- which is the status a tuning knob should
      have.\<close>

fun isqrt_iter :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "isqrt_iter n 0 x = x"
| "isqrt_iter n (Suc f) x = (let y = (x + n div x) div 2 in if y < x then isqrt_iter n f y else x)"

definition isqrt :: "nat \<Rightarrow> nat" where
  "isqrt n = (if n = 0 then 0 else isqrt_iter n n n)"

subsection \<open>The fallback, imperatively\<close>

text \<open>The verified network simplex, packaged as the fallback the certifier's pipeline expects.  Two
      things have to be arranged around it.  \<^emph>\<open>The balance array is a different shape\<close>: the pipeline
      carries the reduced instance's balances, of length @{term \<open>Suc n\<close>} with the reserved slot
      @{term \<open>0::nat\<close>} first, whereas the simplex wants a name-indexed array of length
      @{term \<open>Suc (Suc n)\<close>} whose last cell is the artificial root's zero balance.  Since the
      reserved slot \<^emph>\<open>is\<close> zero, the second is the first with a zero appended, so one allocation and
      one copy suffice --- and this is the rejected-certificate path, so an @{term n}-sized copy
      costs nothing.  \<^emph>\<open>The status is a different type\<close>, and is renamed.

      Like every other program here it is defined outside all locales, and it takes the tuning
      parameters as arguments.\<close>

definition ns_cleanup_imp ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> verdict_flag Heap"
  where
  "ns_cleanup_imp nn mm blk mnc mxc fa sa ca oa ba fla =
     do {
       b2 \<leftarrow> Array.new (Suc (Suc nn)) 0;
       _  \<leftarrow> arr_copy_imp ba b2 0 (Suc nn);
       s  \<leftarrow> solve_imp nn mm blk mnc mxc fa sa ca oa fla b2;
       Heap_Monad.return (case s of OptimalF \<Rightarrow> VOptimumF
                                  | InfeasibleF \<Rightarrow> VInfeasibleF
                                  | NegInfCycleF \<Rightarrow> VUnboundedF) }"

subsection \<open>The instance\<close>

text \<open>The lists of a parsed instance, plus the untrusted solver.  The assumptions are those of
      @{locale dimacs_lists_network}, verbatim; the embedding is not among them because at
      @{typ int} it is a fact.\<close>

locale dimacs_solver =
  dimacs_lists where lower = "lower :: int list" for lower +
  fixes oracle_solve :: "int flow_instance \<Rightarrow> int oracle_answer"
  assumes length_fst_list:     "length fst_list = m"
      and length_snd_list:     "length snd_list = m"
      and length_lower:        "length lower = m"
      and length_upper:        "length upper = m"
      and length_cost_list:    "length cost_list = m"
      and length_balance_list: "length balance_list = n"
      and nodes_nonempty:      "0 < n"
      and fst_list_vertex:     "\<And> e. e < m \<Longrightarrow> fst_list ! e \<in> {1..<n}"
      and snd_list_vertex:     "\<And> e. e < m \<Longrightarrow> snd_list ! e \<in> {1..<n}"
begin


end

locale dimacs_solver_m =
  dimacs_solver +
  assumes edges_non_empty:"m > 0"
begin

sublocale dimacs_lists_network 
  where lower = lower and h = "of_int :: int \<Rightarrow> real"
proof(unfold_locales, goal_cases)
  case (9 e) thus ?case using fst_list_vertex[of e] by simp
next
  case (10 e) thus ?case using snd_list_vertex[of e] by simp
qed (simp_all add: length_fst_list length_snd_list length_lower length_upper length_cost_list
                   edges_non_empty length_balance_list nodes_nonempty)

text \<open>@{typ int} is a @{class heap} type, so the reduction's imperative layer is available here with
      nothing further to prove.\<close>

sublocale dimacs_lists_network_heap where lower = lower and h = "of_int :: int \<Rightarrow> real"
  by unfold_locales

subsection \<open>The balances the certifier is instantiated at\<close>

text \<open>The reduction's balance list has the certifier's format only once the feasibility flag has
      passed, and a locale interpretation cannot be conditional.  So the certifier is instantiated at
      the list below: the reduced balances when the flag holds, and an all-zero placeholder of the
      same length otherwise.  The placeholder is never computed --- the program does not reach the
      pipeline when the flag fails --- and the identity with the reduced list is available wherever
      it does.\<close>

definition cert_bal :: "int list" where
  "cert_bal = (if red_ok then red_balance_list else replicate n 0)"

lemma cert_bal_ok: "red_ok \<Longrightarrow> cert_bal = red_balance_list"
  by(simp add: cert_bal_def)

lemma cert_length: "length cert_bal = Suc (n - Suc 0)"
  using orc_lengths(5) orc_nodes by(simp add: cert_bal_def)

lemma cert_sentinel: "cert_bal ! 0 = 0"
  using orc_sentinel orc_nodes by(simp add: cert_bal_def)

lemma cert_sum: "sum_list cert_bal = 0"
  using orc_sum_zero by(cases red_ok) (simp_all add: cert_bal_def sum_list_replicate)

lemma cert_isolated:
  assumes v: "v \<in> {Suc 0..n - Suc 0}"
      and lonely: "\<And> e. e < m \<Longrightarrow> fst_list ! e \<noteq> v \<and> snd_list ! e \<noteq> v"
  shows "cert_bal ! v = 0"
proof(cases red_ok)
  case True
  have "v \<in> {Suc 0..n - 1}" using v by simp
  thus ?thesis using orc_isolated[OF True _ lonely] True by(simp add: cert_bal_def)
next
  case False
  have "v < n" using v orc_nodes by auto
  thus ?thesis using False by(simp add: cert_bal_def)
qed

text \<open>Hence the certifier's format holds of it unconditionally.  Its node count is @{term \<open>n - Suc 0\<close>}
      --- the vertex names are @{term \<open>{1..<n}\<close>} without the reserved slot --- and its arcs are the
      original ones, so the endpoints and the costs are the input lists themselves.\<close>

lemma cert_is_oracle_instance:
  "mcf_oracle fst_list snd_list cost_list cert_bal m (n - Suc 0) red_upper (of_int :: int \<Rightarrow> real)"
proof(unfold_locales, goal_cases)
  case (8 e) thus ?case using orc_endpoints[OF 8] by simp
next
  case (9 e) thus ?case using orc_endpoints[OF 9] by simp
next
  case (10 e) thus ?case using orc_capacity by simp
next
  case (13 v) thus ?case using cert_isolated[of v] by fastforce
qed (auto simp add: orc_lengths cert_length cert_sentinel cert_sum orc_nodes)

subsection \<open>The fallback: the verified network simplex\<close>

text \<open>The certifier's fallback takes the instance and a flow and must return a true verdict.  The
      network simplex of \<open>Network_Simplex_Int\<close> is exactly such a procedure, so the fallback is not a
      parameter here --- it is that procedure, run on the reduced instance.

      Two adjustments are needed to hand it the oracle's flow as a warm start.  \<^emph>\<open>The flow must be
      capacity-feasible\<close>, which the oracle's is not known to be: it is untrusted, and by the time the
      fallback runs its certificate has already been rejected.  So the flow is clamped, in one pass,
      into the admissible box --- a negative entry up to @{term \<open>0::int\<close>}, an entry above a finite
      capacity down to it, an uncapacitated arc left alone.  \<^emph>\<open>The flow must have the right length\<close>,
      which again is not known, so the pass is over @{term \<open>[0..<m]\<close>} and reads a missing entry
      as @{term \<open>0::int\<close>}.  Neither adjustment is a correctness argument: a warm start is a
      performance device, and the network simplex is correct from any feasible start.\<close>

definition ns_clamp :: "int \<Rightarrow> int \<Rightarrow> int" where
  "ns_clamp c x = (if x < 0 then 0 else if c \<noteq> - 1 \<and> c < x then c else x)"

definition ns_flow :: "int list \<Rightarrow> int list" where
  "ns_flow g = map (\<lambda> e. ns_clamp (red_upper ! e) (if e < length g then g ! e else 0)) [0..<m]"

text \<open>The three tuning parameters of the candidate-list pivot rule, \<^emph>\<open>computed from the instance\<close>:
      the block scanned between two boundary checks, the capacity of the candidate list, and the
      floor below which a block boundary does not stop the scan.  The shapes are those of the
      reference implementation the untrusted oracle is derived from, which sets its block to the
      square root of the number of arcs it prices (floor ten), its candidate list to a quarter of
      that (floor ten), and its minor limit to a tenth of the list (floor three).

      \<^emph>\<open>Which arc count.\<close>  The reference implementation, on an instance whose balances sum to zero
      --- which the reduction guarantees --- prices the \<^emph>\<open>original\<close> arcs only: its artificial arcs
      start in the tree and are never scanned.  So the count taken here is the arc count of the
      problem line, the reduction leaving it unchanged.  A different value would cost time and never
      soundness: the selector is correct whatever the three parameters are.

      The parameters are \<^emph>\<open>derived\<close>, not fixed, and the @{const max} does double duty: it is the
      floor the reference implementation uses \<^emph>\<open>and\<close> it is what makes \<open>0 < block_size\<close>,
      \<open>0 < min_candidates\<close> and \<open>min_candidates \<le> max_candidates\<close> facts rather than assumptions.
      That is what keeps this locale free of anything the reduction does not already assume.\<close>

definition ns_arcs :: nat where "ns_arcs = m"

definition ns_block :: nat where "ns_block = max 10 (isqrt ns_arcs)"
definition ns_max :: nat where "ns_max = max 10 (isqrt ns_arcs div 4)"
definition ns_min :: nat where "ns_min = max 3 (ns_max div 10)"

text \<open>The simplex, run on the reduced instance from a given start, and its answer read as a verdict.
      Both are stated for an \<^emph>\<open>arbitrary\<close> start that is capacity-feasible, because the imperative
      layer hands over a flow that has been clamped in the caller's array rather than by
      @{const ns_flow}; the functional cleanup is the instance at @{term \<open>ns_flow g\<close>}.\<close>

definition ns_run :: "int list \<Rightarrow> int ns_outcome" where
  "ns_run fl = initial_basis_code_spec.solve red_upper cost_list fst_list snd_list
                 fl m (n - Suc 0) (tl cert_bal) ns_block ns_min ns_max"

fun ns_verdict :: "int ns_outcome \<Rightarrow> int solver_verdict" where
  "ns_verdict (Optimum fs) = VOptimum fs"
| "ns_verdict Infeasible = VInfeasible"
| "ns_verdict Neg_inf_cycle = VUnbounded"

definition ns_cleanup :: "int flow_instance \<Rightarrow> int list \<Rightarrow> int solver_verdict" where
  "ns_cleanup inst g = ns_verdict (ns_run (ns_flow g))"

text \<open>Every assumption of @{locale int_selector} holds of the reduced lists.  The five lengths, the
      capacity format, the endpoint range, the non-empty arc set and the isolated-vertex condition
      are the format facts the certifier already established; the balance sum is zero because the
      reduction makes it so; and the two flow conditions are what the clamp was for.\<close>

lemma ns_flow_length: "length (ns_flow g) = m"
  by(simp add: ns_flow_def)

lemma ns_flow_nth:
  "e < m \<Longrightarrow> ns_flow g ! e = ns_clamp (red_upper ! e) (if e < length g then g ! e else 0)"
  by(simp add: ns_flow_def)

lemma ns_flow_nonneg: "e < m \<Longrightarrow> 0 \<le> ns_flow g ! e"
  using orc_capacity[of e] by(auto simp add: ns_flow_nth ns_clamp_def)

lemma ns_flow_le_cap: "e < m \<Longrightarrow> red_upper ! e \<noteq> - 1 \<Longrightarrow> ns_flow g ! e \<le> red_upper ! e"
  using orc_capacity[of e] by(auto simp add: ns_flow_nth ns_clamp_def)

lemma cert_bal_tl_length: "length (tl cert_bal) = n - Suc 0"
  using cert_length by simp

lemma cert_bal_tl_nth: "tl cert_bal ! i = cert_bal ! Suc i"
proof -
  have "cert_bal \<noteq> []" using cert_length by auto
  then obtain a bs where "cert_bal = a # bs" by(cases cert_bal) auto
  thus ?thesis by simp
qed

lemma cert_bal_tl_sum: "sum_list (tl cert_bal) = 0"
proof -
  have "cert_bal \<noteq> []" using cert_length by auto
  then obtain a bs where c: "cert_bal = a # bs" by(cases cert_bal) auto
  thus ?thesis using cert_sum cert_sentinel by(simp add: c)
qed

lemma red_cap_set: "c \<in> set red_upper \<Longrightarrow> 0 \<le> c \<or> c = - 1"
  using orc_capacity orc_lengths(3) by(metis in_set_conv_nth)

lemma red_endpoints_set: "set fst_list \<union> set snd_list \<subseteq> {1..n - Suc 0}"
  using orc_endpoints orc_lengths(1,2)
  by(fastforce simp add: in_set_conv_nth)

lemma cert_bal_tl_isolated:
  assumes "i < n - Suc 0" and "Suc i \<notin> set fst_list \<union> set snd_list"
  shows "tl cert_bal ! i = 0"
proof -
  have "\<And> e. e < m \<Longrightarrow> fst_list ! e \<noteq> Suc i \<and> snd_list ! e \<noteq> Suc i"
    using assms(2) orc_lengths(1,2) by(auto simp add: in_set_conv_nth)
  thus ?thesis
    using cert_isolated[of "Suc i"] assms(1) by(simp add: cert_bal_tl_nth)
qed

definition ns_start :: "int list \<Rightarrow> bool" where
  "ns_start fl = (length fl = m \<and> (\<forall> e < m. 0 \<le> fl ! e)
                  \<and> (\<forall> e < m. red_upper ! e \<noteq> - 1 \<longrightarrow> fl ! e \<le> red_upper ! e))"

lemma ns_start_ns_flow: "ns_start (ns_flow g)"
  by(simp add: ns_start_def ns_flow_length ns_flow_nonneg ns_flow_le_cap)

lemma ns_int_selector:
  assumes "ns_start fl"
  shows "int_selector cost_list fst_list snd_list fl m (n - Suc 0)
           (tl cert_bal) ns_block ns_min ns_max red_upper"
  using assms
  by(unfold_locales)
    (use red_endpoints_set in
       \<open>auto simp add: ns_start_def orc_lengths cert_length red_cap_set
                       cert_bal_tl_isolated cert_bal_tl_sum
                       ns_block_def ns_min_def ns_max_def\<close>)

subsection \<open>The reduced instance, seen by the certifier\<close>

text \<open>@{thm [source] cert_is_oracle_instance} says the reduction's output has the format the
      certifier assumes, so the certifier's locale is available at that instance --- with the oracle
      of this locale and no assumption about it.\<close>

sublocale reduced: mcf_oracle
  where fst_list = fst_list and snd_list = snd_list and capacity_list = red_upper
    and cost_list = cost_list and balance_list = cert_bal
    and m = m and n = "n - Suc 0" and oracle_solve = oracle_solve and h = "of_int :: int \<Rightarrow> real"
  by(rule cert_is_oracle_instance)

text \<open>A DIMACS instance is integral by definition, so \<open>cost_integer\<close> holds of the reduced costs for
      free: \<open>h\<close> is \<^const>\<open>of_int\<close>, and \<^term>\<open>of_int k \<in> \<int>\<close> for every \<open>k\<close>.  This is what lets the
      solver run its imperative pipeline in \<open>CheckerEpsilontic\<close> mode and still conclude exact
      optimality: the cheaper check is all a \<open>CertEps\<close>-tagged oracle answer has to clear, and this
      sublocale is what turns the resulting dual-slack witness back into \<open>reduced.verdict_ok\<close>.\<close>

sublocale reduced: mcf_oracle_eps
  where fst_list = fst_list and snd_list = snd_list and capacity_list = red_upper
    and cost_list = cost_list and balance_list = cert_bal
    and m = m and n = "n - Suc 0" and oracle_solve = oracle_solve and h = "of_int :: int \<Rightarrow> real"
  by(unfold_locales) simp

text \<open>The instance's own bound \<open>n - Suc 0 < n\<close> is what \<open>verdict_ok_dispatch_exact\<close> needs, so \<open>n\<close> is
      the \<open>M\<close> the imperative pipeline below is run at: any larger value would do just as well, and
      this is the smallest that always qualifies.\<close>

lemma reduced_verdict_ok_dispatch_exact:
  assumes "reduced.verdict_ok_dispatch CheckerEpsilontic n r"
  shows "reduced.verdict_ok r"
  using orc_nodes by(intro reduced.verdict_ok_dispatch_exact[OF assms]) simp

text \<open>\<^emph>\<open>One network, three readings.\<close>  The reduction, the certifier and the network simplex each read
      the reduced lists as a cost flow network, and the three readings differ only in how the
      capacity is written: as a non-negativity test, as a test against the sentinel, and as a nested
      conditional.  The capacity format makes them the same function, and hence the three
      interpretations the same one --- which is what lets a statement proved by one be used by
      another with no transfer at all.\<close>

lemma cap_u_ns:
  "(\<lambda> e. if e < m then (if red_upper ! e = - 1 then \<infinity> else ereal (of_int (red_upper ! e))) else \<infinity>)
     = reduced.cap_u"
  by(rule ext) (auto simp add: reduced.cap_u_def reduced.uncapacitated_def)

lemma cap_u_eq_red_u: "reduced.cap_u = red_u"
proof(rule ext)
  fix e show "reduced.cap_u e = red_u e"
    using orc_capacity[of e]
    by(auto simp add: reduced.cap_u_def reduced.uncapacitated_def red_u_def)
qed

lemma ns_u_eq_red_u:
  "(\<lambda> e. if e < m then (if red_upper ! e = - 1 then \<infinity> else ereal (of_int (red_upper ! e))) else \<infinity>)
     = red_u"
  using cap_u_ns cap_u_eq_red_u by simp

text \<open>The certifier reads the balances off @{const cert_bal}, the reduction off its own list, so the
      two agree exactly where the feasibility flag holds.\<close>

lemma bal_is_red_b: "red_ok \<Longrightarrow> reduced.bal = red_b"
  unfolding reduced.bal_def red_b_def by(simp add: cert_bal_ok)

text \<open>The balances agree only on the vertex set --- the network simplex indexes them from
      @{term \<open>0::nat\<close>} through a list of length @{term \<open>n - Suc 0\<close>}, the certifier through a list of
      length @{term n} with a reserved slot --- so the two statements that mention a balance are
      needed up to agreement on the vertices.\<close>

lemma isbflow_cong:
  assumes "\<And> v. v \<in> original_network.\<V> \<Longrightarrow> b1 v = b2 v"
  shows "reduced_network.isbflow f b1 = reduced_network.isbflow f b2"
  using assms by(auto simp add: reduced_network.isbflow_def)

lemma is_Opt_cong:
  assumes "\<And> v. v \<in> original_network.\<V> \<Longrightarrow> b1 v = b2 v"
  shows "reduced_network.is_Opt b1 f = reduced_network.is_Opt b2 f"
  using isbflow_cong[OF assms] by(auto simp add: reduced_network.is_Opt_def)

text \<open>A negative cycle of infinite capacity is one whatever ordered ring the costs are read in, so
      the simplex's integer certificate is the real-valued statement the reduction wants.\<close>

lemma foldr_cost_of_int:
  "foldr (\<lambda> e. (+) (of_int (c e))) D (0::real) = of_int (foldr (\<lambda> e. (+) (c e)) D (0::int))"
  by(induction D) simp_all

lemma neg_infty_int_to_real:
  assumes "has_neg_infty_cycle original_network.make_pair {0..<m} (\<lambda> e. cost_list ! e) red_u"
  shows "has_neg_infty_cycle original_network.make_pair {0..<m}
           (\<lambda> e. (of_int (cost_list ! e) :: real)) red_u"
proof -
  from assms obtain D
    where D: "closed_w (original_network.make_pair ` {0..<m}) (map original_network.make_pair D)"
             "foldr (\<lambda> e. (+) (cost_list ! e)) D 0 < 0"
             "set D \<subseteq> {0..<m}" "\<And> e. e \<in> set D \<Longrightarrow> red_u e = \<infinity>"
    by(auto elim!: has_neg_infty_cycleE)
  have "foldr (\<lambda> e. (+) (of_int (cost_list ! e))) D (0::real) < 0"
    using foldr_cost_of_int[where c = "\<lambda> e. cost_list ! e" and D = D] D(2) by simp
  thus ?thesis using D by(auto intro!: has_neg_infty_cycleI)
qed

subsection \<open>The fallback is correct, so the pipeline is\<close>

text \<open>The one obligation @{locale mcf_oracle_cleanup} makes about a fallback, discharged: whichever
      of the three answers the network simplex returns, it says something true about the reduced
      instance.  This is where the two developments meet --- and it is a \<^emph>\<open>proof\<close>, so the assembled
      pipeline assumes nothing beyond the shape of the parsed input.\<close>

lemma ns_run_ok:
  assumes st: "ns_start fl"
  shows "reduced.verdict_ok (ns_verdict (ns_run fl))"
proof -
  interpret NS: int_selector cost_list fst_list snd_list fl m "n - Suc 0"
                  "tl cert_bal" ns_block ns_min ns_max red_upper
    by(rule ns_int_selector[OF st])
  have bl: "of_int (NS.b_lookup v) = reduced.bal v" if "v \<in> original_network.\<V>" for v
  proof -
    have v: "Suc 0 \<le> v" "v \<le> n - Suc 0" using that reduced.net_V_subset by auto
    have "NS.b_lookup v = tl cert_bal ! (v - Suc 0)"
      using v NS.b_lookup_nth NS.set_vs_list by simp
    also have "\<dots> = cert_bal ! Suc (v - Suc 0)" using cert_bal_tl_nth by simp
    also have "\<dots> = cert_bal ! v" using v by simp
    finally show ?thesis by(simp add: reduced.bal_def)
  qed
  show ?thesis
  proof(cases "NS.solve")
    case (Optimum fs)
    hence v: "ns_verdict (ns_run fl) = VOptimum fs" by(simp add: ns_run_def)
    have "reduced_network.is_Opt (\<lambda> v. of_int (NS.b_lookup v)) (of_int \<circ> nth fs)"
      using NS.int_solve_correct(1)[OF Optimum] by(simp add: ns_u_eq_red_u)
    hence "reduced_network.is_Opt reduced.bal (\<lambda> e. of_int (fs ! e))"
      using is_Opt_cong[of "\<lambda> v. of_int (NS.b_lookup v)" reduced.bal] bl by(simp add: o_def)
    thus ?thesis
      using v by(simp add: reduced.verdict_ok_def cap_u_eq_red_u)
  next
    case Infeasible
    hence v: "ns_verdict (ns_run fl) = VInfeasible" by(simp add: ns_run_def)
    have "\<nexists> f. reduced_network.isbflow f (\<lambda> v. of_int (NS.b_lookup v))"
      using NS.int_solve_correct(2)[OF Infeasible] by(simp add: ns_u_eq_red_u)
    hence "\<nexists> f. reduced_network.isbflow f reduced.bal"
      using isbflow_cong[of "\<lambda> v. of_int (NS.b_lookup v)" reduced.bal] bl by simp
    thus ?thesis using v by(simp add: reduced.verdict_ok_def cap_u_eq_red_u)
  next
    case Neg_inf_cycle
    hence v: "ns_verdict (ns_run fl) = VUnbounded" by(simp add: ns_run_def)
    have "has_neg_infty_cycle original_network.make_pair {0..<m}
            (\<lambda> e. cost_list ! e) red_u"
      using NS.int_solve_correct(3)[OF Neg_inf_cycle] by(simp add: ns_u_eq_red_u)
    thus ?thesis
      using v neg_infty_int_to_real by(simp add: reduced.verdict_ok_def cap_u_eq_red_u)
  qed
qed

lemma ns_cleanup_ok: "reduced.verdict_ok (ns_cleanup inst g)"
  using ns_run_ok[OF ns_start_ns_flow] by(simp add: ns_cleanup_def)

sublocale reduced: mcf_oracle_cleanup
  where fst_list = fst_list and snd_list = snd_list and capacity_list = red_upper
    and cost_list = cost_list and balance_list = cert_bal
    and m = m and n = "n - Suc 0" and oracle_solve = oracle_solve and h = "of_int :: int \<Rightarrow> real"
    and cleanup = ns_cleanup
  by(unfold_locales) (rule ns_cleanup_ok)

text \<open>\<^emph>\<open>The functional solver goes through the pluggable pipeline.\<close>  \<open>reduced.pluggable.solve'\<close>
      instantiates \<open>Mincost_Oracle_Certificates_Pluggable\<close>'s generic pipeline with the current
      checker, and \<open>decide'_current_checker_eq_decide\<close> says that is pointwise the same computation
      as \<open>reduced.solve\<close> --- so every fact already proved about \<open>reduced.solve\<close> transfers across this
      one rewrite.\<close>

lemma reduced_solve'_eq_solve: "reduced.pluggable.solve' = reduced.solve"
  by(simp add: reduced.pluggable.solve'_def reduced.solve_def
               reduced.decide'_current_checker_eq_decide)

text \<open>A flow reported as optimal has the length the reduced instance prescribes --- either because
      the certifier checked it, or because the network simplex produced it.\<close>

lemma ns_run_length:
  assumes st: "ns_start fl" and v: "ns_verdict (ns_run fl) = VOptimum gs"
  shows "length gs = m"
proof -
  interpret NS: int_selector cost_list fst_list snd_list fl m "n - Suc 0"
                  "tl cert_bal" ns_block ns_min ns_max red_upper
    by(rule ns_int_selector[OF st])
  have "NS.solve = Optimum gs"
    using v by(cases "NS.solve") (simp_all add: ns_run_def)
  thus ?thesis using NS.int_solve_correct(1) by simp
qed

lemma ns_cleanup_length:
  "ns_cleanup inst g = VOptimum gs \<Longrightarrow> length gs = m"
  using ns_run_length[OF ns_start_ns_flow] by(simp add: ns_cleanup_def)

lemma solve_flow_length:
  assumes "reduced.solve = VOptimum gs" shows "length gs = m"
proof(cases "reduced.screen reduced.orc_answer")
  case None
  thus ?thesis
    using assms ns_cleanup_length by(simp add: reduced.solve_def reduced.decide_def)
next
  case (Some b)
  hence chk: "reduced.check_answer b" "b = reduced.orc_answer"
    by(auto simp add: reduced.screen_def split: if_splits)
  have "reduced.verdict_of b = VOptimum gs"
    using assms Some by(simp add: reduced.solve_def reduced.decide_def)
  then obtain pot certm where "b = OracleOptimum gs pot certm"
    by(cases b) (auto simp add: reduced.verdict_of_def)
  thus ?thesis
    using chk(1) by(simp add: reduced.check_answer_def reduced.check_optimum_def)
qed

subsection \<open>The answer to the DIMACS instance\<close>

text \<open>The whole solver.  The immediate check comes first: an arc of empty range makes the instance
      infeasible outright and there is nothing to solve.  Otherwise the reduced instance goes to the
      pipeline, and its answer is read back --- an optimal reduced flow becomes an optimal DIMACS
      flow by adding the lower bounds again, and either failure verdict means the DIMACS instance had
      no flow at all.  So the answer is binary: @{term \<open>Some fs\<close>} is an optimal flow, @{term None} is
      a proof that none exists.\<close>

definition dimacs_solve :: "int list option" where
  "dimacs_solve =
     (if \<not> red_ok then None
      else case reduced.pluggable.solve' of VOptimum gs \<Rightarrow> Some (orig_flow gs) | _ \<Rightarrow> None)"

text \<open>Reading a true verdict about the reduced instance as a statement about the DIMACS one.  These
      two are the whole content of the composition: the certifier and the simplex both deliver a
      \<open>verdict_ok\<close>, and the reduction's three final theorems turn it into an answer about the
      original problem.  They are stated about a \<^emph>\<open>verdict\<close> so that the imperative pipeline, whose
      result is not literally \<open>reduced.solve\<close>, can use them too.\<close>

lemma verdict_dimacs_Opt:
  assumes ok: "red_ok" and v: "reduced.verdict_ok (VOptimum gs)"
  shows "original_network.is_dimacs_Opt {1..<n} (\<lambda> e. of_int (orig_flow gs ! e))"
proof -
  have "reduced_network.is_Opt red_b (\<lambda> e. of_int (gs ! e))"
    using v by(simp add: reduced.verdict_ok_def bal_is_red_b[OF ok] cap_u_eq_red_u)
  thus ?thesis by(rule orig_flow_is_dimacs_Opt[OF ok])
qed

lemma verdict_dimacs_fail:
  assumes ok: "red_ok" and v: "reduced.verdict_ok r" and fail: "r = VInfeasible \<or> r = VUnbounded"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
proof -
  have "has_neg_infty_cycle original_network.make_pair {0..<m}
          (\<lambda> e. (of_int (cost_list ! e) :: real)) red_u
        \<or> (\<nexists> g. reduced_network.isbflow g red_b)"
    using v fail by(auto simp add: reduced.verdict_ok_def bal_is_red_b[OF ok] cap_u_eq_red_u)
  thus ?thesis by(rule original_infeasible_if_reduced_fails[OF red_ok_arcsD[OF ok]])
qed

theorem dimacs_solve_Opt:
  assumes "dimacs_solve = Some fs"
  shows "original_network.is_dimacs_Opt {1..<n} (\<lambda> e. of_int (fs ! e))"
proof -
  obtain gs
    where ok: "red_ok" and s': "reduced.pluggable.solve' = VOptimum gs" and fs: "fs = orig_flow gs"
    using assms
    by(auto simp add: dimacs_solve_def split: if_splits solver_verdict.splits)
  have s: "reduced.solve = VOptimum gs" using s' reduced_solve'_eq_solve by simp
  have "reduced.verdict_ok (VOptimum gs)" using reduced.solve_correct s by simp
  thus ?thesis using verdict_dimacs_Opt[OF ok] fs by simp
qed

theorem dimacs_solve_None:
  assumes "dimacs_solve = None"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
proof(cases "red_ok")
  case False
  thus ?thesis by(rule no_dimacs_flow_if_not_red_ok)
next
  case True
  have "reduced.pluggable.solve' = VInfeasible \<or> reduced.pluggable.solve' = VUnbounded"
    using assms True by(cases "reduced.pluggable.solve'") (auto simp add: dimacs_solve_def)
  hence "reduced.solve = VInfeasible \<or> reduced.solve = VUnbounded"
    using reduced_solve'_eq_solve by simp
  thus ?thesis using verdict_dimacs_fail[OF True reduced.solve_correct] by simp
qed

text \<open>The solution line \<open>s <F>\<close> of the output format: @{const dimacs_lists.orig_cost} taken on the
      recovered flow is the objective the DIMACS specification asks to minimise, computed in
      @{typ int}.\<close>

lemma fold_add_sum_list:
  "fold (\<lambda> e s. s + c e) xs (a::'a::comm_monoid_add) = a + sum_list (map c xs)"
  by(induction xs arbitrary: a) (simp_all add: add.assoc)

lemma orig_cost_sum: "orig_cost fs = (\<Sum> e \<in> {0..<m}. cost_list ! e * fs ! e)"
  by(simp add: orig_cost_def fold_add_sum_list sum_list_distinct_conv_sum_set)

theorem orig_cost_eq_C:
  "of_int (orig_cost fs) = original_network.\<C> (\<lambda> e. of_int (fs ! e))"
  by(simp add: orig_cost_sum original_network.\<C>_def mult.commute)

subsection \<open>The fallback refines\<close>

text \<open>The simplex's heap layer is available at the reduced instance for every capacity-feasible
      start, and its scattered balance array is the reduced balance list with the root's zero
      appended --- which is exactly what @{const ns_cleanup_imp} builds.\<close>

lemma ns_heap:
  assumes "ns_start fl"
  shows "initial_basis_selector_heap cost_list fst_list snd_list fl m (n - Suc 0)
           (tl cert_bal) ns_block ns_min ns_max red_upper (of_int :: int \<Rightarrow> real)"
proof -
  interpret NS: int_selector cost_list fst_list snd_list fl m "n - Suc 0"
                  "tl cert_bal" ns_block ns_min ns_max red_upper
    by(rule ns_int_selector[OF assms])
  show ?thesis by unfold_locales
qed

lemma ns_b_arr:
  assumes st: "ns_start fl"
  shows "initial_basis_code_spec.b_arr (n - Suc 0) (tl cert_bal) = cert_bal @ [0]"
proof -
  interpret NS: int_selector cost_list fst_list snd_list fl m "n - Suc 0"
                  "tl cert_bal" ns_block ns_min ns_max red_upper
    by(rule ns_int_selector[OF st])
  have len: "length NS.b_arr = Suc (Suc (n - Suc 0))"
    using NS.length_b_arr NS.vcount_eq by simp
  have z: "NS.b_arr ! 0 = 0"
  proof -
    have "v \<noteq> 0" if "(v, x) \<in> set (zip NS.vs_list (tl cert_bal))" for v x
    proof
      assume "v = 0"
      moreover have "v \<in> set NS.vs_list" using that by(rule set_zip_leftD)
      ultimately show False using NS.zero_notin_vs_list by simp
    qed
    hence "NS.b_arr ! 0 = replicate (Suc NS.vcount) (0::int) ! 0"
      unfolding NS.b_arr_def by(rule NS.foldl_scatter_miss)
    thus ?thesis by simp
  qed
  show ?thesis
  proof(rule nth_equalityI)
    show "length NS.b_arr = length (cert_bal @ [0])"
      using len cert_length by simp
  next
    fix v assume "v < length NS.b_arr"
    hence vlt: "v < Suc (Suc (n - Suc 0))" using len by simp
    show "NS.b_arr ! v = (cert_bal @ [0]) ! v"
    proof(cases "v = 0")
      case True
      thus ?thesis using z cert_sentinel cert_length by(simp add: nth_append)
    next
      case False
      show ?thesis
      proof(cases "v = Suc (n - Suc 0)")
        case True
        have "NS.b_arr ! v = 0"
          using NS.b_lookup_root NS.vcount_eq True by(simp add: NS.b_lookup_def)
        thus ?thesis using True cert_length by(simp add: nth_append)
      next
        case False
        hence vr: "v \<in> set NS.vs_list" using vlt \<open>v \<noteq> 0\<close> NS.set_vs_list by auto
        have "NS.b_arr ! v = tl cert_bal ! (v - Suc 0)"
          using NS.b_lookup_nth[OF vr] by(simp add: NS.b_lookup_def)
        also have "\<dots> = cert_bal ! v"
          using vlt False \<open>v \<noteq> 0\<close> cert_bal_tl_nth[of "v - Suc 0"] by simp
        finally show ?thesis using vlt False cert_length by(simp add: nth_append)
      qed
    qed
  qed
qed

text \<open>The certifier's heap layer at the reduced instance.  It is assumption-free --- it only fixes
      the array assertion \<open>inst_assn\<close> and the reading of a flag --- so there is nothing to
      discharge.\<close>

sublocale reduced: mcf_oracle_heap_spec
  where fst_list = fst_list and snd_list = snd_list and capacity_list = red_upper
    and cost_list = cost_list and balance_list = cert_bal
    and m = m and n = "n - Suc 0" and oracle_solve = oracle_solve
  by unfold_locales

definition ns_flag :: "solve_status \<Rightarrow> verdict_flag" where
  "ns_flag s = (case s of OptimalF \<Rightarrow> VOptimumF | InfeasibleF \<Rightarrow> VInfeasibleF
                        | NegInfCycleF \<Rightarrow> VUnboundedF)"

text \<open>Renaming the status is sound: the flag and the flow left in the caller's array read back as the
      verdict the simplex actually delivered.  The optimal case is the only one that says anything
      about the array, and there the returned list \<^emph>\<open>is\<close> the simplex's flow, because it has exactly
      the length the simplex prescribes.\<close>

lemma ns_flag_ok:
  assumes st: "ns_start fl"
      and tk: "\<And> fs. ns_run fl = Optimum fs \<Longrightarrow> fs' = fs"
  shows "reduced.verdict_ok (reduced.verdict_of_flag (ns_flag (status_of (ns_run fl))) fs')"
proof(cases "ns_run fl")
  case (Optimum fs)
  have "fs' = fs" by(rule tk[OF Optimum])
  thus ?thesis
    using ns_run_ok[OF st] Optimum by(simp add: ns_flag_def reduced.verdict_of_flag_def)
next
  case Infeasible
  thus ?thesis using ns_run_ok[OF st] by(simp add: ns_flag_def reduced.verdict_of_flag_def)
next
  case Neg_inf_cycle
  thus ?thesis using ns_run_ok[OF st] by(simp add: ns_flag_def reduced.verdict_of_flag_def)
qed

lemma drop_zeros: "drop k (0 # replicate k (0::int)) = [0]"
  by(induction k) simp_all

text \<open>The two DIMACS conclusions once more, now keyed on the \<^emph>\<open>flag\<close> the imperative pipeline returns
      rather than on a verdict --- which is the form the final proof needs.\<close>

lemma verdict_flag_opt:
  assumes "red_ok" "length fl' = m"
      and "reduced.verdict_ok (reduced.verdict_of_flag VOptimumF fl')"
  shows "original_network.is_dimacs_Opt {1..<n} (\<lambda> e. of_int (orig_flow fl' ! e))"
  using assms verdict_dimacs_Opt by(simp add: reduced.verdict_of_flag_def)

lemma verdict_flag_fail:
  assumes "red_ok" and "reduced.verdict_ok (reduced.verdict_of_flag r fl')" and "r \<noteq> VOptimumF"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
  using assms verdict_dimacs_fail[of "reduced.verdict_of_flag r fl'"]
  by(cases r) (auto simp add: reduced.verdict_of_flag_def)

text \<open>The same two, in the shape the imperative proof meets them: the \<open>M\<close> of the dispatch already
      discharged, and the vertex set in the normal form the verification condition generator leaves
      behind, so that \<open>rule\<close> applies without a rewrite.\<close>

lemma verdict_flag_opt':
  assumes "red_ok" "length fl' = m"
      and "reduced.verdict_ok_dispatch CheckerEpsilontic n (reduced.verdict_of_flag VOptimumF fl')"
  shows "original_network.is_dimacs_Opt {Suc 0..<n} (\<lambda> e. of_int (orig_flow fl' ! e))"
  using verdict_flag_opt[OF assms(1,2) reduced_verdict_ok_dispatch_exact[OF assms(3)]] by simp

lemma verdict_flag_fail':
  assumes "red_ok" and "r \<noteq> VOptimumF"
      and "reduced.verdict_ok_dispatch CheckerEpsilontic n (reduced.verdict_of_flag r fl')"
  shows "\<not> original_network.is_dimacs_flow {Suc 0..<n} f"
  using verdict_flag_fail[OF assms(1) reduced_verdict_ok_dispatch_exact[OF assms(3)] assms(2)]
  by simp

text \<open>The recovered flow has exactly the arcs of the instance, so the \<open>take\<close> of the final statement
      is the identity on it.\<close>

lemma orig_flow_length: "length (orig_flow gs) = m"
  by(simp add: orig_flow_def)

text \<open>\<^emph>\<open>The fallback refines.\<close>  This is the obligation @{locale mcf_oracle_heap} \<^emph>\<open>assumes\<close> of a
      cleanup, discharged for the verified network simplex.  Its three premises are exactly
      @{const ns_start}, which is what the pipeline's rectification pass establishes, so nothing is
      left for the caller.\<close>

lemma ns_cleanup_imp_rule:
  assumes st: "ns_start fl"
  shows
   "<reduced.inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
      ns_cleanup_imp (n - Suc 0) m ns_block ns_min ns_max fa sa ca oa ba fla
    <\<lambda>r. \<exists>\<^sub>A fl'. reduced.inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
         * \<up>(length fl' = m \<and> reduced.verdict_ok (reduced.verdict_of_flag r fl'))>"
proof -
  interpret NSH: initial_basis_selector_heap cost_list fst_list snd_list fl m "n - Suc 0"
                   "tl cert_bal" ns_block ns_min ns_max red_upper "of_int :: int \<Rightarrow> real"
    by(rule ns_heap[OF st])
  have barr: "NSH.b_arr = cert_bal @ [0]" by(rule ns_b_arr[OF st])
  have slv: "NSH.solve = ns_run fl" by(simp add: ns_run_def)
  show ?thesis
    unfolding ns_cleanup_imp_def reduced.inst_assn_def
    apply(sep_auto heap: arr_copy_imp_rule NSH.solve_imp_correct[unfolded barr slv]
                   simp: cert_length drop_zeros ns_flag_def[symmetric])
    apply(drule sym)
    apply(sep_auto simp: ns_flag_ok[OF st])
    done
qed

end

subsection \<open>The imperative pipeline: the oracle is the only thing left assumed\<close>
text \<open>One layer more, and it fixes \<^emph>\<open>one\<close> thing: the imperative oracle, with the single assumption
      that it refines the functional one --- a refinement statement, not a correctness one, since
      the functional oracle is itself unconstrained.  That assumption is unavoidable: the oracle is
      an external program.

      \<^emph>\<open>Everything else is discharged here.\<close>  The certifier's pipeline
      @{locale mcf_oracle_heap} asks for two triples; the second is
      @{thm [source] dimacs_solver_m.ns_cleanup_imp_rule}, proved above from the verified network
      simplex.  So the interpretation below leaves exactly one obligation open, and it is the
      oracle's.\<close>

locale dimacs_solver_imp = dimacs_solver_m +
  fixes oracle_imp ::
    "nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int answer_imp Heap"
  assumes oracle_imp_rule:
    "length fl = m \<Longrightarrow>
     <reduced.inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
       oracle_imp fa sa ca oa ba fla
     <\<lambda> ai. reduced.inst_assn fa sa ca oa ba * reduced.answer_assn fla reduced.orc_answer ai>"
    and oracle_wf: "reduced.answer_wf reduced.orc_answer"
begin

sublocale reduced: mcf_oracle_heap
  where fst_list = fst_list and snd_list = snd_list and capacity_list = red_upper
    and cost_list = cost_list and balance_list = cert_bal
    and m = m and n = "n - Suc 0" and oracle_solve = oracle_solve and h = "of_int :: int \<Rightarrow> real"
    and oracle_imp = oracle_imp
    and cleanup_imp = "ns_cleanup_imp (n - Suc 0) m ns_block ns_min ns_max"
proof(unfold_locales, goal_cases)
  case (1 fl fa sa ca oa ba fla) thus ?case by(rule oracle_imp_rule)
next
  case (2 fl fa sa ca oa ba fla)
  thus ?case by(intro ns_cleanup_imp_rule) (simp add: ns_start_def)
qed

subsection \<open>The whole solver, imperatively\<close>

text \<open>Reduce, solve, read the answer back.  The reduction rewrites the caller's capacity and balance
      arrays in place and leaves the arcs, the costs and the lower bounds where they were, so the
      pipeline is handed the very same six arrays; one array is allocated, for the flow the oracle
      fills.  The certifier's pipeline runs the oracle, checks its certificate and falls back on the
      network simplex; and on an optimal answer @{const orig_flow_imp} adds the lower bounds back in
      place, so the cells of that array are the DIMACS flow.

      The immediate check is honoured first: an arc of empty range, an out-of-range balance or a
      non-zero balance sum makes the instance infeasible and nothing is solved.  The flow array is
      returned in every case --- it is the caller's to free --- but only the \<^emph>\<open>True\<close> answer says
      anything about it.  The capacity and balance arrays come back holding the \<^emph>\<open>reduced\<close> instance:
      the reduction is in place, and what the caller still needs is the lower bounds and the flow.\<close>

definition dimacs_solve_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array
   \<Rightarrow> (bool \<times> int array) Heap" where
  "dimacs_solve_imp fa sa la ua oa ba =
     reduce_imp fa sa la ua oa ba m n \<bind>
     (\<lambda>(sh, ok).
        do {
          fla \<leftarrow> Array.new m 0;
          if \<not> ok then Heap_Monad.return (False, fla)
          else do {
            v \<leftarrow> reduced.pluggable.solve_imp' CheckerEpsilontic n fa sa ua oa ba fla;
            if v = VOptimumF
            then do { _ \<leftarrow> orig_flow_imp la fla 0 m; Heap_Monad.return (True, fla) }
            else Heap_Monad.return (False, fla) } })"



text \<open>\<^emph>\<open>The solver is correct.\<close>  Run on the arrays of a parsed instance, it answers @{term True} only
      with an optimal DIMACS flow in the array it returns, and @{term False} only when the instance
      has no flow at all.  Nothing in the statement mentions the reduction, the certificates or the
      simplex: they are the \<^emph>\<open>method\<close>, and what is claimed is a property of the problem on the
      problem's own terms.  The capacity and balance arrays are left existential: the reduction has
      overwritten them, and nothing downstream reads them again.

      The proof splits on the feasibility flag, because the certifier's instance is the reduced one
      only when the flag holds --- and it is the flag that decides whether the pipeline runs at all.
      Three heap rules do the rest, \<open>reduce_imp_rule\<close>, \<open>solve_imp'_correct\<close> (whose two obligations
      are the assumed oracle rule and the \<^emph>\<open>proved\<close> \<open>ns_cleanup_imp_rule\<close>) and
      \<open>orig_flow_imp_correct\<close>, leaving one goal per branch: an assertion about a heap that still
      carries an existential over the arrays' contents, which \<open>rule exI\<close> supplies.  The
      \<open>eq_commute\<close> steps are there because the pipeline's own length fact is used by the simplifier
      to rewrite @{term m} away, and the DIMACS facts are stated in @{term m}.\<close>

theorem dimacs_solve_imp_correct:
  "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a upper * oa \<mapsto>\<^sub>a cost_list *
    ba \<mapsto>\<^sub>a balance_list>
     dimacs_solve_imp fa sa la ua oa ba
   <\<lambda>(b, ga). fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * oa \<mapsto>\<^sub>a cost_list *
              (\<exists>\<^sub>A us. ua \<mapsto>\<^sub>a us) * (\<exists>\<^sub>A bs. ba \<mapsto>\<^sub>a bs) *
              (\<exists>\<^sub>A gs. ga \<mapsto>\<^sub>a gs
               * \<up>((b \<longrightarrow> original_network.is_dimacs_Opt {1..<n}
                          (\<lambda> e. of_int (take m gs ! e)))
                   \<and> (\<not> b \<longrightarrow> (\<forall> f. \<not> original_network.is_dimacs_flow {1..<n} f))))>"
proof(cases red_ok)
  case ok: True
  show ?thesis
    unfolding dimacs_solve_imp_def
    apply(sep_auto heap: reduce_imp_rule[unfolded cert_bal_ok[OF ok, symmetric]]
                         reduced.pluggable.solve_imp'_correct[OF _ oracle_wf nodes_nonempty,
                           unfolded reduced.inst_assn_def]
                         orig_flow_imp_correct
                   simp: orc_lengths ok)
     apply(simp only: eq_commute[where a = m])
     subgoal for okk ra fl' aa baa
       apply(subgoal_tac
               "original_network.is_dimacs_Opt {Suc 0..<n} (\<lambda> e. of_int (orig_flow fl' ! e))")
        apply(thin_tac "length fl' = m")
        apply(sep_auto simp: mod_ex_dist orig_flow_length)
       apply(simp only: eq_commute[where a = m])
       apply(rule verdict_flag_opt'[OF ok]; assumption)
       done
     subgoal for h ha r sh okk hb ra hc rb fl'
       apply(subgoal_tac "\<forall> f. \<not> original_network.is_dimacs_flow {Suc 0..<n} f")
        apply(elim conjE)
        apply(thin_tac "length fl' = m")
        apply(sep_auto simp: mod_ex_dist)
        apply(rule exI[where x = fl'], rule exI[where x = cert_bal],
              rule exI[where x = red_upper])
        apply sep_auto
       apply(simp only: eq_commute[where a = m])
       apply(erule notE[OF verdict_flag_fail'[OF ok]]; assumption)
       done
    done
next
  case notok: False
  show ?thesis
    unfolding dimacs_solve_imp_def
    apply(sep_auto heap: reduce_imp_rule simp: orc_lengths notok)
     subgoal for okk aa baa ra
       apply(subgoal_tac "\<forall> f. \<not> original_network.is_dimacs_flow {Suc 0..<n} f")
        prefer 2
        apply(insert no_dimacs_flow_if_not_red_ok[OF notok], simp)
       apply(sep_auto simp: mod_ex_dist)
       done
    apply(insert notok, simp)
    done
qed

text \<open>\<^emph>\<open>The marker is exact.\<close>  The theorem above gives the two implications; because the answer is a
      \<^emph>\<open>boolean\<close>, they are together a biconditional, and it is worth stating as one.  A DIMACS
      instance whose bounds are integers has finite capacities on every arc, so its feasible region
      is a bounded polyhedron: if it has a flow at all then it has an optimal one.  Hence the flag is
      set exactly when the instance is feasible --- \<open>True\<close> is never returned without an optimum to
      show for it, and \<open>False\<close> is never returned when a flow exists.\<close>

corollary dimacs_solve_imp_marker:
  "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a upper * oa \<mapsto>\<^sub>a cost_list *
    ba \<mapsto>\<^sub>a balance_list>
     dimacs_solve_imp fa sa la ua oa ba
   <\<lambda>(b, ga). fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * oa \<mapsto>\<^sub>a cost_list *
              (\<exists>\<^sub>A us. ua \<mapsto>\<^sub>a us) * (\<exists>\<^sub>A bs. ba \<mapsto>\<^sub>a bs) *
              (\<exists>\<^sub>A gs. ga \<mapsto>\<^sub>a gs
               * \<up>((b \<longleftrightarrow> (\<exists> f. original_network.is_dimacs_flow {1..<n} f))
                   \<and> (b \<longrightarrow> original_network.is_dimacs_Opt {1..<n}
                            (\<lambda> e. of_int (take m gs ! e)))))>"
  apply(rule ht_cons_post_prec[OF dimacs_solve_imp_correct])
  apply(sep_auto simp: original_network.is_dimacs_Opt_def)
  done

end

subsection \<open>Code generation\<close>

text \<open>A @{command partial_function} does not register its equation as a code equation --- termination
      is exactly what it does not claim --- so the four loops of the reduction are declared here.
      They are tail-recursive in the heap monad, so the generated ML is a loop.\<close>

declare red_arcs_imp.simps [code] orig_flow_imp.simps [code]
        shift_imp.simps [code] sweep_imp.simps [code]

text \<open>The whole thing as \<^emph>\<open>one top-level program\<close>, with the oracle as an argument --- which is what a
      caller can actually run: the external solver is supplied at link time, and everything else is
      the verified code.\<close>

definition dimacs_solve_prog ::
  "(nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int answer_imp Heap)
   \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> int array \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> (bool \<times> int array) Heap" where
  "dimacs_solve_prog orc fa sa la ua oa ba mm nn =
     reduce_imp fa sa la ua oa ba mm nn \<bind>
     (\<lambda>(sh, ok).
        do {
          fla \<leftarrow> Array.new mm 0;
          if \<not> ok then Heap_Monad.return (False, fla)
          else if mm = 0 then Heap_Monad.return (True, fla)
          else do {
            v \<leftarrow> mcf_oracle_heap_pluggable_checker_spec.solve_imp' mm orc
                  (ns_cleanup_imp (nn - Suc 0) mm (max 10 (isqrt mm))
                     (max 3 (max 10 (isqrt mm div 4) div 10))
                     (max 10 (isqrt mm div 4)))
                  (mcf_oracle_heap_pipeline_spec.current_checker_imp mm (nn - Suc 0))
                  CheckerEpsilontic nn
                  fa sa ua oa ba fla;
            if v = VOptimumF
            then do { _ \<leftarrow> orig_flow_imp la fla 0 mm; Heap_Monad.return (True, fla) }
            else Heap_Monad.return (False, fla) } })"

text \<open>On an instance with arcs the exported program \<^emph>\<open>is\<close> the program the theorems above speak
      about: the reduction leaves the arcs alone, so the pivot sizes it recomputes from the problem
      line are the ones the locale fixes, and the arrays it hands the pipeline are the caller's.  So
      the two are equated outright and the triple transfers by a rewrite.  The one unfolding below
      is what identifies the pipeline assembled from the exported arguments with the locale's.\<close>

context dimacs_solver_imp
begin

lemma solve_imp_unfold':
  "mcf_oracle_heap_pluggable_checker_spec.solve_imp' m oracle_imp
     (ns_cleanup_imp (n - Suc 0) m (max 10 (isqrt m))
        (max 3 (max 10 (isqrt m div 4) div 10))
        (max 10 (isqrt m div 4)))
     (mcf_oracle_heap_pipeline_spec.current_checker_imp m (n - Suc 0))
   = reduced.pluggable.solve_imp'"
  by(intro ext)
    (simp add: ns_block_def ns_min_def ns_max_def ns_arcs_def
               mcf_oracle_heap_pluggable_checker_spec.solve_imp'_def
               reduced.pluggable.solve_imp'_def
               mcf_oracle_heap_pluggable_checker_spec.decide_imp'_def
               reduced.pluggable.decide_imp'_def
               mcf_oracle_heap_pipeline_spec.current_checker_imp_def
               reduced.current_checker_imp_def)

lemma dimacs_solve_prog_eq:
  "dimacs_solve_prog oracle_imp fa sa la ua oa ba m n = dimacs_solve_imp fa sa la ua oa ba"
  apply(simp add: dimacs_solve_prog_def dimacs_solve_imp_def)
  apply(simp only: if_not_P[OF edges_non_empty[THEN gr_implies_not0]])
  apply(simp only: solve_imp_unfold')
  done

theorem dimacs_solve_prog_correct:
  "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a upper * oa \<mapsto>\<^sub>a cost_list *
    ba \<mapsto>\<^sub>a balance_list>
     dimacs_solve_prog oracle_imp fa sa la ua oa ba m n
   <\<lambda>(b, ga). fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * oa \<mapsto>\<^sub>a cost_list *
              (\<exists>\<^sub>A us. ua \<mapsto>\<^sub>a us) * (\<exists>\<^sub>A bs. ba \<mapsto>\<^sub>a bs) *
              (\<exists>\<^sub>A gs. ga \<mapsto>\<^sub>a gs
               * \<up>((b \<longrightarrow> original_network.is_dimacs_Opt {1..<n}
                          (\<lambda> e. of_int (take m gs ! e)))
                   \<and> (\<not> b \<longrightarrow> (\<forall> f. \<not> original_network.is_dimacs_flow {1..<n} f))))>"
  unfolding dimacs_solve_prog_eq by(rule dimacs_solve_imp_correct)

corollary dimacs_solve_prog_marker:
  "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a upper * oa \<mapsto>\<^sub>a cost_list *
    ba \<mapsto>\<^sub>a balance_list>
     dimacs_solve_prog oracle_imp fa sa la ua oa ba m n
   <\<lambda>(b, ga). fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * oa \<mapsto>\<^sub>a cost_list *
              (\<exists>\<^sub>A us. ua \<mapsto>\<^sub>a us) * (\<exists>\<^sub>A bs. ba \<mapsto>\<^sub>a bs) *
              (\<exists>\<^sub>A gs. ga \<mapsto>\<^sub>a gs
               * \<up>((b \<longleftrightarrow> (\<exists> f. original_network.is_dimacs_flow {1..<n} f))
                   \<and> (b \<longrightarrow> original_network.is_dimacs_Opt {1..<n}
                            (\<lambda> e. of_int (take m gs ! e)))))>"
  unfolding dimacs_solve_prog_eq by(rule dimacs_solve_imp_marker)

end

subsection \<open>The empty instance\<close>

text \<open>An instance with no arcs is the one case the pipeline cannot be run on: the certifier's format
      asks for at least one arc, and with none there is nothing for an oracle to solve.  It is also
      the one case that needs no solving.  With no arcs every flow has zero excess everywhere and
      zero cost, so the instance is feasible exactly when every balance is @{term \<open>0::int\<close>}, and then
      the empty flow is optimal --- which is why the program answers from the feasibility flag alone
      and returns the array of length @{term \<open>0::nat\<close>} that @{term \<open>Array.new 0\<close>} allocates.

      That the flag says the right thing is the content below.  The reduction's own rule is
      unavailable here, being stated in a locale that assumes an arc, so the pass is re-run at
      @{term \<open>0::nat\<close>} arcs: the arc loop and the four shifts are empty, and what is left is the
      three vertex sweeps, whose conjunction pins every balance between @{term \<open>0::int\<close>} and
      @{term \<open>0::int\<close>}.\<close>

lemma sum_list_map_zero:
  "(\<And> u. v \<le> u \<Longrightarrow> u < w \<Longrightarrow> L ! u = 0) \<Longrightarrow> sum_list (map ((!) L) [v..<w]) = (0 :: 'a :: comm_monoid_add)"
  by(induction w) auto

lemma sweep_imp_rule0:
  "v + k \<le> length L \<Longrightarrow>
   <bal \<mapsto>\<^sub>a L>
     sweep_imp bal c v k tot ok
   <\<lambda>r. bal \<mapsto>\<^sub>a L
        * \<up>(fst r = tot + sum_list (map ((!) L) [v..<v + k])
            \<and> snd r = (ok \<and> (\<forall> u. v \<le> u \<and> u < v + k \<longrightarrow> c * L ! u \<le> 0)))>"
proof(induction k arbitrary: v tot ok)
  case 0
  thus ?case by(subst sweep_imp.simps) sep_auto
next
  case (Suc k)
  have vl: "v < length L" using Suc.prems by simp
  have IH: "<bal \<mapsto>\<^sub>a L>
              sweep_imp bal c (Suc v) k tot' ok'
            <\<lambda>r. bal \<mapsto>\<^sub>a L
                 * \<up>(fst r = tot' + sum_list (map ((!) L) [Suc v..<Suc v + k])
                     \<and> snd r = (ok' \<and> (\<forall> u. Suc v \<le> u \<and> u < Suc v + k \<longrightarrow> c * L ! u \<le> 0)))>"
    for tot' and ok'
    by(rule Suc.IH) (use Suc.prems in simp)
  note [simp del] = upt_Suc
  have peel: "sum_list (map ((!) L) [v..<v + Suc k])
                = L ! v + sum_list (map ((!) L) [Suc v..<Suc v + k])"
    by(simp add: upt_conv_Cons)
  have qpeel: "(\<forall> u. v \<le> u \<and> u < Suc (v + k) \<longrightarrow> Q u)
                 = (Q v \<and> (\<forall> u. Suc v \<le> u \<and> u < Suc (v + k) \<longrightarrow> Q u))" for Q
    by(auto simp add: le_Suc_eq) (metis le_neq_implies_less less_Suc_eq_le not_less_eq)
  show ?case
    unfolding peel
    by(subst sweep_imp.simps) (sep_auto simp: vl qpeel add.assoc heap: IH)
qed

lemma shift_imp_0: "shift_imp ia va bal c e 0 = Heap_Monad.return ()"
  by(subst shift_imp.simps) simp

lemma red_arcs_imp_0: "red_arcs_imp fa sa la ua oa bal i 0 sh ok = Heap_Monad.return (sh, ok)"
  by(subst red_arcs_imp.simps) simp

lemma bal_zero_iff:
  "((\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> bl ! u \<le> 0)
    \<and> (\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> 0 \<le> bl ! u)
    \<and> sum_list (map ((!) (list_update bl 0 0)) [Suc 0..<nn]) = (0 :: int))
   = (\<forall> v. Suc 0 \<le> v \<and> v < nn \<longrightarrow> bl ! v = 0)"
proof(rule iffI)
  assume "(\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> bl ! u \<le> 0)
          \<and> (\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> 0 \<le> bl ! u)
          \<and> sum_list (map ((!) (list_update bl 0 0)) [Suc 0..<nn]) = (0 :: int)"
  thus "\<forall> v. Suc 0 \<le> v \<and> v < nn \<longrightarrow> bl ! v = 0" by(auto intro: order_antisym)
next
  assume z: "\<forall> v. Suc 0 \<le> v \<and> v < nn \<longrightarrow> bl ! v = 0"
  have s: "sum_list (map ((!) (list_update bl 0 0)) [Suc 0..<nn]) = (0 :: int)"
    by(rule sum_list_map_zero) (use z in simp)
  show "(\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> bl ! u \<le> 0)
        \<and> (\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> 0 \<le> bl ! u)
        \<and> sum_list (map ((!) (list_update bl 0 0)) [Suc 0..<nn]) = (0 :: int)"
    using z s by auto
qed

lemma reduce_imp_rule0:
  assumes len: "length bl = nn" and nn: "0 < nn"
  shows
   "<fa \<mapsto>\<^sub>a fl * sa \<mapsto>\<^sub>a sl * la \<mapsto>\<^sub>a ll * ua \<mapsto>\<^sub>a ul * oa \<mapsto>\<^sub>a cl * ba \<mapsto>\<^sub>a bl>
      reduce_imp fa sa la ua oa ba 0 nn
    <\<lambda>r. fa \<mapsto>\<^sub>a fl * sa \<mapsto>\<^sub>a sl * la \<mapsto>\<^sub>a ll * ua \<mapsto>\<^sub>a ul * oa \<mapsto>\<^sub>a cl
         * ba \<mapsto>\<^sub>a list_update bl 0 0
         * \<up>(fst r = 0
             \<and> snd r = ((\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> bl ! u \<le> 0)
                        \<and> (\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> 0 \<le> bl ! u)
                        \<and> sum_list (map ((!) (list_update bl 0 0)) [Suc 0..<nn]) = 0))>"
proof -
  have sw: "<ba \<mapsto>\<^sub>a list_update bl 0 0>
              sweep_imp ba c (Suc 0) (nn - Suc 0) 0 True
            <\<lambda>r. ba \<mapsto>\<^sub>a list_update bl 0 0
                 * \<up>(fst r = sum_list (map ((!) (list_update bl 0 0)) [Suc 0..<nn])
                     \<and> snd r = (\<forall> u. Suc 0 \<le> u \<and> u < nn \<longrightarrow> c * bl ! u \<le> 0))>" for c
    using sweep_imp_rule0[of "Suc 0" "nn - Suc 0" "list_update bl 0 0" ba c 0 True] nn len
    by simp
  show ?thesis
    unfolding reduce_imp_def reduce_tail_raw_def bal_tail_def bal_out_test_def bal_in_test_def
              bal_sum_test_def red_arcs_imp_0 shift_imp_0
    by(sep_auto heap: sw simp: len nn)
qed

text \<open>The DIMACS problem itself, with no arcs: validity is the balance condition alone, and every
      valid flow costs the same, so validity and optimality coincide.\<close>

lemma dimacs_flow_no_arcs:
  "dimacs_spec.is_dimacs_flow efst esnd uu {} ll bb V f = (\<forall> v \<in> V. bb v = 0)"
  by(simp add: dimacs_spec.is_dimacs_flow_def flow_network_spec.ex_def
               multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def)

lemma dimacs_Opt_no_arcs:
  "dimacs_spec.is_dimacs_Opt efst esnd uu cc {} ll bb V f = (\<forall> v \<in> V. bb v = 0)"
  by(simp add: dimacs_spec.is_dimacs_Opt_def dimacs_flow_no_arcs cost_flow_spec.\<C>_def)

lemma dimacs_solve_prog_no_arcs:
  assumes len: "length balance_list = n" and nn: "0 < n"
  shows
   "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a upper * oa \<mapsto>\<^sub>a cost_list *
     ba \<mapsto>\<^sub>a balance_list>
      dimacs_solve_prog orc fa sa la ua oa ba 0 n
    <\<lambda>(b, ga). fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * oa \<mapsto>\<^sub>a cost_list *
               (\<exists>\<^sub>A us. ua \<mapsto>\<^sub>a us) * (\<exists>\<^sub>A bs. ba \<mapsto>\<^sub>a bs) *
               (\<exists>\<^sub>A gs. ga \<mapsto>\<^sub>a gs
                * \<up>(b = (\<forall> v. Suc 0 \<le> v \<and> v < n \<longrightarrow> balance_list ! v = 0)))>"
  unfolding dimacs_solve_prog_def
  by(sep_auto heap: reduce_imp_rule0[OF len nn] simp: bal_zero_iff)

subsection \<open>The theorem about the exported code\<close>

text \<open>Finally the same statement with \<^emph>\<open>no locale left\<close>.  The locale's assumptions become premises:
      the nine well-formedness conditions on the six input lists --- the lengths, a non-empty node
      range and endpoints that name declared nodes --- and, separately, \<open>dimacs_solver_imp_axioms\<close>,
      which is the pair of oracle assumptions \<open>oracle_imp_rule\<close> and \<open>oracle_wf\<close> of the locale above.
      That one is not a condition on the input and cannot be discharged here: the oracle is an
      external program, and the assumption says only that it refines the functional oracle.

      The optimality is spelled out too, since \<open>original_network\<close> is gone with the locale: it is
      \<open>dimacs_spec.is_dimacs_Opt\<close>, the reduction's formalisation of the DIMACS problem, at the
      endpoints, capacities, costs, lower bounds and supplies read off the input lists, over the
      node set \<open>{1..<n}\<close> of the problem line.  Nothing of the method survives in the statement.\<close>

theorem solve_dimacs_correct:
  fixes fst_list snd_list :: "nat list"
    and lower upper cost_list balance_list :: "int list"
    and m n :: nat
  defines "efst \<equiv> (\<lambda> e. if e < m then fst_list ! e else fst (prod_decode (e - m)))"
      and "esnd \<equiv> (\<lambda> e. if e < m then snd_list ! e else snd (prod_decode (e - m)))"
  assumes "length fst_list = m" and "length snd_list = m" and "length lower = m"
      and "length upper = m" and "length cost_list = m" and bal: "length balance_list = n"
      and nn: "0 < n" and "\<forall> e < m. fst_list ! e \<in> {1..<n}" and "\<forall> e < m. snd_list ! e \<in> {1..<n}"
      and "dimacs_solver_imp_axioms fst_list snd_list upper cost_list balance_list m n lower
             oracle_solve orc"
    shows
  "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a upper * oa \<mapsto>\<^sub>a cost_list *
    ba \<mapsto>\<^sub>a balance_list>
     dimacs_solve_prog orc fa sa la ua oa ba m n
   <\<lambda>(b, ga). fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * oa \<mapsto>\<^sub>a cost_list *
              (\<exists>\<^sub>A us. ua \<mapsto>\<^sub>a us) * (\<exists>\<^sub>A bs. ba \<mapsto>\<^sub>a bs) *
              (\<exists>\<^sub>A gs. ga \<mapsto>\<^sub>a gs
               * \<up>((b \<longleftrightarrow> (\<exists> f. dimacs_spec.is_dimacs_flow efst esnd
                                (\<lambda> e. ereal (of_int (upper ! e))) {0..<m}
                                (\<lambda> e. ereal (of_int (lower ! e)))
                                (\<lambda> v. of_int (balance_list ! v)) {1..<n} f))
                   \<and> (b \<longrightarrow> dimacs_spec.is_dimacs_Opt efst esnd
                             (\<lambda> e. ereal (of_int (upper ! e))) (\<lambda> e. of_int (cost_list ! e))
                             {0..<m} (\<lambda> e. ereal (of_int (lower ! e)))
                             (\<lambda> v. of_int (balance_list ! v)) {1..<n}
                             (\<lambda> e. of_int (take m gs ! e)))))>"
proof(cases "m = 0")
  case m0: True
  show ?thesis
    unfolding efst_def esnd_def m0
    by(rule ht_cons_post_prec[OF dimacs_solve_prog_no_arcs[OF bal nn]])
      (sep_auto simp: dimacs_flow_no_arcs dimacs_Opt_no_arcs)
next
  case False
  show ?thesis
    unfolding efst_def esnd_def
    by(rule dimacs_solver_imp.dimacs_solve_prog_marker[where oracle_solve = oracle_solve])
      (insert assms False, auto simp: dimacs_solver_imp_def dimacs_solver_m_def
                                      dimacs_solver_m_axioms_def dimacs_solver_def)
qed

declare mcf_oracle_heap_pluggable_checker_spec.solve_imp'_def [code]
        mcf_oracle_heap_pluggable_checker_spec.decide_imp'_def [code]
        mcf_oracle_heap_pipeline_spec.current_checker_imp_def [code]
        mcf_oracle_heap_pipeline_spec.check_answer_imp_def [code]
        mcf_oracle_heap_pipeline_spec.flag_of.simps [code]
        mcf_oracle_heap_pipeline_spec.rectify_imp.simps [code]
        mcf_oracle_heap_spec.check_optimum_imp_def [code]
        mcf_oracle_heap_spec.check_optimum_dispatch_imp_def [code]
        mcf_oracle_heap_spec.check_optimum_eps_imp_def [code]
        mcf_oracle_heap_spec.check_infeasible_imp_def [code]
        mcf_oracle_heap_spec.check_unbounded_imp_def [code]
        mcf_oracle_heap_spec.opt_loop_imp.simps [code]
        mcf_oracle_heap_spec.opt_loop_eps_imp.simps [code]
        mcf_oracle_heap_spec.cyc_loop_imp.simps [code]
        mcf_oracle_heap_spec.demand_loop_imp.simps [code]
        mcf_oracle_heap_spec.cut_loop_imp.simps [code]
        mcf_oracle_heap_spec.arr_eq_imp.simps [code]

export_code dimacs_solve_prog reduce_imp orig_flow_imp ns_cleanup_imp isqrt
  integer_of_nat integer_of_int OptimumI InfeasibleI UnboundedI
  in SML module_name DIMACS_Solver_Code

text \<open>The same code, written into the generated\_sml directory -- the one the MLton build
      compiles from -- so that an external driver can compile it: the solver, the reduction and
      the back-transformation, plus the integer constructors a driver needs in order to build the
      six input arrays.

      It used to be written next to this theory and copied into generated\_sml by hand. The copy is
      what the driver builds, so a forgotten copy step meant building against code that was no
      longer what had been proved -- and nothing about that failure is visible from the outside:
      every test passes, against the wrong program. Writing it where the build reads it does not
      detect that, it makes it impossible. The path is still anchored at this theory's own
      directory, so generation stays unaware of how the surrounding project is organised.\<close>
ML \<open>
  val (files, _) =
    Code_Target.produce_code \<^context> false
      [\<^const_name>\<open>dimacs_solve_prog\<close>, \<^const_name>\<open>reduce_imp\<close>,
       \<^const_name>\<open>orig_flow_imp\<close>, \<^const_name>\<open>ns_cleanup_imp\<close>,
       \<^const_name>\<open>isqrt\<close>, \<^const_name>\<open>nat_of_integer\<close>,
       \<^const_name>\<open>int_of_integer\<close>, \<^const_name>\<open>integer_of_nat\<close>,
       \<^const_name>\<open>integer_of_int\<close>, \<^const_name>\<open>OptimumI\<close>,
       \<^const_name>\<open>InfeasibleI\<close>, \<^const_name>\<open>UnboundedI\<close>]
      "SML" "DIMACS_Solver_Code" NONE [];
  val code = String.concat (map (fn (_, b) => Bytes.content b) files);
  val dir =
    Isabelle_System.make_directory
      (Path.append (Resources.master_directory \<^theory>) (Path.basic "generated_sml"));
  val path = Path.append dir (Path.basic "DIMACS_Solver_Code.sml");
  val () = File.write path code;
  writeln ("wrote " ^ Path.implode path ^ ": " ^ Int.toString (size code) ^ " chars")
\<close>

end
