section \<open>An untrusted min-cost-flow oracle and its certificates\<close>

text \<open>The middle stage of the solver pipeline. The DIMACS reduction of \<open>Mincost_Solver_Reduction\<close>
      turns an instance into the library's standard format, and this theory hands such an instance
      to an \<^emph>\<open>external, untrusted\<close> solver. The solver returns one of three verdicts \<^emph>\<open>together
      with a certificate\<close>, which a checker validates; only if the check fails does the pipeline fall
      back on a verified procedure.

      \<^emph>\<open>Nothing whatever is assumed about the oracle.\<close> Its type fixes the format of what comes
      back, and every other property --- that the flow has the right length, that it respects the
      capacities, that the cut is a set of vertices, that the cycle is a cycle --- is the checker's
      job. The proof locales below carry assumptions about the \<^emph>\<open>instance\<close> only, never about
      @{term oracle_solve}.\<close>

theory Mincost_Oracle_Certificates
  imports Mincost_Solver_Reduction
          Flow_Theory.Optimality_Certification Data_Structures.Real_Embedding
begin

subsection \<open>The instance handed to the oracle\<close>

text \<open>The instance in the shape the reduction produces: the arcs are @{term \<open>{0..<fi_m}\<close>} and carry
      four parallel lists; the vertices are the names @{term \<open>{1..fi_n}\<close>} and carry one balance list
      of length @{term \<open>Suc fi_n\<close>}, indexed by the vertex name, whose slot @{term \<open>0::nat\<close>} is a
      reserved sentinel. A capacity of @{term \<open>- 1\<close>} denotes an uncapacitated arc; every other entry
      is non-negative. A record keeps @{term oracle_solve} a one-argument function. The reserved slot
      travels to the solver as an ordinary isolated node of balance \<open>0\<close>, which cannot change its
      verdict.\<close>

record 'n flow_instance =
  fi_n    :: nat
  fi_m    :: nat
  fi_fst  :: "nat list"
  fi_snd  :: "nat list"
  fi_cap  :: "'n list"
  fi_cost :: "'n list"
  fi_bal  :: "'n list"

subsection \<open>The oracle's answer\<close>

text \<open>The three verdicts, each with the certificate that witnesses it:
      \<^item> @{text OracleOptimum}: a primal-dual pair, the flow indexed by arc and the potentials
        indexed by vertex name, together with a scale @{text oa_mode} (see below).
      \<^item> @{text OracleInfeasible}: a cut, as an indicator over the vertex names (a non-zero cell
        means the vertex is in the cut).
      \<^item> @{text OracleUnbounded}: a cycle, as a list of arc indices, the shape
        @{const has_neg_infty_cycle} quantifies over.

      Every verdict carries the flow the solver stopped at, so that a verified procedure can be
      warm-started from it when the certificate is rejected. Nothing is constrained here; a
      certificate is a \<^emph>\<open>claim\<close>.

      Two modes govern how an optimality claim is checked. @{text checker_mode} is a parameter of the
      checker: \<open>CheckerNormal\<close> always runs the exact check, \<open>CheckerEpsilontic\<close> accepts the
      epsilon-slack one. @{text oa_mode} is part of the certificate and names the scale \<open>Mn\<close> its
      potentials were computed against. The soundness theorem of the epsilon check
      (\<open>optimality_from_eps_potentials\<close>) holds for \<^emph>\<open>every\<close> scale exceeding the vertex count, so no
      trust in the value is needed; a scale that is too small is routed to the exact check.\<close>

datatype checker_mode = CheckerNormal | CheckerEpsilontic

datatype 'n oracle_answer =
    OracleOptimum    (oa_flow: "'n list") (oa_pot: "'n list") (oa_mode: "'n")
  | OracleInfeasible (oa_flow: "'n list") (oa_cut: "nat list")
  | OracleUnbounded  (oa_flow: "'n list") (oa_cycle: "nat list")

text \<open>What the pipeline finally reports is a verdict without a certificate; the optimal case keeps
      the flow.\<close>

datatype 'n solver_verdict =
    VOptimum (v_flow: "'n list")
  | VInfeasible
  | VUnbounded

subsection \<open>The code locale\<close>

text \<open>Assumption-free: it fixes the instance data and the oracle and holds the executable
      material. The embedding @{term h} into the reals is a proof device and not a parameter here,
      exactly as in \<open>initial_basis_code_spec\<close>.\<close>

locale mcf_oracle_spec =
  fixes fst_list      :: "nat list"
    and snd_list      :: "nat list"
    and capacity_list :: "('n :: linordered_idom) list"
    and cost_list     :: "'n list"
    and balance_list  :: "'n list"
    and m             :: nat
    and n             :: nat
    and oracle_solve  :: "'n flow_instance \<Rightarrow> 'n oracle_answer"
begin

definition orc_input :: "'n flow_instance" where
  "orc_input = \<lparr> fi_n = n, fi_m = m, fi_fst = fst_list, fi_snd = snd_list,
                 fi_cap = capacity_list, fi_cost = cost_list, fi_bal = balance_list \<rparr>"

definition orc_answer :: "'n oracle_answer" where
  "orc_answer = oracle_solve orc_input"

text \<open>Reading the format.  Arcs are the indices below @{term m} and the vertices the names
      @{term \<open>{Suc 0..n}\<close>}; neither set is materialised, the sweeps below counting instead.  These
      accessors name the format's conventions for the reader --- what a cell of each list means and
      how a capacity is decoded --- and are used where the cost of a call does not matter; the loops
      write the loads out.\<close>

definition tail_of :: "nat \<Rightarrow> nat" where "tail_of e = fst_list ! e"

definition head_of :: "nat \<Rightarrow> nat" where "head_of e = snd_list ! e"

definition cost_of :: "nat \<Rightarrow> 'n" where "cost_of e = cost_list ! e"

text \<open>An arc is uncapacitated exactly when its capacity cell holds the sentinel @{term \<open>- 1\<close>}.\<close>

definition uncapacitated :: "nat \<Rightarrow> bool" where
  "uncapacitated e = (capacity_list ! e = - 1)"

definition cap_of :: "nat \<Rightarrow> 'n" where "cap_of e = capacity_list ! e"

text \<open>The balance of a vertex, and the potential a dual certificate assigns to it: both lists are
      indexed by the vertex name, so slot @{term \<open>0::nat\<close>} of either is never consulted at a
      vertex.\<close>

definition balance_of :: "nat \<Rightarrow> 'n" where "balance_of v = balance_list ! v"

definition pot_of :: "'n list \<Rightarrow> nat \<Rightarrow> 'n" where "pot_of pot v = pot ! v"

subsection \<open>The certificate checkers\<close>

text \<open>Ported from the SML mock \<open>ns_tree_benchmark/adaptor/lemon_ns_check.sml\<close>, which fixes the
      certificate conventions of the external oracle. Two departures: the lengths of the
      certificate arrays are checked first, since @{const nth} past the end is an unspecified value;
      and an uncapacitated arc is recognised by the sentinel @{term \<open>cap e = - 1\<close>}.

      Each check is one counted loop: a first-order tail-recursive function with a cursor, a
      remaining count and its accumulators as separate arguments. Nothing is materialised (no
      @{term \<open>[0..<m]\<close>}, no @{const filter}), nothing is passed as a function, no cell is loaded
      twice, and every guard is a conjunct in front of the recursive call, so a rejection stops the
      loop at once. The predicates each loop fuses are kept alongside it as its specification. All
      arithmetic is in the instance's own \<^class>\<open>linordered_idom\<close> @{typ 'n}, with no division, so
      the checks are exact; the @{typ nat}s are positions, counters and the flags of a cut.\<close>

text \<open>The reduced cost of an arc under a dual certificate: @{term \<open>\<c> e + \<pi> (fst e) - \<pi> (snd e)\<close>}.\<close>

definition rc_of :: "'n list \<Rightarrow> nat \<Rightarrow> 'n" where
  "rc_of pot e = cost_list ! e + pot ! (fst_list ! e) - pot ! (snd_list ! e)"

text \<open>Primal feasibility of one arc together with complementary slackness on it: a strictly positive
      reduced cost forces the arc empty, a strictly negative one forces it saturated --- and therefore
      forces it to be capacitated at all, an uncapacitated arc of negative reduced cost being exactly
      the unbounded case.\<close>

definition arc_ok_opt :: "'n list \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow> bool" where
  "arc_ok_opt fl pot e =
     (0 \<le> fl ! e \<and>
      (\<not> uncapacitated e \<longrightarrow> fl ! e \<le> capacity_list ! e) \<and>
      (0 < rc_of pot e \<longrightarrow> fl ! e = 0) \<and>
      (rc_of pot e < 0 \<longrightarrow> \<not> uncapacitated e \<and> fl ! e = capacity_list ! e))"

text \<open>The net out-flow of every vertex, scattered in one arc sweep into a list indexed by vertex
      name.  The head is updated first and read back by the tail update, so a self-loop cancels
      instead of counting twice --- the same order the reduction's pass uses.\<close>

definition net_out :: "'n list \<Rightarrow> 'n list" where
  "net_out fl =
     fold (\<lambda>e acc. let a = acc[snd_list ! e := acc ! (snd_list ! e) - fl ! e]
                   in a[fst_list ! e := a ! (fst_list ! e) + fl ! e])
          [0..<m] (replicate (Suc n) 0)"

text \<open>\<^emph>\<open>Optimality.\<close> One sweep decides @{const arc_ok_opt} for each arc and scatters its flow
      into the accumulator @{const net_out} would build. The flow and the capacity are loaded first,
      as they decide primal feasibility alone. The loop ends by comparing the accumulator with the
      balance array, which covers the sentinel slot too.\<close>

fun opt_loop :: "'n list \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> bool" where
  "opt_loop fl pot e 0 net = (net = balance_list)"
| "opt_loop fl pot e (Suc k) net =
     (let f = fl ! e; c = capacity_list ! e
      in 0 \<le> f \<and> (c = - 1 \<or> f \<le> c)
         \<and> (let u = fst_list ! e; v = snd_list ! e
            in (let rc = cost_list ! e + pot ! u - pot ! v
                in if 0 < rc then f = 0 else if rc < 0 then c \<noteq> - 1 \<and> f = c else True)
               \<and> (let net' = net[v := net ! v - f]
                  in opt_loop fl pot (Suc e) k (net'[u := net' ! u + f]))))"

definition check_optimum :: "'n list \<Rightarrow> 'n list \<Rightarrow> bool" where
  "check_optimum fl pot =
     (length fl = m \<and> length pot = Suc n \<and> opt_loop fl pot 0 m (replicate (Suc n) 0))"

text \<open>\<^emph>\<open>{\isasymepsilon}-optimality.\<close> A cheaper certificate, which a cost-scaling oracle
      produces without a final correction pass: every residual arc need only clear a slack of one
      unit once its reduced cost is scaled by \<open>Mn\<close>: \<open>Mn \<sqdot> rc(e) \<ge> -1\<close> if the arc
      can still take flow, and \<open>Mn \<sqdot> rc(e) \<le> 1\<close> if it carries flow. \<open>Mn\<close> is the
      certificate's @{const oa_mode}, and the check tests the one condition the soundness theorem
      needs, \<open>n < Mn\<close>.\<close>

definition scaled_rc_of :: "'n \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow> 'n" where
  "scaled_rc_of Mn pot e = Mn * cost_list ! e + pot ! (fst_list ! e) - pot ! (snd_list ! e)"

definition arc_ok_eps :: "'n \<Rightarrow> 'n list \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow> bool" where
  "arc_ok_eps Mn fl pot e =
     (0 \<le> fl ! e \<and>
      (\<not> uncapacitated e \<longrightarrow> fl ! e \<le> capacity_list ! e) \<and>
      (uncapacitated e \<or> fl ! e < capacity_list ! e \<longrightarrow> - 1 \<le> scaled_rc_of Mn pot e) \<and>
      (0 < fl ! e \<longrightarrow> scaled_rc_of Mn pot e \<le> 1))"

fun opt_loop_eps :: "'n \<Rightarrow> 'n list \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> bool" where
  "opt_loop_eps Mn fl pot e 0 net = (net = balance_list)"
| "opt_loop_eps Mn fl pot e (Suc k) net =
     (let f = fl ! e; c = capacity_list ! e
      in 0 \<le> f \<and> (c = - 1 \<or> f \<le> c)
         \<and> (let u = fst_list ! e; v = snd_list ! e
            in (let rc = Mn * cost_list ! e + pot ! u - pot ! v
                in (c = - 1 \<or> f < c \<longrightarrow> - 1 \<le> rc) \<and> (0 < f \<longrightarrow> rc \<le> 1))
               \<and> (let net' = net[v := net ! v - f]
                  in opt_loop_eps Mn fl pot (Suc e) k (net'[u := net' ! u + f]))))"

definition check_optimum_eps :: "'n \<Rightarrow> 'n list \<Rightarrow> 'n list \<Rightarrow> bool" where
  "check_optimum_eps Mn fl pot =
     (length fl = m \<and> length pot = Suc n \<and> of_nat n < Mn \<and>
      opt_loop_eps Mn fl pot 0 m (replicate (Suc n) 0))"

text \<open>\<^emph>\<open>Dispatch.\<close> The routing test is the epsilon check's own gate
      \<open>of_nat n < \<bar>oa_mode\<bar>\<close>, so a scale that would be rejected there goes to the exact
      check instead, which may still accept it. In \<open>CheckerNormal\<close> mode @{const oa_mode} is
      not inspected.\<close>

definition check_optimum_dispatch :: "checker_mode \<Rightarrow> 'n list \<Rightarrow> 'n list \<Rightarrow> 'n \<Rightarrow> bool" where
  "check_optimum_dispatch cm fl pot certm =
     (case cm of
        CheckerNormal     \<Rightarrow> check_optimum fl pot
      | CheckerEpsilontic \<Rightarrow> (if of_nat n < \<bar>certm\<bar> then check_optimum_eps \<bar>certm\<bar> fl pot
                              else check_optimum fl pot))"

text \<open>\<^emph>\<open>Unboundedness.\<close> The conjuncts are the premises of
      @{thm [source] has_neg_infty_cycleI}: non-empty, closed, inside the arc set, every arc
      uncapacitated, of negative cost.\<close>

definition cyc_linked :: "nat list \<Rightarrow> bool" where
  "cyc_linked cyc =
     list_all (\<lambda>i. snd_list ! (cyc ! i) = fst_list ! (cyc ! ((Suc i) mod length cyc)))
              [0..<length cyc]"

text \<open>One traversal decides all of them. The loop carries the head of the previous arc, seeded with
      the tail of the first, so linkage is one comparison and closure is the same comparison after
      the last step. The cycle is the one certificate read sequentially, by pattern matching.\<close>

fun cyc_loop :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> bool" where
  "cyc_loop [] prev s tot = (prev = s \<and> tot < 0)"
| "cyc_loop (e # es) prev s tot =
     (e < m \<and> capacity_list ! e = - 1 \<and> prev = fst_list ! e
      \<and> cyc_loop es (snd_list ! e) s (tot + cost_list ! e))"

definition check_unbounded :: "nat list \<Rightarrow> bool" where
  "check_unbounded cyc =
     (case cyc of [] \<Rightarrow> False
                | e0 # _ \<Rightarrow> e0 < m \<and> (let s = fst_list ! e0 in cyc_loop cyc s s 0))"

text \<open>\<^emph>\<open>Infeasibility.\<close> The certificate is the vertex set \<open>S\<close> of a Gale--Hoffman
      violating cut, as an indicator: more must leave \<open>S\<close> than the arcs out of it can
      carry, and no uncapacitated arc may leave it. Marking the reserved slot \<open>0\<close> changes
      neither side.\<close>

definition in_cut :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "in_cut S v = (S ! v \<noteq> 0)"

definition leaves_cut :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "leaves_cut S e = (in_cut S (fst_list ! e) \<and> \<not> in_cut S (snd_list ! e))"

definition cut_capacity :: "nat list \<Rightarrow> 'n" where
  "cut_capacity S = sum_list (map (\<lambda>e. capacity_list ! e) (filter (leaves_cut S) [0..<m]))"

text \<open>The demand is swept first and handed to the arc loop as a scalar; the arc loop either rejects
      an uncapacitated arc leaving the cut or adds its capacity.\<close>

fun demand_loop :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n" where
  "demand_loop S v 0 acc = acc"
| "demand_loop S v (Suc k) acc =
     demand_loop S (Suc v) k (if S ! v \<noteq> 0 then acc + balance_list ! v else acc)"

fun cut_loop :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool" where
  "cut_loop S e 0 cap dem = (cap < dem)"
| "cut_loop S e (Suc k) cap dem =
     (if S ! (fst_list ! e) \<noteq> 0 \<and> S ! (snd_list ! e) = 0
      then let c = capacity_list ! e in c \<noteq> - 1 \<and> cut_loop S (Suc e) k (cap + c) dem
      else cut_loop S (Suc e) k cap dem)"

definition check_infeasible :: "nat list \<Rightarrow> bool" where
  "check_infeasible S =
     (length S = Suc n \<and> cut_loop S 0 m 0 (demand_loop S 0 (Suc n) 0))"

text \<open>The dispatcher checks each verdict against its own certificate; a rejected certificate says
      nothing about the instance. The mode-aware dispatcher differs only for \<open>OracleOptimum\<close>.\<close>

definition check_answer :: "'n oracle_answer \<Rightarrow> bool" where
  "check_answer a =
     (case a of OracleOptimum fl pot _ \<Rightarrow> check_optimum fl pot
              | OracleInfeasible _ S   \<Rightarrow> check_infeasible S
              | OracleUnbounded _ cyc  \<Rightarrow> check_unbounded cyc)"

definition check_answer_dispatch :: "checker_mode \<Rightarrow> 'n oracle_answer \<Rightarrow> bool" where
  "check_answer_dispatch cm a =
     (case a of OracleOptimum fl pot certm \<Rightarrow> check_optimum_dispatch cm fl pot certm
              | OracleInfeasible _ S       \<Rightarrow> check_infeasible S
              | OracleUnbounded _ cyc      \<Rightarrow> check_unbounded cyc)"

text \<open>Screening is its own function, so that @{const orc_answer} occurs once and the external
      solver runs once. A verdict drops the certificate.\<close>

definition screen :: "'n oracle_answer \<Rightarrow> 'n oracle_answer option" where
  "screen a = (if check_answer a then Some a else None)"

definition checked_answer :: "'n oracle_answer option" where
  "checked_answer = screen orc_answer"

text \<open>Reporting an answer that survived the check: the certificate has done its work and is dropped,
      leaving the verdict and, where there is one, the solution.  This is where the checking layer
      ends --- @{term None} means the oracle was no use, and it is the next layer's business what to
      do about it.\<close>

definition verdict_of :: "'n oracle_answer \<Rightarrow> 'n solver_verdict" where
  "verdict_of a = (case a of OracleOptimum fl _ _  \<Rightarrow> VOptimum fl
                           | OracleInfeasible _ _  \<Rightarrow> VInfeasible
                           | OracleUnbounded _ _   \<Rightarrow> VUnbounded)"

definition checked_verdict :: "'n solver_verdict option" where
  "checked_verdict = map_option verdict_of checked_answer"

end

subsection \<open>Smoke tests\<close>

text \<open>Each line is one behaviour: the accepted certificate, then the ways of failing it, including a
      self-loop, a rotated cycle, a cut marking the reserved slot, and a certificate of the wrong
      length.\<close>

lemma opt_accept:    "mcf_oracle_spec.check_optimum [1] [2] [5::int] [3] [0,1,-1] 1 2 [1] [0,0,3]"
  and opt_selfloop:  "mcf_oracle_spec.check_optimum [1] [1] [5::int] [0] [0,0] 1 1 [3] [0,0]"
  and opt_balance:   "\<not> mcf_oracle_spec.check_optimum [1] [2] [5::int] [3] [0,1,-1] 1 2 [2] [0,0,3]"
  and opt_slack:     "\<not> mcf_oracle_spec.check_optimum [1] [2] [5::int] [3] [0,1,-1] 1 2 [1] [0,0,0]"
  and opt_length:    "\<not> mcf_oracle_spec.check_optimum [1] [2] [5::int] [3] [0,1,-1] 1 2 [1,1] [0,0,3]"
  by (simp_all add: mcf_oracle_spec.check_optimum_def mcf_oracle_spec.opt_loop.simps
                   eval_nat_numeral)

lemma unb_accept:   "mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 [0,1]"
  and unb_rotated:  "mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 [1,0]"
  and unb_open:     "\<not> mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 [0]"
  and unb_finite:   "\<not> mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,4::int] [-1,0] 2 [0,1]"
  and unb_empty:    "\<not> mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 []"
  and unb_range:    "\<not> mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [-1,0] 2 [5]"
  and unb_cost:     "\<not> mcf_oracle_spec.check_unbounded [1,2] [2,1] [-1,-1::int] [1,0] 2 [0,1]"
  by (simp_all add: mcf_oracle_spec.check_unbounded_def mcf_oracle_spec.cyc_loop.simps)

lemma inf_accept:   "mcf_oracle_spec.check_infeasible [1] [2] [1::int] [0,5,-5] 1 2 [0,1,0]"
  and inf_sentinel: "mcf_oracle_spec.check_infeasible [1] [2] [1::int] [0,5,-5] 1 2 [1,1,0]"
  and inf_empty:    "\<not> mcf_oracle_spec.check_infeasible [1] [2] [1::int] [0,5,-5] 1 2 [0,0,0]"
  and inf_infinite: "\<not> mcf_oracle_spec.check_infeasible [1] [2] [-1::int] [0,5,-5] 1 2 [0,1,0]"
  and inf_length:   "\<not> mcf_oracle_spec.check_infeasible [1] [2] [1::int] [0,5,-5] 1 2 [0,1]"
  by (simp_all add: mcf_oracle_spec.check_infeasible_def mcf_oracle_spec.cut_loop.simps
                   mcf_oracle_spec.demand_loop.simps eval_nat_numeral)

subsection \<open>The proof locale\<close>

text \<open>The instance format, and nothing else: exactly the properties the reduction establishes for
      its output. That the balances sum to zero makes an optimality certificate possible at all; a
      vertex without arcs has balance zero because the reduction's range test forces it, and the
      balance condition of \<open>check_optimum\<close> is a list equality over \<^emph>\<open>all\<close> slots. There is
      deliberately no assumption on @{term oracle_solve}.\<close>

locale mcf_oracle =
  mcf_oracle_spec where capacity_list = capacity_list +
  real_embedding where h = "h :: 'n \<Rightarrow> real"
  for capacity_list :: "('n :: linordered_idom) list" and h +
  assumes length_fst_list:  "length fst_list = m"
      and length_snd_list:  "length snd_list = m"
      and length_capacity:  "length capacity_list = m"
      and length_cost_list: "length cost_list = m"
      and length_balance:   "length balance_list = Suc n"
      and arcs_nonempty:    "0 < m"
      and nodes_nonempty:   "0 < n"
      and tail_is_vertex:   "\<And>e. e < m \<Longrightarrow> fst_list ! e \<in> {Suc 0..n}"
      and head_is_vertex:   "\<And>e. e < m \<Longrightarrow> snd_list ! e \<in> {Suc 0..n}"
      and capacity_format:  "\<And>e. e < m \<Longrightarrow> 0 \<le> capacity_list ! e \<or> capacity_list ! e = - 1"
      and balance_sentinel: "balance_list ! 0 = 0"
      and balance_sum_zero: "sum_list balance_list = 0"
      and isolated_zero:    "\<And>v. \<lbrakk>v \<in> {Suc 0..n}; \<forall> e < m. fst_list ! e \<noteq> v \<and> snd_list ! e \<noteq> v\<rbrakk> \<Longrightarrow> balance_list ! v = 0"
begin

subsection \<open>What the lists mean\<close>

text \<open>The instance read as a cost-flow network, as the reduction reads its output: the arcs are
      the indices below @{term m}, and the sentinel @{term \<open>- 1::'n\<close>} is decoded as @{term \<infinity>}. The
      synthetic edges of @{term create_edge} lie outside @{term \<open>{0..<m}\<close>}. The soundness statements
      below are phrased in the library's notions for this network.\<close>

definition cap_u :: "nat \<Rightarrow> ereal" where
  "cap_u e = (if e < m \<and> \<not> uncapacitated e then ereal (h (capacity_list ! e)) else \<infinity>)"

definition bal :: "nat \<Rightarrow> real" where
  "bal v = h (balance_list ! v)"

lemma cap_u_nonneg: "0 \<le> cap_u e"
  using capacity_format[of e]
  by (auto simp: cap_u_def uncapacitated_def zero_ereal_def)

sublocale network: cost_flow_network
  where \<E>           = "{0..<m}"
    and fst          = "\<lambda> e. if e < m then fst_list ! e else Product_Type.fst (prod_decode (e - m))"
    and snd          = "\<lambda> e. if e < m then snd_list ! e else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "\<lambda> u v. m + prod_encode (u, v)"
    and \<u>           = cap_u
    and \<c>           = "\<lambda> e. h (cost_list ! e)"
  by (unfold_locales) (auto simp: arcs_nonempty cap_u_nonneg)

lemma net_delta_plus:  "network.delta_plus v  = {e. e < m \<and> fst_list ! e = v}"
  and net_delta_minus: "network.delta_minus v = {e. e < m \<and> snd_list ! e = v}"
  by (auto simp: multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def)

lemma net_make_pair: "e < m \<Longrightarrow> network.make_pair e = (fst_list ! e, snd_list ! e)"
  by (simp add: multigraph_spec.make_pair_def)

lemma net_endpoints_V:
  "e < m \<Longrightarrow> fst_list ! e \<in> network.\<V>" "e < m \<Longrightarrow> snd_list ! e \<in> network.\<V>"
  using net_make_pair[of e]
  by force+

lemma net_V_subset: "network.\<V> \<subseteq> {Suc 0..n}"
  using tail_is_vertex head_is_vertex
  by (fastforce simp: dVs_def multigraph_spec.make_pair_def)

lemma card_V_le_n: "card network.\<V> \<le> n"
  using card_mono[OF finite_atLeastAtMost net_V_subset]
  by simp

lemma h_foldr_cost:
  "foldr (\<lambda> e. (+) (h (cost_list ! e))) cyc 0 = h (foldr (\<lambda> e. (+) (cost_list ! e)) cyc 0)"
  by (induction cyc) (auto simp: h_add)

text \<open>Every loop below consumes one index and recurses on the rest.\<close>

subsection \<open>Unboundedness: the cycle certificate is sound\<close>

text \<open>The walk of @{const cyc_loop} passes only uncapacitated arcs of the instance, chains them into
      a walk from the seed, and accumulates a negative cost.\<close>

lemma cyc_loop_props:
  "cyc_loop cyc prev s tot \<Longrightarrow>
     (\<forall> e \<in> set cyc. e < m \<and> uncapacitated e)
     \<and> cas prev (map network.make_pair cyc) s
     \<and> foldr (\<lambda> e. (+) (cost_list ! e)) cyc 0 + tot < 0"
proof(induction cyc arbitrary: prev tot)
  case (Cons e es)
  show ?case
    using Cons.prems Cons.IH[of "snd_list ! e" "tot + cost_list ! e"]
    by (auto simp: uncapacitated_def net_make_pair algebra_simps)
qed simp

lemma check_unbounded_sound:
  assumes "check_unbounded cyc"
  shows "has_neg_infty_cycle network.make_pair {0..<m} (\<lambda> e. h (cost_list ! e)) cap_u"
proof-
  obtain e0 es where "cyc = e0 # es" "e0 < m" "cyc_loop cyc (fst_list ! e0) (fst_list ! e0) 0"
    using assms
    by (auto simp: check_unbounded_def split: list.splits)
  moreover hence "awalk (network.make_pair ` {0..<m}) (fst_list ! e0) (map network.make_pair cyc) (fst_list ! e0)"
    using cyc_loop_props[of cyc "fst_list ! e0" "fst_list ! e0" 0] net_endpoints_V(1)[of e0]
    by (auto simp: awalk_def)
  ultimately show ?thesis
    using cyc_loop_props[of cyc "fst_list ! e0" "fst_list ! e0" 0]
    by (intro has_neg_infty_cycleI) (auto simp: closed_w_def cap_u_def h_foldr_cost)
qed

subsection \<open>Infeasibility: the cut certificate is sound\<close>

lemma demand_loop_sum:
  "demand_loop S v k acc = acc + (\<Sum> i \<in> {i \<in> {v..<v + k}. in_cut S i}. balance_list ! i)"
proof(induction k arbitrary: v acc)
  case (Suc k)
  have "v \<notin> {i \<in> {Suc v..<Suc v + k}. in_cut S i}"
    by auto
  thus ?case
    using Suc.IH[of "Suc v"]
    unfolding range_split_first
    by (auto simp: in_cut_def algebra_simps)
qed simp

lemma cut_loop_props:
  "cut_loop S e k cap dem \<Longrightarrow>
     (\<forall> i \<in> {e..<e + k}. leaves_cut S i \<longrightarrow> \<not> uncapacitated i)
     \<and> cap + (\<Sum> i \<in> {i \<in> {e..<e + k}. leaves_cut S i}. capacity_list ! i) < dem"
proof(induction k arbitrary: e cap)
  case (Suc k)
  have "e \<notin> {i \<in> {Suc e..<Suc e + k}. leaves_cut S i}"
    by auto
  thus ?case
    using Suc.prems Suc.IH[of "Suc e" "cap + capacity_list ! e"] Suc.IH[of "Suc e" cap]
    unfolding range_split_first
    by (cases "leaves_cut S e")
       (auto simp: uncapacitated_def leaves_cut_def in_cut_def Let_def algebra_simps order_le_less)
qed simp

text \<open>The flagged vertices form a cut whose crossing arcs are the ones @{const leaves_cut} selects,
      as both endpoints of an arc are vertices.\<close>

lemma net_Delta_plus_cut:
  "network.Delta_plus {v \<in> network.\<V>. in_cut S v} = {e \<in> {0..<m}. leaves_cut S e}"
  using net_endpoints_V
  by (auto simp: multigraph_spec.Delta_plus_def leaves_cut_def)

text \<open>A flagged slot that is not a vertex has balance zero: slot \<open>0\<close> by the sentinel, a name no arc
      mentions by @{thm [source] isolated_zero}.\<close>

lemma cut_balance_sum:
  "(\<Sum> i \<in> {i \<in> {0..<Suc n}. in_cut S i}. balance_list ! i)
     = (\<Sum> v \<in> {v \<in> network.\<V>. in_cut S v}. balance_list ! v)"
proof(rule sum.mono_neutral_right)
  show "{v \<in> network.\<V>. in_cut S v} \<subseteq> {i \<in> {0..<Suc n}. in_cut S i}"
    using net_V_subset
    by auto
  have "balance_list ! i = 0" if "i \<in> {i \<in> {0..<Suc n}. in_cut S i} - {v \<in> network.\<V>. in_cut S v}" for i
    using that balance_sentinel net_endpoints_V
    by (cases "i = 0") (auto intro!: isolated_zero)
  thus "\<forall> i \<in> {i \<in> {0..<Suc n}. in_cut S i} - {v \<in> network.\<V>. in_cut S v}. balance_list ! i = 0"
    by blast
qed simp

text \<open>Soundness is the Gale--Hoffman bound @{thm [source] network.flow_less_cut}: the balances
      inside a vertex set never exceed the capacity leaving it.\<close>

lemma check_infeasible_sound:
  assumes "check_infeasible S"
  shows "\<nexists> f. network.isbflow f bal"
proof-
  define X where "X = {v \<in> network.\<V>. in_cut S v}"
  have "(\<forall> i \<in> {0..<m}. leaves_cut S i \<longrightarrow> \<not> uncapacitated i)
        \<and> h (\<Sum> i \<in> {i \<in> {0..<m}. leaves_cut S i}. capacity_list ! i) < h (\<Sum> v \<in> X. balance_list ! v)"
    using assms cut_loop_props[of S 0 m 0 "demand_loop S 0 (Suc n) 0"] demand_loop_sum[of S 0 "Suc n" 0] cut_balance_sum[of S]
    by (simp add: check_infeasible_def X_def)
  hence "network.Cap X < sum bal X"
    by (simp add: flow_network_spec.Cap_def X_def net_Delta_plus_cut cap_u_def bal_def h_sum)
  thus ?thesis
    using network.flow_less_cut[of _ bal X]
    by (force simp: X_def)
qed

subsection \<open>Optimality: the primal-dual certificate is sound\<close>

text \<open>One step of the scatter at one vertex; the two updates cancel at a self-loop.\<close>

lemma net_step_nth:
  "\<lbrakk>u < length net; v < length net; w < length net\<rbrakk> \<Longrightarrow>
     (let net' = net[v := net ! v - f] in net'[u := net' ! u + f]) ! w
       = net ! w + (if u = w then f else 0) - (if v = w then (f::'n) else 0)"
  by (auto simp: nth_list_update Let_def)

text \<open>The invariant of both optimality loops, for any loop \<open>L\<close> that checks \<open>P\<close> at the current
      arc and scatters its flow: at the end the accumulator is the balance array, so the net
      out-flow of every vertex is its balance.\<close>

lemma scatter_loop_props:
  assumes "\<And> e k net. L e (Suc k) net \<Longrightarrow> P e \<and> L (Suc e) k
             (let net' = net[snd_list ! e := net ! (snd_list ! e) - fl ! e]
              in net'[fst_list ! e := net' ! (fst_list ! e) + fl ! e])"
    "\<And> e net. L e 0 net \<Longrightarrow> net = balance_list"
  shows "\<lbrakk>L e k net; length net = Suc n; e + k \<le> m\<rbrakk> \<Longrightarrow>
     (\<forall> i \<in> {e..<e + k}. P i)
     \<and> (\<forall> v \<le> n. balance_list ! v = net ! v
                    + (\<Sum> i \<in> {i \<in> {e..<e + k}. fst_list ! i = v}. fl ! i)
                    - (\<Sum> i \<in> {i \<in> {e..<e + k}. snd_list ! i = v}. fl ! i))"
proof(induction k arbitrary: e net)
  case 0
  thus ?case
    using assms(2)
    by auto
next
  case (Suc k)
  define net' where "net' = (let nn = net[snd_list ! e := net ! (snd_list ! e) - fl ! e]
                             in nn[fst_list ! e := nn ! (fst_list ! e) + fl ! e])"
  have "P e" "L (Suc e) k net'" "length net' = Suc n"
    using assms(1) Suc.prems
    by (auto simp: net'_def Let_def)
  hence "(\<forall> i \<in> {Suc e..<Suc e + k}. P i)
         \<and> (\<forall> v \<le> n. balance_list ! v = net' ! v
                    + (\<Sum> i \<in> {i \<in> {Suc e..<Suc e + k}. fst_list ! i = v}. fl ! i)
                    - (\<Sum> i \<in> {i \<in> {Suc e..<Suc e + k}. snd_list ! i = v}. fl ! i))"
    using Suc.IH[of "Suc e" net'] Suc.prems(3)
    by simp
  moreover have "net' ! w = net ! w + (if fst_list ! e = w then fl ! e else 0)
                              - (if snd_list ! e = w then fl ! e else 0)" if "w \<le> n" for w
    using that Suc.prems(2,3) tail_is_vertex[of e] head_is_vertex[of e]
          net_step_nth[of "fst_list ! e" net "snd_list ! e" w "fl ! e"]
    by (auto simp: net'_def)
  moreover have "{e..<e + Suc k} = insert e {Suc e..<Suc e + k}" "e \<notin> {i \<in> {Suc e..<Suc e + k}. Q i}" for Q
    by auto
  ultimately show ?case
    using \<open>P e\<close>
    unfolding range_split_first
    by (auto simp: algebra_simps)
qed

lemma opt_loop_props:
  "\<lbrakk>opt_loop fl pot e k net; length net = Suc n; e + k \<le> m\<rbrakk> \<Longrightarrow>
     (\<forall> i \<in> {e..<e + k}. arc_ok_opt fl pot i)
     \<and> (\<forall> v \<le> n. balance_list ! v = net ! v
                    + (\<Sum> i \<in> {i \<in> {e..<e + k}. fst_list ! i = v}. fl ! i)
                    - (\<Sum> i \<in> {i \<in> {e..<e + k}. snd_list ! i = v}. fl ! i))"
  by (rule scatter_loop_props[where L = "opt_loop fl pot" and P = "arc_ok_opt fl pot"])
     (auto simp: arc_ok_opt_def uncapacitated_def rc_of_def Let_def split: if_splits)

lemma check_optimum_flow:
  assumes "check_optimum fl pot"
  shows "\<And> i. i < m \<Longrightarrow> arc_ok_opt fl pot i"
    and "\<And> v. v \<le> n \<Longrightarrow> balance_list ! v = (\<Sum> i \<in> {i \<in> {0..<m}. fst_list ! i = v}. fl ! i)
                                        - (\<Sum> i \<in> {i \<in> {0..<m}. snd_list ! i = v}. fl ! i)"
  using assms opt_loop_props[of fl pot 0 m "replicate (Suc n) 0"]
  by (auto simp: check_optimum_def simp del: replicate_Suc)

text \<open>A flow that is feasible arc by arc and meets the balances as computed by the loops is a
      @{term b}-flow of the network.\<close>

lemma isbflow_of_certified:
  assumes "\<And> i. i < m \<Longrightarrow> 0 \<le> fl ! i \<and> (\<not> uncapacitated i \<longrightarrow> fl ! i \<le> capacity_list ! i)"
    "\<And> v. v \<le> n \<Longrightarrow> balance_list ! v = (\<Sum> i \<in> {i \<in> {0..<m}. fst_list ! i = v}. fl ! i)
                                        - (\<Sum> i \<in> {i \<in> {0..<m}. snd_list ! i = v}. fl ! i)"
  shows "network.isbflow (\<lambda> e. h (fl ! e)) bal"
proof(rule flow_network_spec.isbflowI)
  show "network.isuflow (\<lambda> e. h (fl ! e))"
    using assms(1)
    by (auto simp: flow_network_spec.isuflow_def cap_u_def)
  show "- network.ex (\<lambda> e. h (fl ! e)) v = bal v" if "v \<in> network.\<V>" for v
    using that assms(2)[of v] net_V_subset
    by (auto simp: flow_network_spec.ex_def net_delta_plus net_delta_minus bal_def h_sum)
qed

lemma check_optimum_isbflow:
  assumes "check_optimum fl pot"
  shows "network.isbflow (\<lambda> e. h (fl ! e)) bal"
  using check_optimum_flow[OF assms]
  by (auto intro!: isbflow_of_certified simp: arc_ok_opt_def)

text \<open>The reduced cost the checker computes in @{typ 'n} is the image of the one in @{typ real}.\<close>

lemma rc_h: "e < m \<Longrightarrow>
   h (cost_list ! e) + h (pot ! (fst_list ! e)) - h (pot ! (snd_list ! e)) = h (rc_of pot e)"
  by (simp add: rc_of_def h_add)

text \<open>Soundness is @{thm [source] network.optimality_from_potentials}: each of its three
      complementary slackness conditions is the contrapositive of a conjunct of
      @{const arc_ok_opt}.\<close>

lemma check_optimum_sound:
  assumes "check_optimum fl pot"
  shows "network.is_Opt bal (\<lambda> e. h (fl ! e))"
  by (intro network.optimality_from_potentials[where \<pi> = "\<lambda> v. h (pot ! v)"] check_optimum_isbflow[OF assms])
     (fastforce dest: check_optimum_flow(1)[OF assms]
                simp: arc_ok_opt_def cap_u_def uncapacitated_def zero_ereal_def rc_h)+

text \<open>Whatever the oracle returns, if @{const check_answer} accepts it then its verdict is true of
      this instance.\<close>

lemma check_answer_sound:
  assumes "check_answer a"
  shows "case a of OracleOptimum fl pot _ \<Rightarrow> network.is_Opt bal (\<lambda> e. h (fl ! e))
                 | OracleInfeasible _ S   \<Rightarrow> \<nexists> f. network.isbflow f bal
                 | OracleUnbounded _ cyc  \<Rightarrow>
                     has_neg_infty_cycle network.make_pair {0..<m} (\<lambda> e. h (cost_list ! e)) cap_u"
  using assms
  by (cases a) (auto simp: check_answer_def check_optimum_sound check_infeasible_sound check_unbounded_sound)

text \<open>The same statements as a property of a \<^emph>\<open>verdict\<close>: the common currency of an accepted
      answer and of a verified procedure.\<close>

definition verdict_ok :: "'n solver_verdict \<Rightarrow> bool" where
  "verdict_ok r =
     (case r of VOptimum f \<Rightarrow> network.is_Opt bal (\<lambda> e. h (f ! e))
              | VInfeasible \<Rightarrow> \<nexists> f. network.isbflow f bal
              | VUnbounded  \<Rightarrow>
                  has_neg_infty_cycle network.make_pair {0..<m} (\<lambda> e. h (cost_list ! e)) cap_u)"

lemma verdict_of_sound: "check_answer a \<Longrightarrow> verdict_ok (verdict_of a)"
  using check_answer_sound[of a]
  by (cases a) (auto simp: verdict_of_def verdict_ok_def)

text \<open>The checking layer, complete: an accepted answer is a true verdict about this instance.\<close>

lemma checked_verdict_sound: "checked_verdict = Some r \<Longrightarrow> verdict_ok r"
  using verdict_of_sound
  by (auto simp: checked_verdict_def checked_answer_def screen_def split: if_splits)

text \<open>The mode-aware verdict predicate: in \<open>CheckerEpsilontic\<close> mode a \<open>VOptimum\<close> verdict only
      promises a @{term b}-flow with dual slack \<open>1/M\<close>; the flow has to be stated separately, as the
      slack alone does not imply feasibility.\<close>

definition verdict_ok_dispatch :: "checker_mode \<Rightarrow> nat \<Rightarrow> 'n solver_verdict \<Rightarrow> bool" where
  "verdict_ok_dispatch cm M r =
     (case r of
        VOptimum f \<Rightarrow> (case cm of
                        CheckerNormal \<Rightarrow> network.is_Opt bal (\<lambda> e. h (f ! e))
                      | CheckerEpsilontic \<Rightarrow>
                          network.isbflow (\<lambda> e. h (f ! e)) bal \<and>
                          (\<exists> \<pi>. \<forall> e \<in> network.\<EE>. network.rcap (\<lambda> e. h (f ! e)) e > 0 \<longrightarrow>
                                 network.\<cc> e + \<pi> (network.fstv e) - \<pi> (network.sndv e) \<ge> - (1 / real M)))
      | VInfeasible \<Rightarrow> \<nexists> f. network.isbflow f bal
      | VUnbounded  \<Rightarrow> has_neg_infty_cycle network.make_pair {0..<m} (\<lambda> e. h (cost_list ! e)) cap_u)"

text \<open>An exact verdict meets the weaker bar for every mode and scale.\<close>

lemma verdict_ok_imp_dispatch:
  assumes "verdict_ok r" "0 < M"
  shows "verdict_ok_dispatch cm M r"
  using assms network.is_Opt_imp_eps_complementary_slack[of _ bal "1 / real M"]
  by (cases r)
     (auto simp: verdict_ok_def verdict_ok_dispatch_def network.is_Opt_def split: checker_mode.splits)

text \<open>\<^emph>\<open>The {\isasymepsilon}-slack check.\<close> Only the step from scaled slack to exact
      optimality needs integer costs (locale \<open>mcf_oracle_eps\<close> below).\<close>

lemma opt_loop_eps_props:
  "\<lbrakk>opt_loop_eps Mn fl pot e k net; length net = Suc n; e + k \<le> m\<rbrakk> \<Longrightarrow>
     (\<forall> i \<in> {e..<e + k}. arc_ok_eps Mn fl pot i)
     \<and> (\<forall> v \<le> n. balance_list ! v = net ! v
                    + (\<Sum> i \<in> {i \<in> {e..<e + k}. fst_list ! i = v}. fl ! i)
                    - (\<Sum> i \<in> {i \<in> {e..<e + k}. snd_list ! i = v}. fl ! i))"
  by (rule scatter_loop_props[where L = "opt_loop_eps Mn fl pot" and P = "arc_ok_eps Mn fl pot"])
     (auto simp: arc_ok_eps_def uncapacitated_def scaled_rc_of_def Let_def split: if_splits)

lemma check_optimum_eps_flow:
  assumes "check_optimum_eps Mn fl pot"
  shows "\<And> i. i < m \<Longrightarrow> arc_ok_eps Mn fl pot i"
    and "\<And> v. v \<le> n \<Longrightarrow> balance_list ! v = (\<Sum> i \<in> {i \<in> {0..<m}. fst_list ! i = v}. fl ! i)
                                        - (\<Sum> i \<in> {i \<in> {0..<m}. snd_list ! i = v}. fl ! i)"
  using assms opt_loop_eps_props[of Mn fl pot 0 m "replicate (Suc n) 0"]
  by (auto simp: check_optimum_eps_def simp del: replicate_Suc)

lemma scaled_rc_eps_h:
  "e < m \<Longrightarrow> h Mn * h (cost_list ! e) + h (pot ! (fst_list ! e)) - h (pot ! (snd_list ! e))
            = h (scaled_rc_of Mn pot e)"
  by (simp add: scaled_rc_of_def h_add h_mult)

lemma check_optimum_eps_isbflow:
  assumes "check_optimum_eps Mn fl pot"
  shows "network.isbflow (\<lambda> e. h (fl ! e)) bal"
  using check_optimum_eps_flow[OF assms]
  by (auto intro!: isbflow_of_certified simp: arc_ok_eps_def)

text \<open>The scaled slack of the check, divided by \<open>Mn\<close>, on both orientations of a residual arc:
      a forward arc needs the arc not saturated, a backward one positive flow.\<close>

lemma check_optimum_eps_slack:
  assumes "check_optimum_eps Mn fl pot" "0 < h Mn" "e \<in> network.\<EE>" "0 < network.rcap (\<lambda> e. h (fl ! e)) e"
  shows "- (1 / h Mn) \<le> network.\<cc> e + h (pot ! network.fstv e) / h Mn - h (pot ! network.sndv e) / h Mn"
proof-
  obtain d where "d < m" "e = F d \<or> e = B d"
    using assms(3)
    by (auto simp: network.\<EE>_def)
  moreover hence "(uncapacitated d \<or> fl ! d < capacity_list ! d \<longrightarrow> - 1 \<le> scaled_rc_of Mn pot d)
                  \<and> (0 < fl ! d \<longrightarrow> scaled_rc_of Mn pot d \<le> 1)"
    using check_optimum_eps_flow(1)[OF assms(1)]
    by (auto simp: arc_ok_eps_def)
  ultimately have "- 1 \<le> h Mn * network.\<cc> e + h (pot ! network.fstv e) - h (pot ! network.sndv e)"
    using assms(4) h_mono[of "- 1" "scaled_rc_of Mn pot d"] h_mono[of "scaled_rc_of Mn pot d" 1]
    by (cases "uncapacitated d")
       (auto simp: cap_u_def uncapacitated_def scaled_rc_eps_h[symmetric])
  from divide_right_mono[OF this, of "h Mn"]
  show ?thesis
    using assms(2)
    by (simp add: add_divide_distrib diff_divide_distrib)
qed

end

subsection \<open>The reduction's output is an instance of that format\<close>

text \<open>Every assumption of @{locale mcf_oracle} holds for the lists the reduction leaves behind, so
      the pipeline may hand them to the oracle. The node count is \<open>n - 1\<close>, as the vertex names are
      \<open>{1..<n}\<close>. That the balances sum to zero and that a vertex no arc touches has balance \<open>0\<close> is
      what \<open>red_ok\<close> tests.\<close>

context dimacs_lists_network
begin

lemma orc_nodes: "Suc 0 < n"
  using m_pos_n[OF arcs_nonempty]
  by simp

lemma orc_lengths:
  "length fst_list = m" "length snd_list = m"
  "length red_upper = m" "length cost_list = m"
  "length red_balance_list = Suc (n - 1)" "0 < m"
  using length_fst_list length_snd_list length_cost_list red_upper_length
        red_balance_list_length nodes_nonempty arcs_nonempty
  by auto

lemma orc_endpoints:
  "e < m \<Longrightarrow> fst_list ! e \<in> {Suc 0..n - 1}" "e < m \<Longrightarrow> snd_list ! e \<in> {Suc 0..n - 1}"
  using fst_list_vertex[of e] snd_list_vertex[of e]
  by auto

lemma orc_capacity: "e < m \<Longrightarrow> 0 \<le> red_upper ! e \<or> red_upper ! e = - 1"
  by (simp add: red_upper_orig_nonneg)

lemma orc_sentinel: "red_balance_list ! 0 = 0"
  by (simp add: red_balance_list_def red_balance_raw_sentinel)

lemma orc_sum_zero: "red_ok \<Longrightarrow> sum_list red_balance_list = 0"
  by (simp add: red_ok_def red_balance_list_def sum_ok_def)

lemma orc_isolated:
  assumes "red_ok" "v \<in> {Suc 0..n - 1}" "\<And> e. e < m \<Longrightarrow> fst_list ! e \<noteq> v \<and> snd_list ! e \<noteq> v"
  shows "red_balance_list ! v = 0"
  using assms orc_nodes red_balance_raw_isolated[of v]
  by (auto simp: red_ok_def red_balance_list_nth orig_delta)

text \<open>Hence a feasible reduced instance has the format the certifier assumes, for any oracle.\<close>

lemma reduced_is_oracle_instance:
  assumes "red_ok"
  shows "mcf_oracle fst_list snd_list cost_list red_balance_list m (n - 1) red_upper h"
proof(unfold_locales, goal_cases)
  case (8 e)
  thus ?case
    using orc_endpoints(1)
    by simp
next
  case (9 e)
  thus ?case
    using orc_endpoints(2)
    by simp
next
  case (13 v)
  thus ?case
    using orc_isolated[OF assms]
    by fastforce
qed (auto simp: orc_lengths orc_sentinel orc_sum_zero[OF assms] orc_nodes orc_capacity)

end

subsection \<open>The pipeline: check the oracle, else clean up\<close>

text \<open>\<^emph>\<open>{\isasymepsilon}-optimality is sound given integer costs.\<close> Integrality is
      automatic in the concrete pipeline (\<open>'n = int\<close>, \<open>h = of_int\<close>) but not for an
      arbitrary embedding, so it is the assumption of a separate locale.\<close>

locale mcf_oracle_eps = mcf_oracle where capacity_list = capacity_list and h = h
  for capacity_list :: "('n :: linordered_idom) list" and h +
  assumes cost_integer: "\<And>e. e < m \<Longrightarrow> h (cost_list ! e) \<in> \<int>"
begin

lemma residual_cost_integer: "e \<in> network.\<EE> \<Longrightarrow> network.\<cc> e \<in> \<int>"
  using cost_integer
  by (auto simp: network.\<EE>_def)

lemma check_optimum_eps_sound:
  assumes "check_optimum_eps Mn fl pot"
  shows "network.is_Opt bal (\<lambda> e. h (fl ! e))"
proof-
  have "real n < h Mn"
    using assms h_less_iff[of "of_nat n" Mn]
    by (simp add: check_optimum_eps_def)
  moreover hence "0 < h Mn"
    using le_less_trans[OF of_nat_0_le_iff]
    by blast
  moreover have "real (card network.\<V>) \<le> real n"
    using card_V_le_n
    by simp
  ultimately have "0 < 1 / h Mn" "real (card network.\<V>) * (1 / h Mn) < 1"
    by (auto simp: field_simps)
  thus ?thesis
    using check_optimum_eps_slack[OF assms]
    by (intro network.optimality_from_eps_potentials[where \<epsilon> = "1 / h Mn" and \<pi> = "\<lambda> v. h (pot ! v) / h Mn"]
              check_optimum_eps_isbflow[OF assms] residual_cost_integer ballI impI)
       auto
qed

text \<open>The uniform contract, indexed by checker mode: both branches are pushed to \<open>is_Opt\<close> and then
      weakened to the slack at the caller's scale \<open>M\<close>, so the certificate's scale does not occur in
      the conclusion.\<close>

lemma check_optimum_dispatch_sound:
  assumes "check_optimum_dispatch cm fl pot certm" "0 < M"
  shows "case cm of
           CheckerNormal \<Rightarrow> network.is_Opt bal (\<lambda> e. h (fl ! e))
         | CheckerEpsilontic \<Rightarrow>
             network.isbflow (\<lambda> e. h (fl ! e)) bal \<and>
             (\<exists> \<pi>. \<forall> e \<in> network.\<EE>. network.rcap (\<lambda> e. h (fl ! e)) e > 0 \<longrightarrow>
                    network.\<cc> e + \<pi> (network.fstv e) - \<pi> (network.sndv e) \<ge> - (1 / real M))"
proof-
  have "network.is_Opt bal (\<lambda> e. h (fl ! e))"
    using assms(1)
    by (auto simp: check_optimum_dispatch_def check_optimum_sound check_optimum_eps_sound
             split: checker_mode.splits if_splits)
  thus ?thesis
    using network.is_Opt_imp_eps_complementary_slack[of "\<lambda> e. h (fl ! e)" bal "1 / real M"]
    by (auto simp: network.is_Opt_def split: checker_mode.splits)
qed

lemma check_answer_dispatch_sound:
  assumes "check_answer_dispatch cm a" "0 < M"
  shows "case a of
           OracleOptimum fl pot certm \<Rightarrow>
             (case cm of
                CheckerNormal \<Rightarrow> network.is_Opt bal (\<lambda> e. h (fl ! e))
              | CheckerEpsilontic \<Rightarrow>
                  network.isbflow (\<lambda> e. h (fl ! e)) bal \<and>
                  (\<exists> \<pi>. \<forall> e \<in> network.\<EE>. network.rcap (\<lambda> e. h (fl ! e)) e > 0 \<longrightarrow>
                         network.\<cc> e + \<pi> (network.fstv e) - \<pi> (network.sndv e) \<ge> - (1 / real M)))
         | OracleInfeasible _ S  \<Rightarrow> \<nexists> f. network.isbflow f bal
         | OracleUnbounded _ cyc \<Rightarrow>
             has_neg_infty_cycle network.make_pair {0..<m} (\<lambda> e. h (cost_list ! e)) cap_u"
  using assms
  by (cases a)
     (auto simp: check_answer_dispatch_def check_optimum_dispatch_sound check_infeasible_sound
                 check_unbounded_sound)

lemma verdict_of_dispatch_sound:
  "\<lbrakk>check_answer_dispatch cm a; 0 < M\<rbrakk> \<Longrightarrow> verdict_ok_dispatch cm M (verdict_of a)"
  using check_answer_dispatch_sound[of cm a M]
  by (cases a) (auto simp: verdict_of_def verdict_ok_dispatch_def)

text \<open>Given integer costs, the slack verdict of \<open>CheckerEpsilontic\<close> mode is exact for
      \<open>n < M\<close>.\<close>

lemma verdict_ok_dispatch_exact:
  assumes "verdict_ok_dispatch CheckerEpsilontic M r" "n < M"
  shows "verdict_ok r"
proof-
  have "real (card network.\<V>) * (1 / real M) < 1"
    using card_V_le_n assms(2)
    by (simp add: field_simps)
  thus ?thesis
    using assms
    by (cases r)
       (auto simp: verdict_ok_dispatch_def verdict_ok_def
             intro!: network.optimality_from_eps_potentials[where \<epsilon> = "1 / real M"] residual_cost_integer)
qed

end

locale mcf_oracle_cleanup_spec =
  mcf_oracle_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: linordered_idom) list" +
  fixes cleanup :: "'n flow_instance \<Rightarrow> 'n list \<Rightarrow> 'n solver_verdict"
begin

definition decide :: "'n oracle_answer \<Rightarrow> 'n solver_verdict" where
  "decide a = (case screen a of Some b \<Rightarrow> verdict_of b
                              | None   \<Rightarrow> cleanup orc_input (oa_flow a))"

definition solve :: "'n solver_verdict" where
  "solve = decide orc_answer"

end

text \<open>The proof locale assumes only that the cleanup's verdict is true of this instance; the flow
      it is given is a warm start, a performance argument, never a correctness one. Still nothing
      is assumed about @{term oracle_solve}.\<close>

locale mcf_oracle_cleanup = mcf_oracle + mcf_oracle_cleanup_spec +
  assumes cleanup_correct: "\<And> g. verdict_ok (cleanup orc_input g)"
begin

text \<open>Hence the pipeline is correct whatever the oracle does: an accepted certificate gives its
      own verdict, a rejected one the cleanup's.\<close>

lemma solve_correct: "verdict_ok solve"
  using verdict_of_sound cleanup_correct
  by (auto simp: solve_def decide_def screen_def split: if_splits)

end

end

