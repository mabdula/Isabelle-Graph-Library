theory Mincost_Solver_Reduction_Refinement
  imports Use_Network_Simplex.Mincost_Solver_Reduction
           Separation_Logic_Imperative_HOL_Partial.Array_Blit
begin

section \<open>Imperative refinement of the DIMACS reduction\<close>

text \<open>The reduction of \<open>Mincost_Solver_Reduction\<close> is a fold over a four-tuple: two lists and two
      scalars.  Here it becomes a pass over arrays.

      \<^emph>\<open>The programs are defined outside every locale.\<close>  That is not a stylistic choice: the code
      locale @{locale dimacs_lists} \<^emph>\<open>fixes\<close> the input lists, whereas an imperative reduction receives
      them --- it is handed arrays by whoever parsed the file, and the counts @{term m} and
      @{term n} along with them.  A program that referred to locale parameters could not be applied
      to a second instance.  So every input is an argument, and the definitions below mention
      nothing but their arguments.

      The \<^emph>\<open>refinement proofs\<close>, by contrast, belong inside the proof locale
      @{locale dimacs_lists_network}: they say that running a program on the arrays holding
      @{term upper} and @{term balance_list} leaves them holding @{term red_upper} and
      @{term red_balance_raw}, which is a statement about that instance and needs its
      well-formedness assumptions.

      \<^emph>\<open>Nothing is allocated.\<close>  The six arrays of the problem --- the two endpoint arrays, the two
      bounds, the costs and the balances --- are the only arrays that occur, and the reduced
      instance is those same arrays.  Where the range test would want a vertex-indexed accumulator
      of incident capacity, the balance array carries it instead: the capacity is shifted onto the
      balances, the sign of the result is the test, and the shift is undone.\<close>

subsection \<open>The pass\<close>

text \<open>The reduced instance has the arcs it was given, so the endpoints and the costs are not touched
      at all and only two arrays change: the capacities, in place at the position each was read
      from, and the balances, which the parser's array receives by scattering. Of the input only
      \<open>lower\<close> is still needed afterwards, to add the bounds back to the flow.

      Two further differences from the fold, both of them things the functional level could not say.

      \<^item> \<^emph>\<open>The scalars are registers.\<close>  The cost shift and the range flag are accumulator
        arguments, not cells of a tuple rebuilt each step.
      \<^item> \<^emph>\<open>Each input cell is read once\<close>, and the two balance updates are ordered head-then-tail so
        a self-loop cancels, exactly as the fold's \<open>a = bal[y := bal ! y + li]\<close> does.\<close>

text \<open>The capacity an arc contributes, as a \<^emph>\<open>named\<close> function.  Writing the \<open>if\<close> inline would be the
      same computation, but the verification condition generator normalises the resulting array
      contents with a case split and then loses the shape of the heap for every operation that
      follows the write; a constant keeps the written value atomic.\<close>

definition arc_cap :: "'a :: {ord, minus, zero} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "arc_cap li ui = (if li \<le> ui then ui - li else 0)"

text \<open>The arc loop, \<^emph>\<open>in place\<close>.\<close>

partial_function (heap) red_arcs_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> bool \<Rightarrow> ('n \<times> bool) Heap" where
  "red_arcs_imp fa sa la ua oa bal i k sh ok =
     (if k = 0 then return (sh, ok)
      else do {
        x  \<leftarrow> Array.nth fa i;
        y  \<leftarrow> Array.nth sa i;
        li \<leftarrow> Array.nth la i;
        ui \<leftarrow> Array.nth ua i;
        ci \<leftarrow> Array.nth oa i;
        _  \<leftarrow> Array.upd i (arc_cap li ui) ua;
        byv \<leftarrow> Array.nth bal y;
        _  \<leftarrow> Array.upd y (byv + li) bal;
        bxv \<leftarrow> Array.nth bal x;
        _  \<leftarrow> Array.upd x (bxv - li) bal;
        red_arcs_imp fa sa la ua oa bal
                     (Suc i) (k - 1) (sh + ci * li) (ok \<and> li \<le> ui) })"

text \<open>The pass: the DIMACS sentinel \<open>0\<close>, which no arc touches and which the fold's \<open>red_bal_init\<close>
      clears, and then the loop.

      This is a procedure of its own. That is not decoration: a Hoare rule can only be \<^emph>\<open>applied\<close> to
      a program the verification condition generator still sees as one term, and the generator
      decomposes a \<open>\<bind>\<close> chain into its leftmost atom before it looks for a rule.\<close>

definition reduce_tail_raw ::
  "nat array \<Rightarrow> nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array
   \<Rightarrow> nat \<Rightarrow> ('n \<times> bool) Heap" where
  "reduce_tail_raw fa sa la ua oa bal mm =
     do {
       _ \<leftarrow> Array.upd 0 0 bal;
       red_arcs_imp fa sa la ua oa bal 0 mm 0 True }"

text \<open>Reading the answer back: the solver's flow on the reduced arcs is a flow of the original
      instance once the lower bounds are added back, and that is again one pass, in place.\<close>

partial_function (heap) orig_flow_imp ::
  "('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "orig_flow_imp la ga i k =
     (if k = 0 then return ()
      else do {
        g \<leftarrow> Array.nth ga i;
        l \<leftarrow> Array.nth la i;
        _ \<leftarrow> Array.upd i (g + l) ga;
        orig_flow_imp la ga (Suc i) (k - 1) })"

subsection \<open>Testing the balances\<close>

text \<open>The reduced instance is feasible only if every emitted balance lies within the capacity
      incident at its vertex, and the pass reports that. Reading \<open>capout\<close> off its definition would
      traverse the arc list once \<^emph>\<open>per vertex\<close>, and accumulating it per vertex would want an array
      that the problem does not provide. So the incident capacity is never stored: one arc sweep
      shifts it onto the balances with a sign, a vertex sweep reads off the sign of the shifted
      balance, and the mirror sweep puts the balances back. The same loop serves all four shifts,
      the index array and the sign being its arguments.\<close>

partial_function (heap) shift_imp ::
  "nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
  where
  "shift_imp ia va bal c e k =
     (if k = 0 then return ()
      else do {
        v  \<leftarrow> Array.nth ia e;
        uv \<leftarrow> Array.nth va e;
        bv \<leftarrow> Array.nth bal v;
        _  \<leftarrow> Array.upd v (bv + c * uv) bal;
        shift_imp ia va bal c (Suc e) (k - 1) })"

text \<open>The vertex sweep. It runs over the real vertices only --- slot \<open>0\<close> is the DIMACS sentinel ---
      and writes nothing: an out-of-range balance is not something to correct but a proof that the
      instance is infeasible, so it clears the flag. It also totals what it reads, which on the
      restored array is the total the equality semantics requires to vanish.\<close>

partial_function (heap) sweep_imp ::
  "('n :: {heap, linordered_idom}) array \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> bool \<Rightarrow> ('n \<times> bool) Heap" where
  "sweep_imp bal c v k tot ok =
     (if k = 0 then return (tot, ok)
      else do {
        x \<leftarrow> Array.nth bal v;
        sweep_imp bal c (Suc v) (k - 1) (tot + x) (ok \<and> c * x \<le> 0) })"

text \<open>The testing half of the pass, as a procedure of its own. It runs \<^emph>\<open>after\<close> the pass rather than
      inside it, and that is what keeps the proof small: @{const reduce_tail_raw} already leaves the
      capacity array holding \<open>red_upper\<close> and the balance array holding \<open>red_balance_raw\<close>, which are
      exactly the two things the shifts and the sweeps read.

      The first shift subtracts the out-capacity, so a non-positive balance is the upper test; the
      third adds the in-capacity, so a non-negative balance is the lower test; the second and fourth
      undo them. The last sweep sees the restored array and totals it.\<close>

definition bal_out_test ::
  "nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bal_out_test fa us bal mm nn =
     do {
       _ \<leftarrow> shift_imp fa us bal (- 1) 0 mm;
       t \<leftarrow> sweep_imp bal 1 (Suc 0) (nn - Suc 0) 0 True;
       _ \<leftarrow> shift_imp fa us bal 1 0 mm;
       return (snd t) }"

definition bal_in_test ::
  "nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bal_in_test sa us bal mm nn =
     do {
       _ \<leftarrow> shift_imp sa us bal 1 0 mm;
       t \<leftarrow> sweep_imp bal (- 1) (Suc 0) (nn - Suc 0) 0 True;
       _ \<leftarrow> shift_imp sa us bal (- 1) 0 mm;
       return (snd t) }"

definition bal_sum_test ::
  "('n :: {heap, linordered_idom}) array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bal_sum_test bal nn =
     do {
       t \<leftarrow> sweep_imp bal 0 (Suc 0) (nn - Suc 0) 0 True;
       return (fst t = 0) }"

definition bal_tail ::
  "nat array \<Rightarrow> nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "bal_tail fa sa us bal mm nn =
     do {
       q1 \<leftarrow> bal_out_test fa us bal mm nn;
       q2 \<leftarrow> bal_in_test sa us bal mm nn;
       q3 \<leftarrow> bal_sum_test bal nn;
       return (q1 \<and> q2 \<and> q3) }"

text \<open>The whole reduction: the pass and the test, on the caller's six arrays and nothing else.  What
      comes back is the cost shift and the flag; the lists are where they were.\<close>

definition reduce_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('n \<times> bool) Heap" where
  "reduce_imp fa sa la ua oa ba mm nn =
     do {
       p   \<leftarrow> reduce_tail_raw fa sa la ua oa ba mm;
       ok2 \<leftarrow> bal_tail fa sa ua ba mm nn;
       return (fst p, snd p \<and> ok2) }"

text \<open>The numeric type must carry @{class heap} for its values to live in arrays, and a sort cannot
      be strengthened inside a context, so the refinement proofs live in a heap-strengthened copy of
      the proof locale.\<close>

locale dimacs_lists_network_heap =
  dimacs_lists_network where lower = "lower :: ('n :: {heap, linordered_idom}) list"
  for lower
begin

text \<open>Every endpoint is a slot of the balance array.\<close>

lemma fst_lt_n: "j < m \<Longrightarrow> fst_list ! j < n"
  and snd_lt_n: "j < m \<Longrightarrow> snd_list ! j < n"
  using fst_list_vertex[of j] snd_list_vertex[of j] by auto

text \<open>One arc's scatter into the balance array, as a fact about lists.  The head is written first and
      read back by the tail update, so at a self-loop the two cancel --- which is exactly what
      @{const dimacs_lists.bal_step_at} says, and why the functional pass and the program agree
      there.\<close>

lemma bal_upd_step:
  assumes "fst_list ! i < length bl" "snd_list ! i < length bl" "v < length bl" "i < m"
  defines "bl1 \<equiv> list_update bl (snd_list ! i) (bl ! (snd_list ! i) + lower ! i)"
  shows "list_update bl1 (fst_list ! i) (bl1 ! (fst_list ! i) - lower ! i) ! v
         = bl ! v + bal_step_at i v"
  using assms by(auto simp add: bl1_def bal_step_at_def nth_list_update)

text \<open>\<^emph>\<open>The arc loop refines.\<close> The capacity array is described pointwise --- a cell in the swept
      range holds what the arc there prescribes, a cell outside it is untouched --- and the balance
      array by the running sum of \<^const>\<open>dimacs_lists.bal_step_at\<close>, which is precisely the form
      \<open>red_balance_raw_nth\<close> states the functional pass in. The two scalars come out as the cost
      shift accumulated so far and the conjunction of the range tests.

      The capacity array is read \<^emph>\<open>and\<close> written, so its hypothesis is one-sided: the unswept part
      still carries the parsed bound. That is what makes the write at the position just read sound,
      and it is restored across a step because a step touches only its own index.\<close>

text \<open>The two arrays the loop writes, as \<^emph>\<open>constants\<close>: what the capacity array holds once the
      range \<open>[i..<i+k]\<close> has been swept, and what the balance array holds once those arcs have
      scattered.  Naming them keeps the induction's rewrites atomic --- an inline \<open>map\<close> is
      normalised by the verification condition generator and then no longer matches the induction
      hypothesis, and an existentially quantified array leaves the generator to guess it.\<close>

definition upd_range :: "nat \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list" where
  "upd_range i k xu = map (\<lambda> j. if i \<le> j \<and> j < i + k then red_upper_at j else xu ! j) [0..<m]"

definition bal_range :: "nat \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list" where
  "bal_range i k bl =
     map (\<lambda> v. bl ! v + sum_list (map (\<lambda> j. bal_step_at j v) [i..<i + k])) [0..<n]"

lemma upd_range_length [simp]: "length (upd_range i k xu) = m"
  by(simp add: upd_range_def)

lemma bal_range_length [simp]: "length (bal_range i k bl) = n"
  by(simp add: bal_range_def)

lemma upd_range_0: "length xu = m \<Longrightarrow> upd_range i 0 xu = xu"
  unfolding upd_range_def by(intro nth_equalityI) auto

lemma bal_range_0: "length bl = n \<Longrightarrow> bal_range i 0 bl = bl"
  unfolding bal_range_def by(intro nth_equalityI) auto

lemma upd_range_step:
  assumes "i < m" "length xu = m"
      and "\<And> j. j < m \<Longrightarrow> L ! j = (if j = i then red_upper_at i else xu ! j)"
  shows "upd_range i (Suc k) xu = upd_range (Suc i) k L"
  unfolding upd_range_def
  by(rule map_cong) (auto simp add: assms(3))

lemma bal_range_step:
  assumes "\<And> v. v < n \<Longrightarrow> L ! v = bl ! v + bal_step_at i v"
  shows "bal_range i (Suc k) bl = bal_range (Suc i) k L"
proof(intro nth_equalityI)
  show "length (bal_range i (Suc k) bl) = length (bal_range (Suc i) k L)" by simp
next
  fix v assume "v < length (bal_range i (Suc k) bl)"
  hence v: "v < n" by simp
  have peel: "[i..<i + Suc k] = i # [Suc i..<Suc i + k]" by(simp add: upt_conv_Cons)
  have "bal_range i (Suc k) bl ! v
          = bl ! v + sum_list (map (\<lambda> j. bal_step_at j v) [i..<i + Suc k])"
    using v by(simp add: bal_range_def)
  also have "\<dots> = (bl ! v + bal_step_at i v)
                    + sum_list (map (\<lambda> j. bal_step_at j v) [Suc i..<Suc i + k])"
    by(simp only: peel, simp add: add.assoc)
  also have "\<dots> = bal_range (Suc i) k L ! v"
    using v assms[OF v] by(simp add: bal_range_def)
  finally show "bal_range i (Suc k) bl ! v = bal_range (Suc i) k L ! v" .
qed

lemma upd_range_full: "length xu = m \<Longrightarrow> upd_range 0 m xu = red_upper"
  unfolding upd_range_def
  by(intro nth_equalityI) (auto simp add: red_upper_length red_arc_nth)

lemma bal_range_full: "bal_range 0 m (balance_list[0 := 0]) = red_balance_raw"
  unfolding bal_range_def
  by(intro nth_equalityI)
    (auto simp add: red_balance_raw_length red_balance_raw_nth red_bal_init_def)

text \<open>\<^emph>\<open>The arc loop refines.\<close> The capacity array comes out as the parsed one with the swept range
      replaced by what the arcs there prescribe, and the balance array as the one it started from
      with the lower bounds of the swept arcs scattered onto it --- which is precisely the form
      \<open>red_balance_raw_nth\<close> states the functional pass in. The two scalars come out as the cost shift
      accumulated so far and the conjunction of the range tests.

      The capacity array is read \<^emph>\<open>and\<close> written, so its hypothesis is one-sided: the unswept part
      still carries the parsed bound. That is what makes the write at the position just read sound,
      and it is restored across a step because a step touches only its own index.\<close>

lemma red_arcs_imp_rule:
  "\<lbrakk>i + k \<le> m; length xu = m; \<And> j. \<lbrakk>i \<le> j; j < m\<rbrakk> \<Longrightarrow> xu ! j = upper ! j;
    length bl = n\<rbrakk> \<Longrightarrow>
   <fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a xu *
    oa \<mapsto>\<^sub>a cost_list * bal \<mapsto>\<^sub>a bl>
     red_arcs_imp fa sa la ua oa bal i k sh ok
   <\<lambda>r. fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * oa \<mapsto>\<^sub>a cost_list *
        ua \<mapsto>\<^sub>a upd_range i k xu * bal \<mapsto>\<^sub>a bal_range i k bl
        * \<up>(fst r = sh + sum_list (map (\<lambda> j. cost_list ! j * lower ! j) [i..<i + k])
            \<and> snd r = (ok \<and> (\<forall> j. i \<le> j \<and> j < i + k \<longrightarrow> lower ! j \<le> upper ! j)))>"
proof(induction k arbitrary: i xu bl sh ok)
  case 0
  thus ?case
    by(subst red_arcs_imp.simps)
      (sep_auto simp: upd_range_0 bal_range_0 "0.prems"(2,4))
next
  case (Suc k)
  have im: "i < m" using Suc.prems by simp
  have bnd: "i < length fst_list" "i < length snd_list" "i < length lower" "i < length cost_list"
    using im length_fst_list length_snd_list length_lower length_cost_list by simp_all
  have ualen: "i < length xu" using im Suc.prems(2) by simp
  have uai: "xu ! i = upper ! i" by(rule Suc.prems(3)[OF order.refl im])
  have vtx: "fst_list ! i < n" "snd_list ! i < n" using fst_lt_n[OF im] snd_lt_n[OF im] by simp_all
  have vb: "fst_list ! i < length bl" "snd_list ! i < length bl"
    using vtx Suc.prems(4) by simp_all
  let ?bl1 = "list_update bl (snd_list ! i) (bl ! (snd_list ! i) + lower ! i)"
  let ?bl2 = "list_update ?bl1 (fst_list ! i) (?bl1 ! (fst_list ! i) - lower ! i)"
  let ?xu2 = "list_update xu i (arc_cap (lower ! i) (upper ! i))"
  have bl2_len: "length ?bl2 = n" using Suc.prems(4) by simp
  have bl2_nth: "?bl2 ! v = bl ! v + bal_step_at i v" if "v < n" for v
    using bal_upd_step[OF vb(1) vb(2) _ im] that Suc.prems(4) by simp
  have xu2_len: "length ?xu2 = m" using Suc.prems(2) by simp
  have xu2_keep: "?xu2 ! j = upper ! j" if "Suc i \<le> j" "j < m" for j
    using that Suc.prems(3)[of j] ualen by(simp add: nth_list_update)
  have at: "red_upper_at i = arc_cap (lower ! i) (upper ! i)"
    by(simp add: red_upper_at_def arc_cap_def)
  have ur: "upd_range i (Suc k) xu = upd_range (Suc i) k ?xu2"
    by(rule upd_range_step[OF im Suc.prems(2)]) (simp add: nth_list_update ualen at)
  have br: "bal_range i (Suc k) bl = bal_range (Suc i) k ?bl2"
    by(rule bal_range_step) (simp add: bl2_nth)
  have qpeel: "(\<forall> j. i \<le> j \<and> j < Suc (i + k) \<longrightarrow> Q j)
                 = (Q i \<and> (\<forall> j. Suc i \<le> j \<and> j < Suc (i + k) \<longrightarrow> Q j))" for Q
    by(auto simp add: le_Suc_eq) (metis le_neq_implies_less less_Suc_eq_le not_less_eq)
  have IH: "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a ?xu2 *
             oa \<mapsto>\<^sub>a cost_list * bal \<mapsto>\<^sub>a ?bl2>
              red_arcs_imp fa sa la ua oa bal (Suc i) k
                           (sh + cost_list ! i * lower ! i) (ok \<and> lower ! i \<le> upper ! i)
            <\<lambda>r. fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * oa \<mapsto>\<^sub>a cost_list *
                 ua \<mapsto>\<^sub>a upd_range (Suc i) k ?xu2 * bal \<mapsto>\<^sub>a bal_range (Suc i) k ?bl2
                 * \<up>(fst r = sh + cost_list ! i * lower ! i
                              + sum_list (map (\<lambda> j. cost_list ! j * lower ! j)
                                              [Suc i..<Suc i + k])
                     \<and> snd r = ((ok \<and> lower ! i \<le> upper ! i)
                                \<and> (\<forall> j. Suc i \<le> j \<and> j < Suc i + k \<longrightarrow> lower ! j \<le> upper ! j)))>"
    by(rule Suc.IH[OF _ xu2_len xu2_keep bl2_len]) (use Suc.prems(1) in simp)
  have peel: "[i..<Suc (i + k)] = i # [Suc i..<Suc (i + k)]" by(simp add: upt_conv_Cons)
  note [simp del] = upt_Suc
  show ?case
    by(subst red_arcs_imp.simps)
      (sep_auto simp: bnd vtx vb im ualen uai Suc.prems(2,4) ur br
                      length_fst_list length_snd_list length_cost_list length_lower
                      peel qpeel add.assoc
                heap: IH)
qed

subsection \<open>Reading the answer back\<close>

text \<open>Adding the lower bounds back is the mirror image of the arc phase, and its result is named
      for the same reason the two ranges above are: an inline \<open>map\<close> does not survive the
      verification condition generator's normalisation.\<close>

definition add_range :: "nat \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list" where
  "add_range i k gs = map (\<lambda> j. if i \<le> j \<and> j < i + k then gs ! j + lower ! j else gs ! j) [0..<m]"

lemma add_range_length [simp]: "length (add_range i k gs) = m"
  by(simp add: add_range_def)

lemma add_range_0: "length gs = m \<Longrightarrow> add_range i 0 gs = gs"
  unfolding add_range_def by(intro nth_equalityI) auto

lemma add_range_step:
  assumes "i < m" "length gs = m"
      and "\<And> j. j < m \<Longrightarrow> L ! j = (if j = i then gs ! i + lower ! i else gs ! j)"
  shows "add_range i (Suc k) gs = add_range (Suc i) k L"
  unfolding add_range_def
  by(rule map_cong) (auto simp add: assms(3))

lemma add_range_full: "length gs = m \<Longrightarrow> add_range 0 m gs = orig_flow gs"
  unfolding add_range_def orig_flow_def by(intro nth_equalityI) auto

lemma orig_flow_imp_rule:
  "i + k \<le> m \<Longrightarrow> length gs = m \<Longrightarrow>
   <la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a gs>
     orig_flow_imp la ga i k
   <\<lambda>_. la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a add_range i k gs>"
proof(induction k arbitrary: i gs)
  case 0
  thus ?case by(subst orig_flow_imp.simps) (sep_auto simp: add_range_0 "0.prems"(2))
next
  case (Suc k)
  have im: "i < m" using Suc.prems(1) by simp
  have il: "i < length lower" using im length_lower by simp
  have ig: "i < length gs" using im Suc.prems(2) by simp
  let ?gs2 = "list_update gs i (gs ! i + lower ! i)"
  have gs2_len: "length ?gs2 = m" using Suc.prems(2) by simp
  have ar: "add_range i (Suc k) gs = add_range (Suc i) k ?gs2"
    by(rule add_range_step[OF im Suc.prems(2)]) (simp add: nth_list_update ig)
  have IH: "<la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a ?gs2>
              orig_flow_imp la ga (Suc i) k
            <\<lambda>_. la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a add_range (Suc i) k ?gs2>"
    by(rule Suc.IH[OF _ gs2_len]) (use Suc.prems(1) in simp)
  show ?case
    by(subst orig_flow_imp.simps) (sep_auto simp: im il ig Suc.prems(2) ar heap: IH)
qed

text \<open>Run over the arcs, the array is @{const dimacs_lists.orig_flow}.\<close>

lemma orig_flow_imp_correct:
  assumes "length gs = m"
  shows
   "<la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a gs>
     orig_flow_imp la ga 0 m
   <\<lambda>_. la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a orig_flow gs>"
  using orig_flow_imp_rule[of 0 m gs la ga] assms by(simp add: add_range_full)

subsection \<open>What the functional pass leaves in the arrays\<close>

text \<open>The refinement needs one fact about the pass that the functional development did not have to
      state, because it never had to build the arrays cell by cell: the cost shift as a plain sum
      over the arcs.\<close>

lemma red_step_sh:
  "(case red_step i (us, bal, sh, ok) of (_, _, sh', _) \<Rightarrow> sh') = sh + cost_list ! i * lower ! i"
  by(auto simp add: red_step_def Let_def)

lemma red_sh_fold:
  "(case fold red_step es (us, bal, sh, ok) of (_, _, sh', _) \<Rightarrow> sh')
   = sh + sum_list (map (\<lambda> i. cost_list ! i * lower ! i) es)"
proof(induction es arbitrary: us bal sh ok)
  case (Cons a es)
  obtain us' bal' sh' ok' where
    step: "red_step a (us, bal, sh, ok) = (us', bal', sh', ok')"
    by(cases "red_step a (us, bal, sh, ok)") auto
  have sh': "sh' = sh + cost_list ! a * lower ! a"
    using red_step_sh[of a us bal sh ok] by(simp add: step)
  show ?case
    using Cons.IH[of us' bal' sh' ok'] by(simp add: step sh' add.assoc)
qed simp

lemma cost_shift_eq: "cost_shift = sum_list (map (\<lambda> i. cost_list ! i * lower ! i) [0..<m])"
proof -
  obtain us bal sh ok where f: "fold red_step [0..<m] red_init = (us, bal, sh, ok)"
    by(cases "fold red_step [0..<m] red_init") auto
  have "sh = 0 + sum_list (map (\<lambda> i. cost_list ! i * lower ! i) [0..<m])"
    using red_sh_fold[of "[0..<m]" "replicate m 0" red_bal_init 0 True] f
    by(simp add: red_init_def)
  thus ?thesis
    by(simp add: cost_shift_def red_pass_def f)
qed

subsection \<open>Recognising the finished arrays\<close>

text \<open>A list of the right length whose every cell holds the prescribed value \<^emph>\<open>is\<close> the corresponding
      output of the pass. These two extensionality lemmas are what turns the pointwise descriptions
      the loops produce into the equalities the reduction's statement needs.\<close>

lemma red_upper_eqI: "length L = m \<Longrightarrow> (\<And> j. j < m \<Longrightarrow> L ! j = red_upper_at j) \<Longrightarrow> L = red_upper"
  using red_upper_length red_arc_nth by(intro nth_equalityI) auto

lemma red_balance_raw_eqI:
  assumes "length L = n"
      and "\<And> u. u < n \<Longrightarrow> L ! u = red_bal_init ! u
                                  + sum_list (map (\<lambda> i. bal_step_at i u) [0..<m])"
  shows "L = red_balance_raw"
  using assms red_balance_raw_length red_balance_raw_nth
  by(intro nth_equalityI) auto

lemma sucn: "Suc (n - Suc 0) = n" using nodes_nonempty by simp

subsection \<open>The pass refines\<close>

text \<open>\<^emph>\<open>The pass refines.\<close> The sentinel and the arc loop in one go: the caller's capacity and
      balance arrays come out holding the two outputs of the pass, and the two registers the cost
      shift and the range flag.\<close>

lemma reduce_tail_raw_rule:
  assumes "xu = upper" "bl = balance_list"
  shows
   "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a xu * oa \<mapsto>\<^sub>a cost_list *
     bal \<mapsto>\<^sub>a bl>
     reduce_tail_raw fa sa la ua oa bal m
   <\<lambda>r. fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a red_upper *
        oa \<mapsto>\<^sub>a cost_list * bal \<mapsto>\<^sub>a red_balance_raw
        * \<up>(fst r = cost_shift \<and> snd r = red_ok_arcs)>"
  unfolding reduce_tail_raw_def assms
  by(sep_auto simp: length_balance_list nodes_nonempty length_upper
                    upd_range_full bal_range_full
                    cost_shift_eq[symmetric] red_ok_arcs_iff[symmetric]
              heap: red_arcs_imp_rule)

subsection \<open>The range test refines\<close>

text \<open>The shift, as a fact about lists: one arc adds its capacity, signed, to the cell of its own
      endpoint.\<close>

definition shift_step :: "nat list \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list" where
  "shift_step idx c e a = a[idx ! e := a ! (idx ! e) + c * red_upper ! e]"

lemma shift_fold_length: "length (fold (shift_step idx c) es a) = length a"
  by(induction es arbitrary: a) (simp_all add: shift_step_def)

text \<open>What a whole shift does to one cell: it adds \<open>c\<close> times the capacity of the arcs indexed at that
      vertex, which for the two endpoint arrays is exactly \<open>capout\<close> and \<open>capin\<close>.\<close>

lemma shift_nth:
  assumes "v < length a" and "\<And> j. j < k \<Longrightarrow> idx ! j < length a"
  shows "fold (shift_step idx c) [0..<k] a ! v
           = a ! v + c * sum_list (map (\<lambda> e. if idx ! e = v then red_upper ! e else 0) [0..<k])"
  using assms
proof(induction k)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have IH: "fold (shift_step idx c) [0..<k] a ! v
              = a ! v + c * sum_list (map (\<lambda> e. if idx ! e = v then red_upper ! e else 0) [0..<k])"
    using Suc by simp
  have len: "length (fold (shift_step idx c) [0..<k] a) = length a" by(rule shift_fold_length)
  have kb: "idx ! k < length a" using Suc.prems(2) by simp
  have step: "fold (shift_step idx c) [0..<Suc k] a
                = (fold (shift_step idx c) [0..<k] a)
                    [idx ! k := (fold (shift_step idx c) [0..<k] a) ! (idx ! k) + c * red_upper ! k]"
    by(simp add: shift_step_def)
  show ?case
    unfolding step
    using IH len kb Suc.prems(1)
    by(cases "idx ! k = v") (simp_all add: nth_list_update algebra_simps)
qed

lemma shift_capout:
  assumes "length a = n" and "v < n"
  shows "fold (shift_step fst_list c) [0..<m] a ! v = a ! v + c * capout v"
proof -
  have b: "\<And> j. j < m \<Longrightarrow> fst_list ! j < length a" using fst_lt_n assms(1) by simp
  have v: "v < length a" using assms by simp
  show ?thesis using shift_nth[OF v b] by(simp add: capout_def)
qed

lemma shift_capin:
  assumes "length a = n" and "v < n"
  shows "fold (shift_step snd_list c) [0..<m] a ! v = a ! v + c * capin v"
proof -
  have b: "\<And> j. j < m \<Longrightarrow> snd_list ! j < length a" using snd_lt_n assms(1) by simp
  have v: "v < length a" using assms by simp
  show ?thesis using shift_nth[OF v b] by(simp add: capin_def)
qed

text \<open>The mirror shift puts the array back, cell by cell.\<close>

lemma shift_restore_fst:
  assumes "length a = n"
  shows "fold (shift_step fst_list (- c)) [0..<m] (fold (shift_step fst_list c) [0..<m] a) = a"
proof(rule nth_equalityI)
  show "length (fold (shift_step fst_list (- c)) [0..<m] (fold (shift_step fst_list c) [0..<m] a))
          = length a"
    by(simp add: shift_fold_length)
next
  fix v
  assume "v < length (fold (shift_step fst_list (- c)) [0..<m]
                          (fold (shift_step fst_list c) [0..<m] a))"
  hence v: "v < n" using assms by(simp add: shift_fold_length)
  have l1: "length (fold (shift_step fst_list c) [0..<m] a) = n"
    using assms by(simp add: shift_fold_length)
  show "fold (shift_step fst_list (- c)) [0..<m] (fold (shift_step fst_list c) [0..<m] a) ! v
          = a ! v"
    using shift_capout[OF l1 v, of "- c"] shift_capout[OF assms v, of c] by simp
qed

lemma shift_restore_snd:
  assumes "length a = n"
  shows "fold (shift_step snd_list (- c)) [0..<m] (fold (shift_step snd_list c) [0..<m] a) = a"
proof(rule nth_equalityI)
  show "length (fold (shift_step snd_list (- c)) [0..<m] (fold (shift_step snd_list c) [0..<m] a))
          = length a"
    by(simp add: shift_fold_length)
next
  fix v
  assume "v < length (fold (shift_step snd_list (- c)) [0..<m]
                          (fold (shift_step snd_list c) [0..<m] a))"
  hence v: "v < n" using assms by(simp add: shift_fold_length)
  have l1: "length (fold (shift_step snd_list c) [0..<m] a) = n"
    using assms by(simp add: shift_fold_length)
  show "fold (shift_step snd_list (- c)) [0..<m] (fold (shift_step snd_list c) [0..<m] a) ! v
          = a ! v"
    using shift_capin[OF l1 v, of "- c"] shift_capin[OF assms v, of c] by simp
qed

text \<open>\<^emph>\<open>The shift refines.\<close>\<close>

lemma shift_imp_rule:
  "\<lbrakk>e + k \<le> m; m \<le> length idx; length a = n; \<And> j. j < m \<Longrightarrow> idx ! j < n\<rbrakk> \<Longrightarrow>
   <ia \<mapsto>\<^sub>a idx * va \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a a>
     shift_imp ia va bal c e k
   <\<lambda>_. ia \<mapsto>\<^sub>a idx * va \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a fold (shift_step idx c) [e..<e + k] a>"
proof(induction k arbitrary: e a)
  case 0
  thus ?case by(subst shift_imp.simps) sep_auto
next
  case (Suc k)
  have em: "e < m" using Suc.prems(1) by simp
  have ei: "e < length idx" using em Suc.prems(2) by simp
  have er: "e < length red_upper" using em red_upper_length by simp
  have vlt: "idx ! e < length a" using Suc.prems(4)[OF em] Suc.prems(3) by simp
  have stp: "shift_step idx c e a = list_update a (idx ! e) (a ! (idx ! e) + c * red_upper ! e)"
    by(simp add: shift_step_def)
  have upd: "length (shift_step idx c e a) = n" using Suc.prems(3) by(simp add: shift_step_def)
  have IH: "<ia \<mapsto>\<^sub>a idx * va \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a shift_step idx c e a>
              shift_imp ia va bal c (Suc e) k
            <\<lambda>_. ia \<mapsto>\<^sub>a idx * va \<mapsto>\<^sub>a red_upper
                 * bal \<mapsto>\<^sub>a fold (shift_step idx c) [Suc e..<Suc e + k] (shift_step idx c e a)>"
    using Suc.IH[of "Suc e" "shift_step idx c e a"] Suc.prems(1,2,4) upd by simp
  have lst: "[e..<e + Suc k] = e # [Suc e..<Suc e + k]" by(simp add: upt_conv_Cons)
  have spl: "fold (shift_step idx c) [e..<e + Suc k] a
               = fold (shift_step idx c) [Suc e..<Suc e + k] (shift_step idx c e a)"
    unfolding lst by simp
  show ?case
    unfolding spl
    by(subst shift_imp.simps) (sep_auto simp: ei er vlt stp[symmetric] heap: IH)
qed

text \<open>The running total of a sweep, as a \<^emph>\<open>constant\<close>. Writing it as the \<open>sum_list\<close> over
      \<open>[v..<v + k]\<close> would be the same value, but the simplifier peels \<^const>\<open>upt\<close> from the \<^emph>\<open>right\<close>,
      so the sum in the induction hypothesis and the sum in the goal drift apart, the hypothesis
      stops matching, and the verification condition generator unrolls the loop instead of applying
      it --- which does not terminate.\<close>

definition ssum :: "'n list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n" where
  "ssum L v k = sum_list (map (\<lambda> u. L ! u) [v..<v + k])"

lemma ssum_0: "ssum L v 0 = 0"
  by(simp add: ssum_def)

lemma ssum_Suc: "ssum L v (Suc k) = L ! v + ssum L (Suc v) k"
proof -
  have "[v..<v + Suc k] = v # [Suc v..<Suc v + k]" by(simp add: upt_conv_Cons)
  thus ?thesis by(simp add: ssum_def)
qed

text \<open>\<^emph>\<open>The vertex sweep refines.\<close> It writes nothing, so the balance array is carried through
      unchanged; the two registers come out as the running total and the conjunction of the tests.\<close>

lemma sweep_imp_rule:
  "v + k \<le> length L \<Longrightarrow>
   <bal \<mapsto>\<^sub>a L>
     sweep_imp bal c v k tot ok
   <\<lambda>r. bal \<mapsto>\<^sub>a L
        * \<up>(fst r = tot + ssum L v k
            \<and> snd r = (ok \<and> (\<forall> u. v \<le> u \<and> u < v + k \<longrightarrow> c * L ! u \<le> 0)))>"
proof(induction k arbitrary: v tot ok)
  case 0
  thus ?case by(subst sweep_imp.simps) (sep_auto simp: ssum_0)
next
  case (Suc k)
  have vl: "v < length L" using Suc.prems by simp
  have IH: "<bal \<mapsto>\<^sub>a L>
              sweep_imp bal c (Suc v) k tot' ok'
            <\<lambda>r. bal \<mapsto>\<^sub>a L
                 * \<up>(fst r = tot' + ssum L (Suc v) k
                     \<and> snd r = (ok' \<and> (\<forall> u. Suc v \<le> u \<and> u < Suc v + k \<longrightarrow> c * L ! u \<le> 0)))>"
    for tot' and ok'
    by(rule Suc.IH) (use Suc.prems in simp)
  note [simp del] = upt_Suc
  have qpeel: "(\<forall> u. v \<le> u \<and> u < Suc (v + k) \<longrightarrow> Q u)
                 = (Q v \<and> (\<forall> u. Suc v \<le> u \<and> u < Suc (v + k) \<longrightarrow> Q u))" for Q
    by(auto simp add: le_Suc_eq) (metis le_neq_implies_less less_Suc_eq_le not_less_eq)
  show ?case
    unfolding ssum_Suc
    by(subst sweep_imp.simps) (sep_auto simp: vl qpeel add.assoc heap: IH)
qed

text \<open>The two range tests, as the sign of a shifted balance.\<close>

lemma bal_ok_shifted:
  "bal_ok = ((\<forall> u. Suc 0 \<le> u \<and> u < n
               \<longrightarrow> fold (shift_step fst_list (- 1)) [0..<m] red_balance_raw ! u \<le> 0)
             \<and> (\<forall> u. Suc 0 \<le> u \<and> u < n
               \<longrightarrow> 0 \<le> fold (shift_step snd_list 1) [0..<m] red_balance_raw ! u))"
proof -
  have l: "length red_balance_raw = n" by(rule red_balance_raw_length)
  have o1: "(fold (shift_step fst_list (- 1)) [0..<m] red_balance_raw ! u)
              = red_balance_raw ! u - capout u" if "u < n" for u
    using shift_capout[OF l that, of "- 1"] by simp
  have o2: "(fold (shift_step snd_list 1) [0..<m] red_balance_raw ! u)
              = red_balance_raw ! u + capin u" if "u < n" for u
    using shift_capin[OF l that, of 1] by simp
  have a: "(- capin u \<le> red_balance_raw ! u)
             = (0 \<le> fold (shift_step snd_list 1) [0..<m] red_balance_raw ! u)"
    if "u < n" for u
    unfolding o2[OF that] by(rule iffI; linarith)
  have b: "(red_balance_raw ! u \<le> capout u)
             = (fold (shift_step fst_list (- 1)) [0..<m] red_balance_raw ! u \<le> 0)"
    if "u < n" for u
    unfolding o1[OF that] by(rule iffI; linarith)
  show ?thesis
    by(auto simp add: bal_ok_def a b)
qed

text \<open>The total the last sweep reads is the total of the emitted balances: the sentinel
      contributes \<open>0\<close>.\<close>

lemma ssum_all: "ssum red_balance_raw (Suc 0) (n - Suc 0) = sum_list red_balance_raw"
  using nodes_nonempty red_balance_raw_sum_inner
  by(simp add: ssum_def interv_sum_list_conv_sum_set_nat)

text \<open>\<^emph>\<open>The upper test refines.\<close> Shift the out-capacity off the balances, read the sign, shift it
      back. Each half is a procedure of its own so that its result is one opaque flag: with the
      three flags inlined the verification condition generator splits the conjunction before it has
      finished executing, and then has nothing left to close the branches with.\<close>

lemma bal_out_test_rule:
  "<fa \<mapsto>\<^sub>a fst_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw>
     bal_out_test fa us bal m n
   <\<lambda>r. fa \<mapsto>\<^sub>a fst_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw
        * \<up>(r = (\<forall> v \<in> {1..<n}. red_balance_raw ! v \<le> capout v))>"
proof -
  have l: "length red_balance_raw = n" by(rule red_balance_raw_length)
  let ?L = "fold (shift_step fst_list (- 1)) [0..<m] red_balance_raw"
  have len: "length ?L = n" using l by(simp add: shift_fold_length)
  have r: "fold (shift_step fst_list 1) [0..<m] ?L = red_balance_raw"
    using shift_restore_fst[OF l, of "- 1"] by simp
  have nth: "?L ! u = red_balance_raw ! u - capout u" if "u < n" for u
    using shift_capout[OF l that, of "- 1"] by simp
  have sw: "<bal \<mapsto>\<^sub>a ?L>
              sweep_imp bal 1 (Suc 0) (n - Suc 0) 0 True
            <\<lambda>r. bal \<mapsto>\<^sub>a ?L
                 * \<up>(fst r = 0 + ssum ?L (Suc 0) (n - Suc 0)
                     \<and> snd r = (True \<and> (\<forall> u. Suc 0 \<le> u \<and> u < Suc 0 + (n - Suc 0)
                                    \<longrightarrow> 1 * ?L ! u \<le> 0)))>"
    by(rule sweep_imp_rule) (simp add: len sucn)
  have eq: "(\<forall> u. Suc 0 \<le> u \<and> u < n \<longrightarrow> ?L ! u \<le> 0)
              = (\<forall> v \<in> {1..<n}. red_balance_raw ! v \<le> capout v)"
    using nth by auto
  show ?thesis
    unfolding bal_out_test_def
    by(sep_auto simp: l len r sucn eq length_fst_list fst_lt_n heap: shift_imp_rule sw)
qed

text \<open>\<^emph>\<open>The lower test refines.\<close> The same, with the in-capacity and the other sign.\<close>

lemma bal_in_test_rule:
  "<sa \<mapsto>\<^sub>a snd_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw>
     bal_in_test sa us bal m n
   <\<lambda>r. sa \<mapsto>\<^sub>a snd_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw
        * \<up>(r = (\<forall> v \<in> {1..<n}. - capin v \<le> red_balance_raw ! v))>"
proof -
  have l: "length red_balance_raw = n" by(rule red_balance_raw_length)
  let ?L = "fold (shift_step snd_list 1) [0..<m] red_balance_raw"
  have len: "length ?L = n" using l by(simp add: shift_fold_length)
  have r: "fold (shift_step snd_list (- 1)) [0..<m] ?L = red_balance_raw"
    using shift_restore_snd[OF l, of 1] by simp
  have nth: "?L ! u = red_balance_raw ! u + capin u" if "u < n" for u
    using shift_capin[OF l that, of 1] by simp
  have sw: "<bal \<mapsto>\<^sub>a ?L>
              sweep_imp bal (- 1) (Suc 0) (n - Suc 0) 0 True
            <\<lambda>r. bal \<mapsto>\<^sub>a ?L
                 * \<up>(fst r = 0 + ssum ?L (Suc 0) (n - Suc 0)
                     \<and> snd r = (True \<and> (\<forall> u. Suc 0 \<le> u \<and> u < Suc 0 + (n - Suc 0)
                                    \<longrightarrow> (- 1) * ?L ! u \<le> 0)))>"
    by(rule sweep_imp_rule) (simp add: len sucn)
  have pt: "(0 \<le> ?L ! u) = (- capin u \<le> red_balance_raw ! u)" if "u < n" for u
    unfolding nth[OF that] by(rule iffI; linarith)
  have eq: "(\<forall> u. Suc 0 \<le> u \<and> u < n \<longrightarrow> 0 \<le> ?L ! u)
              = (\<forall> v \<in> {1..<n}. - capin v \<le> red_balance_raw ! v)"
    using pt by auto
  show ?thesis
    unfolding bal_in_test_def
    by(sep_auto simp: l len r sucn eq length_snd_list snd_lt_n heap: shift_imp_rule sw)
qed

text \<open>\<^emph>\<open>The total test refines.\<close> One sweep of the restored array.\<close>

lemma bal_sum_test_rule:
  "<bal \<mapsto>\<^sub>a red_balance_raw>
     bal_sum_test bal n
   <\<lambda>r. bal \<mapsto>\<^sub>a red_balance_raw * \<up>(r = sum_ok)>"
proof -
  have l: "length red_balance_raw = n" by(rule red_balance_raw_length)
  have sw: "<bal \<mapsto>\<^sub>a red_balance_raw>
              sweep_imp bal 0 (Suc 0) (n - Suc 0) 0 True
            <\<lambda>r. bal \<mapsto>\<^sub>a red_balance_raw
                 * \<up>(fst r = 0 + ssum red_balance_raw (Suc 0) (n - Suc 0)
                     \<and> snd r = (True \<and> (\<forall> u. Suc 0 \<le> u \<and> u < Suc 0 + (n - Suc 0)
                                    \<longrightarrow> 0 * red_balance_raw ! u \<le> 0)))>"
    by(rule sweep_imp_rule) (simp add: l sucn)
  show ?thesis
    unfolding bal_sum_test_def
    by(sep_auto simp: ssum_all sum_ok_def heap: sw)
qed

text \<open>\<^emph>\<open>The test half refines.\<close> The three flags; nothing is written that is not put back.\<close>

lemma bal_tail_rule:
  "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw>
     bal_tail fa sa us bal m n
   <\<lambda>ok. fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw
         * \<up>(ok = (bal_ok \<and> sum_ok))>"
  unfolding bal_tail_def
  by(sep_auto simp: bal_ok_def
             heap: bal_out_test_rule bal_in_test_rule bal_sum_test_rule)

text \<open>\<^emph>\<open>The reduction refines.\<close> The pass and the test; every array is the caller's, and comes back
      holding the reduced instance.\<close>

theorem reduce_imp_rule:
  assumes "xu = upper" "bl = balance_list"
  shows
   "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a xu * oa \<mapsto>\<^sub>a cost_list *
     ba \<mapsto>\<^sub>a bl>
     reduce_imp fa sa la ua oa ba m n
   <\<lambda>r. fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a red_upper *
        oa \<mapsto>\<^sub>a cost_list * ba \<mapsto>\<^sub>a red_balance_list
        * \<up>(fst r = cost_shift \<and> snd r = red_ok)>"
  unfolding reduce_imp_def
  by(sep_auto simp: red_ok_def red_balance_list_def
             heap: reduce_tail_raw_rule[OF assms] bal_tail_rule)

end

end
