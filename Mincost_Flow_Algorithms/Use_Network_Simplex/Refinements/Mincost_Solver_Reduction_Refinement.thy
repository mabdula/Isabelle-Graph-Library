theory Mincost_Solver_Reduction_Refinement
  imports Use_Network_Simplex.Mincost_Solver_Reduction
           Separation_Logic_Imperative_HOL_Partial.Array_Blit
begin

provenance ai


section \<open>Imperative refinement of the DIMACS reduction\<close>

text \<open>The fold of \<open>Mincost_Solver_Reduction\<close> becomes a pass over the caller's six arrays; nothing
      is allocated. The programs are defined outside every locale, so every input is an argument;
      the refinement proofs live in the proof locale @{locale dimacs_lists_network}.\<close>

subsection \<open>The pass\<close>

text \<open>The capacities are rewritten in place and the lower bounds are scattered onto the balances,
      head before tail so that a self-loop cancels as in the fold. The cost shift and the range flag
      are accumulator arguments. The capacity an arc contributes is a named function: an inline
      \<open>if\<close> would be split by the verification condition generator.\<close>

definition arc_cap :: "'a :: {ord, minus, zero} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "arc_cap li ui = (if li \<le> ui then ui - li else 0)"

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

text \<open>The sentinel \<open>0\<close> and then the loop, as a procedure of its own: a Hoare rule only applies to a
      program the verification condition generator still sees as one term.\<close>

definition reduce_tail_raw ::
  "nat array \<Rightarrow> nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array
   \<Rightarrow> nat \<Rightarrow> ('n \<times> bool) Heap" where
  "reduce_tail_raw fa sa la ua oa bal mm =
     do {
       _ \<leftarrow> Array.upd 0 0 bal;
       red_arcs_imp fa sa la ua oa bal 0 mm 0 True }"

text \<open>Reading the answer back: the lower bounds are added to the solver's flow, in place.\<close>

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

text \<open>The incident capacity is never stored: an arc sweep shifts it onto the balances with a sign,
      a vertex sweep reads the sign of each shifted balance, and the mirror sweep undoes the shift.
      The vertex sweep skips the sentinel, writes nothing and also totals what it reads.\<close>

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

partial_function (heap) sweep_imp ::
  "('n :: {heap, linordered_idom}) array \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> bool \<Rightarrow> ('n \<times> bool) Heap" where
  "sweep_imp bal c v k tot ok =
     (if k = 0 then return (tot, ok)
      else do {
        x \<leftarrow> Array.nth bal v;
        sweep_imp bal c (Suc v) (k - 1) (tot + x) (ok \<and> c * x \<le> 0) })"

text \<open>Subtracting the out-capacity makes a non-positive balance the upper test; adding the
      in-capacity makes a non-negative balance the lower test. Each test is a procedure of its own,
      so that its result is one opaque flag.\<close>

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

text \<open>The whole reduction: the pass and the test. It returns the cost shift and the flag.\<close>

definition reduce_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> ('n :: {heap, linordered_idom}) array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array
   \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('n \<times> bool) Heap" where
  "reduce_imp fa sa la ua oa ba mm nn =
     do {
       p   \<leftarrow> reduce_tail_raw fa sa la ua oa ba mm;
       ok2 \<leftarrow> bal_tail fa sa ua ba mm nn;
       return (fst p, snd p \<and> ok2) }"

text \<open>The numeric type must carry @{class heap}, so the proofs live in a heap-strengthened copy of
      the proof locale.\<close>

locale dimacs_lists_network_heap =
  dimacs_lists_network where lower = "lower :: ('n :: {heap, linordered_idom}) list"
  for lower
begin

lemma fst_lt_n: "j < m \<Longrightarrow> fst_list ! j < n"
  and snd_lt_n: "j < m \<Longrightarrow> snd_list ! j < n"
  using fst_list_vertex[of j] snd_list_vertex[of j]
  by auto

text \<open>One arc's scatter into the balance array, as a fact about lists. At a self-loop the two
      updates cancel, as in @{const dimacs_lists.bal_step_at}.\<close>

lemma bal_upd_step:
  assumes "fst_list ! i < length bl" "snd_list ! i < length bl" "v < length bl" "i < m"
  defines "bl1 \<equiv> list_update bl (snd_list ! i) (bl ! (snd_list ! i) + lower ! i)"
  shows "list_update bl1 (fst_list ! i) (bl1 ! (fst_list ! i) - lower ! i) ! v
         = bl ! v + bal_step_at i v"
  using assms
  by (auto simp: bl1_def bal_step_at_def nth_list_update)

text \<open>What the two written arrays hold after the arcs \<open>[i..<i+k]\<close> have been swept. They are
      constants so that the rewrites of the induction stay atomic.\<close>

definition upd_range :: "nat \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list" where
  "upd_range i k xu = map (\<lambda> j. if i \<le> j \<and> j < i + k then red_upper_at j else xu ! j) [0..<m]"

definition bal_range :: "nat \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list" where
  "bal_range i k bl =
     map (\<lambda> v. bl ! v + sum_list (map (\<lambda> j. bal_step_at j v) [i..<i + k])) [0..<n]"

lemma upd_range_length [simp]: "length (upd_range i k xu) = m"
  by (simp add: upd_range_def)

lemma bal_range_length [simp]: "length (bal_range i k bl) = n"
  by (simp add: bal_range_def)

lemma upd_range_0: "length xu = m \<Longrightarrow> upd_range i 0 xu = xu"
  unfolding upd_range_def
  by (intro nth_equalityI) auto

lemma bal_range_0: "length bl = n \<Longrightarrow> bal_range i 0 bl = bl"
  unfolding bal_range_def
  by (intro nth_equalityI) auto

lemma upd_range_step:
  "\<lbrakk>i < m; length xu = m; \<And> j. j < m \<Longrightarrow> L ! j = (if j = i then red_upper_at i else xu ! j)\<rbrakk> \<Longrightarrow>
   upd_range i (Suc k) xu = upd_range (Suc i) k L"
  unfolding upd_range_def
  by (rule map_cong) auto

lemma bal_range_step:
  "(\<And> v. v < n \<Longrightarrow> L ! v = bl ! v + bal_step_at i v) \<Longrightarrow>
   bal_range i (Suc k) bl = bal_range (Suc i) k L"
  unfolding bal_range_def
  by (rule map_cong) (simp_all add: upt_conv_Cons add.assoc del: upt_Suc)

lemma upd_range_full: "length xu = m \<Longrightarrow> upd_range 0 m xu = red_upper"
  unfolding upd_range_def
  by (intro nth_equalityI) (auto simp: red_upper_length red_arc_nth)

lemma bal_range_full: "bal_range 0 m (list_update balance_list 0 0) = red_balance_raw"
  unfolding bal_range_def
  by (intro nth_equalityI) (auto simp: red_balance_raw_length red_balance_raw_nth red_bal_init_def)

text \<open>\<^emph>\<open>The arc loop refines.\<close> The capacity array is read and written, so only its unswept part is
      known to hold the parsed bound.\<close>

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
  then show ?case
    by (subst red_arcs_imp.simps) (sep_auto simp: upd_range_0 bal_range_0 "0.prems"(2,4))
next
  case (Suc k)
  have im: "i < m"
    using Suc.prems
    by simp
  have bnd: "i < length fst_list" "i < length snd_list" "i < length lower" "i < length cost_list"
            "i < length xu" "fst_list ! i < length bl" "snd_list ! i < length bl"
    using im Suc.prems(2,4) fst_lt_n[OF im] snd_lt_n[OF im]
    by (simp_all add: length_fst_list length_snd_list length_lower length_cost_list)
  let ?bl1 = "list_update bl (snd_list ! i) (bl ! (snd_list ! i) + lower ! i)"
  let ?bl2 = "list_update ?bl1 (fst_list ! i) (?bl1 ! (fst_list ! i) - lower ! i)"
  let ?xu2 = "list_update xu i (arc_cap (lower ! i) (upper ! i))"
  have ur: "upd_range i (Suc k) xu = upd_range (Suc i) k ?xu2"
    using im Suc.prems(2) bnd(5)
    by (intro upd_range_step) (auto simp: nth_list_update red_upper_at_def arc_cap_def)
  have br: "bal_range i (Suc k) bl = bal_range (Suc i) k ?bl2"
    using bal_upd_step[OF bnd(6,7) _ im] Suc.prems(4)
    by (intro bal_range_step) simp
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
    using Suc.prems
    by (intro Suc.IH) (auto simp: nth_list_update)
  note [simp del] = upt_Suc
  show ?case
    by (subst red_arcs_imp.simps)
      (sep_auto simp: bnd im Suc.prems(2,3,4) ur br upt_conv_Cons all_range_peel add.assoc
                heap: IH)
qed

subsection \<open>Reading the answer back\<close>

definition add_range :: "nat \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list" where
  "add_range i k gs = map (\<lambda> j. if i \<le> j \<and> j < i + k then gs ! j + lower ! j else gs ! j) [0..<m]"

lemma add_range_length [simp]: "length (add_range i k gs) = m"
  by (simp add: add_range_def)

lemma orig_flow_imp_rule:
  "\<lbrakk>i + k \<le> m; length gs = m\<rbrakk> \<Longrightarrow>
   <la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a gs>
     orig_flow_imp la ga i k
   <\<lambda>_. la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a add_range i k gs>"
proof(induction k arbitrary: i gs)
  case 0
  then have "add_range i 0 gs = gs"
    unfolding add_range_def
    by (intro nth_equalityI) auto
  then show ?case
    by (subst orig_flow_imp.simps) sep_auto
next
  case (Suc k)
  then have "add_range i (Suc k) gs = add_range (Suc i) k (list_update gs i (gs ! i + lower ! i))"
    unfolding add_range_def
    by (intro map_cong) (auto simp: nth_list_update)
  with Suc.prems(1) show ?case
    by (subst orig_flow_imp.simps) (sep_auto simp: Suc.prems(2) length_lower heap: Suc.IH)
qed

lemma orig_flow_imp_correct:
  assumes "length gs = m"
  shows
   "<la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a gs>
     orig_flow_imp la ga 0 m
   <\<lambda>_. la \<mapsto>\<^sub>a lower * ga \<mapsto>\<^sub>a orig_flow gs>"
proof-
  have "add_range 0 m gs = orig_flow gs"
    using assms
    unfolding add_range_def orig_flow_def
    by (intro nth_equalityI) auto
  then show ?thesis
    using orig_flow_imp_rule[of 0 m gs la ga] assms
    by simp
qed

subsection \<open>The pass refines\<close>

lemma red_sh_fold:
  "fst (snd (snd (fold red_step es st)))
   = fst (snd (snd st)) + sum_list (map (\<lambda> i. cost_list ! i * lower ! i) es)"
  by (induction es arbitrary: st) (auto simp: red_step_def Let_def add.assoc split: prod.splits)

lemma cost_shift_eq: "cost_shift = sum_list (map (\<lambda> i. cost_list ! i * lower ! i) [0..<m])"
  by (simp add: cost_shift_def red_pass_def red_init_def red_sh_fold split_beta)

text \<open>The caller's capacity and balance arrays come out holding the two outputs of the pass.\<close>

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
  by (sep_auto simp: length_balance_list nodes_nonempty length_upper upd_range_full bal_range_full
                     cost_shift_eq[symmetric] red_ok_arcs_iff[symmetric]
               heap: red_arcs_imp_rule)

subsection \<open>The range test refines\<close>

text \<open>A shift, as a fact about lists: an arc adds its signed capacity to the cell of one endpoint.\<close>

definition shift_step :: "nat list \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list" where
  "shift_step idx c e a = list_update a (idx ! e) (a ! (idx ! e) + c * red_upper ! e)"

lemma shift_step_length [simp]: "length (shift_step idx c e a) = length a"
  by (simp add: shift_step_def)

lemma shift_fold_length: "length (fold (shift_step idx c) es a) = length a"
  by (induction es arbitrary: a) simp_all

lemma shift_nth:
  "\<lbrakk>v < length a; \<And> j. j < k \<Longrightarrow> idx ! j < length a\<rbrakk> \<Longrightarrow>
   fold (shift_step idx c) [0..<k] a ! v
   = a ! v + c * sum_list (map (\<lambda> e. if idx ! e = v then red_upper ! e else 0) [0..<k])"
  by (induction k) (auto simp: shift_step_def shift_fold_length nth_list_update algebra_simps)

lemma shift_capout: "\<lbrakk>length a = n; v < n\<rbrakk> \<Longrightarrow>
  fold (shift_step fst_list c) [0..<m] a ! v = a ! v + c * capout v"
  using fst_lt_n
  by (simp add: shift_nth capout_def)

lemma shift_capin: "\<lbrakk>length a = n; v < n\<rbrakk> \<Longrightarrow>
  fold (shift_step snd_list c) [0..<m] a ! v = a ! v + c * capin v"
  using snd_lt_n
  by (simp add: shift_nth capin_def)

text \<open>The mirror shift puts the array back.\<close>

lemma shift_restore:
  "\<lbrakk>length a = n; \<And> j. j < m \<Longrightarrow> idx ! j < n\<rbrakk> \<Longrightarrow>
   fold (shift_step idx (- c)) [0..<m] (fold (shift_step idx c) [0..<m] a) = a"
  by (intro nth_equalityI) (simp_all add: shift_fold_length shift_nth)

lemma shift_imp_rule:
  "\<lbrakk>e + k \<le> m; m \<le> length idx; length a = n; \<And> j. j < m \<Longrightarrow> idx ! j < n\<rbrakk> \<Longrightarrow>
   <ia \<mapsto>\<^sub>a idx * va \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a a>
     shift_imp ia va bal c e k
   <\<lambda>_. ia \<mapsto>\<^sub>a idx * va \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a fold (shift_step idx c) [e..<e + k] a>"
proof(induction k arbitrary: e a)
  case 0
  then show ?case
    by (subst shift_imp.simps) sep_auto
next
  case (Suc k)
  note [simp del] = upt_Suc
  from Suc.prems have "e < m"
    by simp
  with Suc.prems(1,2,4) show ?case
    by (subst shift_imp.simps)
      (sep_auto simp: Suc.prems(3) red_upper_length upt_conv_Cons shift_step_def[symmetric]
                heap: Suc.IH)
qed

text \<open>The running total of a sweep is a constant: as a \<open>sum_list\<close> over \<open>[v..<v + k]\<close> the simplifier
      would peel \<open>upt\<close> from the right, and the induction hypothesis would stop matching.\<close>

definition ssum :: "'n list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n" where
  "ssum L v k = sum_list (map (\<lambda> u. L ! u) [v..<v + k])"

lemma ssum_Suc: "ssum L v (Suc k) = L ! v + ssum L (Suc v) k"
  by (simp add: ssum_def upt_conv_Cons del: upt_Suc)

lemma sweep_imp_rule:
  "v + k \<le> length L \<Longrightarrow>
   <bal \<mapsto>\<^sub>a L>
     sweep_imp bal c v k tot ok
   <\<lambda>r. bal \<mapsto>\<^sub>a L
        * \<up>(fst r = tot + ssum L v k
            \<and> snd r = (ok \<and> (\<forall> u. v \<le> u \<and> u < v + k \<longrightarrow> c * L ! u \<le> 0)))>"
proof(induction k arbitrary: v tot ok)
  case 0
  then show ?case
    by (subst sweep_imp.simps) (sep_auto simp: ssum_def)
next
  case (Suc k)
  note [simp del] = upt_Suc
  from Suc.prems show ?case
    unfolding ssum_Suc
    by (subst sweep_imp.simps) (sep_auto simp: all_range_peel add.assoc heap: Suc.IH)
qed

lemma ssum_all: "ssum red_balance_raw (Suc 0) (n - Suc 0) = sum_list red_balance_raw"
  using nodes_nonempty red_balance_raw_sum_inner
  by (simp add: ssum_def interv_sum_list_conv_sum_set_nat)

text \<open>\<^emph>\<open>The upper test refines.\<close> Shift the out-capacity off, read the sign, shift it back.\<close>

lemma bal_out_test_rule:
  "<fa \<mapsto>\<^sub>a fst_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw>
     bal_out_test fa us bal m n
   <\<lambda>r. fa \<mapsto>\<^sub>a fst_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw
        * \<up>(r = (\<forall> v \<in> {1..<n}. red_balance_raw ! v \<le> capout v))>"
proof-
  have "(\<forall> u. Suc 0 \<le> u \<and> u < Suc 0 + (n - Suc 0)
           \<longrightarrow> 1 * fold (shift_step fst_list (- 1)) [0..<m] red_balance_raw ! u \<le> 0)
        = (\<forall> v \<in> {1..<n}. red_balance_raw ! v \<le> capout v)"
    using nodes_nonempty
    by (auto simp: shift_capout red_balance_raw_length)
  then show ?thesis
    unfolding bal_out_test_def
    using shift_restore[OF red_balance_raw_length fst_lt_n, of "- 1", simplified]
    by (sep_auto simp: red_balance_raw_length shift_fold_length length_fst_list fst_lt_n
                       nodes_nonempty
                 heap: shift_imp_rule sweep_imp_rule)
qed

lemma bal_in_test_rule:
  "<sa \<mapsto>\<^sub>a snd_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw>
     bal_in_test sa us bal m n
   <\<lambda>r. sa \<mapsto>\<^sub>a snd_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw
        * \<up>(r = (\<forall> v \<in> {1..<n}. - capin v \<le> red_balance_raw ! v))>"
proof-
  have "(\<forall> u. Suc 0 \<le> u \<and> u < Suc 0 + (n - Suc 0)
           \<longrightarrow> - 1 * fold (shift_step snd_list 1) [0..<m] red_balance_raw ! u \<le> 0)
        = (\<forall> v \<in> {1..<n}. - capin v \<le> red_balance_raw ! v)"
    using nodes_nonempty
    by (auto simp: shift_capin red_balance_raw_length minus_le_iff)
  then show ?thesis
    unfolding bal_in_test_def
    using shift_restore[OF red_balance_raw_length snd_lt_n, of 1, simplified]
    by (sep_auto simp: red_balance_raw_length shift_fold_length length_snd_list snd_lt_n
                       nodes_nonempty
                 heap: shift_imp_rule sweep_imp_rule)
qed

lemma bal_sum_test_rule:
  "<bal \<mapsto>\<^sub>a red_balance_raw>
     bal_sum_test bal n
   <\<lambda>r. bal \<mapsto>\<^sub>a red_balance_raw * \<up>(r = sum_ok)>"
  unfolding bal_sum_test_def
  using nodes_nonempty
  by (sep_auto simp: ssum_all sum_ok_def red_balance_raw_length heap: sweep_imp_rule)

lemma bal_tail_rule:
  "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw>
     bal_tail fa sa us bal m n
   <\<lambda>ok. fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * us \<mapsto>\<^sub>a red_upper * bal \<mapsto>\<^sub>a red_balance_raw
         * \<up>(ok = (bal_ok \<and> sum_ok))>"
  unfolding bal_tail_def
  by (sep_auto simp: bal_ok_def heap: bal_out_test_rule bal_in_test_rule bal_sum_test_rule)

text \<open>\<^emph>\<open>The reduction refines.\<close> Every array is the caller's and comes back holding the reduced
      instance.\<close>

lemma reduce_imp_rule:
  assumes "xu = upper" "bl = balance_list"
  shows
   "<fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a xu * oa \<mapsto>\<^sub>a cost_list *
     ba \<mapsto>\<^sub>a bl>
     reduce_imp fa sa la ua oa ba m n
   <\<lambda>r. fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * la \<mapsto>\<^sub>a lower * ua \<mapsto>\<^sub>a red_upper *
        oa \<mapsto>\<^sub>a cost_list * ba \<mapsto>\<^sub>a red_balance_list
        * \<up>(fst r = cost_shift \<and> snd r = red_ok)>"
  unfolding reduce_imp_def
  by (sep_auto simp: red_ok_def red_balance_list_def
               heap: reduce_tail_raw_rule[OF assms] bal_tail_rule)

end

end
