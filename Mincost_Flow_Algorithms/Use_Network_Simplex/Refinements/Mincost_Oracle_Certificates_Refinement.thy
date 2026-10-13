theory Mincost_Oracle_Certificates_Refinement
  imports Use_Network_Simplex.Mincost_Oracle_Certificates 
          Separation_Logic_Imperative_HOL_Partial.Array_Blit
begin

section \<open>Imperative refinement of the certificate checkers and the oracle call\<close>

text \<open>The functional theory reads the instance and the certificates as lists and pretends that
      @{const nth} is a load; here they are @{class heap} arrays and it is one.  The structure is
      carried over unchanged --- one counted loop per check, the same guards in the same order, the
      same single accumulator --- so that each imperative program is the functional one with the
      list operations replaced by array operations, and each refinement lemma says exactly that:
      the program returns what the functional check returns and leaves the instance where it was.

      The two things the pipeline does not compute itself are parameters with an assumed Hoare
      triple: the \<^emph>\<open>oracle\<close>, whose triple says only that it agrees with the functional oracle (it is
      untrusted, so nothing else may be assumed), and the \<^emph>\<open>verified cleanup\<close>, whose triple says its
      verdict is true of the instance.  The latter is the interface a verified implementation is
      plugged into.\<close>

subsection \<open>The instance and the certificates as arrays\<close>

text \<open>The five input arrays travel together; the certificates are separate arrays handed over by the
      oracle.  Following the refinements of the network simplex, the bundle is a tuple and every
      read destructures it, so no record lookup survives into the generated code.\<close>

text \<open>The numeric type has to carry @{class heap} as well as @{class linordered_idom} for its values
      to live in arrays, and a sort cannot be strengthened inside a context, so the imperative layer
      is a locale of its own --- assumption-free, like the functional code locale it extends.

      The five arrays are passed one by one rather than bundled: a bundle would have to be taken
      apart inside every loop, and a destructured recursive call no longer matches the induction
      hypothesis of its own refinement proof.  It is also how the network simplex passes its
      instance.\<close>

locale mcf_oracle_heap_spec =
  mcf_oracle_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list"
begin

definition inst_assn ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> assn" where
  "inst_assn fa sa ca oa ba =
     fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * ca \<mapsto>\<^sub>a capacity_list *
     oa \<mapsto>\<^sub>a cost_list * ba \<mapsto>\<^sub>a balance_list"

text \<open>Comparing the first @{term k} cells of two arrays, which is what the balance condition of the
      optimality check comes down to once the accumulator has been filled.  It stops at the first
      difference.\<close>

partial_function (heap) arr_eq_imp :: "'n array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "arr_eq_imp a b k =
     (if k = 0 then return True
      else let j = k - 1
           in do {
             x \<leftarrow> Array.nth a j;
             y \<leftarrow> Array.nth b j;
             if x = y then arr_eq_imp a b j else return False })"

lemma arr_eq_imp_rule:
  "\<lbrakk>k \<le> length xs; k \<le> length ys\<rbrakk> \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys> arr_eq_imp a b k
   <\<lambda>r. a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys * \<up>(r = (\<forall> i < k. xs ! i = ys ! i))>"
proof(induction k)
  case 0
  thus ?case by(subst arr_eq_imp.simps) sep_auto
next
  case (Suc k)
  have kx: "k < length xs" and ky: "k < length ys" using Suc.prems by simp_all
  have IH: "<a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys> arr_eq_imp a b k
             <\<lambda>r. a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys * \<up>(r = (\<forall> i < k. xs ! i = ys ! i))>"
    using Suc.IH Suc.prems by simp
  have split: "(\<forall> i < Suc k. xs ! i = ys ! i) = ((\<forall> i < k. xs ! i = ys ! i) \<and> xs ! k = ys ! k)"
    by(auto simp add: less_Suc_eq)
  show ?case
    by(subst arr_eq_imp.simps) (sep_auto simp: kx ky split heap: IH)
qed

subsection \<open>Unboundedness\<close>

text \<open>The cycle arrives as the solver leaves it: a buffer and the number of arcs written into it, so
      the walk is over the first @{term k} cells from position @{term i} rather than along a list.
      The guards are in the functional order --- range, then capacity, then linkage --- so an arc
      that fails the range test is never used to index anything.\<close>

partial_function (heap) cyc_loop_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> bool Heap" where
  "cyc_loop_imp fa sa ca oa cyca i k prev s tot =
     (if k = 0 then return (prev = s \<and> tot < 0)
      else do {
        e \<leftarrow> Array.nth cyca i;
        if \<not> e < m then return False
        else do {
          c \<leftarrow> Array.nth ca e;
          if c \<noteq> - 1 then return False
          else do {
            u \<leftarrow> Array.nth fa e;
            if prev \<noteq> u then return False
            else do {
              v \<leftarrow> Array.nth sa e;
              ce \<leftarrow> Array.nth oa e;
              cyc_loop_imp fa sa ca oa cyca (Suc i) (k - 1) v s (tot + ce) } } } })"

lemma cyc_loop_imp_rule:
  "\<lbrakk>length fst_list = m; length snd_list = m; length capacity_list = m; length cost_list = m;
    i + k \<le> length xs\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs>
     cyc_loop_imp fa sa ca oa cyca i k prev s tot
   <\<lambda>r. inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs
        * \<up>(r = cyc_loop (take k (drop i xs)) prev s tot)>"
proof(induction k arbitrary: i prev tot)
  case 0
  thus ?case by(subst cyc_loop_imp.simps) (sep_auto simp: inst_assn_def)
next
  case (Suc k)
  have ix: "i < length xs" using Suc.prems by simp
  have tk: "take (Suc k) (drop i xs) = xs ! i # take k (drop (Suc i) xs)"
    by(subst Cons_nth_drop_Suc[OF ix, symmetric]) simp
  have IH: "<inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs>
              cyc_loop_imp fa sa ca oa cyca (Suc i) k v s t
            <\<lambda>r. inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs
                 * \<up>(r = cyc_loop (take k (drop (Suc i) xs)) v s t)>"
    for v t
    using Suc.IH Suc.prems by simp
  show ?case
    by(subst cyc_loop_imp.simps)
      (sep_auto simp: inst_assn_def tk ix Suc.prems uncapacitated_def
                heap: IH[unfolded inst_assn_def])
qed

text \<open>The check itself: the buffer is empty when the solver wrote no arcs, and the seed is read only
      after the first arc has passed the range test.\<close>

definition check_unbounded_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "check_unbounded_imp fa sa ca oa cyca k =
     (if k = 0 then return False
      else do {
        e0 \<leftarrow> Array.nth cyca 0;
        if \<not> e0 < m then return False
        else do {
          s \<leftarrow> Array.nth fa e0;
          cyc_loop_imp fa sa ca oa cyca 0 k s s 0 } })"

lemma check_unbounded_imp_rule:
  "\<lbrakk>length fst_list = m; length snd_list = m; length capacity_list = m; length cost_list = m;
    k \<le> length xs\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs>
     check_unbounded_imp fa sa ca oa cyca k
   <\<lambda>r. inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs * \<up>(r = check_unbounded (take k xs))>"
proof(cases "k = 0")
  case True
  thus ?thesis
    by(simp add: check_unbounded_imp_def check_unbounded_def)
      (sep_auto simp: inst_assn_def)
next
  case False
  assume prems: "length fst_list = m" "length snd_list = m" "length capacity_list = m"
                "length cost_list = m" "k \<le> length xs"
  have kx: "0 < length xs" using False prems(5) by(cases xs) auto
  have hdx: "take k xs = xs ! 0 # take (k - 1) (drop (Suc 0) xs)"
    using False kx by(cases k; cases xs) auto
  have unf: "check_unbounded (take k xs)
               = (xs ! 0 < m \<and> cyc_loop (take k xs) (fst_list ! (xs ! 0)) (fst_list ! (xs ! 0)) 0)"
    using False kx by(simp add: check_unbounded_def hdx)
  have loop: "<inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs>
                cyc_loop_imp fa sa ca oa cyca 0 k s s 0
              <\<lambda>r. inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs
                   * \<up>(r = cyc_loop (take k xs) s s 0)>" for s
    using cyc_loop_imp_rule[OF prems(1-4), of 0 k xs fa sa ca oa ba cyca] prems(5) by simp
  show ?thesis
    unfolding check_unbounded_imp_def inst_assn_def
    using False kx
    by(sep_auto simp: prems(1) unf heap: loop[unfolded inst_assn_def])
qed

subsection \<open>Infeasibility\<close>

text \<open>The vertex sweep and the arc sweep, in the functional order: the demand first, then the arcs,
      which are the ones that can reject.\<close>

partial_function (heap) demand_loop_imp ::
  "'n array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n Heap" where
  "demand_loop_imp ba sca v k acc =
     (if k = 0 then return acc
      else do {
        s \<leftarrow> Array.nth sca v;
        if s \<noteq> 0 then do { b \<leftarrow> Array.nth ba v; demand_loop_imp ba sca (Suc v) (k - 1) (acc + b) }
        else demand_loop_imp ba sca (Suc v) (k - 1) acc })"

partial_function (heap) cut_loop_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool Heap" where
  "cut_loop_imp fa sa ca sca e k cap dem =
     (if k = 0 then return (cap < dem)
      else do {
        u \<leftarrow> Array.nth fa e;
        su \<leftarrow> Array.nth sca u;
        if su = 0 then cut_loop_imp fa sa ca sca (Suc e) (k - 1) cap dem
        else do {
          v \<leftarrow> Array.nth sa e;
          sv \<leftarrow> Array.nth sca v;
          if sv \<noteq> 0 then cut_loop_imp fa sa ca sca (Suc e) (k - 1) cap dem
          else do {
            c \<leftarrow> Array.nth ca e;
            if c = - 1 then return False
            else cut_loop_imp fa sa ca sca (Suc e) (k - 1) (cap + c) dem } } })"

definition check_infeasible_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> nat array \<Rightarrow> bool Heap" where
  "check_infeasible_imp fa sa ca ba sca =
     do {
       dem \<leftarrow> demand_loop_imp ba sca 0 (Suc n) 0;
       cut_loop_imp fa sa ca sca 0 m 0 dem }"

subsection \<open>Optimality\<close>

text \<open>The fused sweep: the primal test on the flow and the capacity, then --- only once that has
      passed --- the endpoints, the cost and the two potentials for the dual test, and the two
      writes that scatter the arc's flow into the accumulator.  The accumulator is allocated by the
      check and compared with the balance array at the end.\<close>

partial_function (heap) opt_loop_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> 'n array \<Rightarrow> bool Heap" where
  "opt_loop_imp fa sa ca oa ba fla pota e k neta =
     (if k = 0 then arr_eq_imp neta ba (Suc n)
      else do {
        f \<leftarrow> Array.nth fla e;
        c \<leftarrow> Array.nth ca e;
        if \<not> (0 \<le> f \<and> (c = - 1 \<or> f \<le> c)) then return False
        else do {
          u \<leftarrow> Array.nth fa e;
          v \<leftarrow> Array.nth sa e;
          ce \<leftarrow> Array.nth oa e;
          pu \<leftarrow> Array.nth pota u;
          pv \<leftarrow> Array.nth pota v;
          if (let rc = ce + pu - pv
              in if 0 < rc then f \<noteq> 0 else if rc < 0 then c = - 1 \<or> f \<noteq> c else False)
          then return False
          else do {
            nv \<leftarrow> Array.nth neta v;
            _ \<leftarrow> Array.upd v (nv - f) neta;
            nu \<leftarrow> Array.nth neta u;
            _ \<leftarrow> Array.upd u (nu + f) neta;
            opt_loop_imp fa sa ca oa ba fla pota (Suc e) (k - 1) neta } } })"

definition check_optimum_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> bool Heap" where
  "check_optimum_imp fa sa ca oa ba fla pota =
     do {
       neta \<leftarrow> Array.new (Suc n) 0;
       opt_loop_imp fa sa ca oa ba fla pota 0 m neta }"

text \<open>Exactly \<open>opt_loop_imp\<close>, with the already-converted \<open>Mn :: 'n\<close> carried as a plain by-value
      argument --- it is never read from an array, since it is not part of the certificate, and
      never converted here either, since \<open>check_optimum_eps_imp\<close> below does that once --- and the
      fused dual test relaxed to \<open>arc_ok_eps\<close>'s two one-sided bounds in place of the exact
      trichotomy.\<close>

partial_function (heap) opt_loop_eps_imp ::
  "'n \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> 'n array \<Rightarrow> bool Heap" where
  "opt_loop_eps_imp Mn fa sa ca oa ba fla pota e k neta =
     (if k = 0 then arr_eq_imp neta ba (Suc n)
      else do {
        f \<leftarrow> Array.nth fla e;
        c \<leftarrow> Array.nth ca e;
        if \<not> (0 \<le> f \<and> (c = - 1 \<or> f \<le> c)) then return False
        else do {
          u \<leftarrow> Array.nth fa e;
          v \<leftarrow> Array.nth sa e;
          ce \<leftarrow> Array.nth oa e;
          pu \<leftarrow> Array.nth pota u;
          pv \<leftarrow> Array.nth pota v;
          if (let rc = Mn * ce + pu - pv
              in \<not> ((c = - 1 \<or> f < c \<longrightarrow> - 1 \<le> rc) \<and> (0 < f \<longrightarrow> rc \<le> 1)))
          then return False
          else do {
            nv \<leftarrow> Array.nth neta v;
            _ \<leftarrow> Array.upd v (nv - f) neta;
            nu \<leftarrow> Array.nth neta u;
            _ \<leftarrow> Array.upd u (nu + f) neta;
            opt_loop_eps_imp Mn fa sa ca oa ba fla pota (Suc e) (k - 1) neta } } })"

text \<open>\<open>n < M\<close> is tested \<^emph>\<open>before\<close> the accumulator is allocated, not after --- the same "a rejection
      stops the loop, having allocated nothing" discipline the fused arc sweep itself follows,
      applied here to the one allocation the check makes.\<close>

definition check_optimum_eps_imp ::
  "'n \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> bool Heap" where
  "check_optimum_eps_imp Mn fa sa ca oa ba fla pota =
     (if of_nat n < Mn then do {
        neta \<leftarrow> Array.new (Suc n) 0;
        opt_loop_eps_imp Mn fa sa ca oa ba fla pota 0 m neta }
      else return False)"

text \<open>\<^emph>\<open>Dispatch.\<close> Exactly \<open>check_optimum_dispatch\<close>, run for its side effect: \<open>CheckerNormal\<close> always
      calls \<open>check_optimum_imp\<close>; \<open>CheckerEpsilontic\<close> reads \<open>certm\<close> as the scale itself --- a plain
      by-value argument, never read from the heap --- routing to \<open>check_optimum_eps_imp\<close> only once
      it clears the same \<open>n < \<bar>certm\<bar>\<close> gate the functional dispatcher uses, and to the exact check
      otherwise.\<close>

definition check_optimum_dispatch_imp ::
  "checker_mode \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array
   \<Rightarrow> 'n \<Rightarrow> bool Heap" where
  "check_optimum_dispatch_imp cm fa sa ca oa ba fla pota certm =
     (case cm of
        CheckerNormal     \<Rightarrow> check_optimum_imp fa sa ca oa ba fla pota
      | CheckerEpsilontic \<Rightarrow> (if of_nat n < \<bar>certm\<bar>
                              then check_optimum_eps_imp \<bar>certm\<bar> fa sa ca oa ba fla pota
                              else check_optimum_imp fa sa ca oa ba fla pota))"

end

subsection \<open>The remaining checks refine, given the format\<close>

text \<open>The two loops of the infeasibility check and the fused loop of the optimality check read the
      instance through indices they take from the certificates, so their refinement needs the format
      itself: the lengths, and the fact that an arc's endpoints are vertex names and therefore index
      the cut, the potentials and the accumulator in range.  Those are the assumptions of the
      functional proof locale, so the rules live in a locale that has them.\<close>

locale mcf_oracle_heap_checks =
  mcf_oracle_eps where capacity_list = capacity_list and h = h +
  mcf_oracle_heap_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h
begin

lemma demand_loop_imp_rule:
  "\<lbrakk>v + k \<le> Suc n; length S = Suc n\<rbrakk> \<Longrightarrow>
   <ba \<mapsto>\<^sub>a balance_list * sca \<mapsto>\<^sub>a S>
     demand_loop_imp ba sca v k acc
   <\<lambda>r. ba \<mapsto>\<^sub>a balance_list * sca \<mapsto>\<^sub>a S * \<up>(r = demand_loop S v k acc)>"
proof(induction k arbitrary: v acc)
  case 0
  thus ?case by(subst demand_loop_imp.simps) sep_auto
next
  case (Suc k)
  have vb: "v < length balance_list" and vs: "v < length S"
    using Suc.prems length_balance by simp_all
  have IH: "<ba \<mapsto>\<^sub>a balance_list * sca \<mapsto>\<^sub>a S>
              demand_loop_imp ba sca (Suc v) k a
            <\<lambda>r. ba \<mapsto>\<^sub>a balance_list * sca \<mapsto>\<^sub>a S * \<up>(r = demand_loop S (Suc v) k a)>" for a
    using Suc.IH Suc.prems by simp
  show ?case
    by(subst demand_loop_imp.simps) (sep_auto simp: vb vs heap: IH)
qed

lemma cut_loop_imp_rule:
  "\<lbrakk>e + k \<le> m; length S = Suc n\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S>
     cut_loop_imp fa sa ca sca e k cap dem
   <\<lambda>r. inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S * \<up>(r = cut_loop S e k cap dem)>"
proof(induction k arbitrary: e cap)
  case 0
  thus ?case by(subst cut_loop_imp.simps) (sep_auto simp: inst_assn_def)
next
  case (Suc k)
  have em: "e < m" using Suc.prems by simp
  have ef: "e < length fst_list" and es: "e < length snd_list" and ec: "e < length capacity_list"
    using em length_fst_list length_snd_list length_capacity by simp_all
  have uf: "fst_list ! e < length S" and us: "snd_list ! e < length S"
    using tail_is_vertex[OF em] head_is_vertex[OF em] Suc.prems(2) by auto
  have IH: "<inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S>
              cut_loop_imp fa sa ca sca (Suc e) k c dem
            <\<lambda>r. inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S * \<up>(r = cut_loop S (Suc e) k c dem)>" for c
    using Suc.IH Suc.prems by simp
  show ?case
    by(subst cut_loop_imp.simps)
      (sep_auto simp: inst_assn_def ef es ec uf us heap: IH[unfolded inst_assn_def])
qed

lemma check_infeasible_imp_rule:
  assumes True: "length S = Suc n"
  shows "<inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S>
     check_infeasible_imp fa sa ca ba sca
   <\<lambda>r. inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S * \<up>(r = check_infeasible S)>"
proof -
  have dem: "<ba \<mapsto>\<^sub>a balance_list * sca \<mapsto>\<^sub>a S>
               demand_loop_imp ba sca 0 (Suc n) 0
             <\<lambda>r. ba \<mapsto>\<^sub>a balance_list * sca \<mapsto>\<^sub>a S * \<up>(r = demand_loop S 0 (Suc n) 0)>"
    using demand_loop_imp_rule[of 0 "Suc n" S ba sca 0] True by simp
  have cut: "<inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S>
               cut_loop_imp fa sa ca sca 0 m 0 d
             <\<lambda>r. inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S * \<up>(r = cut_loop S 0 m 0 d)>" for d
    using cut_loop_imp_rule[of 0 m S] True by simp
  show ?thesis
    unfolding check_infeasible_imp_def inst_assn_def
    using True
    by(sep_auto simp: check_infeasible_def
                heap: dem cut[unfolded inst_assn_def])
qed

text \<open>The optimality loop is the only one that writes, so its postcondition frames the accumulator
      existentially: what it ends up holding does not matter, only that the loop decided the same
      boolean the functional sweep decides.  Its base case compares the accumulator with the balance
      array cell by cell, which is list equality because both have the same length.\<close>

lemma opt_loop_imp_rule:
  "\<lbrakk>length fl = m; length pot = Suc n; length net = Suc n; e + k \<le> m\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net>
     opt_loop_imp fa sa ca oa ba fla pota e k neta
   <\<lambda>r. \<exists>\<^sub>A net'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net'
                 * \<up>(r = opt_loop fl pot e k net)>"
proof(induction k arbitrary: e net)
  case 0
  have eq: "(\<forall> i < Suc n. net ! i = balance_list ! i) = (net = balance_list)"
    using "0.prems"(3) length_balance by(auto simp add: list_eq_iff_nth_eq)
  have aeq: "<neta \<mapsto>\<^sub>a net * ba \<mapsto>\<^sub>a balance_list> arr_eq_imp neta ba (Suc n)
             <\<lambda>r. neta \<mapsto>\<^sub>a net * ba \<mapsto>\<^sub>a balance_list * \<up>(r = (net = balance_list))>"
    using arr_eq_imp_rule[of "Suc n" net balance_list neta ba] "0.prems"(3) length_balance eq
    by simp
  show ?case
    by(subst opt_loop_imp.simps)
      (sep_auto simp: inst_assn_def "0.prems"(3) heap: aeq)
next
  case (Suc k)
  have em: "e < m" using Suc.prems by simp
  have bnd: "e < length fl" "e < length capacity_list" "e < length fst_list"
             "e < length snd_list" "e < length cost_list"
    using em Suc.prems(1) length_capacity length_fst_list length_snd_list length_cost_list
    by simp_all
  have vtx: "fst_list ! e < Suc n" "snd_list ! e < Suc n"
    using tail_is_vertex[OF em] head_is_vertex[OF em] by auto
  have vp: "fst_list ! e < length pot" "snd_list ! e < length pot"
    using vtx Suc.prems(2) by simp_all
  have vn: "fst_list ! e < length net" "snd_list ! e < length net"
    using vtx Suc.prems(3) by simp_all
  have lenu: "length (list_update (list_update net (snd_list ! e) x) (fst_list ! e) y) = Suc n"
    for x y
    using Suc.prems(3) by simp
  have IH: "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a nt>
              opt_loop_imp fa sa ca oa ba fla pota (Suc e) k neta
            <\<lambda>r. \<exists>\<^sub>A net'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net'
                          * \<up>(r = opt_loop fl pot (Suc e) k nt)>"
    if "length nt = Suc n" for nt
    using Suc.IH[OF Suc.prems(1,2) that] Suc.prems(4) by simp
  show ?case
    by(subst opt_loop_imp.simps)
      (sep_auto simp: inst_assn_def bnd vtx vp vn lenu Suc.prems(3) Let_def
                heap: IH[unfolded inst_assn_def])
qed

lemma check_optimum_imp_rule:
  assumes True: "length fl = m \<and> length pot = Suc n"
  shows "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot>
     check_optimum_imp fa sa ca oa ba fla pota
   <\<lambda>r. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * \<up>(r = check_optimum fl pot)>"
proof -
  have loop: "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a replicate (Suc n) 0>
                opt_loop_imp fa sa ca oa ba fla pota 0 m neta
              <\<lambda>r. \<exists>\<^sub>A net'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net'
                            * \<up>(r = opt_loop fl pot 0 m (replicate (Suc n) 0))>" for neta
    using opt_loop_imp_rule[of fl pot "replicate (Suc n) 0" 0 m] True
    by(simp del: replicate_Suc)
  show ?thesis
    unfolding check_optimum_imp_def inst_assn_def
    using True
    by(sep_auto simp: check_optimum_def heap: loop[unfolded inst_assn_def])
qed

text \<open>Exactly \<open>opt_loop_imp_rule\<close>, with \<open>M\<close> threaded through unchanged --- it is never read from the
      heap, so no bound on it is ever needed --- and the fused test's simp form matched to
      \<open>opt_loop_eps_imp\<close>'s instead of \<open>opt_loop_imp\<close>'s.\<close>

lemma opt_loop_eps_imp_rule:
  "\<lbrakk>length fl = m; length pot = Suc n; length net = Suc n; e + k \<le> m\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net>
     opt_loop_eps_imp Mn fa sa ca oa ba fla pota e k neta
   <\<lambda>r. \<exists>\<^sub>A net'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net'
                 * \<up>(r = opt_loop_eps Mn fl pot e k net)>"
proof(induction k arbitrary: e net)
  case 0
  have eq: "(\<forall> i < Suc n. net ! i = balance_list ! i) = (net = balance_list)"
    using "0.prems"(3) length_balance by(auto simp add: list_eq_iff_nth_eq)
  have aeq: "<neta \<mapsto>\<^sub>a net * ba \<mapsto>\<^sub>a balance_list> arr_eq_imp neta ba (Suc n)
             <\<lambda>r. neta \<mapsto>\<^sub>a net * ba \<mapsto>\<^sub>a balance_list * \<up>(r = (net = balance_list))>"
    using arr_eq_imp_rule[of "Suc n" net balance_list neta ba] "0.prems"(3) length_balance eq
    by simp
  show ?case
    by(subst opt_loop_eps_imp.simps)
      (sep_auto simp: inst_assn_def "0.prems"(3) heap: aeq)
next
  case (Suc k)
  have em: "e < m" using Suc.prems by simp
  have bnd: "e < length fl" "e < length capacity_list" "e < length fst_list"
             "e < length snd_list" "e < length cost_list"
    using em Suc.prems(1) length_capacity length_fst_list length_snd_list length_cost_list
    by simp_all
  have vtx: "fst_list ! e < Suc n" "snd_list ! e < Suc n"
    using tail_is_vertex[OF em] head_is_vertex[OF em] by auto
  have vp: "fst_list ! e < length pot" "snd_list ! e < length pot"
    using vtx Suc.prems(2) by simp_all
  have vn: "fst_list ! e < length net" "snd_list ! e < length net"
    using vtx Suc.prems(3) by simp_all
  have lenu: "length (list_update (list_update net (snd_list ! e) x) (fst_list ! e) y) = Suc n"
    for x y
    using Suc.prems(3) by simp
  have IH: "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a nt>
              opt_loop_eps_imp Mn fa sa ca oa ba fla pota (Suc e) k neta
            <\<lambda>r. \<exists>\<^sub>A net'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net'
                          * \<up>(r = opt_loop_eps Mn fl pot (Suc e) k nt)>"
    if "length nt = Suc n" for nt
    using Suc.IH[OF Suc.prems(1,2) that] Suc.prems(4) by simp
  show ?case
    by(subst opt_loop_eps_imp.simps)
      (sep_auto simp: inst_assn_def bnd vtx vp vn lenu Suc.prems(3) Let_def
                heap: IH[unfolded inst_assn_def])
qed

lemma check_optimum_eps_imp_rule:
  assumes True: "length fl = m \<and> length pot = Suc n"
  shows "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot>
     check_optimum_eps_imp Mn fa sa ca oa ba fla pota
   <\<lambda>r. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * \<up>(r = check_optimum_eps Mn fl pot)>"
proof -
  have loop: "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a replicate (Suc n) 0>
                opt_loop_eps_imp Mn fa sa ca oa ba fla pota 0 m neta
              <\<lambda>r. \<exists>\<^sub>A net'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net'
                            * \<up>(r = opt_loop_eps Mn fl pot 0 m (replicate (Suc n) 0))>"
    for neta
    using opt_loop_eps_imp_rule[where fl = fl and pot = pot and net = "replicate (Suc n) 0"
                                  and e = 0 and k = m and Mn = Mn] True
    by(simp del: replicate_Suc)
  show ?thesis
    unfolding check_optimum_eps_imp_def inst_assn_def
    using True
    by(sep_auto simp: check_optimum_eps_def heap: loop[unfolded inst_assn_def])
qed

text \<open>The dispatcher refines: whichever branch \<open>cm\<close> and \<open>certm\<close> pick out, the imperative check
      agrees with the functional one --- the routing test is the same \<open>of_nat n < \<bar>certm\<bar>\<close> gate
      both sides use, so \<open>cases\<close> on it lines the two dispatchers up directly.\<close>

lemma check_optimum_dispatch_imp_rule:
  assumes True: "length fl = m \<and> length pot = Suc n"
  shows "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot>
     check_optimum_dispatch_imp cm fa sa ca oa ba fla pota certm
   <\<lambda>r. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot
        * \<up>(r = check_optimum_dispatch cm fl pot certm)>"
  unfolding check_optimum_dispatch_imp_def check_optimum_dispatch_def
  apply(cases cm)
  apply simp_all
  apply (sep_auto heap: check_optimum_imp_rule[OF True])
  apply(cases "of_nat n < \<bar>certm\<bar>")
  apply simp_all
  apply (sep_auto heap: check_optimum_eps_imp_rule[OF True])
  apply (sep_auto heap: check_optimum_imp_rule[OF True])
  done

text \<open>The dispatcher rule --- \<open>check_answer_imp\<close> agrees with \<open>check_answer_dispatch\<close> under
      \<open>answer_assn\<close> --- and the capstone triple for \<open>solve_imp\<close> are proved below, together with
      \<open>decide_imp_correct\<close> in between: nesting \<open>cases a\<close> inside \<open>cases ai\<close> per certificate, rather
      than one flat \<open>cases ai\<close>, is what makes each of the three cases a one-line application of the
      rule for that certificate.\<close>

end

subsection \<open>The oracle and the verified cleanup as parameters\<close>

text \<open>What the oracle hands back.  The flow is \<^emph>\<open>not\<close> part of it: the flow array belongs to the caller
      and the solver fills it as a side effect, exactly as the C entry point fills its @{text
      flow_out} buffer and as the verified network simplex leaves its optimum in the flow array it
      was given.  So the caller still has the flow when the call returns, and the answer carries only
      the certificate --- the potentials, or the cut, or the cycle buffer together with the number of
      arcs written into it, that buffer being allowed to be longer than the cycle it holds.\<close>

datatype 'n answer_imp =
    OptimumI "'n array" 'n
  | InfeasibleI "nat array"
  | UnboundedI "nat array" nat

text \<open>The verdict of the cleanup is a flag, and the flow it computed is left in the flow array --- the
      convention the verified network simplex already uses (@{text solve_imp} returns a status and
      leaves the optimum in the first @{term m} cells).\<close>

datatype verdict_flag = VOptimumF | VInfeasibleF | VUnboundedF

context mcf_oracle_heap_spec
begin

text \<open>Reading a flag and a flow array back as a verdict.\<close>

definition verdict_of_flag :: "verdict_flag \<Rightarrow> 'n list \<Rightarrow> 'n solver_verdict" where
  "verdict_of_flag r fl = (case r of VOptimumF \<Rightarrow> VOptimum fl
                                   | VInfeasibleF \<Rightarrow> VInfeasible
                                   | VUnboundedF \<Rightarrow> VUnbounded)"

text \<open>The heap counterpart of an answer: the certificates are the arrays the oracle filled, and the
      abstract answer is what they contain.  The cycle buffer is allowed to be longer than the cycle
      it holds, exactly as the solver leaves it.\<close>

text \<open>The sizes are part of what the oracle returns, not something the checkers rediscover: the
      buffers are allocated at the boundary from @{term m} and @{term n}, so a certificate of the
      wrong length is a marshalling error rather than a bad certificate, and the place to record
      that is here --- in the assertion the assumed triple of the oracle establishes.  The checkers
      below then carry the lengths as premises and do no length arithmetic at all.

      The cycle buffer is the exception, and it needs no separate condition: it is stated as the
      cycle followed by an unconstrained remainder, so @{term k} arcs are in range by construction
      however long the buffer is.\<close>

definition answer_wf :: "'n oracle_answer \<Rightarrow> bool" where
  "answer_wf a =
     (length (oa_flow a) = m \<and>
      (case a of OracleOptimum _ pot _ \<Rightarrow> length pot = Suc n
               | OracleInfeasible _ S  \<Rightarrow> length S = Suc n
               | OracleUnbounded _ _   \<Rightarrow> True))"

definition answer_assn :: "'n array \<Rightarrow> 'n oracle_answer \<Rightarrow> 'n answer_imp \<Rightarrow> assn" where
  "answer_assn fla a ai =
     fla \<mapsto>\<^sub>a oa_flow a *
     (case (a, ai) of
        (OracleOptimum _ pot certm, OptimumI pota certm') \<Rightarrow> pota \<mapsto>\<^sub>a pot * \<up>(certm' = certm)
      | (OracleInfeasible _ S, InfeasibleI sa) \<Rightarrow> sa \<mapsto>\<^sub>a S
      | (OracleUnbounded _ cyc, UnboundedI cyca k) \<Rightarrow>
          (\<exists>\<^sub>A r. cyca \<mapsto>\<^sub>a (cyc @ r)) * \<up>(k = length cyc)
      | _ \<Rightarrow> false)"

end

text \<open>The imperative pipeline.  Both external procedures are parameters with an assumed triple, and
      the two assumptions say very different things.

      \<^item> The \<^emph>\<open>oracle\<close>'s triple says only that it computes the answer the functional oracle computes.
        That is a refinement statement and nothing more: @{term oracle_solve} is an arbitrary
        function, so this assumes nothing whatever about the answer's truth.  It is what lets an
        external, untrusted program stand where the functional specification has a value.
      \<^item> The \<^emph>\<open>cleanup\<close>'s triple says its flag and the flow it leaves behind form a true verdict about
        the instance.  This is the interface a verified implementation is plugged into: the verified
        network simplex takes the same five arrays plus a flow array, returns a three-valued flag and
        leaves the optimum in the flow array, which is precisely the shape below.

      Both triples leave the instance arrays untouched and framed, so the caller can hand the same
      arrays to the checkers afterwards.\<close>

text \<open>The code layer: the two procedures are fixed, nothing is assumed, and the program that joins
      them is written here.  It is the imperative reading of @{const mcf_oracle_cleanup_spec.decide}
      and @{const mcf_oracle_cleanup_spec.solve}: call the oracle once, check the certificate it
      carries, and take its verdict or hand the instance and its flow to the cleanup.  The oracle is
      called once and the answer is a value from then on, so no branch can run it again.\<close>

locale mcf_oracle_heap_pipeline_spec =
  mcf_oracle_heap_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" +
  fixes oracle_imp ::
      "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n answer_imp Heap"
    and cleanup_imp ::
      "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> verdict_flag Heap"
begin

text \<open>The verdict an answer claims.  There is no projection for the flow: it is in the caller's
      array throughout, written first by the oracle and then, if the certificate is rejected, by the
      cleanup --- which is why the flag alone is enough to return.\<close>

fun flag_of :: "'n answer_imp \<Rightarrow> verdict_flag" where
  "flag_of (OptimumI _ _)  = VOptimumF"
| "flag_of (InfeasibleI _) = VInfeasibleF"
| "flag_of (UnboundedI _ _) = VUnboundedF"

text \<open>The dispatcher: each verdict is sent to the check for its own certificate, and nothing else
      happens here.  The sizes are not tested --- they come with the answer, by \<open>answer_assn\<close> --- and
      the flow array is the caller's, so its length is a precondition of the pipeline.\<close>

text \<open>\<open>M\<close> is kept in the signature, unused, purely so \<open>decide_imp\<close>/\<open>solve_imp\<close> and their call sites
      do not have to change shape: it plays no part in checking \<open>ai\<close> --- that is \<open>certm\<close>'s job now
      --- only in the scale the \<^emph>\<open>outer\<close> Hoare-triple postcondition states, in \<open>decide_imp_correct\<close>/
      \<open>solve_imp_correct\<close> below.\<close>

definition check_answer_imp ::
  "checker_mode \<Rightarrow> nat \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n answer_imp \<Rightarrow> bool Heap"
  where
  "check_answer_imp cm M fa sa ca oa ba fla ai =
     (case ai of OptimumI pota certm \<Rightarrow> check_optimum_dispatch_imp cm fa sa ca oa ba fla pota certm
               | InfeasibleI sca     \<Rightarrow> check_infeasible_imp fa sa ca ba sca
               | UnboundedI cyca k   \<Rightarrow> check_unbounded_imp fa sa ca oa cyca k)"

text \<open>Rectifying the flow.  The cleanup is only correct on a flow that already respects the
      capacities --- @{text flow_nonneg} and @{text flow_le_cap} of \<open>initial_basis_correct\<close>, two
      locales above the triple it is stated in --- and the oracle is untrusted, so the flow it left
      behind has to be made feasible before it can be used as a warm start.  A negative cell is
      raised to @{term \<open>0::'n\<close>} and a cell over a finite capacity is lowered to it; an uncapacitated
      arc has nothing to violate.  One pass, in place, keeping whatever the oracle got right --- the
      point of a warm start --- and it runs only when the certificate was rejected.\<close>

partial_function (heap) rectify_imp ::
  "'n array \<Rightarrow> 'n array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "rectify_imp ca fla e k =
     (if k = 0 then return ()
      else do {
        f \<leftarrow> Array.nth fla e;
        c \<leftarrow> Array.nth ca e;
        _ \<leftarrow> Array.upd e (if f < 0 then 0 else if c \<noteq> - 1 \<and> c < f then c else f) fla;
        rectify_imp ca fla (Suc e) (k - 1) })"

definition decide_imp ::
  "checker_mode \<Rightarrow> nat \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n answer_imp
   \<Rightarrow> verdict_flag Heap" where
  "decide_imp cm M fa sa ca oa ba fla ai =
     do {
       ok \<leftarrow> check_answer_imp cm M fa sa ca oa ba fla ai;
       if ok then return (flag_of ai)
       else do {
         _ \<leftarrow> rectify_imp ca fla 0 m;
         cleanup_imp fa sa ca oa ba fla } }"

definition solve_imp ::
  "checker_mode \<Rightarrow> nat \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> verdict_flag Heap" where
  "solve_imp cm M fa sa ca oa ba fla =
     do {
       ai \<leftarrow> oracle_imp fa sa ca oa ba fla;
       decide_imp cm M fa sa ca oa ba fla ai }"

end

text \<open>The proof layer adds the two triples and nothing else.\<close>

locale mcf_oracle_heap =
  mcf_oracle_heap_checks where capacity_list = capacity_list and h = h +
  mcf_oracle_heap_pipeline_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h +
  assumes oracle_imp_rule:
      "length fl = m \<Longrightarrow>
       <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
         oracle_imp fa sa ca oa ba fla
       <\<lambda>ai. inst_assn fa sa ca oa ba * answer_assn fla orc_answer ai>"
    and cleanup_imp_rule:
      "\<lbrakk>length fl = m;
        \<And>e. e < m \<Longrightarrow> 0 \<le> fl ! e;
        \<And>e. \<lbrakk>e < m; capacity_list ! e \<noteq> - 1\<rbrakk> \<Longrightarrow> fl ! e \<le> capacity_list ! e\<rbrakk> \<Longrightarrow>
       <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
         cleanup_imp fa sa ca oa ba fla
       <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
                    * \<up>(length fl' = m \<and> verdict_ok (verdict_of_flag r fl'))>"
begin

text \<open>The dispatcher refines: whichever certificate the answer carries, the imperative check agrees
      with the functional one.  Each case is one application of the rule for that certificate, the
      length premise coming from \<open>answer_assn\<close> rather than from a test.\<close>

lemma check_answer_imp_rule:
  assumes wf: "answer_wf a" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
     check_answer_imp cm M fa sa ca oa ba fla ai
   <\<lambda>r. inst_assn fa sa ca oa ba * answer_assn fla a ai * \<up>(r = check_answer_dispatch cm a)>"
proof(cases a)
  case (OracleOptimum fl pot certm)
  have len: "length fl = m \<and> length pot = Suc n"
    using wf by(simp add: answer_wf_def OracleOptimum)
  show ?thesis
  proof(cases ai)
    case (OptimumI pota certm')
    show ?thesis
      unfolding OracleOptimum OptimumI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: check_optimum_dispatch_imp_rule[OF len])
  qed (simp_all add: OracleOptimum answer_assn_def)
next
  case (OracleInfeasible fl S)
  have len: "length S = Suc n"
    using wf by(simp add: answer_wf_def OracleInfeasible)
  show ?thesis
  proof(cases ai)
    case (InfeasibleI sca)
    show ?thesis
      unfolding OracleInfeasible InfeasibleI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: check_infeasible_imp_rule[OF len])
  qed (simp_all add: OracleInfeasible answer_assn_def)
next
  case (OracleUnbounded fl cyc)
  have rule: "<inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a (cyc @ rst)>
                check_unbounded_imp fa sa ca oa cyca (length cyc)
              <\<lambda>r. inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a (cyc @ rst)
                   * \<up>(r = check_unbounded cyc)>" for rst cyca
    using check_unbounded_imp_rule[OF length_fst_list length_snd_list length_capacity
                                      length_cost_list, of "length cyc" "cyc @ rst"]
    by simp
  show ?thesis
  proof(cases ai)
    case (UnboundedI cyca k)
    show ?thesis
      unfolding OracleUnbounded UnboundedI check_answer_imp_def answer_assn_def
      by(sep_auto simp: check_answer_dispatch_def heap: rule)
  qed (simp_all add: OracleUnbounded answer_assn_def)
qed

subsection \<open>The rectification\<close>

text \<open>The pass exists only to establish a precondition, so unlike the checkers it has no counterpart
      in the specification.  We give it one here, purely for the proof: then its refinement lemma
      has the same shape as all the others, and what it \<^emph>\<open>achieves\<close> becomes a fact about lists,
      provable without heaps.\<close>

definition clamp1 :: "'n \<Rightarrow> 'n \<Rightarrow> 'n" where
  "clamp1 c f = (if f < 0 then 0 else if c \<noteq> - 1 \<and> c < f then c else f)"

fun rectify :: "'n list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list" where
  "rectify fl e 0 = fl"
| "rectify fl e (Suc k) = rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k"

definition cap_ok :: "'n list \<Rightarrow> nat \<Rightarrow> bool" where
  "cap_ok fl i = (0 \<le> fl ! i \<and> (capacity_list ! i \<noteq> - 1 \<longrightarrow> fl ! i \<le> capacity_list ! i))"

text \<open>The refinement: the pass computes exactly that function.\<close>

lemma rectify_imp_rule:
  "\<lbrakk>e + k \<le> length fl; length capacity_list = m; e + k \<le> m\<rbrakk> \<Longrightarrow>
   <ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a fl>
     rectify_imp ca fla e k
   <\<lambda>_. ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a rectify fl e k>"
proof(induction k arbitrary: e fl)
  case 0
  thus ?case by(subst rectify_imp.simps) sep_auto
next
  case (Suc k)
  have ef: "e < length fl" and ec: "e < length capacity_list" using Suc.prems by simp_all
  have IH: "<ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a (fl[e := clamp1 (capacity_list ! e) (fl ! e)])>
              rectify_imp ca fla (Suc e) k
            <\<lambda>_. ca \<mapsto>\<^sub>a capacity_list
                 * fla \<mapsto>\<^sub>a rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k>"
    using Suc.IH[of "Suc e" "fl[e := clamp1 (capacity_list ! e) (fl ! e)]"] Suc.prems by simp
  show ?case
    by(subst rectify_imp.simps) (sep_auto simp: ef ec clamp1_def[symmetric] heap: IH)
qed

text \<open>What it achieves, as three facts about lists: the length is preserved, the cells outside the
      range are untouched, and the cells inside it are capacity-feasible.  The last is where
      @{thm [source] capacity_format} enters --- a capacity is non-negative unless it is the
      uncapacitated sentinel, and the clamped value is in range either way.\<close>

lemma rectify_length: "length (rectify fl e k) = length fl"
  by(induction k arbitrary: e fl) simp_all

lemma rectify_outside: "i < e \<or> e + k \<le> i \<Longrightarrow> rectify fl e k ! i = fl ! i"
  by(induction k arbitrary: e fl) (auto simp add: nth_list_update)

lemma cap_ok_clamp1:
  assumes "e < m" "e < length fl"
  shows "cap_ok (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) e"
  using assms capacity_format[OF assms(1)] by(auto simp add: cap_ok_def clamp1_def)

lemma rectify_inside:
  "\<lbrakk>e + k \<le> m; e + k \<le> length fl; e \<le> i; i < e + k\<rbrakk> \<Longrightarrow> cap_ok (rectify fl e k) i"
proof(induction k arbitrary: e fl)
  case 0
  thus ?case by simp
next
  case (Suc k)
  show ?case
  proof(cases "i = e")
    case True
    have "rectify (fl[e := clamp1 (capacity_list ! e) (fl ! e)]) (Suc e) k ! e
            = fl[e := clamp1 (capacity_list ! e) (fl ! e)] ! e"
      by(rule rectify_outside) simp
    thus ?thesis
      using cap_ok_clamp1[of e fl] Suc.prems True by(simp add: cap_ok_def)
  next
    case False
    hence "Suc e \<le> i" using Suc.prems by simp
    thus ?thesis
      using Suc.IH[of "Suc e" "fl[e := clamp1 (capacity_list ! e) (fl ! e)]"] Suc.prems by simp
  qed
qed

text \<open>Run at the full range, it delivers precisely the three premises of
      @{thm [source] cleanup_imp_rule}.\<close>

lemma rectify_facts:
  assumes fl: "length fl = m"
  shows "length (rectify fl 0 m) = m"
    and "e < m \<Longrightarrow> 0 \<le> rectify fl 0 m ! e"
    and "\<lbrakk>e < m; capacity_list ! e \<noteq> - 1\<rbrakk> \<Longrightarrow> rectify fl 0 m ! e \<le> capacity_list ! e"
  using rectify_length[of fl 0 m] fl rectify_inside[of 0 m fl e]
  by(auto simp add: cap_ok_def)

subsection \<open>The pipeline is correct\<close>

text \<open>First the bridge between the two verdict representations: on an answer whose certificate
      arrays are the ones the assertion describes --- which is the only case in which the assertion
      is not @{term false} --- reading the flag back together with the flow gives the verdict the
      functional layer assigns to the answer.\<close>

lemma verdict_of_flag_of:
  "answer_assn fla a ai = false \<or> verdict_of_flag (flag_of ai) (oa_flow a) = verdict_of a"
  by(cases a; cases ai)
    (auto simp add: answer_assn_def verdict_of_flag_def verdict_of_def)

text \<open>Deciding is correct.  If the certificate holds, the verdict is the oracle's own and
      @{thm [source] verdict_of_sound} --- the functional soundness theorem --- makes it true; if it
      does not, the flow is clamped into the capacities, which is exactly what
      @{thm [source] cleanup_imp_rule} demands, and the verdict is the cleanup's.  Either way the
      flow left in the array is the one the verdict speaks about.\<close>

text \<open>The cleanup's guarantee weakens the same way \<open>verdict_ok_imp_dispatch\<close> weakens it in the
      functional layer: it is unconditionally exact, hence meets the checker-mode-indexed bar too,
      for any \<open>cm\<close> and any \<open>M\<close>.\<close>

lemma decide_imp_correct:
  assumes wf: "answer_wf a" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
           decide_imp cm M fa sa ca oa ba fla ai
         <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
              * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
proof(cases "answer_assn fla a ai = false")
  case True
  thus ?thesis by(simp add: decide_imp_def)
next
  case False
  hence vf: "verdict_of_flag (flag_of ai) (oa_flow a) = verdict_of a"
    using verdict_of_flag_of by blast
  have flm: "length (oa_flow a) = m" using wf by(simp add: answer_wf_def)
  have rect: "<ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a oa_flow a>
                rectify_imp ca fla 0 m
              <\<lambda>_. ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a rectify (oa_flow a) 0 m>"
    by(rule rectify_imp_rule) (simp_all add: flm length_capacity)
  have clean: "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a rectify (oa_flow a) 0 m>
                 cleanup_imp fa sa ca oa ba fla
               <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
                    * \<up>(length fl' = m \<and> verdict_ok (verdict_of_flag r fl'))>"
    by(rule cleanup_imp_rule) (auto simp add: rectify_facts[OF flm])
  have clean_dispatch: "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a rectify (oa_flow a) 0 m>
                 cleanup_imp fa sa ca oa ba fla
               <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
                    * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
    using Mpos by(sep_auto heap: clean simp: verdict_ok_imp_dispatch)
  show ?thesis
    unfolding decide_imp_def
    apply(sep_auto heap: check_answer_imp_rule[OF wf Mpos])
     apply(sep_auto simp: answer_assn_def vf flm verdict_of_dispatch_sound Mpos)
    apply(sep_auto simp: answer_assn_def inst_assn_def
                   heap: rect[unfolded inst_assn_def] clean_dispatch[unfolded inst_assn_def])
    done
qed

text \<open>And the pipeline: call the untrusted oracle, check what it says, and if the certificate does
      not hold fall back on the verified cleanup.  Whatever the oracle returns, the flag that comes
      out and the flow left in the array are a true verdict about this instance, at the bar \<open>cm\<close>
      sets.\<close>

theorem solve_imp_correct:
  assumes fl: "length fl = m" and wf: "answer_wf orc_answer" and Mpos: "0 < M"
  shows "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
           solve_imp cm M fa sa ca oa ba fla
         <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
              * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
  unfolding solve_imp_def
  by(sep_auto heap: oracle_imp_rule[OF fl] decide_imp_correct[OF wf Mpos])

end

end
