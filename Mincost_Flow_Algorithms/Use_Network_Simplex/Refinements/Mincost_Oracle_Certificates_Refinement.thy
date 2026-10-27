theory Mincost_Oracle_Certificates_Refinement
  imports Use_Network_Simplex.Mincost_Oracle_Certificates 
          Separation_Logic_Imperative_HOL_Partial.Array_Blit
begin

named_theorems certificate_heap_rules "Heap rules for the min-cost-flow certificate pipeline"

section \<open>Imperative refinement of the certificate checkers and the oracle call\<close>

text \<open>The instance and the certificates become @{class heap} arrays. Each program is the functional
      check with list reads replaced by array reads: one counted loop per check, the same guards in
      the same order. Each refinement lemma says the program returns what the functional check
      returns and leaves the instance unchanged. The oracle and the verified cleanup are parameters
      with an assumed Hoare triple.\<close>

subsection \<open>The instance and the certificates as arrays\<close>

text \<open>The numeric type also needs @{class heap}, and a sort cannot be strengthened inside a context,
      so the imperative layer is a locale of its own. The five instance arrays are passed one by one,
      as in the network simplex refinement.\<close>

locale mcf_oracle_heap_spec =
  mcf_oracle_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list"
begin

definition inst_assn ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> assn" where
  "inst_assn fa sa ca oa ba =
     fa \<mapsto>\<^sub>a fst_list * sa \<mapsto>\<^sub>a snd_list * ca \<mapsto>\<^sub>a capacity_list *
     oa \<mapsto>\<^sub>a cost_list * ba \<mapsto>\<^sub>a balance_list"

text \<open>Comparing the first @{term k} cells of two arrays; it stops at the first difference.\<close>

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
  by (induction k; subst arr_eq_imp.simps) (sep_auto simp: All_less_Suc)+

subsection \<open>Unboundedness\<close>

text \<open>The cycle is a buffer and the number of arcs written into it. The guards are in the functional
      order, so an arc that fails the range test never indexes anything.\<close>

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

lemma cyc_loop_imp_rule[certificate_heap_rules]:
  "\<lbrakk>length fst_list = m; length snd_list = m; length capacity_list = m; length cost_list = m;
    i + k \<le> length xs\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs>
     cyc_loop_imp fa sa ca oa cyca i k prev s tot
   <\<lambda>r. inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs
        * \<up>(r = cyc_loop (take k (drop i xs)) prev s tot)>"
  unfolding inst_assn_def
  by (induction k arbitrary: i prev tot; subst cyc_loop_imp.simps)
    (sep_auto simp: uncapacitated_def Cons_nth_drop_Suc[symmetric])+

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

lemma check_unbounded_imp_rule[certificate_heap_rules]:
  "\<lbrakk>length fst_list = m; length snd_list = m; length capacity_list = m; length cost_list = m;
    k \<le> length xs\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs>
     check_unbounded_imp fa sa ca oa cyca k
   <\<lambda>r. inst_assn fa sa ca oa ba * cyca \<mapsto>\<^sub>a xs * \<up>(r = check_unbounded (take k xs))>"
  unfolding check_unbounded_imp_def check_unbounded_def inst_assn_def
  by (cases k; cases xs) (sep_auto heap: certificate_heap_rules[unfolded inst_assn_def])+

subsection \<open>Infeasibility\<close>

text \<open>The vertex sweep and the arc sweep, in the functional order.\<close>

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

text \<open>The fused sweep: the primal test, then the dual test, then the two writes that scatter the
      arc's flow into the accumulator. The accumulator is allocated by the check and compared with
      the balance array at the end.\<close>

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

text \<open>The same sweep with the scale \<open>Mn\<close> as a by-value argument and the dual test of
      \<open>arc_ok_eps\<close>.\<close>

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

text \<open>\<open>n < M\<close> is tested before the accumulator is allocated.\<close>

definition check_optimum_eps_imp ::
  "'n \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> bool Heap" where
  "check_optimum_eps_imp Mn fa sa ca oa ba fla pota =
     (if of_nat n < Mn then do {
        neta \<leftarrow> Array.new (Suc n) 0;
        opt_loop_eps_imp Mn fa sa ca oa ba fla pota 0 m neta }
      else return False)"

text \<open>The imperative \<open>check_optimum_dispatch\<close>.\<close>

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

text \<open>These loops index the instance with values read from the certificates, so their refinement
      needs the format assumptions of the functional proof locale.\<close>

locale mcf_oracle_heap_checks =
  mcf_oracle_eps where capacity_list = capacity_list and h = h +
  mcf_oracle_heap_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h
begin

lemma arc_in_range:
  "e < m \<Longrightarrow> e < length fst_list \<and> e < length snd_list \<and> e < length capacity_list
             \<and> e < length cost_list \<and> fst_list ! e < Suc n \<and> snd_list ! e < Suc n"
  using tail_is_vertex[of e] head_is_vertex[of e]
  by (auto simp: length_fst_list length_snd_list length_capacity length_cost_list)

lemma demand_loop_imp_rule[certificate_heap_rules]:
  "\<lbrakk>v + k \<le> Suc n; length S = Suc n\<rbrakk> \<Longrightarrow>
   <ba \<mapsto>\<^sub>a balance_list * sca \<mapsto>\<^sub>a S>
     demand_loop_imp ba sca v k acc
   <\<lambda>r. ba \<mapsto>\<^sub>a balance_list * sca \<mapsto>\<^sub>a S * \<up>(r = demand_loop S v k acc)>"
  by (induction k arbitrary: v acc; subst demand_loop_imp.simps)
    (sep_auto simp: length_balance)+

lemma cut_loop_imp_rule[certificate_heap_rules]:
  "\<lbrakk>e + k \<le> m; length S = Suc n\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S>
     cut_loop_imp fa sa ca sca e k cap dem
   <\<lambda>r. inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S * \<up>(r = cut_loop S e k cap dem)>"
  unfolding inst_assn_def
  by (induction k arbitrary: e cap; subst cut_loop_imp.simps)
    (sep_auto simp: arc_in_range)+

lemma check_infeasible_imp_rule[certificate_heap_rules]:
  "length S = Suc n \<Longrightarrow>
   <inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S>
     check_infeasible_imp fa sa ca ba sca
   <\<lambda>r. inst_assn fa sa ca oa ba * sca \<mapsto>\<^sub>a S * \<up>(r = check_infeasible S)>"
  unfolding check_infeasible_imp_def
  by (sep_auto simp: check_infeasible_def inst_assn_def
               heap: certificate_heap_rules[unfolded inst_assn_def])

text \<open>The optimality loops write the accumulator, so their postconditions frame it existentially.\<close>

lemma arr_eq_balance_rule[certificate_heap_rules]:
  "length net = Suc n \<Longrightarrow>
   <neta \<mapsto>\<^sub>a net * ba \<mapsto>\<^sub>a balance_list> arr_eq_imp neta ba (Suc n)
   <\<lambda>r. neta \<mapsto>\<^sub>a net * ba \<mapsto>\<^sub>a balance_list * \<up>(r = (net = balance_list))>"
  using arr_eq_imp_rule[of "Suc n" net balance_list neta ba]
  by (simp add: length_balance list_eq_iff_nth_eq)

lemma opt_loop_imp_rule[certificate_heap_rules]:
  "\<lbrakk>length fl = m; length pot = Suc n; length net = Suc n; e + k \<le> m\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net>
     opt_loop_imp fa sa ca oa ba fla pota e k neta
   <\<lambda>r. \<exists>\<^sub>A net'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot
                 * neta \<mapsto>\<^sub>a net' * \<up>(r = opt_loop fl pot e k net)>"
  unfolding inst_assn_def
  by (induction k arbitrary: e net; subst opt_loop_imp.simps)
    (sep_auto simp: arc_in_range Let_def heap: certificate_heap_rules)+

lemma check_optimum_imp_rule[certificate_heap_rules]:
  "length fl = m \<and> length pot = Suc n \<Longrightarrow>
   <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot>
     check_optimum_imp fa sa ca oa ba fla pota
   <\<lambda>r. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot
        * \<up>(r = check_optimum fl pot)>"
  unfolding check_optimum_imp_def
  by (sep_auto simp: check_optimum_def heap: certificate_heap_rules)

lemma opt_loop_eps_imp_rule[certificate_heap_rules]:
  "\<lbrakk>length fl = m; length pot = Suc n; length net = Suc n; e + k \<le> m\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot * neta \<mapsto>\<^sub>a net>
     opt_loop_eps_imp Mn fa sa ca oa ba fla pota e k neta
   <\<lambda>r. \<exists>\<^sub>A net'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot
                 * neta \<mapsto>\<^sub>a net' * \<up>(r = opt_loop_eps Mn fl pot e k net)>"
  unfolding inst_assn_def
  by (induction k arbitrary: e net; subst opt_loop_eps_imp.simps)
    (sep_auto simp: arc_in_range Let_def heap: certificate_heap_rules)+

lemma check_optimum_eps_imp_rule[certificate_heap_rules]:
  "length fl = m \<and> length pot = Suc n \<Longrightarrow>
   <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot>
     check_optimum_eps_imp Mn fa sa ca oa ba fla pota
   <\<lambda>r. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot
        * \<up>(r = check_optimum_eps Mn fl pot)>"
  unfolding check_optimum_eps_imp_def
  by (sep_auto simp: check_optimum_eps_def heap: certificate_heap_rules)

lemma check_optimum_dispatch_imp_rule[certificate_heap_rules]:
  assumes "length fl = m \<and> length pot = Suc n"
  shows "<inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot>
           check_optimum_dispatch_imp cm fa sa ca oa ba fla pota certm
         <\<lambda>r. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl * pota \<mapsto>\<^sub>a pot
              * \<up>(r = check_optimum_dispatch cm fl pot certm)>"
  unfolding check_optimum_dispatch_imp_def check_optimum_dispatch_def
  by (cases cm; cases "of_nat n < \<bar>certm\<bar>")
    (sep_auto simp: assms heap: certificate_heap_rules)+

end

subsection \<open>The oracle and the verified cleanup as parameters\<close>

text \<open>The oracle's answer carries only the certificate: the flow array belongs to the caller and the
      oracle fills it as a side effect. A cycle buffer may be longer than the cycle it holds.\<close>

datatype 'n answer_imp =
    OptimumI "'n array" 'n
  | InfeasibleI "nat array"
  | UnboundedI "nat array" nat

text \<open>The cleanup returns a flag and leaves its flow in the flow array, as the verified network
      simplex does.\<close>

datatype verdict_flag = VOptimumF | VInfeasibleF | VUnboundedF

context mcf_oracle_heap_spec
begin

definition verdict_of_flag :: "verdict_flag \<Rightarrow> 'n list \<Rightarrow> 'n solver_verdict" where
  "verdict_of_flag r fl = (case r of VOptimumF \<Rightarrow> VOptimum fl
                                   | VInfeasibleF \<Rightarrow> VInfeasible
                                   | VUnboundedF \<Rightarrow> VUnbounded)"

text \<open>The certificate lengths are part of what the oracle returns, so they are recorded here and
      not tested by the checkers. The cycle buffer is the cycle followed by an arbitrary rest.\<close>

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

text \<open>The code layer: the imperative reading of @{const mcf_oracle_cleanup_spec.decide} and
      @{const mcf_oracle_cleanup_spec.solve}. The oracle is called once; its certificate is checked,
      and if it is rejected the flow is clamped into the capacities and handed to the cleanup.
      \<open>M\<close> is unused by the checks; it only fixes the bar of the postconditions below.\<close>

locale mcf_oracle_heap_pipeline_spec =
  mcf_oracle_heap_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" +
  fixes oracle_imp ::
      "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n answer_imp Heap"
    and cleanup_imp ::
      "nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> verdict_flag Heap"
begin

fun flag_of :: "'n answer_imp \<Rightarrow> verdict_flag" where
  "flag_of (OptimumI _ _)  = VOptimumF"
| "flag_of (InfeasibleI _) = VInfeasibleF"
| "flag_of (UnboundedI _ _) = VUnboundedF"

definition check_answer_imp ::
  "checker_mode \<Rightarrow> nat \<Rightarrow>
   nat array \<Rightarrow> nat array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n array \<Rightarrow> 'n answer_imp \<Rightarrow> bool Heap"
  where
  "check_answer_imp cm M fa sa ca oa ba fla ai =
     (case ai of OptimumI pota certm \<Rightarrow> check_optimum_dispatch_imp cm fa sa ca oa ba fla pota certm
               | InfeasibleI sca     \<Rightarrow> check_infeasible_imp fa sa ca ba sca
               | UnboundedI cyca k   \<Rightarrow> check_unbounded_imp fa sa ca oa cyca k)"

text \<open>Rectifying the untrusted flow in place: a negative cell becomes \<open>0\<close>, a cell over a finite
      capacity becomes the capacity.\<close>

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

text \<open>The parts of the pipeline that need the format but neither assumed triple.\<close>

locale mcf_oracle_heap_pipeline =
  mcf_oracle_heap_checks where capacity_list = capacity_list and h = h +
  mcf_oracle_heap_pipeline_spec where capacity_list = capacity_list
  for capacity_list :: "('n :: {heap, linordered_idom}) list" and h
begin

lemma check_answer_imp_rule[certificate_heap_rules]:
  assumes "answer_wf a" "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
           check_answer_imp cm M fa sa ca oa ba fla ai
         <\<lambda>r. inst_assn fa sa ca oa ba * answer_assn fla a ai * \<up>(r = check_answer_dispatch cm a)>"
proof(cases a)
  case (OracleOptimum fl pot certm)
  with assms(1) have "length fl = m \<and> length pot = Suc n"
    by (simp add: answer_wf_def)
  show ?thesis
    unfolding OracleOptimum check_answer_imp_def answer_assn_def
    by (cases ai)
      (sep_auto simp: check_answer_dispatch_def
                heap: check_optimum_dispatch_imp_rule[OF \<open>length fl = m \<and> length pot = Suc n\<close>])+
next
  case (OracleInfeasible fl S)
  with assms(1) have "length S = Suc n"
    by (simp add: answer_wf_def)
  show ?thesis
    unfolding OracleInfeasible check_answer_imp_def answer_assn_def
    by (cases ai)
      (sep_auto simp: check_answer_dispatch_def
                heap: check_infeasible_imp_rule[OF \<open>length S = Suc n\<close>])+
next
  case (OracleUnbounded fl cyc)
  show ?thesis
    unfolding OracleUnbounded check_answer_imp_def answer_assn_def
    by (cases ai)
      (sep_auto simp: check_answer_dispatch_def
                heap: check_unbounded_imp_rule[OF length_fst_list length_snd_list length_capacity
                                                  length_cost_list])+
qed

lemma verdict_of_flag_of:
  "answer_assn fla a ai = false \<or> verdict_of_flag (flag_of ai) (oa_flow a) = verdict_of a"
  by (cases a; cases ai) (auto simp: answer_assn_def verdict_of_flag_def verdict_of_def)

subsection \<open>The rectification\<close>

text \<open>A list counterpart of \<open>rectify_imp\<close>, for the proof only.\<close>

definition clamp1 :: "'n \<Rightarrow> 'n \<Rightarrow> 'n" where
  "clamp1 c f = (if f < 0 then 0 else if c \<noteq> - 1 \<and> c < f then c else f)"

fun rectify :: "'n list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n list" where
  "rectify fl e 0 = fl"
| "rectify fl e (Suc k) = rectify (list_update fl e (clamp1 (capacity_list ! e) (fl ! e))) (Suc e) k"

lemma rectify_imp_rule[certificate_heap_rules]:
  "\<lbrakk>e + k \<le> length fl; e + k \<le> m\<rbrakk> \<Longrightarrow>
   <ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a fl>
     rectify_imp ca fla e k
   <\<lambda>_. ca \<mapsto>\<^sub>a capacity_list * fla \<mapsto>\<^sub>a rectify fl e k>"
  by (induction k arbitrary: e fl; subst rectify_imp.simps)
    (sep_auto simp: length_capacity clamp1_def[symmetric])+

lemma rectify_length[simp]: "length (rectify fl e k) = length fl"
  by (induction k arbitrary: e fl) simp_all

lemma rectify_outside: "i < e \<or> e + k \<le> i \<Longrightarrow> rectify fl e k ! i = fl ! i"
  by (induction k arbitrary: e fl) (auto simp: nth_list_update)

lemma rectify_inside:
  "\<lbrakk>e + k \<le> m; e + k \<le> length fl; e \<le> i; i < e + k\<rbrakk> \<Longrightarrow>
   0 \<le> rectify fl e k ! i \<and> (capacity_list ! i \<noteq> - 1 \<longrightarrow> rectify fl e k ! i \<le> capacity_list ! i)"
proof(induction k arbitrary: e fl)
  case (Suc k)
  then show ?case
    using capacity_format[of e] rectify_outside[of e "Suc e" k]
    by (cases "i = e") (auto simp: clamp1_def)
qed simp

text \<open>Over the full range, the rectified flow meets the premises of \<open>cleanup_imp_rule\<close>.\<close>

lemma rectify_facts:
  "length fl = m \<Longrightarrow> length (rectify fl 0 m) = m"
  "\<lbrakk>length fl = m; e < m\<rbrakk> \<Longrightarrow> 0 \<le> rectify fl 0 m ! e"
  "\<lbrakk>length fl = m; e < m; capacity_list ! e \<noteq> - 1\<rbrakk> \<Longrightarrow> rectify fl 0 m ! e \<le> capacity_list ! e"
  using rectify_inside[of 0 m fl e]
  by auto

end

text \<open>The proof layer adds the two triples: the oracle computes the functional oracle's answer
      (nothing about its truth), and the cleanup's verdict is true of the instance.\<close>

locale mcf_oracle_heap =
  mcf_oracle_heap_pipeline where capacity_list = capacity_list and h = h
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

subsection \<open>The pipeline is correct\<close>

text \<open>An accepted certificate is true by \<open>verdict_of_dispatch_sound\<close>; otherwise the rectified flow
      meets the premises of \<open>cleanup_imp_rule\<close>, and an exact verdict meets every bar.\<close>

lemma decide_imp_correct[certificate_heap_rules]:
  assumes "answer_wf a" "0 < M"
  shows "<inst_assn fa sa ca oa ba * answer_assn fla a ai>
           decide_imp cm M fa sa ca oa ba fla ai
         <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
              * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
  using verdict_of_flag_of[of fla a ai]
  unfolding decide_imp_def
  by (sep_auto heap: check_answer_imp_rule[OF assms])
    (sep_auto simp: answer_assn_def inst_assn_def assms[unfolded answer_wf_def]
                   rectify_facts verdict_of_dispatch_sound verdict_ok_imp_dispatch
              heap: certificate_heap_rules[unfolded inst_assn_def] cleanup_imp_rule[unfolded inst_assn_def])+

text \<open>Whatever the untrusted oracle returns, the flag and the flow left in the array are a true
      verdict at the bar \<open>cm\<close> sets.\<close>

lemma solve_imp_correct[certificate_heap_rules]:
  "\<lbrakk>length fl = m; answer_wf orc_answer; 0 < M\<rbrakk> \<Longrightarrow>
   <inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl>
     solve_imp cm M fa sa ca oa ba fla
   <\<lambda>r. \<exists>\<^sub>A fl'. inst_assn fa sa ca oa ba * fla \<mapsto>\<^sub>a fl'
              * \<up>(length fl' = m \<and> verdict_ok_dispatch cm M (verdict_of_flag r fl'))>"
  unfolding solve_imp_def
  by (sep_auto heap: oracle_imp_rule certificate_heap_rules)

end

end
