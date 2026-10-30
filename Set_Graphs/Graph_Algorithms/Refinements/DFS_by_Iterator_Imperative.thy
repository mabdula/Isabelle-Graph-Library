theory DFS_by_Iterator_Imperative
  imports Graph_Algorithms_Dev.DFS_by_Iterator Imperative.Imperative_DS
    Data_Structures.Imp_Array_Stack Data_Structures.Imp_Bool_Set
    Directed_Set_Graphs.CSR_Edge_Input

begin

provenance ai


section \<open>Imperative DFS by Neighbourhood Iterators\<close>

subsection \<open>Setup\<close>

text \<open>As in @{text DFS_Imperative}, we gather the imperative ADT locales, and then sublocale
      @{locale DFS_by_Iterator}. Unlike there, the functional ADTs are not instantiated: the stack,
      the seen set and the neighbourhood iterators stay abstract, such that, e.g., the CSR
      implementing the iterators is not exposed. The graph is a ghost: the program only accesses it
      through the iterators.

      The program does not allocate: the stack, the seen set and the iterators are passed in as
      heap handles. Initially, the stack and the seen set are empty, and the iterators are at
      @{term nbs_init}.\<close>

record ('stki, 'si, 'nbsi) DFS_it_imp_state =
  imp_stack :: 'stki
  imp_seen  :: 'si
  imp_its   :: 'nbsi

text \<open>The program only uses the imperative operations, and the code locale fixes nothing else and
      has no assumptions.\<close>

locale imp_DFS_by_Iterator_code =
  fixes stack_is_empty_imp :: "'stki \<Rightarrow> bool Heap"
    and stack_top_imp :: "'stki \<Rightarrow> 'v::heap Heap"
    and stack_push_imp :: "'stki \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and stack_pop_imp :: "'stki \<Rightarrow> unit Heap"
    and seen_isin_imp :: "'si \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and seen_insert_imp :: "'v \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and nbs_has_imp :: "'nbsi \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and nbs_current_imp :: "'nbsi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and nbs_move_imp :: "'nbsi \<Rightarrow> 'v \<Rightarrow> unit Heap"
begin

subsection \<open>Main Algorithm\<close>

partial_function (heap) DFS_it_imperative :: "'v \<Rightarrow> (_, _, _) DFS_it_imp_state \<Rightarrow> return Heap" where
  "DFS_it_imperative t sti = do {
     e \<leftarrow> stack_is_empty_imp (imp_stack sti);
     if e then Heap_Monad.return NotReachable
     else do {
       v \<leftarrow> stack_top_imp (imp_stack sti);
       if v = t then Heap_Monad.return Reachable
       else do {
         b \<leftarrow> nbs_has_imp (imp_its sti) v;
         if b then do {
           u \<leftarrow> nbs_current_imp (imp_its sti) v;
           nbs_move_imp (imp_its sti) v;
           sn \<leftarrow> seen_isin_imp (imp_seen sti) u;
           if sn then DFS_it_imperative t sti
           else do {
             stack_push_imp (imp_stack sti) u;
             seen_insert_imp u (imp_seen sti);
             DFS_it_imperative t sti }}
         else do {
           stack_pop_imp (imp_stack sti);
           DFS_it_imperative t sti }}}}"

lemmas [code] = DFS_it_imperative.simps

subsection \<open>Algorithm combined with Initial State\<close>

definition DFS_it_imperative' :: "'v \<Rightarrow> 'v \<Rightarrow> (_, _, _) DFS_it_imp_state \<Rightarrow> return Heap" where
  "DFS_it_imperative' s t sti = do {
     stack_push_imp (imp_stack sti) s;
     seen_insert_imp s (imp_seen sti);
     DFS_it_imperative t sti }"

end

locale imp_DFS_by_Iterator =
  stk: bounded_stack_imp where stack_abstract = stack_abstract +
  seen_imp: fixed_univ_set_basic_imp where U = U
      and fixed_univ_set_invar = seen_invar and fixed_univ_set_abstract = seen_abstract
      and fixed_univ_set_empty = seen_empty and fixed_univ_set_insert = seen_insert
      and fixed_univ_set_delete = seen_delete and fixed_univ_set_isin = seen_isin
      and fixed_univ_set_assn = seen_assn and fixed_univ_set_insert_imp = seen_insert_imp
      and fixed_univ_set_delete_imp = seen_delete_imp and fixed_univ_set_isin_imp = seen_isin_imp +
  nbs_imp: indexed_iterable_set_imp where
      idx_invar = nbs_invar and idx_abstract = nbs_abstract and idx_current = nbs_current
      and idx_has = nbs_has and idx_iterated = nbs_iterated and idx_remaining = nbs_remaining
      and idx_move = nbs_move and idx_reset = nbs_reset and K = K
      and idx_assn = nbs_assn and idx_current_imp = nbs_current_imp
      and idx_has_imp = nbs_has_imp and idx_move_imp = nbs_move_imp
      and idx_reset_imp = nbs_reset_imp +
  imp_DFS_by_Iterator_code
  for stack_abstract :: "'stk \<Rightarrow> 'v::heap list"
  and U :: "'v set" and K :: "'v set"
  and nbs_abstract :: "'nbs \<Rightarrow> 'v \<Rightarrow> 'v set"
  and nbs_invar nbs_current nbs_has nbs_iterated nbs_remaining nbs_move nbs_reset
  and seen_invar seen_abstract seen_empty seen_insert seen_delete seen_isin
  and seen_assn seen_delete_imp
  and nbs_assn nbs_reset_imp
begin

sublocale DFS_by_Iterator
  where empty = idm_empty and delete = idm_delete and insert = dls_insert and isin = dls_isin
  and t_set = dls_set and sel = dls_sel and update = idm_update and adjmap_inv = idm_invar
  and vset_empty = dls_empty and vset_delete = dls_delete and vset_inv = dls_invar
  and union = dls_union and inter = dls_inter and diff = dls_diff and lookup = idm_lookup
  and G = G and s = s and t = t
  and nbs_invar = nbs_invar and nbs_abstract = nbs_abstract and nbs_current = nbs_current
  and nbs_has = nbs_has and nbs_iterated = nbs_iterated and nbs_remaining = nbs_remaining
  and nbs_move = nbs_move and nbs_reset = nbs_reset
  and seen_invar = seen_invar and seen_abstract = seen_abstract and seen_empty = seen_empty
  and seen_insert = seen_insert and seen_delete = seen_delete and seen_isin = seen_isin
  and U = U and K = K and nbs_init = nbs_init
  for G :: "'v \<rightharpoonup> 'v list" and s t nbs_init
  by unfold_locales


subsection \<open>State\<close>

definition "DFS_it_state_assn st sti \<equiv>
  (\<exists>\<^sub>AS. stack_assn S (imp_stack sti) * \<up>(stack_invar S) * \<up>(stack_abstract S = stack st)) *
  seen_assn (seen st) (imp_seen sti) * nbs_assn (its st) (imp_its sti)"

end

section \<open>Combined Correctness Theorem\<close>

locale imp_DFS_by_Iterator_thms =
  imp_DFS_by_Iterator +
  DFS_by_Iterator_thms
    where empty = idm_empty and delete = idm_delete and insert = dls_insert and isin = dls_isin
    and t_set = dls_set and sel = dls_sel and update = idm_update and adjmap_inv = idm_invar
    and vset_empty = dls_empty and vset_delete = dls_delete and vset_inv = dls_invar
    and union = dls_union and inter = dls_inter and diff = dls_diff and lookup = idm_lookup
    and G = G and s = s and t = t
    and nbs_invar = nbs_invar and nbs_abstract = nbs_abstract and nbs_current = nbs_current
    and nbs_has = nbs_has and nbs_iterated = nbs_iterated and nbs_remaining = nbs_remaining
    and nbs_move = nbs_move and nbs_reset = nbs_reset
    and seen_invar = seen_invar and seen_abstract = seen_abstract and seen_empty = seen_empty
    and seen_insert = seen_insert and seen_delete = seen_delete and seen_isin = seen_isin
    and U = U and K = K and nbs_init = nbs_init
  for G s t nbs_init +
  assumes vertices_cap: "card (dVs (Graph.digraph_abs G)) \<le> cap"
begin

lemma DFS_it_state_assnI:
  "\<lbrakk>stack_invar S; stack_abstract S = stack st\<rbrakk> \<Longrightarrow>
   stack_assn S (imp_stack sti) * seen_assn (seen st) (imp_seen sti) * nbs_assn (its st) (imp_its sti)
   \<Longrightarrow>\<^sub>A DFS_it_state_assn st sti"
  unfolding DFS_it_state_assn_def by sep_auto

lemma DFS_it_imperative_rule:
  "invar_it G st \<longrightarrow>
   <DFS_it_state_assn st sti> DFS_it_imperative t sti
   <\<lambda>r. DFS_it_state_assn (DFS_it t st) sti * \<up>(r = DFS_state.return (DFS_it t st))>"
proof (induction arbitrary: st rule: DFS_it_imperative.fixp_induct)
  case (3 f)
  note IH = ht_cons_pre[OF DFS_it_state_assnI "3"[rule_format]]
  let "?I \<longrightarrow> <?P> ?body <?Q>" = ?case
  show ?case
  proof
    assume I: "invar_it G st"
    have dom: "DFS_it_dom t st"
      using DFS_it_terminates[OF I] .
    have K: "\<And>v tl. stack st = v # tl \<Longrightarrow> v \<in> K"
      using top_in_K[OF I] .
    have nbs: "\<And>v tl. \<lbrakk>stack st = v # tl; nbs_has (its st) v\<rbrakk> \<Longrightarrow>
               nbs_remaining (its st) v \<noteq> {} \<and> nbs_current (its st) v \<in> U"
      using current_in_neighbourhood[OF I K] vertices_in_U by auto
    have len: "DFS_it_call_1_conds t st \<Longrightarrow> length (stack st) < cap"
      using DFS_it_push_length[OF I] vertices_cap by fastforce
    note facts = K nbs I[unfolded invar_it_def] stk.stack_is_empty stk.stack_top stk.stack_push
                 stk.stack_pop
    show "<?P> ?body <?Q>"
    proof (rule DFS_it_cases[of t st])
      assume c: "DFS_it_call_1_conds t st"
      then obtain v tl where stack: "stack st = v # tl"
        by (auto simp: DFS_it_call_1_conds_def split: list.splits)
      have IH': "\<And>S. \<lbrakk>stack_invar S; stack_abstract S = nbs_current (its st) v # v # tl\<rbrakk> \<Longrightarrow>
        <(stack_assn S (imp_stack sti) * seen_assn (seen_insert (nbs_current (its st) v) (seen st)) (imp_seen sti)
         * nbs_assn (nbs_move (its st) v) (imp_its sti))> f t sti <?Q>"
        using IH[OF _ _ invar_it_holds(1)[OF I c]]
        by (simp add: DFS_it_simps(1)[OF dom c] DFS_it_upd1_def Let_def stack)
      show "<?P> ?body <?Q>"
        using c len[OF c] unfolding DFS_it_state_assn_def[of st]
        by (sep_auto heap: IH' simp: facts stack DFS_it_call_1_conds_def)
    next
      assume c: "DFS_it_call_2_conds t st"
      then obtain v tl where stack: "stack st = v # tl"
        by (auto simp: DFS_it_call_2_conds_def split: list.splits)
      have IH': "\<And>S. \<lbrakk>stack_invar S; stack_abstract S = v # tl\<rbrakk> \<Longrightarrow>
        <(stack_assn S (imp_stack sti) * seen_assn (seen st) (imp_seen sti)
         * nbs_assn (nbs_move (its st) v) (imp_its sti))> f t sti <?Q>"
        using IH[OF _ _ invar_it_holds(2)[OF I c]]
        by (simp add: DFS_it_simps(2)[OF dom c] DFS_it_upd2_def stack)
      show "<?P> ?body <?Q>"
        using c unfolding DFS_it_state_assn_def[of st]
        by (sep_auto heap: IH' simp: facts stack DFS_it_call_2_conds_def)
    next
      assume c: "DFS_it_call_3_conds t st"
      then obtain v tl where stack: "stack st = v # tl"
        by (auto simp: DFS_it_call_3_conds_def split: list.splits)
      have IH': "\<And>S. \<lbrakk>stack_invar S; stack_abstract S = tl\<rbrakk> \<Longrightarrow>
        <(stack_assn S (imp_stack sti) * seen_assn (seen st) (imp_seen sti)
         * nbs_assn (its st) (imp_its sti))> f t sti <?Q>"
        using IH[OF _ _ invar_it_holds(3)[OF I c]]
        by (simp add: DFS_it_simps(3)[OF dom c] DFS_it_upd3_def stack)
      show "<?P> ?body <?Q>"
        using c unfolding DFS_it_state_assn_def[of st]
        by (sep_auto heap: IH' simp: facts stack DFS_it_call_3_conds_def)
    next
      assume c: "DFS_it_ret_1_conds st"
      then show "<?P> ?body <?Q>"
        by (sep_auto simp: DFS_it_simps(4)[OF dom c] DFS_it_ret1_def DFS_it_ret_1_conds_def
                           DFS_it_state_assn_def facts)
    next
      assume c: "DFS_it_ret_2_conds t st"
      then obtain tl where stack: "stack st = t # tl"
        by (auto simp: DFS_it_ret_2_conds_def split: list.splits)
      show "<?P> ?body <?Q>"
        unfolding DFS_it_simps(5)[OF dom c] DFS_it_ret2_def DFS_it_state_assn_def
        by (sep_auto simp: stack stk.stack_is_empty) (sep_auto simp: stack stk.stack_is_empty stk.stack_top)
    qed
  qed
qed simp_all

subsection \<open>A Ghost Graph Ordered as the Iteration\<close>

text \<open>The iterators may iterate the neighbourhoods in any order. The original DFS selects the first unseen
      neighbour in its graph. Hence, we show that the neighbourhood lists of @{term G} can be ordered such
      that, in the states that the run passes through, the iterators choose the neighbour the original DFS
      selects.\<close>

lemma DFS_it_step_reach:
  assumes "(DFS_it_step t)\<^sup>*\<^sup>* st st'" "st' \<noteq> st"
  obtains "DFS_it_call_1_conds t st" "(DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd1 st) st'"
    | "DFS_it_call_2_conds t st" "(DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd2 st) st'"
    | "DFS_it_call_3_conds t st" "(DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd3 st) st'"
proof-
  obtain st'' where "DFS_it_step t st st''" "(DFS_it_step t)\<^sup>*\<^sup>* st'' st'"
    using assms by (metis converse_rtranclpE)
  thus ?thesis
    using that by (auto simp: DFS_it_step_def)
qed

lemma DFS_it_conds_excl:
  "DFS_it_call_1_conds t st \<Longrightarrow> \<not> DFS_it_call_2_conds t st \<and> \<not> DFS_it_call_3_conds t st"
  "DFS_it_call_2_conds t st \<Longrightarrow> \<not> DFS_it_call_3_conds t st"
  "DFS_it_ret_1_conds st \<Longrightarrow>
     \<not> DFS_it_call_1_conds t st \<and> \<not> DFS_it_call_2_conds t st \<and> \<not> DFS_it_call_3_conds t st"
  "DFS_it_ret_2_conds t st \<Longrightarrow>
     \<not> DFS_it_call_1_conds t st \<and> \<not> DFS_it_call_2_conds t st \<and> \<not> DFS_it_call_3_conds t st"
  by (auto simp: DFS_it_call_1_conds_def DFS_it_call_2_conds_def DFS_it_call_3_conds_def
                 DFS_it_ret_1_conds_def DFS_it_ret_2_conds_def split: list.splits)

lemma ghost_hist_move:
  assumes "nbs_invar C" "v \<in> K" "nbs_remaining C v \<noteq> {}"
          "\<forall>w\<in>K. distinct (hist w) \<and> set (hist w) = nbs_iterated C w"
  defines "hist' \<equiv> fun_upd hist v (hist v @ [nbs_current C v])"
  shows "\<forall>w\<in>K. distinct (hist' w) \<and> set (hist' w) = nbs_iterated (nbs_move C v) w"
        "\<forall>w\<in>K. \<exists>zs. H w = hist' w @ zs \<and> distinct zs \<and> set zs = nbs_remaining (nbs_move C v) w
         \<Longrightarrow> (\<forall>w\<in>K. \<exists>zs. H w = hist w @ zs \<and> distinct zs \<and> set zs = nbs_remaining C w) \<and>
             (\<exists>zs. H v = hist v @ nbs_current C v # zs)"
proof-
  have u: "nbs_current C v \<in> nbs_remaining C v" "nbs_current C v \<notin> nbs_iterated C v"
    using nbs_imp.idx_current[OF assms(1-3)] nbs_imp.idx_partition_disjoint[OF assms(1,2)] by auto
  show "\<forall>w\<in>K. distinct (hist' w) \<and> set (hist' w) = nbs_iterated (nbs_move C v) w"
    using assms(4) u(2) nbs_imp.idx_move_iterated[OF assms(1-3)]
          nbs_imp.idx_move_iterated_other[OF assms(1-3)]
    by (auto simp: hist'_def)
  assume H: "\<forall>w\<in>K. \<exists>zs. H w = hist' w @ zs \<and> distinct zs \<and> set zs = nbs_remaining (nbs_move C v) w"
  obtain zs where zs: "H v = hist' v @ zs" "distinct zs" "set zs = nbs_remaining (nbs_move C v) v"
    using H assms(2) by blast
  have Hv: "H v = hist v @ nbs_current C v # zs"
    using zs(1) by (simp add: hist'_def)
  have "\<exists>zs. H w = hist w @ zs \<and> distinct zs \<and> set zs = nbs_remaining C w" if "w \<in> K" for w
  proof(cases "w = v")
    case True
    thus ?thesis
      using Hv zs(2,3) u(1) nbs_imp.idx_move_remaining[OF assms(1-3)]
      by (intro exI[of _ "nbs_current C v # zs"]) auto
  qed (use H that nbs_imp.idx_move_remaining_other[OF assms(1-3)] in \<open>auto simp: hist'_def\<close>)
  thus "(\<forall>w\<in>K. \<exists>zs. H w = hist w @ zs \<and> distinct zs \<and> set zs = nbs_remaining C w) \<and>
             (\<exists>zs. H v = hist v @ nbs_current C v # zs)"
    using Hv by blast
qed

lemma ghost_order_exists:
  fixes st :: "(_, _, _) DFS_it_state"
  assumes "invar_it G st" "\<forall>v\<in>K. distinct (hist v) \<and> set (hist v) = nbs_iterated (its st) v"
  shows "\<exists>H. (\<forall>v\<in>K. \<exists>zs. H v = hist v @ zs \<and> distinct zs \<and> set zs = nbs_remaining (its st) v) \<and>
             (\<forall>st' v stack_tl. (DFS_it_step t)\<^sup>*\<^sup>* st st' \<longrightarrow> DFS_it_call_1_conds t st' \<longrightarrow>
                stack st' = v # stack_tl \<longrightarrow>
                v \<in> K \<and> nbs_current (its st') v = hd (filter (\<lambda>x. x \<notin> seen_abstract (seen st')) (H v)))"
  using assms
proof(induction arbitrary: hist rule: DFS_it_induct[OF DFS_it_terminates[OF assms(1)]])
  case IH: (1 st)
  have ret: ?case
    if nc: "\<not> DFS_it_call_1_conds t st" "\<not> DFS_it_call_2_conds t st" "\<not> DFS_it_call_3_conds t st"
  proof-
    define Z where "Z w = (SOME zs. distinct zs \<and> set zs = nbs_remaining (its st) w)" for w
    have Z: "distinct (Z w) \<and> set (Z w) = nbs_remaining (its st) w" if "w \<in> K" for w
    proof-
      have "nbs_remaining (its st) w \<subseteq> set ((\<N>\<^sub>G G) w)"
        using nbs_imp.idx_partition_union[of "its st" w] IH(5) that by (auto simp: invar_it_def)
      hence "\<exists>zs. distinct zs \<and> set zs = nbs_remaining (its st) w"
        using finite_distinct_list finite_subset by (metis List.finite_set)
      thus ?thesis
        unfolding Z_def by (rule someI_ex)
    qed
    have "\<not> DFS_it_call_1_conds t st'" if "(DFS_it_step t)\<^sup>*\<^sup>* st st'" for st'
    proof(cases "st' = st")
      case False
      show ?thesis
        using DFS_it_step_reach[OF that False] nc by metis
    qed (use nc(1) in simp)
    thus ?case
      using Z by (intro exI[of _ "\<lambda>w. hist w @ Z w"] conjI) blast+
  qed
  show ?case
  proof(rule DFS_it_cases[of t st])
    assume c: "DFS_it_call_1_conds t st"
    obtain v tl where stack: "stack st = v # tl" and has: "nbs_has (its st) v"
      and unseen: "\<not> seen_isin (seen st) (nbs_current (its st) v)"
      using c by (auto simp: DFS_it_call_1_conds_def split: list.splits)
    have K: "v \<in> K"
      using top_in_K[OF IH(5) stack] .
    have C: "nbs_invar (its st)" "nbs_iterated (its st) v \<subseteq> seen_abstract (seen st)"
      "seen_invar (seen st)"
      using IH(5) K by (auto simp: invar_it_def)
    have its: "its (DFS_it_upd1 st) = nbs_move (its st) v"
      by (simp add: DFS_it_upd1_def Let_def stack)
    note hm = ghost_hist_move[OF C(1) K current_in_neighbourhood(1)[OF IH(5) K has] IH(6)]
    obtain H where H: "\<forall>w\<in>K. \<exists>zs. H w = (fun_upd hist v (hist v @ [nbs_current (its st) v])) w @ zs \<and>
                         distinct zs \<and> set zs = nbs_remaining (nbs_move (its st) v) w"
      and sel: "\<forall>st' w stack_tl. (DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd1 st) st' \<longrightarrow> DFS_it_call_1_conds t st' \<longrightarrow>
                stack st' = w # stack_tl \<longrightarrow>
                w \<in> K \<and> nbs_current (its st') w = hd (filter (\<lambda>x. x \<notin> seen_abstract (seen st')) (H w))"
      using IH(2)[OF c invar_it_holds(1)[OF IH(5) c] hm(1)[folded its]] by (auto simp: its)
    note shape = hm(2)[OF H]
    show ?thesis
    proof(rule exI[of _ H], rule conjI, use shape in blast, intro allI impI)
      fix st' w stack_tl
      assume r: "(DFS_it_step t)\<^sup>*\<^sup>* st st'" "DFS_it_call_1_conds t st'" "stack st' = w # stack_tl"
      show "w \<in> K \<and> nbs_current (its st') w = hd (filter (\<lambda>x. x \<notin> seen_abstract (seen st')) (H w))"
      proof(cases "st' = st")
        case True
        have w: "w = v"
          using r(3) stack by (simp add: True)
        obtain zs where Hv: "H v = hist v @ nbs_current (its st) v # zs"
          using shape by blast
        have "filter (\<lambda>x. x \<notin> seen_abstract (seen st)) (hist v) = []"
          using IH(6) K C(2) by (auto simp: filter_empty_conv)
        thus ?thesis
          using K unseen seen_imp.fixed_univ_set_isin[OF C(3)] by (simp add: True w Hv)
      next
        case False
        have "(DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd1 st) st'"
          using DFS_it_step_reach[OF r(1) False] DFS_it_conds_excl(1)[OF c] by metis
        thus ?thesis
          using sel r(2,3) by blast
      qed
    qed
  next
    assume c: "DFS_it_call_2_conds t st"
    obtain v tl where stack: "stack st = v # tl" and has: "nbs_has (its st) v"
      using c by (auto simp: DFS_it_call_2_conds_def split: list.splits)
    have K: "v \<in> K"
      using top_in_K[OF IH(5) stack] .
    have C: "nbs_invar (its st)"
      using IH(5) by (auto simp: invar_it_def)
    have its: "its (DFS_it_upd2 st) = nbs_move (its st) v"
      by (simp add: DFS_it_upd2_def stack)
    note hm = ghost_hist_move[OF C K current_in_neighbourhood(1)[OF IH(5) K has] IH(6)]
    obtain H where H: "\<forall>w\<in>K. \<exists>zs. H w = (fun_upd hist v (hist v @ [nbs_current (its st) v])) w @ zs \<and>
                         distinct zs \<and> set zs = nbs_remaining (nbs_move (its st) v) w"
      and sel: "\<forall>st' w stack_tl. (DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd2 st) st' \<longrightarrow> DFS_it_call_1_conds t st' \<longrightarrow>
                stack st' = w # stack_tl \<longrightarrow>
                w \<in> K \<and> nbs_current (its st') w = hd (filter (\<lambda>x. x \<notin> seen_abstract (seen st')) (H w))"
      using IH(3)[OF c invar_it_holds(2)[OF IH(5) c] hm(1)[folded its]] by (auto simp: its)
    have "(DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd2 st) st'"
      if "(DFS_it_step t)\<^sup>*\<^sup>* st st'" "DFS_it_call_1_conds t st'" for st'
      using DFS_it_step_reach[OF that(1)] DFS_it_conds_excl(1,2)[of st] c that(2) by metis
    thus ?thesis
      using sel hm(2)[OF H] by blast
  next
    assume c: "DFS_it_call_3_conds t st"
    have its: "its (DFS_it_upd3 st) = its st"
      by (simp add: DFS_it_upd3_def)
    obtain H where H: "\<forall>w\<in>K. \<exists>zs. H w = hist w @ zs \<and> distinct zs \<and> set zs = nbs_remaining (its st) w"
      and sel: "\<forall>st' w stack_tl. (DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd3 st) st' \<longrightarrow> DFS_it_call_1_conds t st' \<longrightarrow>
                stack st' = w # stack_tl \<longrightarrow>
                w \<in> K \<and> nbs_current (its st') w = hd (filter (\<lambda>x. x \<notin> seen_abstract (seen st')) (H w))"
      using IH(4)[OF c invar_it_holds(3)[OF IH(5) c] IH(6)[folded its]] by (auto simp: its)
    have "(DFS_it_step t)\<^sup>*\<^sup>* (DFS_it_upd3 st) st'"
      if "(DFS_it_step t)\<^sup>*\<^sup>* st st'" "DFS_it_call_1_conds t st'" for st'
      using DFS_it_step_reach[OF that(1)] DFS_it_conds_excl(1,2)[of st] c that(2) by metis
    thus ?thesis
      using sel H by blast
  next
    assume c: "DFS_it_ret_1_conds st"
    thus ?thesis
      using ret DFS_it_conds_excl(3) by blast
  next
    assume c: "DFS_it_ret_2_conds t st"
    thus ?thesis
      using ret DFS_it_conds_excl(4) by blast
  qed
qed

text \<open>The ghost graph has the neighbourhoods of @{term G}, ordered as the run iterates them.\<close>

definition "ghost_G = (SOME G'. dom G' = dom G \<and> (\<forall>v. set ((\<N>\<^sub>G G') v) = set ((\<N>\<^sub>G G) v)) \<and>
   Graph.graph_inv G' \<and>
   (\<forall>st v stack_tl X. (DFS_it_step t)\<^sup>*\<^sup>* (initial_state_it s nbs_init) st \<longrightarrow>
      DFS_it_call_1_conds t st \<longrightarrow> stack st = v # stack_tl \<longrightarrow> distinct X \<longrightarrow>
      set X = seen_abstract (seen st) \<longrightarrow> nbs_current (its st) v = hd (dls_diff ((\<N>\<^sub>G G') v) X)))"

lemma ghost_G:
  "dom ghost_G = dom G" "\<And>v. set ((\<N>\<^sub>G ghost_G) v) = set ((\<N>\<^sub>G G) v)" "Graph.graph_inv ghost_G"
  "\<And>st v stack_tl X. \<lbrakk>(DFS_it_step t)\<^sup>*\<^sup>* (initial_state_it s nbs_init) st;
      DFS_it_call_1_conds t st; stack st = v # stack_tl; distinct X;
      set X = seen_abstract (seen st)\<rbrakk> \<Longrightarrow> nbs_current (its st) v = hd (dls_diff ((\<N>\<^sub>G ghost_G) v) X)"
proof-
  obtain H where H: "\<forall>v\<in>K. \<exists>zs. H v = [] @ zs \<and> distinct zs \<and> set zs = nbs_remaining nbs_init v"
    and sel: "\<forall>st v stack_tl. (DFS_it_step t)\<^sup>*\<^sup>* (initial_state_it s nbs_init) st \<longrightarrow>
                DFS_it_call_1_conds t st \<longrightarrow> stack st = v # stack_tl \<longrightarrow>
                v \<in> K \<and> nbs_current (its st) v = hd (filter (\<lambda>x. x \<notin> seen_abstract (seen st)) (H v))"
    using ghost_order_exists[OF invar_it_initial, of "\<lambda>_. []"] nbs_init_iterated
    by (auto simp: initial_state_it_def)
  define G' where "G' = (\<lambda>v. if v \<in> K then map_option (\<lambda>_. H v) (G v) else G v)"
  have N: "(\<N>\<^sub>G G') v = H v" if "v \<in> K" for v
    using H nbs_init_remaining that by (fastforce simp: G'_def Graph.neighbourhood_def split: option.splits)
  have "dom G' = dom G \<and> (\<forall>v. set ((\<N>\<^sub>G G') v) = set ((\<N>\<^sub>G G) v)) \<and> Graph.graph_inv G' \<and>
   (\<forall>st v stack_tl X. (DFS_it_step t)\<^sup>*\<^sup>* (initial_state_it s nbs_init) st \<longrightarrow>
      DFS_it_call_1_conds t st \<longrightarrow> stack st = v # stack_tl \<longrightarrow> distinct X \<longrightarrow>
      set X = seen_abstract (seen st) \<longrightarrow> nbs_current (its st) v = hd (dls_diff ((\<N>\<^sub>G G') v) X))"
    (is "?P G'")
  proof(intro conjI allI impI)
    show "dom G' = dom G"
      by (auto simp: G'_def split: if_splits)
    show "set ((\<N>\<^sub>G G') v) = set ((\<N>\<^sub>G G) v)" for v
      using N H nbs_init_remaining by (cases "v \<in> K") (auto simp: G'_def Graph.neighbourhood_def)
    show "Graph.graph_inv G'"
      using graph_inv(1) H by (auto simp: G'_def Graph.graph_inv_def)
    show "nbs_current (its st) v = hd (dls_diff ((\<N>\<^sub>G G') v) X)"
      if "(DFS_it_step t)\<^sup>*\<^sup>* (initial_state_it s nbs_init) st" "DFS_it_call_1_conds t st"
         "stack st = v # stack_tl" "set X = seen_abstract (seen st)" for st v stack_tl X
      using sel that N by (auto simp: dls_diff_def)
  qed
  hence "?P ghost_G"
    unfolding ghost_G_def by (rule someI[where P = ?P])
  thus "dom ghost_G = dom G" "\<And>v. set ((\<N>\<^sub>G ghost_G) v) = set ((\<N>\<^sub>G G) v)" "Graph.graph_inv ghost_G"
    "\<And>st v stack_tl X. \<lbrakk>(DFS_it_step t)\<^sup>*\<^sup>* (initial_state_it s nbs_init) st;
      DFS_it_call_1_conds t st; stack st = v # stack_tl; distinct X;
      set X = seen_abstract (seen st)\<rbrakk> \<Longrightarrow> nbs_current (its st) v = hd (dls_diff ((\<N>\<^sub>G ghost_G) v) X)"
    by blast+
qed

lemma ghost_G_digraph_abs: "Graph.digraph_abs ghost_G = Graph.digraph_abs G"
  by (simp only: Graph.digraph_abs_def dls_isin_def ghost_G(2))

interpretation ghost: DFS_by_Iterator_thms
  where empty = idm_empty and delete = idm_delete and insert = dls_insert and isin = dls_isin
  and t_set = dls_set and sel = dls_sel and update = idm_update and adjmap_inv = idm_invar
  and vset_empty = dls_empty and vset_delete = dls_delete and vset_inv = dls_invar
  and union = dls_union and inter = dls_inter and diff = dls_diff and lookup = idm_lookup
  and G = ghost_G and s = s and t = t
  and nbs_invar = nbs_invar and nbs_abstract = nbs_abstract and nbs_current = nbs_current
  and nbs_has = nbs_has and nbs_iterated = nbs_iterated and nbs_remaining = nbs_remaining
  and nbs_move = nbs_move and nbs_reset = nbs_reset
  and seen_invar = seen_invar and seen_abstract = seen_abstract and seen_empty = seen_empty
  and seen_insert = seen_insert and seen_delete = seen_delete and seen_isin = seen_isin
  and U = U and K = K and nbs_init = nbs_init
proof unfold_locales
  show "DFS_axioms ghost_G s"
    using DFS_axioms ghost_G(1,3)
    by (auto simp: DFS_axioms_def Graph.finite_graph_def Graph.finite_vsets_def ghost_G_digraph_abs
                   dom_def)
qed (use vertices_in_U vertices_in_K nbs_init_invar nbs_init_iterated nbs_init_remaining in
     \<open>simp_all add: ghost_G_digraph_abs ghost_G(2)\<close>)

subsection \<open>Correctness\<close>

lemma DFS_it_correct_NotReachable:
  assumes "DFS_state.return (DFS_it t (initial_state_it s nbs_init)) = NotReachable"
  shows "\<nexists>p. vwalk_bet (Graph.digraph_abs G) s p t"
  by (rule ghost.DFS_it_correct_1_strong[OF ghost_G(4) assms, unfolded ghost_G_digraph_abs])

lemma DFS_it_correct_Reachable:
  assumes "DFS_state.return (DFS_it t (initial_state_it s nbs_init)) = Reachable"
  shows "vwalk_bet (Graph.digraph_abs G) s (rev (stack (DFS_it t (initial_state_it s nbs_init)))) t"
        "distinct (stack (DFS_it t (initial_state_it s nbs_init)))"
  using ghost.DFS_it_correct_2[OF ghost_G(4) assms] by (simp_all only: ghost_G_digraph_abs distinct_rev)

text \<open>The caller supplies an empty stack, an empty seen set and the iterators at @{term nbs_init}.\<close>

lemma DFS_it_imperative'_rule:
  assumes "stack_invar S" "stack_abstract S = []"
  shows "<(stack_assn S (imp_stack sti)) * seen_assn seen_empty (imp_seen sti) * nbs_assn nbs_init (imp_its sti)>
           DFS_it_imperative' s t sti
         <\<lambda>r. DFS_it_state_assn (DFS_it t (initial_state_it s nbs_init)) sti *
              \<up>(r = DFS_state.return (DFS_it t (initial_state_it s nbs_init)))>"
proof-
  have "0 < card (dVs (Graph.digraph_abs G))"
    using Graph.finite_vertices[OF graph_inv] s_in_G card_gt_0_iff by blast
  hence cap: "0 < cap"
    using vertices_cap by linarith
  have U: "s \<in> U"
    using vertices_in_U by blast
  have IH: "\<And>S. \<lbrakk>stack_invar S; stack_abstract S = [s]\<rbrakk> \<Longrightarrow>
    <(stack_assn S (imp_stack sti)) * seen_assn (seen_insert s seen_empty) (imp_seen sti) *
      nbs_assn nbs_init (imp_its sti)>
      DFS_it_imperative t sti
    <\<lambda>r. DFS_it_state_assn (DFS_it t (initial_state_it s nbs_init)) sti *
         \<up>(r = DFS_state.return (DFS_it t (initial_state_it s nbs_init)))>"
    using ht_cons_pre[OF DFS_it_state_assnI DFS_it_imperative_rule[rule_format, OF invar_it_initial]]
    by (simp add: initial_state_it_def)
  have push: "stack_invar (stack_push S s)" "stack_abstract (stack_push S s) = [s]"
    using stk.stack_push[OF assms(1)] assms(2) cap by simp_all
  show ?thesis
    using assms cap U unfolding DFS_it_imperative'_def
    by (sep_auto heap: IH[OF push] simp: seen_imp.fixed_univ_set_empty(1))
qed

theorem DFS_it_imperative'_correct:
  assumes "stack_invar S" "stack_abstract S = []"
  shows "<(stack_assn S (imp_stack sti)) * seen_assn seen_empty (imp_seen sti) * nbs_assn nbs_init (imp_its sti)>
           DFS_it_imperative' s t sti
         <\<lambda>r. (\<exists>\<^sub>A(st::(_, _, _) DFS_it_state). DFS_it_state_assn st sti * \<up>(
            case r of NotReachable \<Rightarrow> \<nexists>p. vwalk_bet (Graph.digraph_abs G) s p t
            | Reachable \<Rightarrow> vwalk_bet (Graph.digraph_abs G) s (rev (stack st)) t \<and> distinct (stack st)))>"
  using DFS_it_correct_NotReachable DFS_it_correct_Reachable
  by (sep_auto heap: DFS_it_imperative'_rule[OF assms] split: return.splits)

end

section \<open>Instantiation with a Graph in CSR Form\<close>

text \<open>The neighbourhood iterators are the cursors of a graph in CSR form whose entries are the
      targets (@{locale csr_graph_imp}). The CSR programs are global, so the code part only fixes
      the imperative stack and seen set operations and has no assumptions.\<close>

locale imp_DFS_by_Iterator_CSR = imp_DFS_by_Iterator_code
  where nbs_has_imp = csr_has_imp and nbs_current_imp = csr_current_imp
  and nbs_move_imp = csr_move_imp

text \<open>For the correctness proof, the blocks of the CSR, read as lists, form the graph of the DFS.
      The caller supplies the cursor array at the starts of the blocks.\<close>

locale imp_DFS_by_Iterator_CSR_thms =
  stk: bounded_stack_imp where stack_abstract = stack_abstract +
  seen_imp: fixed_univ_set_basic_imp where U = U
      and fixed_univ_set_invar = seen_invar and fixed_univ_set_abstract = seen_abstract
      and fixed_univ_set_empty = seen_empty and fixed_univ_set_insert = seen_insert
      and fixed_univ_set_delete = seen_delete and fixed_univ_set_isin = seen_isin
      and fixed_univ_set_assn = seen_assn and fixed_univ_set_insert_imp = seen_insert_imp
      and fixed_univ_set_delete_imp = seen_delete_imp and fixed_univ_set_isin_imp = seen_isin_imp +
  csr_graph_imp n "{..<n}" B E +
  imp_DFS_by_Iterator_CSR
  for stack_abstract :: "'stk \<Rightarrow> nat list" and U :: "nat set"
  and seen_invar seen_abstract seen_empty seen_insert seen_delete seen_isin
  and seen_assn seen_delete_imp
  and n B and E :: "nat list" +
  fixes s t :: nat
  assumes E_bound: "set E \<subseteq> {..<n}"
    and U_bound: "{..<n} \<subseteq> U"
    and n_cap: "n \<le> cap"
    and s_in_G: "s \<in> dVs {(u, E ! i) | u i. u < n \<and> B ! u \<le> i \<and> i < B ! Suc u}"
begin

sublocale imp_DFS_by_Iterator where nbs_invar = csr_invar and nbs_abstract = csr_abstract
  and nbs_current = csr_current and nbs_has = csr_has and nbs_iterated = csr_iterated
  and nbs_remaining = csr_remaining and nbs_move = csr_move and nbs_reset = csr_reset
  and K = "{..<n}" and nbs_assn = csr_assn and nbs_current_imp = csr_current_imp
  and nbs_has_imp = csr_has_imp and nbs_move_imp = csr_move_imp and nbs_reset_imp = csr_reset_imp
  by unfold_locales

lemma csr_map_neighbourhood: "v < n \<Longrightarrow> set (Graph.neighbourhood csr_map v) = csr_abstract c v"
  by (simp add: Graph.neighbourhood_def csr_map_def csr_list_def csr_abstract_eq)

lemma csr_map_digraph_abs:
  "Graph.digraph_abs csr_map = {(u, E ! i) | u i. u < n \<and> B ! u \<le> i \<and> i < B ! Suc u}"
proof-
  have "v \<in> set (Graph.neighbourhood csr_map u) \<longleftrightarrow> u < n \<and> v \<in> (!) E ` {B ! u..<B ! Suc u}" for u v
    by (simp add: Graph.neighbourhood_def csr_map_def csr_list_def)
  thus ?thesis
    by (auto simp: Graph.digraph_abs_def dls_isin_def)
qed

sublocale imp_DFS_by_Iterator_thms where nbs_invar = csr_invar and nbs_abstract = csr_abstract
  and nbs_current = csr_current and nbs_has = csr_has and nbs_iterated = csr_iterated
  and nbs_remaining = csr_remaining and nbs_move = csr_move and nbs_reset = csr_reset
  and K = "{..<n}" and nbs_assn = csr_assn and nbs_current_imp = csr_current_imp
  and nbs_has_imp = csr_has_imp and nbs_move_imp = csr_move_imp and nbs_reset_imp = csr_reset_imp
  and G = csr_map and s = s and t = t and nbs_init = "\<lambda>v. B ! v"
proof unfold_locales
  have "E ! i < n" if "u < n" "i < B ! Suc u" for u i
    using E_bound nth_mem[OF order.strict_trans2[OF that(2) B_bound[OF that(1)]]] by blast
  thus V: "dVs (Graph.digraph_abs csr_map) \<subseteq> {..<n}"
    by (auto simp: csr_map_digraph_abs dVs_def)
  thus "dVs (Graph.digraph_abs csr_map) \<subseteq> U"
    using U_bound by blast
  show "card (dVs (Graph.digraph_abs csr_map)) \<le> cap"
    using card_mono[OF finite_lessThan V] n_cap by simp
  have "Graph.graph_inv csr_map"
    using E_distinct by (auto simp: Graph.graph_inv_def csr_map_def csr_list_def distinct_map split: if_splits)
  thus "DFS_axioms csr_map s"
    using s_in_G
    by (simp add: DFS_axioms_def Graph.finite_graph_def Graph.finite_vsets_def csr_map_def csr_list_def
                  csr_map_digraph_abs)
  show "csr_remaining ((!) B) v = set (Graph.neighbourhood csr_map v)" if "v \<in> {..<n}" for v
    using csr.idx_partition_union[OF csr_init_invar, of v] csr_init_iterated[of v]
          csr_map_neighbourhood[of v "(!) B"] that
    by simp
qed (simp_all add: csr_init_invar csr_init_iterated)

end

section \<open>Instantiation with a Graph Given by Edge Lists\<close>

text \<open>The code: the stack is an array stack (@{theory Data_Structures.Imp_Array_Stack}) and the
      seen set is a Boolean array (@{theory Data_Structures.Imp_Bool_Set}).\<close>

global_interpretation dfs_code: imp_DFS_by_Iterator_CSR ars_is_empty_imp ars_top_imp ars_push_imp
    ars_pop_imp bool_array_set_isin_imp bool_array_set_insert_imp
  defines dfs_csr_loop = dfs_code.DFS_it_imperative
    and dfs_csr = dfs_code.DFS_it_imperative'
  done

text \<open>The program takes the number \<open>n\<close> of vertices and the arrays of the first and of the second
      endpoints of the edges. It builds the CSR of the heads grouped by the tails
      (@{const csr_build_heads}), initialises the cursors, allocates the stack and the seen set and
      runs the DFS. It returns the result and the stack, which holds the path found.\<close>

definition dfs_edges_run :: "nat \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (return \<times> nat arsi) Heap" where
  "dfs_edges_run n Fa Ta s t = do {
     (Ba, Ea) \<leftarrow> csr_build_heads n (Fa, Ta) 0;
     Ca \<leftarrow> csr_cursor_init n Ba;
     Si \<leftarrow> ars_empty_imp n 0;
     Vi \<leftarrow> Array.new n False;
     r \<leftarrow> dfs_csr s t \<lparr>imp_stack = Si, imp_seen = Vi, imp_its = (Ba, Ea, Ca)\<rparr>;
     return (r, Si) }"

export_code dfs_edges_run checking SML_imp

text \<open>For the correctness proof, the endpoint lists have equal length, the vertices are below
      \<open>n\<close> and there are no parallel edges. The functional CSR is the one built by
      @{locale csr_buildup}, with the heads as entries.\<close>

locale imp_DFS_by_Iterator_edges =
  fixes n :: nat and fs ts :: "nat list" and s t :: nat
  assumes ts_length: "length ts = length fs"
    and fs_bound: "i < length fs \<Longrightarrow> fs ! i < n" and ts_bound: "i < length fs \<Longrightarrow> ts ! i < n"
    and edges_distinct: "distinct (zip fs ts)"
    and s_in_G: "s \<in> dVs (set (zip fs ts))"
begin

sublocale ei: csr_edge_input n fs ts "e_src fs" src_imp
  by unfold_locales
     (use ts_length src_imp_rule[of _ fs ts] in \<open>auto simp: in_set_conv_nth fs_bound ts_bound\<close>)

lemma heads_edges:
  "{(u, map (e_tgt fs ts) ei.inp.E_spec ! i) | u i.
      u < n \<and> ei.inp.B_spec ! u \<le> i \<and> i < ei.inp.B_spec ! Suc u} = set (zip fs ts)"
proof -
  have blk: "(!) (map (e_tgt fs ts) ei.inp.E_spec) ` {ei.inp.B_spec ! u..<ei.inp.B_spec ! Suc u} =
             {ts ! e | e. e < length fs \<and> fs ! e = u}" if "u < n" for u
  proof -
    have "(!) (map (e_tgt fs ts) ei.inp.E_spec) ` {ei.inp.B_spec ! u..<ei.inp.B_spec ! Suc u} =
          e_tgt fs ts ` (!) ei.inp.E_spec ` {ei.inp.B_spec ! u..<ei.inp.B_spec ! Suc u}"
      unfolding image_image by (rule image_cong[OF refl]) (use ei.B_spec_bound[OF that] in simp)
    thus ?thesis
      by (auto simp: ei.block_key[OF that])
  qed
  have nbs: "(u < n \<and> v \<in> (!) (map (e_tgt fs ts) ei.inp.E_spec) `
                              {ei.inp.B_spec ! u..<ei.inp.B_spec ! Suc u}) \<longleftrightarrow>
             (\<exists>e. e < length fs \<and> fs ! e = u \<and> ts ! e = v)" for u v
    by (cases "u < n") (auto simp: blk fs_bound)
  have "{(u, map (e_tgt fs ts) ei.inp.E_spec ! i) | u i.
          u < n \<and> ei.inp.B_spec ! u \<le> i \<and> i < ei.inp.B_spec ! Suc u} =
        {(u, v) | u v. u < n \<and> v \<in> (!) (map (e_tgt fs ts) ei.inp.E_spec) `
                                    {ei.inp.B_spec ! u..<ei.inp.B_spec ! Suc u}}"
    by auto
  also have "\<dots> = {(u, v) | u v. \<exists>e. e < length fs \<and> fs ! e = u \<and> ts ! e = v}"
    by (simp only: nbs)
  also have "\<dots> = set (zip fs ts)"
    by (auto simp: set_zip ts_length)
  finally show ?thesis .
qed

sublocale imp_DFS_by_Iterator_CSR_thms where cap = n and stack_invar = "ars_invar n"
  and stack_abstract = ars_abstract and stack_empty = "ars_empty n 0" and stack_push = ars_push
  and stack_pop = ars_pop and stack_top = ars_top and stack_is_empty = ars_is_empty
  and stack_assn = ars_assn and stack_empty_imp = "ars_empty_imp n 0"
  and stack_push_imp = ars_push_imp and stack_pop_imp = ars_pop_imp
  and stack_top_imp = ars_top_imp and stack_is_empty_imp = ars_is_empty_imp
  and U = "{..<n}" and seen_invar = "\<lambda>X. X \<subseteq> {..<n}" and seen_abstract = id
  and seen_empty = "{}" and seen_insert = insert and seen_delete = "\<lambda>x X. X - {x}"
  and seen_isin = "\<lambda>X x. x \<in> X" and seen_assn = "bool_array_set_assn n"
  and seen_insert_imp = bool_array_set_insert_imp and seen_delete_imp = bool_array_set_delete_imp
  and seen_isin_imp = bool_array_set_isin_imp
  and n = n and B = ei.inp.B_spec and E = "map (e_tgt fs ts) ei.inp.E_spec" and s = s and t = t
proof (intro imp_DFS_by_Iterator_CSR_thms.intro, goal_cases)
  case 1 show ?case by (rule ars_bounded_stack_imp)
next
  case 2 show ?case by (rule fixed_univ_set_imp.axioms(1)[OF bool_array_set_fixed_univ_set_imp])
next
  case 3 show ?case
  proof (unfold_locales, goal_cases)
    case (1 v)
    have "inj_on (e_tgt fs ts) {e \<in> edges fs. e_src fs e = v}"
    proof (rule inj_onI)
      fix e e'
      assume "e \<in> {e \<in> edges fs. e_src fs e = v}" "e' \<in> {e \<in> edges fs. e_src fs e = v}"
        "e_tgt fs ts e = e_tgt fs ts e'"
      then have "zip fs ts ! e = zip fs ts ! e'" "e < length (zip fs ts)" "e' < length (zip fs ts)"
        by (auto simp: ts_length)
      then show "e = e'"
        using nth_eq_iff_index_eq[OF edges_distinct] by blast
    qed
    then have inj: "inj_on (e_tgt fs ts \<circ> (!) ei.inp.E_spec) {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}"
      using comp_inj_on[OF ei.graph.E_distinct[OF 1]] ei.block_key[OF 1] by simp
    have eq: "map (e_tgt fs ts) ei.inp.E_spec ! i = (e_tgt fs ts \<circ> (!) ei.inp.E_spec) i"
      if "i \<in> {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}" for i
      using that ei.B_spec_bound[OF 1] by simp
    show ?case
    proof (rule inj_onI)
      fix i j
      assume i: "i \<in> {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}"
        and j: "j \<in> {ei.inp.B_spec ! v..<ei.inp.B_spec ! Suc v}"
        and e: "map (e_tgt fs ts) ei.inp.E_spec ! i = map (e_tgt fs ts) ei.inp.E_spec ! j"
      show "i = j"
        using e unfolding eq[OF i] eq[OF j] by (rule inj_onD[OF inj _ i j])
    qed
  qed
next
  case 4 show ?case
  proof unfold_locales
    show "set (map (e_tgt fs ts) ei.inp.E_spec) \<subseteq> {..<n}"
      using ei.edge_bound by (auto simp: ei.E_spec_edges)
  qed (simp_all add: s_in_G heads_edges)
qed

theorem dfs_edges_run_correct:
  "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> dfs_edges_run n Fa Ta s t
   <\<lambda>(r, Si). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * (\<exists>\<^sub>AS. ars_assn S Si * \<up>(ars_invar n S \<and>
      (case r of NotReachable \<Rightarrow> \<nexists>p. vwalk_bet (set (zip fs ts)) s p t
       | Reachable \<Rightarrow> vwalk_bet (set (zip fs ts)) s (rev (ars_abstract S)) t \<and>
                     distinct (ars_abstract S)))) * true>"
proof -
  have build: "<Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts> csr_build_heads n (Fa, Ta) 0
    <\<lambda>(Ba, Ea). Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts * Ba \<mapsto>\<^sub>a ei.inp.B_spec * Ea \<mapsto>\<^sub>a map (e_tgt fs ts) ei.inp.E_spec>"
    by (rule ei.csr_build_heads_rule[of Fa Ta, unfolded csr_build_heads])
  note dfs = DFS_it_imperative'_correct[OF stk.stack_empty,
                where sti = "\<lparr>imp_stack = Si, imp_seen = Vi, imp_its = Gi\<rparr>" for Si Vi Gi,
                unfolded csr_map_digraph_abs heads_edges, simplified]
  note ars_assn.simps[simp del]
  show ?thesis
    unfolding dfs_edges_run_def dfs_csr_def
    by (sep_auto heap: build csr_cursor_init_rule stk.stack_empty_rule bool_array_set_assn_new dfs
                 simp: DFS_it_state_assn_def split: return.splits)
qed

end

end
