theory Matroid_Weighted_Intersection_Imp_Loop
  imports Matroid_Weighted_Intersection_Path_Loop Matroid_Intersection_Imp_Loop
    Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

provenance ai


section \<open>The Weighted Loop in Imperative HOL\<close>

text \<open>The imperative counterpart of @{locale weighted_intersection_path_loop}, as
  @{theory Matroid_Intersection.Matroid_Intersection_Imp_Loop} is that of the unweighted loop.
  Elements are the nats below \<open>n\<close>. The current solution is an abstract imperative set
  (@{locale imp_nat_set}), the weight maps are abstract handles, and the
  context of a round is held by the operations themselves; the loop only sees assertions for
  them. The only array the loop knows is the path array, since the functional path is a list.
  Weights have an abstract executable type \<open>'n\<close> that is read in the reals through an
  order-preserving ring embedding. Each operation refines the functional operation of the same
  name, and the loop allocates nothing: it works on the handles it receives. The handles end up
  representing the functional result.\<close>

subsection \<open>A Ring Embedding into the Reals\<close>

text \<open>A copy of @{text real_embedding} of @{text Abstract_ADTs}.\<close>

locale real_embedding =
  fixes h :: "'n :: linordered_idom \<Rightarrow> real"
  assumes h_add:  "\<And>a b. h (a + b) = h a + h b"
      and h_mult: "\<And>a b. h (a * b) = h a * h b"
      and h_one:  "h 1 = 1"
      and h_strict_mono: "\<And>a b. a < b \<Longrightarrow> h a < h b"
begin

lemma h_zero [simp]: "h 0 = 0"
  using h_add[of 0 0]
  by simp

lemma h_uminus [simp]: "h (- a) = - h a"
  using h_add[of a "- a"]
  by simp

lemma h_diff [simp]: "h (a - b) = h a - h b"
  using h_add[of a "- b"]
  by simp

lemma h_less_iff [simp]: "h a < h b \<longleftrightarrow> a < b"
  by (cases a b rule: linorder_cases) (auto dest: h_strict_mono)

lemma h_le_iff [simp]: "h a \<le> h b \<longleftrightarrow> a \<le> b"
  by (simp only: not_less[symmetric] h_less_iff)

lemma h_eq_iff [simp]: "h a = h b \<longleftrightarrow> a = b"
  by (simp add: order.eq_iff)

lemma h_one' [simp]: "h 1 = 1"
  by (rule h_one)

lemma h_neg_one [simp]: "h (- 1) = - 1"
  by simp

lemma h_mono: "a \<le> b \<Longrightarrow> h a \<le> h b"
  by simp

lemma h_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> h a"
  using h_le_iff[of 0 a]
  by simp

lemma h_less_zero [simp]: "h a < 0 \<longleftrightarrow> a < 0"
  using h_less_iff[of a 0]
  by simp
lemma h_zero_less [simp]: "0 < h a \<longleftrightarrow> 0 < a"
  using h_less_iff[of 0 a]
  by simp
lemma h_le_zero  [simp]: "h a \<le> 0 \<longleftrightarrow> a \<le> 0"
  using h_le_iff[of a 0]
  by simp
lemma h_zero_le  [simp]: "0 \<le> h a \<longleftrightarrow> 0 \<le> a"
  using h_le_iff[of 0 a]
  by simp
lemma h_eq_zero  [simp]: "h a = 0 \<longleftrightarrow> a = 0"
  using h_eq_iff[of a 0]
  by simp
lemma h_eq_neg1  [simp]: "h a = - 1 \<longleftrightarrow> a = - 1"
  using h_eq_iff[of a "- 1"]
  by simp
lemma h_neg1_eq  [simp]: "- 1 = h a \<longleftrightarrow> a = - 1"
  by (simp only: eq_commute[of "-1" "h a"] h_eq_neg1)

lemma h_min [simp]: "h (min a b) = min (h a) (h b)"
  by (cases "a \<le> b") (simp_all add: min_def)

lemma h_max [simp]: "h (max a b) = max (h a) (h b)"
  by (cases "a \<le> b") (simp_all add: max_def)

lemma h_sum: "h (sum f A) = (\<Sum>a\<in>A. h (f a))"
  by (induction A rule: infinite_finite_induct) (simp_all add: h_add)

end

subsection \<open>Code\<close>

text \<open>The operations: reading an entry of a weight map, copying and zeroing weight maps,
  building the context of a round, the tight path (written into the path array, as in the
  unweighted loop), the reweighting amount, and the shift of a weight map on the reachable set.
  All work in place.\<close>

locale weighted_intersection_imp_loop_spec =
  intersection_augment_imp_spec sins_imp sdel_imp
  for sins_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and sdel_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap" +
  fixes cval_imp :: "'ci \<Rightarrow> nat \<Rightarrow> 'n :: {linordered_idom, heap} Heap"
    and ccopy_imp :: "'ci \<Rightarrow> 'ci \<Rightarrow> unit Heap"
    and czero_imp :: "'ci \<Rightarrow> unit Heap"
    and tight_ctx_imp :: "'si \<Rightarrow> 'ci \<Rightarrow> 'ci \<Rightarrow> unit Heap"
    and tight_path_imp :: "nat array \<Rightarrow> nat option Heap"
    and eps_imp :: "'si \<Rightarrow> 'ci \<Rightarrow> 'ci \<Rightarrow> 'n option Heap"
    and shift_imp :: "'n \<Rightarrow> 'ci \<Rightarrow> unit Heap"
begin

text \<open>The counterparts of @{const weighted_intersection_path_loop_spec.path_gain} (as the test of
  positivity), @{const weighted_intersection_path_loop_spec.reweight} and
  @{const weighted_intersection_path_loop_spec.weighted_initial_state}. The path is in the first
  \<open>k\<close> cells of the path array, reversed, so it starts in cell \<open>k - 1\<close> and ends in cell
    \<open>0\<close>.\<close>

definition "gain_imp C1 C2 Ra k = do {
   u \<leftarrow> Array.nth Ra (k - 1);
   v \<leftarrow> Array.nth Ra 0;
   a \<leftarrow> cval_imp C1 u;
   b \<leftarrow> cval_imp C2 v;
   return (0 < a + b) }"

definition "reweight_imp e C1 C2 = do { shift_imp (- e) C1; shift_imp e C2 }"

definition "winit_imp Co C1 C2 = do { ccopy_imp Co C1; czero_imp C2 }"

text \<open>The counterpart of @{const weighted_intersection_path_loop_spec.weighted_matroid_intersection}.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) wmi_loop_imp :: "'si \<Rightarrow> 'ci \<Rightarrow> 'ci \<Rightarrow> nat array \<Rightarrow>
    unit Heap" where
  "wmi_loop_imp Si C1 C2 Ra = do {
     tight_ctx_imp Si C1 C2;
     r \<leftarrow> tight_path_imp Ra;
     (case r of
        Some k \<Rightarrow> do {
          g \<leftarrow> gain_imp C1 C2 Ra k;
          if g then do { aug_imp Si Ra k; wmi_loop_imp Si C1 C2 Ra } else return () }
      | None \<Rightarrow> do {
          e \<leftarrow> eps_imp Si C1 C2;
          (case e of
             None \<Rightarrow> return ()
           | Some e \<Rightarrow> do { reweight_imp e C1 C2; wmi_loop_imp Si C1 C2 Ra }) }) }"

definition "wmi_run_imp Si Co C1 C2 Ra = do {
   winit_imp Co C1 C2;
   wmi_loop_imp Si C1 C2 Ra }"

end

subsection \<open>Correctness\<close>

text \<open>The functional loop with the set model of solutions and real weight maps. The operations
  refine the functional ones. \<open>ctx_assn K\<close> holds the context \<open>K\<close> built by the last
  \<open>tight_ctx_imp\<close>, \<open>ws\<close> the stale context, and \<open>st\<close> the data of the operations
    that the loop
  passes on untouched. The context is not owned by the solution or the weight maps, so shifting
  the weight maps keeps it.\<close>

locale weighted_intersection_imp_loop =
  weighted_intersection_imp_loop_spec sins_imp sdel_imp cval_imp ccopy_imp czero_imp
    tight_ctx_imp tight_path_imp eps_imp shift_imp +
  intersection_augment_imp n sol_assn smemb_imp sins_imp sdel_imp +
  c: fixed_univ_map_copy_imp "{..<n}" "\<lambda> _. True" "\<lambda> c. c" h wmap_assn cval_imp ccopy_imp +
  c: fixed_univ_map_clear_imp "{..<n}" "\<lambda> _. True" "\<lambda> c. c" h wmap_assn cval_imp "\<lambda> _. 0"
    czero_imp +
  real_embedding h +
  weighted_intersection_path_loop where set_insert = "insert :: nat \<Rightarrow> nat set \<Rightarrow> nat set"
    and set_delete = "\<lambda> x X. X - {x}" and to_set = "\<lambda> X. X" and set_invar = finite
    and set_empty = "{}" and c_lookup = "\<lambda> c. c" and c_invar = "\<lambda> _. True"
    and c_zero = "\<lambda> _. 0"
    and c_shift = "c_shift :: 'rset \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat
      \<Rightarrow> real"
    and tight_ctx = "tight_ctx :: nat set \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow>
      real) \<Rightarrow> 'ctx"
  for n sol_assn smemb_imp sins_imp sdel_imp
    and cval_imp :: "'ci \<Rightarrow> nat \<Rightarrow> 'n :: {linordered_idom, heap} Heap"
    and ccopy_imp czero_imp tight_ctx_imp tight_path_imp eps_imp shift_imp h c_shift tight_ctx
    and wmap_assn :: "(nat \<Rightarrow> real) \<Rightarrow> 'ci \<Rightarrow> assn" +
  fixes ctx_assn :: "'ctx \<Rightarrow> assn"
    and ws :: assn
    and st :: assn
  assumes carrier_bound: "carrier \<subseteq> {..<n}"
    and tight_ctx_rule: "\<And> X c1 c2 Si C1 C2. \<lbrakk>finite X; X \<subseteq> carrier; indep1 X; indep2 X;
      matroid1.local_opt c1 X; matroid2.local_opt c2 X\<rbrakk> \<Longrightarrow>
      <sol_assn X Si * wmap_assn c1 C1 * wmap_assn c2 C2 * ws * st> tight_ctx_imp Si C1 C2
      <\<lambda> _. sol_assn X Si * wmap_assn c1 C1 * wmap_assn c2 C2 * ctx_assn (tight_ctx X c1 c2) * st>"
    and tight_path_rule: "\<And> X c1 c2 Ra. \<lbrakk>finite X; X \<subseteq> carrier; indep1 X; indep2 X;
      matroid1.local_opt c1 X; matroid2.local_opt c2 X\<rbrakk> \<Longrightarrow>
      <ctx_assn (tight_ctx X c1 c2) * parr_assn n Ra> tight_path_imp Ra
      <\<lambda> r. ctx_assn (tight_ctx X c1 c2) * path_assn n (tight_path (tight_ctx X c1 c2)) r Ra>"
    and eps_rule: "\<And> X c1 c2 Si C1 C2. \<lbrakk>finite X; X \<subseteq> carrier; indep1 X; indep2 X;
      matroid1.local_opt c1 X; matroid2.local_opt c2 X; tight_path (tight_ctx X c1 c2) = None\<rbrakk> \<Longrightarrow>
      <sol_assn X Si * wmap_assn c1 C1 * wmap_assn c2 C2 * ctx_assn (tight_ctx X c1 c2) * st>
        eps_imp Si C1 C2
      <\<lambda> r. sol_assn X Si * wmap_assn c1 C1 * wmap_assn c2 C2 * ctx_assn (tight_ctx X c1 c2) * st *
            \<up>(map_option h r = eps (tight_ctx X c1 c2))>"
    and shift_rule: "\<And> X c1 c2 c e C. \<lbrakk>finite X; X \<subseteq> carrier; indep1 X; indep2 X;
      matroid1.local_opt c1 X; matroid2.local_opt c2 X; tight_path (tight_ctx X c1 c2) = None\<rbrakk> \<Longrightarrow>
      <ctx_assn (tight_ctx X c1 c2) * wmap_assn c C> shift_imp e C
      <\<lambda> _. ctx_assn (tight_ctx X c1 c2) * wmap_assn (c_shift (reach (tight_ctx X c1 c2)) (h e) c) C>"
    and ctx_stale: "\<And> X c1 c2. \<lbrakk>finite X; X \<subseteq> carrier; indep1 X; indep2 X\<rbrakk>
      \<Longrightarrow>
      ctx_assn (tight_ctx X c1 c2) \<Longrightarrow>\<^sub>A ws"
begin

text \<open>The handles represent the solution and the split of a state of the functional loop; the
  original weight does not change.\<close>

definition "wstate_assn s Si C1 C2 =
  sol_assn (wsol s) Si * wmap_assn (wc1 s) C1 * wmap_assn (wc2 s) C2"

lemma rev_take_ends:
  assumes "k \<le> length ps" "rev (take k ps) = p" "p \<noteq> []"
  shows "k - 1 < length ps" "0 < length ps" "hd p = ps ! (k - 1)" "last p = ps ! 0"
  using assms(1,3)
  unfolding assms(2)[symmetric]
  by (simp_all add: hd_rev last_rev last_conv_nth hd_conv_nth) (arith)

lemma \<^marker>\<open>provenance ai_human\<close> gain_imp_rule:
  assumes "length ps = n" "k \<le> n" "rev (take k ps) = p" "p \<noteq> []" "set p \<subseteq> {..<n}"
  shows "<wmap_assn c1 C1 * wmap_assn c2 C2 * Ra \<mapsto>\<^sub>a ps> gain_imp C1 C2 Ra k
         <\<lambda> g. wmap_assn c1 C1 * wmap_assn c2 C2 * Ra \<mapsto>\<^sub>a ps *
               \<up>(g \<longleftrightarrow> 0 < c1 (hd p) + c2 (last p))>"
proof-
  note ends = rev_take_ends[OF assms(2)[folded assms(1)] assms(3,4)]
  have "ps ! (k - 1) \<in> {..<n}" "ps ! 0 \<in> {..<n}"
    using assms(4,5) hd_in_set[of p] last_in_set[of p] unfolding ends(3,4)
    by auto
  note lookup = c.fixed_univ_map_lookup_rule[OF TrueI this(1)]
    c.fixed_univ_map_lookup_rule[OF TrueI this(2)]
  note hs = h_zero_less[of "_ + _", unfolded h_add, symmetric]
  show ?thesis
    unfolding gain_imp_def
    using ends(1,2)
    by (sep_auto heap: lookup simp: ends(3,4) hs)
qed

lemma \<^marker>\<open>provenance ai_human\<close> reweight_imp_rule:
  assumes "finite X" "X \<subseteq> carrier" "indep1 X" "indep2 X" "matroid1.local_opt c1 X"
    "matroid2.local_opt c2 X" "tight_path (tight_ctx X c1 c2) = None"
  shows "<ctx_assn (tight_ctx X c1 c2) * wmap_assn c1 C1 * wmap_assn c2 C2> reweight_imp e C1 C2
         <\<lambda> _. ctx_assn (tight_ctx X c1 c2) *
               wmap_assn (c_shift (reach (tight_ctx X c1 c2)) (- h e) c1) C1 *
               wmap_assn (c_shift (reach (tight_ctx X c1 c2)) (h e) c2) C2>"
  unfolding reweight_imp_def
  by (sep_auto heap: shift_rule[OF assms, where e = "- e", simplified] shift_rule[OF assms])

lemma \<^marker>\<open>provenance ai_human\<close> winit_imp_rule:
  "<wmap_assn c Co * (\<exists>\<^sub>A d. wmap_assn d C1) * (\<exists>\<^sub>A d. wmap_assn d C2)> winit_imp Co C1 C2
   <\<lambda> _. wmap_assn c Co * wmap_assn c C1 * wmap_assn (\<lambda> _. 0) C2>"
  unfolding winit_imp_def
  by (sep_auto heap: c.fixed_univ_map_copy_rule c.fixed_univ_map_clear_rule)

lemma tight_path_bound:
  assumes "w_invar s" "tight_path (tight_ctx (wsol s) (wc1 s) (wc2 s)) = Some p"
  shows "set p \<subseteq> {..<n}" "p \<noteq> []"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "wc1 s" "wc2 s"
    by unfold_locales
  have "indep1 (wsol s)" "indep2 (wsol s)"
    using assms(1)
    by (simp_all add: w_invar_def)
  note bound = dVs_A1A2_carrier[OF this]
  from assms obtain u v where
    "vwalk_bet (W.Gbar (wsol s)) u p v \<or> (p = [u] \<and> u = v)" "u \<in> W.Sbar (wsol s)"
    by (blast elim: w_invar_tight_path)
  then have "set p \<subseteq> {..<n} \<and> p \<noteq> []"
    using carrier_bound dVs_subset[OF W.Gbar_subset[of "wsol s"]] bound
      W.Sbar_subset[of "wsol s"] vwalk_bet_in_vertices[of "W.Gbar (wsol s)" u p v]
    by (auto simp: S_def; fastforce)
  then show "set p \<subseteq> {..<n}" "p \<noteq> []"
    by simp_all
qed

text \<open>Path results, as preconditions.\<close>

lemma \<^marker>\<open>provenance ai_human\<close> path_None_pre:
  assumes "r = None \<Longrightarrow> <A * parr_assn n Ra> f r <Q>"
  shows "<A * path_assn n None r Ra> f r <Q>"
  by (rule ht_cons_pre[rotated], rule ht_pure_pre, rule assms, assumption)
     (unfold path_assn_def parr_assn_def, sep_auto)

lemma \<^marker>\<open>provenance ai_human\<close> path_Some_pre:
  assumes "\<And> k ps. \<lbrakk>length ps = n; r = Some k; k \<le> n; rev (take k ps) = p\<rbrakk> \<Longrightarrow>
             <A * Ra \<mapsto>\<^sub>a ps> f r <Q>"
  shows "<A * path_assn n (Some p) r Ra> f r <Q>"
proof-
  have "<\<exists>\<^sub>A k ps. A * Ra \<mapsto>\<^sub>a ps * \<up>(length ps = n \<and> r = Some k \<and> k \<le> n
    \<and> rev (take k ps) = p)>
          f r <Q>"
    by (intro ht_ex_pre ht_pure_pre) (elim conjE, rule assms)
  then show ?thesis
    by (rule ht_cons_pre[rotated]) (unfold path_assn_def option.case(2), sep_auto)
qed

lemma \<^marker>\<open>provenance ai_human\<close> wmi_loop_imp_rule:
  assumes "weighted_matroid_intersection_dom s" "w_invar s"
  shows "<wstate_assn s Si C1 C2 * ws * st * parr_assn n Ra> wmi_loop_imp Si C1 C2 Ra
         <\<lambda> _. wstate_assn (weighted_matroid_intersection s) Si C1 C2 * ws * st * parr_assn n Ra>"
  using assms(2)
proof(induction s rule: weighted_matroid_intersection_induct)
  case 1
  show ?case
    by (rule assms(1))
next
  case step: (2 s)
  define X where "X = wsol s"
  define c1 where "c1 = wc1 s"
  define c2 where "c2 = wc2 s"
  define K where "K = tight_ctx X c1 c2"
  have f: "finite X" "X \<subseteq> carrier" "indep1 X" "indep2 X" "matroid1.local_opt c1 X"
    "matroid2.local_opt c2 X"
    using step.prems
    by (simp_all add: w_invar_def X_def c1_def c2_def)
  note C = tight_ctx_rule[OF f, folded K_def]
  note P = tight_path_rule[OF f, folded K_def]
  note stale = ent_star_mono[OF ent_star_mono[OF ent_star_mono[OF ent_refl
    ctx_stale[OF f(1-4), of c1 c2, folded K_def]] ent_refl] ent_refl]
  note cs = ht_frame[OF C, where R = "parr_assn n Ra", unfolded X_def c1_def c2_def,
    folded wstate_assn_def]
  have ps: "<wstate_assn s Si C1 C2 * ctx_assn K * st * parr_assn n Ra> tight_path_imp Ra
            <\<lambda> r. wstate_assn s Si C1 C2 * ctx_assn K * st * path_assn n (tight_path K) r Ra>"
    by (rule ht_frame_ac[OF P, where R = "wstate_assn s Si C1 C2 * st"])
       (simp only: star_aci, rule ent_refl)+
  show ?case
  proof(cases "tight_path K")
    case None
    note pN = None
    note E = eps_rule[OF f pN[unfolded K_def], folded K_def]
    have es: "<wstate_assn s Si C1 C2 * ctx_assn K * st * parr_assn n Ra> eps_imp Si C1 C2
              <\<lambda> r. wstate_assn s Si C1 C2 * ctx_assn K * st * parr_assn n Ra *
                    \<up>(map_option h r = eps K)>"
      by (rule ht_frame_ac[OF E, where R = "parr_assn n Ra"])
         (simp only: wstate_assn_def X_def c1_def c2_def star_aci, rule ent_refl)+
    show ?thesis
    proof(cases "eps K")
      case None
      have "weighted_stop_cond s"
        using pN None
        by (simp add: weighted_stop_cond_def Let_def K_def X_def c1_def c2_def)
      note fin = weighted_matroid_intersection_simps(1)[OF step.hyps this]
      show ?thesis
        unfolding fin
        by (subst wmi_loop_imp.simps, rule ht_bind[OF cs], rule ht_bind[OF ps], simp only: pN,
            rule path_None_pre, simp only: option.case(1), rule ht_bind[OF es], rule ht_pure_pre,
            simp only: None option.map_disc_iff option.case(1), rule ht_cons_pre[OF _ ht_return_wp])
           (rule stale)
    next
      case (Some e)
      note R = reweight_imp_rule[OF f pN[unfolded K_def], folded K_def]
      note upd = weighted_reweight_upd_def[of s, unfolded Let_def,
        folded X_def c1_def c2_def, folded K_def, unfolded Some option.sel]
      have "weighted_reweight_cond s"
        using pN Some
        by (simp add: weighted_reweight_cond_def Let_def K_def X_def c1_def c2_def)
      note fin = weighted_matroid_intersection_simps(3)[OF step.hyps this]
        and IH = step.IH(2)[OF this w_invar_reweight[OF step.prems this], unfolded upd]
      have rw: "<wstate_assn s Si C1 C2 * ctx_assn K * st * parr_assn n Ra> reweight_imp e' C1 C2
                <\<lambda> _. wstate_assn (reweight (reach K) (h e') s) Si C1 C2 * ctx_assn K * st *
                      parr_assn n Ra>" for e'
        by (rule ht_frame_ac[OF R, where R = "sol_assn X Si * st * parr_assn n Ra"])
           (simp_all add: wstate_assn_def reweight_def X_def c1_def c2_def star_aci)
      show ?thesis
        unfolding fin upd
        by (subst wmi_loop_imp.simps, rule ht_bind[OF cs], rule ht_bind[OF ps], simp only: pN,
            rule path_None_pre, simp only: option.case(1), rule ht_bind[OF es], rule ht_pure_pre,
            simp only: Some map_option_eq_Some, elim exE conjE, simp only: option.case(2),
            rule ht_bind[OF rw], rule ht_cons_pre[OF stale], simp only:, rule IH)
    qed
  next
    case (Some p)
    note pS = Some
    note pb = tight_path_bound[OF step.prems pS[unfolded K_def X_def c1_def c2_def]]
    have gs: "<wstate_assn s Si C1 C2 * ctx_assn K * st * Ra \<mapsto>\<^sub>a ps> gain_imp C1 C2 Ra k
              <\<lambda> g. wstate_assn s Si C1 C2 * ctx_assn K * st * Ra \<mapsto>\<^sub>a ps *
                    \<up>(g \<longleftrightarrow> 0 < path_gain s p)>"
      if "length ps = n" "k \<le> n" "rev (take k ps) = p" for k ps
      by (rule ht_frame_ac[OF gain_imp_rule[OF that pb(2,1), of c1 C1 c2 C2],
            where R = "sol_assn X Si * ctx_assn K * st"])
         (simp_all add: wstate_assn_def path_gain_def X_def c1_def c2_def star_aci)
    show ?thesis
    proof(cases "0 < path_gain s p")
      case False
      have "weighted_stop_cond s"
        using pS False
        by (simp add: weighted_stop_cond_def Let_def K_def X_def c1_def c2_def)
      note fin = weighted_matroid_intersection_simps(1)[OF step.hyps this]
      show ?thesis
        unfolding fin
        by (subst wmi_loop_imp.simps, rule ht_bind[OF cs], rule ht_bind[OF ps], simp only: pS,
            rule path_Some_pre, simp only: option.case(2), rule ht_bind[OF gs], assumption+,
            rule ht_pure_pre, simp only: False simp_thms if_False,
            rule ht_cons_pre[OF _ ht_return_wp])
           (unfold parr_assn_def, rule ent_trans[OF stale], sep_auto)
    next
      case True
      note upd = weighted_augment_upd_def[of s, unfolded Let_def,
        folded X_def c1_def c2_def, folded K_def, unfolded pS option.sel]
      have "weighted_augment_cond s"
        using pS True
        by (simp add: weighted_augment_cond_def Let_def K_def X_def c1_def c2_def)
      note fin = weighted_matroid_intersection_simps(2)[OF step.hyps this]
        and IH = step.IH(1)[OF this w_invar_augment[OF step.prems this], unfolded upd]
      have ak: "<wstate_assn s Si C1 C2 * ctx_assn K * st * Ra \<mapsto>\<^sub>a ps> aug_imp Si Ra k
                <\<lambda> _. wstate_assn (s \<lparr>wsol := augment X p\<rparr>) Si C1 C2 * ctx_assn K * st *
                      Ra \<mapsto>\<^sub>a ps>"
        if "length ps = n" "k \<le> n" "rev (take k ps) = p" for k ps
        by (rule ht_frame_ac[OF aug_imp_rule[where X = X, OF that(2)[folded that(1)],
              unfolded that(3), OF pb(1)],
              where R = "wmap_assn c1 C1 * wmap_assn c2 C2 * ctx_assn K * st"])
           (simp_all add: wstate_assn_def X_def c1_def c2_def star_aci)
      note IH' = parr_frame[where F = emp, simplified, OF IH]
      show ?thesis
        unfolding fin upd
        by (subst wmi_loop_imp.simps, rule ht_bind[OF cs], rule ht_bind[OF ps], simp only: pS,
            rule path_Some_pre, simp only: option.case(2), rule ht_bind[OF gs], assumption+,
            rule ht_pure_pre, simp only: True simp_thms if_True, rule ht_bind[OF ak], assumption+,
            rule ht_cons_pre[OF stale], rule IH', assumption)
    qed
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> wmi_run_imp_correct:
  "<sol_assn {} Si * wmap_assn c Co * (\<exists>\<^sub>A d. wmap_assn d C1) * (\<exists>\<^sub>A d. wmap_assn d C2) *
    ws * st * parr_assn n Ra>
     wmi_run_imp Si Co C1 C2 Ra
   <\<lambda> _. \<exists>\<^sub>A X c1 c2. sol_assn X Si * wmap_assn c1 C1 * wmap_assn c2 C2 * wmap_assn c Co *
          ws * st * parr_assn n Ra * \<up>(weighted_double_matroid.is_opt indep1 indep2 c X)>"
proof-
  note init = w_invar_initial[OF TrueI]
  note dom = weighted_matroid_intersection_terminates[OF init refl]
  note opt = impl_total_correctness[OF TrueI, unfolded same_result[OF TrueI]]
  have i: "<sol_assn {} Si * wmap_assn c Co * (\<exists>\<^sub>A d. wmap_assn d C1) *
          (\<exists>\<^sub>A d. wmap_assn d C2) * ws * st * parr_assn n Ra> winit_imp Co C1 C2
    <\<lambda> _. wstate_assn (weighted_initial_state c) Si C1 C2 * wmap_assn c Co * ws * st *
          parr_assn n Ra>"
    by (rule ht_frame_ac[OF winit_imp_rule[of c Co C1 C2],
          where R = "sol_assn {} Si * ws * st * parr_assn n Ra"])
       (simp_all add: wstate_assn_def weighted_initial_state_def star_aci)
  show ?thesis
    unfolding wmi_run_imp_def
    by (rule ht_bind[OF i], rule ht_cons_post[OF ht_frame_ac[OF wmi_loop_imp_rule[OF dom init],
          where R = "wmap_assn c Co"]])
       ((simp only: star_aci, rule ent_refl)+, sep_auto simp: wstate_assn_def opt)
qed

end

end
