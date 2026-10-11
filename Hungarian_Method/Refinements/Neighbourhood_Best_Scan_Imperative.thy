theory Neighbourhood_Best_Scan_Imperative
  imports
    Neighbourhood_Best_Scan
    Directed_Set_Graphs.Weighted_Neighbourhoods_Imperative_Spec
    Data_Structures.Iterable_Set_Specs_Imp
    Data_Structures.Real_Embedding
begin

section \<open>Imperative Scan for the Best Two Neighbours\<close>

text \<open>The imperative counterpart of @{const nb_best_scan_spec.best_two}. The key and the preference
      of the neighbour at the cursor are read by a heap program @{term cur}, which is an argument.
      It may read further state, which is framed through the scan by an assertion @{term Ctx}.
      The program does not allocate.\<close>

locale nb_best_scan_imp_code =
  fixes has_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and move_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
begin

definition better_imp :: "'n::linorder \<times> 'v \<times> bool \<Rightarrow> 'n \<times> 'v \<times> bool \<Rightarrow> bool" where
  "better_imp p q = (fst p < fst q \<or> (fst p = fst q \<and> snd (snd p) \<and> \<not> snd (snd q)))"

definition "best_upd_imp b c =
  (case b of None \<Rightarrow> Some c | Some p \<Rightarrow> if better_imp c p then Some c else b)"

definition "best2_upd_imp bs c =
  (case bs of (b, s) \<Rightarrow>
     (case b of None \<Rightarrow> (Some c, b)
      | Some p \<Rightarrow> if better_imp c p then (Some c, b) else (b, best_upd_imp s c)))"

partial_function (heap) scan_best_imp ::
  "('ci \<Rightarrow> 'v \<Rightarrow> ('n::linorder \<times> 'v \<times> bool) Heap) \<Rightarrow> 'ci \<Rightarrow> 'v \<Rightarrow>
   ('n \<times> 'v \<times> bool) option \<times> ('n \<times> 'v \<times> bool) option \<Rightarrow>
   (('n \<times> 'v \<times> bool) option \<times> ('n \<times> 'v \<times> bool) option) Heap" where
  "scan_best_imp cur Ci u bs = do {
     t \<leftarrow> has_imp Ci u;
     (if t then do { c \<leftarrow> cur Ci u;
                     move_imp Ci u;
                     scan_best_imp cur Ci u (best2_upd_imp bs c) }
      else return bs) }"

definition "best_two_imp cur Ci u = do { reset_imp Ci u; scan_best_imp cur Ci u (None, None) }"

end

locale nb_best_scan_imp =
  nb_best_scan +
  real_embedding h +
  nb: weighted_neighbourhoods_imp_spec
    where idx_invar = rnb_invar and idx_abstract = rnb_abstract and idx_current = rnb_current
      and idx_has = rnb_has and idx_iterated = rnb_iterated and idx_remaining = rnb_remaining
      and idx_move = rnb_move and idx_reset = rnb_reset and K = K
      and cost = cost and wval = wval and nb_init = nb_init and nb_assn = nb_assn
      and has_imp = has_imp and current_imp = current_imp and current_cost_imp = current_cost_imp
      and move_imp = move_imp and reset_imp = reset_imp and reset_all_imp = reset_all_imp
  for h :: "'n::linordered_idom \<Rightarrow> real"
    and cost wval nb_init nb_assn has_imp current_imp current_cost_imp move_imp reset_imp
        reset_all_imp

sublocale nb_best_scan_imp \<subseteq> code: nb_best_scan_imp_code has_imp move_imp reset_imp .

context nb_best_scan_imp
begin

text \<open>The imperative candidate @{term bi} represents the functional one @{term b}.\<close>

definition "best_rel pref bi b =
  (b = map_option (\<lambda>(k, r, f). (h k, r)) bi \<and> (\<forall>k r f. bi = Some (k, r, f) \<longrightarrow> f = pref r))"

definition "best2_rel pref bsi bs = (best_rel pref (fst bsi) (fst bs) \<and> best_rel pref (snd bsi) (snd bs))"

lemma best_rel_None: "best_rel pref bi None \<longleftrightarrow> bi = None"
  by (cases bi) (simp_all add: best_rel_def)

lemma best_rel_Some: "best_rel pref bi (Some (x, j)) \<longleftrightarrow> (\<exists>k. bi = Some (k, j, pref j) \<and> h k = x)"
proof(cases bi)
  case (Some a)
  obtain k r f where a: "a = (k, r, f)" by (cases a) auto
  show ?thesis by (auto simp: best_rel_def Some a)
qed (simp add: best_rel_def)

lemma best_upd_imp_rel:
  "\<lbrakk>best_rel pref bi b; key u r = h k; f = pref r\<rbrakk> \<Longrightarrow>
   best_rel pref (code.best_upd_imp bi (k, r, f)) (best_upd key pref u b r)"
  by (cases bi)
     (auto simp: best_rel_def code.best_upd_imp_def best_upd_def code.better_imp_def better_def)

lemma best2_upd_imp_rel:
  assumes "best2_rel pref bsi bs" "key u r = h k" "f = pref r"
  shows "best2_rel pref (code.best2_upd_imp bsi (k, r, f)) (best2_upd key pref u bs r)"
proof-
  obtain bi si b s where p: "bsi = (bi, si)" "bs = (b, s)" by (cases bsi, cases bs) auto
  have R: "best_rel pref bi b" "best_rel pref si s" using assms(1) by (simp_all add: best2_rel_def p)
  show ?thesis
  proof(cases bi)
    case None
    thus ?thesis using R assms(2,3)
      by (simp add: best2_rel_def best_rel_def p code.best2_upd_imp_def best2_upd_def)
  next
    case (Some c)
    obtain k' r' f' where c: "c = (k', r', f')" by (cases c) auto
    have b: "b = Some (h k', r')" "f' = pref r'" using R(1) by (simp_all add: best_rel_def Some c)
    have bt: "code.better_imp (k, r, f) c = better pref (key u r, r) (h k', r')"
      using assms(2,3) b(2) by (simp add: c code.better_imp_def better_def)
    show ?thesis
    proof(cases "better pref (key u r, r) (h k', r')")
      case True
      thus ?thesis using R(1) assms(2,3) bt
        by (simp add: best2_rel_def best_rel_def p Some b(1) code.best2_upd_imp_def best2_upd_def)
    next
      case False
      thus ?thesis using R(1) best_upd_imp_rel[where key = key and u = u, OF R(2) assms(2,3)] bt
        by (simp add: best2_rel_def p Some b(1) code.best2_upd_imp_def best2_upd_def)
    qed
  qed
qed

text \<open>The candidate program @{term cur} may rely on the current neighbour being in a set
      @{term A} that contains the neighbourhood.\<close>

lemma scan_best_imp_rule:
  assumes cur: "\<And>C. \<lbrakk>rnb_invar C; rnb_remaining C u \<noteq> {}; rnb_current C u \<in> A\<rbrakk> \<Longrightarrow>
                  <nb_assn C Ci * Ctx> cur Ci u
                  <\<lambda>(k, r, f). nb_assn C Ci * Ctx *
                               \<up>(h k = key u r \<and> r = rnb_current C u \<and> f = pref r)>"
      and "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)" "best2_rel pref bsi bs"
      and "rnb_remaining C u \<subseteq> A"
  shows "<nb_assn C Ci * Ctx> code.scan_best_imp cur Ci u bsi
         <\<lambda>bsi'. nb_assn (fst (scan_best key pref u C bs)) Ci * Ctx *
                 \<up>(best2_rel pref bsi' (snd (scan_best key pref u C bs)))>"
  using assms(2-6)
proof(induction "card (rnb_remaining C u)" arbitrary: C bs bsi rule: less_induct)
  case less
  show ?case
  proof(cases "rnb_has C u")
    case True
    have ne: "rnb_remaining C u \<noteq> {}" using rnb.idx_has[OF less.prems(1,2)] True by simp
    have x_in: "rnb_current C u \<in> rnb_remaining C u"
      using rnb.idx_current[OF less.prems(1,2) ne] .
    have xA: "rnb_current C u \<in> A" using x_in less.prems(5) by blast
    have C': "rnb_invar (rnb_move C u)"
             "rnb_remaining (rnb_move C u) u = rnb_remaining C u - {rnb_current C u}"
      using rnb.idx_move_invar[OF less.prems(1,2)] rnb.idx_move_remaining[OF less.prems(1,2) ne]
      by auto
    have card_less: "card (rnb_remaining (rnb_move C u) u) < card (rnb_remaining C u)"
      using card_Diff1_less[OF less.prems(3) x_in] by (simp add: C'(2))
    have fin': "finite (rnb_remaining (rnb_move C u) u)" using less.prems(3) by (simp add: C'(2))
    have A': "rnb_remaining (rnb_move C u) u \<subseteq> A" using less.prems(5) by (auto simp: C'(2))
    define bs' where "bs' = best2_upd key pref u bs (rnb_current C u)"
    have eq: "scan_best key pref u C bs = scan_best key pref u (rnb_move C u) bs'"
      by (simp add: scan_best.simps[of key pref u C bs] True bs'_def)
    have step: "\<And>k. h k = key u (rnb_current C u) \<Longrightarrow>
       <nb_assn (rnb_move C u) Ci * Ctx>
        code.scan_best_imp cur Ci u
          (code.best2_upd_imp bsi (k, rnb_current C u, pref (rnb_current C u)))
       <\<lambda>bsi'. nb_assn (fst (scan_best key pref u C bs)) Ci * Ctx *
               \<up>(best2_rel pref bsi' (snd (scan_best key pref u C bs)))>"
      unfolding eq bs'_def
      by (rule less.hyps[OF card_less C'(1) less.prems(2) fin' best2_upd_imp_rel[OF less.prems(4)]
                            A'])
         simp_all
    show ?thesis
      apply(subst code.scan_best_imp.simps)
      by (sep_auto heap: nb.has_rule cur[OF less.prems(1) ne xA] nb.move_rule step
                   simp: less.prems(1,2) True ne)
  next
    case False
    have eq: "scan_best key pref u C bs = (C, bs)"
      by (simp add: scan_best.simps[of key pref u C bs] False)
    show ?thesis
      apply(subst code.scan_best_imp.simps)
      by (sep_auto heap: nb.has_rule simp: less.prems False eq)
  qed
qed

theorem best_two_imp_rule:
  assumes cur: "\<And>C. \<lbrakk>rnb_invar C; rnb_remaining C u \<noteq> {}; rnb_current C u \<in> A\<rbrakk> \<Longrightarrow>
                  <nb_assn C Ci * Ctx> cur Ci u
                  <\<lambda>(k, r, f). nb_assn C Ci * Ctx *
                               \<up>(h k = key u r \<and> r = rnb_current C u \<and> f = pref r)>"
      and "rnb_invar C" "u \<in> K" "finite (rnb_abstract C u)" "rnb_abstract C u \<subseteq> A"
  shows "<nb_assn C Ci * Ctx> code.best_two_imp cur Ci u
         <\<lambda>bsi. nb_assn (fst (best_two key pref u C)) Ci * Ctx *
                \<up>(best2_rel pref bsi (snd (best_two key pref u C)))>"
proof-
  have R: "rnb_invar (rnb_reset C u)" "finite (rnb_remaining (rnb_reset C u) u)"
          "rnb_remaining (rnb_reset C u) u \<subseteq> A"
    using rnb.idx_reset_invar[OF assms(2,3)] rnb.idx_reset_remaining[OF assms(2,3)] assms(4,5)
    by auto
  note sc = scan_best_imp_rule[where key = key and pref = pref and cur = cur and Ctx = Ctx
                                 and bsi = "(None, None)" and bs = "(None, None)",
                               OF cur R(1) assms(3) R(2) _ R(3)]
  show ?thesis
    unfolding code.best_two_imp_def best_two_def
    by (sep_auto heap: nb.reset_rule sc simp: assms(2,3) best2_rel_def best_rel_def)
qed

end

end
