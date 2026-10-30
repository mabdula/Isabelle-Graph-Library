theory Push_Relabel_RTF_Imperative
  imports
    Push_Relabel_Discharge_Imperative
    Push_Relabel_RTF
    Data_Structures.Fixed_Univ_List_Specs_Imp
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
begin

provenance ai


section \<open>Imperative Relabel-to-Front Push-Relabel\<close>

text \<open>The context of the relabel-to-front strategy in place: the list of vertices, the current
      vertex in two references, a reference holding the flag that tells whether the current vertex
      has been relabelled, and the handle of a structure over which an imperative vertex fold runs.
      The fold builds the initial list. All updates of the context work in place.\<close>

locale push_relabel_rtf_imp_code = push_relabel_ops_imp_code fst_imp snd_imp s t num_verts emap_get_imp
    emap_upd_imp ex_get_imp ex_upd_imp label_get_imp label_upd_imp count_get_imp count_upd_imp
    out_current_imp out_has_imp out_move_imp out_reset_imp out_reset_to_imp in_current_imp
    in_has_imp in_move_imp in_reset_imp in_reset_to_imp gap_fold_imp edge_fold_imp
  for fst_imp snd_imp :: "'ei \<Rightarrow> 'e::heap \<Rightarrow> 'v::heap Heap" and s t num_verts
  and emap_get_imp :: "'fi \<Rightarrow> 'e \<Rightarrow> 'n::{linordered_idom, heap} Heap" and emap_upd_imp
  and ex_get_imp :: "'xi \<Rightarrow> 'v \<Rightarrow> 'n Heap" and ex_upd_imp
  and label_get_imp :: "'li \<Rightarrow> 'v \<Rightarrow> nat Heap" and label_upd_imp
  and count_get_imp :: "'ci \<Rightarrow> nat \<Rightarrow> nat Heap" and count_upd_imp
  and out_current_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e Heap" and out_has_imp out_move_imp out_reset_imp
  and out_reset_to_imp and in_current_imp in_has_imp in_move_imp in_reset_imp in_reset_to_imp
  and gap_fold_imp edge_fold_imp +
  fixes list_push_front_imp :: "'lsi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and list_move_to_front_imp :: "'lsi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and list_first_imp :: "'lsi \<Rightarrow> 'v option Heap"
    and list_next_imp :: "'lsi \<Rightarrow> 'v \<Rightarrow> 'v option Heap"
    and vertex_fold_imp :: "'vs \<Rightarrow> ('v \<Rightarrow> unit Heap) \<Rightarrow> unit Heap"
begin

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) rtf_scan_imp ::
  "'lsi \<Rightarrow> ('fi, 'xi, 'li, 'ci, 'gi, 'ei, 'e) pr_imp \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v option Heap" where
  "rtf_scan_imp Ls Si n u =
     (if n = 0 then return None
      else do {
        x \<leftarrow> ex_get_imp (pi_ex Si) u;
        if 0 < x then return (Some u)
        else do {
          w \<leftarrow> list_next_imp Ls u;
          (case w of None \<Rightarrow> return None | Some w' \<Rightarrow> rtf_scan_imp Ls Si (n - 1) w') } })"

definition "rtf_discharge_imp Rr Si u = do {
   op \<leftarrow> discharge_op_imp False Si u;
   (case op of Relabel _ \<Rightarrow> (Rr := True) | _ \<Rightarrow> return ());
   return op }"

definition "rtf_stop_imp Cf Rr = do { cur_clear_imp Cf; Rr := False; return Done }"

text \<open>The current vertex \<open>u\<close> has become inactive; the list has been updated.\<close>

definition "rtf_next_imp Ls Cf Cu Rr Si u = do {
   w \<leftarrow> list_next_imp Ls u;
   (case w of
      None \<Rightarrow> rtf_stop_imp Cf Rr
    | Some w0 \<Rightarrow> do {
        r \<leftarrow> rtf_scan_imp Ls Si num_verts w0;
        (case r of
           None \<Rightarrow> rtf_stop_imp Cf Rr
         | Some w' \<Rightarrow> do { cur_set_imp Cf Cu w'; Rr := False; rtf_discharge_imp Rr Si w' }) }) }"

definition "rtf_select_imp = (\<lambda> (Ls, Cf, Cu, Rr, Vi) Si. do {
   f \<leftarrow> cur_flag_imp Cf;
   if \<not> f then return Done
   else do {
     u \<leftarrow> cur_get_imp Cu;
     x \<leftarrow> ex_get_imp (pi_ex Si) u;
     if 0 < x then rtf_discharge_imp Rr Si u
     else do {
       rel \<leftarrow> !Rr;
       (if rel then list_move_to_front_imp Ls u else return ());
       rtf_next_imp Ls Cf Cu Rr Si u } } })"

definition "rtf_init_step_imp Ls v = (if v \<noteq> s \<and> v \<noteq> t then list_push_front_imp Ls v else return ())"

definition "rtf_init_ctx_imp = (\<lambda> (Ls, Cf, Cu, Rr, Vi) Si. do {
   vertex_fold_imp Vi (rtf_init_step_imp Ls);
   f \<leftarrow> list_first_imp Ls;
   (case f of None \<Rightarrow> cur_clear_imp Cf | Some u \<Rightarrow> cur_set_imp Cf Cu u);
   Rr := False })"

end

text \<open>The list is a distinct list in place, and the imperative vertex fold implements the
      functional one; its own data are described by @{term vset_assn}.\<close>

locale push_relabel_rtf_imp =
  push_relabel_ops_imp +
  push_relabel_rtf where fst = fst and snd = snd +
  push_relabel_rtf_imp_code fst_imp snd_imp s t num_verts emap_get_imp emap_upd_imp ex_get_imp ex_upd_imp
    label_get_imp label_upd_imp count_get_imp count_upd_imp out_current_imp out_has_imp
    out_move_imp out_reset_imp out_reset_to_imp in_current_imp in_has_imp in_move_imp in_reset_imp
    in_reset_to_imp gap_fold_imp edge_fold_imp list_push_front_imp list_move_to_front_imp
    list_first_imp list_next_imp vertex_fold_imp +
  list_imp: fixed_univ_list_imp \<V> list_invar list_abstract list_empty list_push_front
    list_move_to_front list_first list_next list_assn list_empty_imp list_push_front_imp
    list_move_to_front_imp list_first_imp list_next_imp
  for list_push_front_imp list_move_to_front_imp list_first_imp list_next_imp
    and vertex_fold_imp :: "'vs \<Rightarrow> _" and list_assn list_empty_imp +
  fixes vset_assn :: "'vs \<Rightarrow> assn"
  assumes list_vertex_fold_imp:
    "\<And> Vi. set_fold_imp_rule \<V> (vset_assn Vi) list_vertex_fold (vertex_fold_imp Vi)"
begin

definition "rtf_ctx_assn = (\<lambda> (L, cur, rel) (Ls, Cf, Cu, Rr, Vi).
   list_assn L Ls * cur_assn cur Cf Cu * Rr \<mapsto>\<^sub>r rel * vset_assn Vi)"

definition "rtf_ctx_init_assn = (\<lambda> (Ls, Cf, Cu, Rr, Vi).
   list_assn list_empty Ls * (\<exists>\<^sub>A cur. cur_assn cur Cf Cu) * (\<exists>\<^sub>A rel. Rr \<mapsto>\<^sub>r rel) * vset_assn Vi)"

lemma list_next_in:
  assumes "list_invar L" "u \<in> set (list_abstract L)" "list_next L u = Some w"
  shows "w \<in> set (list_abstract L)"
proof-
  obtain xs ys where xy: "list_abstract L = xs @ u # ys"
    using assms(2) split_list[of u "list_abstract L"]
    by blast
  show ?thesis
    using assms(1,3) xy vlist.list_next[of L xs u ys]
    by (cases ys) auto
qed

lemma rtf_scan_in:
  assumes "list_invar L" "u \<in> set (list_abstract L)" "rtf_scan L x n u = Some w"
  shows "w \<in> set (list_abstract L)"
  using assms
  by (induction n arbitrary: u) (auto split: if_splits option.splits dest: list_next_in)

lemma \<^marker>\<open>provenance ai_human\<close> rtf_scan_imp_rule:
  assumes "list_invar L" "set (list_abstract L) = \<V> - {s, t}" "u \<in> set (list_abstract L)"
          "ex_invar (pr_excess st)"
  shows "<state_assn st Si * list_assn L Ls> rtf_scan_imp Ls Si n u
         <\<lambda>r. state_assn st Si * list_assn L Ls * \<up>(r = rtf_scan L (pr_excess st) n u)>"
  using assms(3)
proof(induction n arbitrary: u)
  case 0
  show ?case
    by (subst rtf_scan_imp.simps) sep_auto
next
  case (Suc n)
  have uV: "u \<in> \<V>"
    using Suc.prems assms(2)
    by auto
  show ?case
  proof(cases "list_next L u")
    case None
    show ?thesis
      by (subst rtf_scan_imp.simps)
         (sep_auto heap: ex_get_state_rule[OF assms(4) uV]
                         list_imp.list_next_rule[OF assms(1) Suc.prems] simp: None)
  next
    case (Some w)
    show ?thesis
      by (subst rtf_scan_imp.simps)
         (sep_auto heap: ex_get_state_rule[OF assms(4) uV] list_imp.list_next_rule[OF assms(1) Suc.prems]
                         Suc.IH[OF list_next_in[OF assms(1) Suc.prems Some]] simp: Some)
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> rtf_discharge_imp_rule:
  assumes "invar_state st" "u \<in> \<V>"
          "rtf_discharge L u rel (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) =
           (op, (L', cur', rel'))"
  shows "<state_assn st Si * Rr \<mapsto>\<^sub>r rel> rtf_discharge_imp Rr Si u
         <\<lambda>r. state_assn st Si * Rr \<mapsto>\<^sub>r rel' * \<up>(r = op \<and> L' = L \<and> cur' = Some u)>"
proof-
  have opd: "discharge_op False (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
    and c: "rel' = (case op of Relabel _ \<Rightarrow> True | _ \<Rightarrow> rel)" "L' = L" "cur' = Some u"
    using assms(3)
    by (auto simp add: rtf_discharge_def Let_def)
  show ?thesis
    unfolding rtf_discharge_imp_def
    by (cases op)
       (sep_auto heap: discharge_op_imp_rule[OF assms(1)[unfolded invar_state_def, THEN conjunct1] assms(2),
                                             where gap = False, unfolded opd]
                 simp: c)+
qed

lemma rtf_next_imp_rule:
  assumes "invar_state st" "list_invar L1" "set (list_abstract L1) = \<V> - {s, t}"
          "u \<in> set (list_abstract L1)"
          "(case list_next L1 u of
              None \<Rightarrow> (Done, (L1, None, False))
            | Some w \<Rightarrow>
                (case rtf_scan L1 (pr_excess st) num_verts w of
                   None \<Rightarrow> (Done, (L1, None, False))
                 | Some w' \<Rightarrow> rtf_discharge L1 w' False (pr_fwd st) (pr_bwd st) (pr_labels st)
                               (pr_out st) (pr_in st))) = (op, (L', cur', rel'))"
  shows "<state_assn st Si * list_assn L1 Ls * cur_assn cur Cf Cu * Rr \<mapsto>\<^sub>r rel>
           rtf_next_imp Ls Cf Cu Rr Si u
         <\<lambda>r. state_assn st Si * list_assn L' Ls * cur_assn cur' Cf Cu * Rr \<mapsto>\<^sub>r rel' *
              \<up>(r = op)>"
proof(cases "list_next L1 u")
  case None
  have "op = Done" "L' = L1" "cur' = None" "rel' = False"
    using assms(5) None
    by simp_all
  thus ?thesis
    unfolding rtf_next_imp_def rtf_stop_imp_def
    by (sep_auto heap: list_imp.list_next_rule[OF assms(2,4)] cur_clear_rule simp: None)
next
  case (Some w)
  note nx = Some
  note wL = list_next_in[OF assms(2,4) nx]
  note sc = rtf_scan_imp_rule[OF assms(2,3) wL
                              invar_basic_maps(3)[OF assms(1)[unfolded invar_state_def, THEN conjunct1]]]
  show ?thesis
  proof(cases "rtf_scan L1 (pr_excess st) num_verts w")
    case None
    have "op = Done" "L' = L1" "cur' = None" "rel' = False"
      using assms(5) nx None
      by simp_all
    thus ?thesis
      unfolding rtf_next_imp_def rtf_stop_imp_def
      by (sep_auto heap: list_imp.list_next_rule[OF assms(2,4)] sc cur_clear_rule simp: nx None)
  next
    case (Some w')
    have w'V: "w' \<in> \<V>"
      using assms(2,3) wL Some rtf_scan_in[of L1 w "pr_excess st" num_verts w']
      by auto
    have "rtf_discharge L1 w' False (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) =
          (op, (L', cur', rel'))"
      using assms(5) nx Some
      by simp
    note r = rtf_discharge_imp_rule[OF assms(1) w'V this]
    show ?thesis
      unfolding rtf_next_imp_def
      by (sep_auto heap: list_imp.list_next_rule[OF assms(2,4)] sc cur_set_rule r simp: nx Some)
  qed
qed

text \<open>What the context invariant gives the current vertex.\<close>

lemma rtf_ctx_invar_cur:
  assumes "rtf_ctx_invar st" "pr_ctx st = (L, cur, rel)"
  shows "list_invar L" "set (list_abstract L) = \<V> - {s, t}"
        "cur = Some u \<Longrightarrow> rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) u rel"
        "cur = Some u \<Longrightarrow> u \<in> set (list_abstract L)" "cur = Some u \<Longrightarrow> u \<in> \<V>"
  using assms
  by (auto simp: rtf_ctx_invar_def rtf_cur_invar_def split: if_splits)

lemma \<^marker>\<open>provenance ai_human\<close> rtf_select_imp_rule:
  assumes "invar_state st" "rtf_ctx_invar st" "rtf.select_of st = (op, c)"
  shows "<state_assn st Si * rtf_ctx_assn (pr_ctx st) Ci> rtf_select_imp Ci Si
         <\<lambda>r. state_assn st Si * rtf_ctx_assn c Ci * \<up>(r = op)>"
proof-
  obtain L cur rel Ls Cf Cu Rr Vi L' cur' rel' where ctx: "pr_ctx st = (L, cur, rel)"
    and Ci: "Ci = (Ls, Cf, Cu, Rr, Vi)" and c: "c = (L', cur', rel')"
    by (cases "pr_ctx st" rule: prod_cases3, cases Ci rule: prod_cases5, cases c rule: prod_cases3) auto
  note I = rtf_ctx_invar_cur[OF assms(2) ctx]
   and exi = invar_basic_maps(3)[OF assms(1)[unfolded invar_state_def, THEN conjunct1]]
  have sel: "rtf_select (L, cur, rel) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
               (pr_counts st) (pr_out st) (pr_in st) = (op, c)"
    using assms(3) ctx
    by (simp add: rtf.select_of_def)
  show ?thesis
  proof(cases cur)
    case None
    have "op = Done" "L' = L" "cur' = None" "rel' = rel"
      using sel None c
      by (simp_all add: rtf_select_def)
    thus ?thesis
      unfolding Ci ctx c rtf_select_imp_def rtf_ctx_assn_def prod.case None
      by (sep_auto heap: cur_flag_rule)
  next
    case (Some u)
    show ?thesis
    proof(cases "0 < ex_get (pr_excess st) u")
      case True
      have "rtf_discharge L u rel (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) =
            (op, (L', cur', rel'))"
        using sel Some True c
        by (simp add: rtf_select_def)
      note r = rtf_discharge_imp_rule[OF assms(1) I(5)[OF Some] this]
      show ?thesis
        unfolding Ci ctx c rtf_select_imp_def rtf_ctx_assn_def prod.case Some
        using True
        by (sep_auto heap: cur_flag_rule cur_get_rule[of "Some u" u] ex_get_state_rule[OF exi I(5)[OF Some]] r)
    next
      case False
      define L1 where "L1 = (if rel then list_move_to_front L u else L)"
      have L1: "list_invar L1" "set (list_abstract L1) = \<V> - {s, t}" "u \<in> set (list_abstract L1)"
        using I(1-3) Some L1_def rtf_move_props[of L "flow_abs st" "labels_abs st" u rel L1]
        by auto
      have sel0: "rtf_select (L, cur, rel) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
                    (pr_counts st) (pr_out st) (pr_in st) =
                  (case list_next L1 u of
                     None \<Rightarrow> (Done, (L1, None, False))
                   | Some w \<Rightarrow>
                       (case rtf_scan L1 (pr_excess st) num_verts w of
                          None \<Rightarrow> (Done, (L1, None, False))
                        | Some w' \<Rightarrow> rtf_discharge L1 w' False (pr_fwd st) (pr_bwd st) (pr_labels st)
                                      (pr_out st) (pr_in st)))"
        unfolding L1_def
        using Some False
        by (cases rel) (simp_all add: rtf_select_def Let_def)
      note nr = rtf_next_imp_rule[OF assms(1) L1 sel[unfolded sel0 c]]
      show ?thesis
      proof(cases rel)
        case True
        show ?thesis
          unfolding Ci ctx c rtf_select_imp_def rtf_ctx_assn_def prod.case Some
          using False
          by (sep_auto heap: cur_flag_rule cur_get_rule[of "Some u" u] ex_get_state_rule[OF exi I(5)[OF Some]]
                             list_imp.list_move_to_front_rule[OF I(1) I(4)[OF Some]]
                             nr[unfolded L1_def if_P[OF True]] simp: True)
      next
        case False
        show ?thesis
          unfolding Ci ctx c rtf_select_imp_def rtf_ctx_assn_def prod.case Some
          using \<open>\<not> 0 < ex_get (pr_excess st) u\<close>
          by (sep_auto heap: cur_flag_rule cur_get_rule[of "Some u" u] ex_get_state_rule[OF exi I(5)[OF Some]]
                             nr[unfolded L1_def if_not_P[OF False]] simp: False)
      qed
    qed
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> rtf_init_ctx_imp_rule:
  "<state_assn rtf.init_state Si * rtf_ctx_init_assn Ci> rtf_init_ctx_imp Ci Si
   <\<lambda>_. state_assn rtf.init_state Si * rtf_ctx_assn (pr_ctx rtf.init_state) Ci>"
proof-
  obtain Ls Cf Cu Rr Vi where Ci: "Ci = (Ls, Cf, Cu, Rr, Vi)"
    by (cases Ci) auto
  define P where "P = (\<lambda> W L. list_invar L \<and> set (list_abstract L) = W - {s, t})"
  have step: "P (insert v W) (rtf_init_step a v) \<and>
              <list_assn a Ls * \<up>(list_invar a)> rtf_init_step_imp Ls v
              <\<lambda>_. list_assn (rtf_init_step a v) Ls * \<up>(list_invar (rtf_init_step a v))>"
    if a: "P W a" "W \<subseteq> \<V>" "v \<in> \<V>" "v \<notin> W" for W a v
  proof-
    have ai: "list_invar a" "v \<notin> set (list_abstract a)"
      using a(1,4)
      by (auto simp add: P_def)
    note p = vlist.list_push_front[OF ai(1) a(3) ai(2)]
    have "P (insert v W) (rtf_init_step a v)"
      using p a(1)
      by (auto simp add: P_def rtf_init_step_def)
    moreover have "<list_assn a Ls * \<up>(list_invar a)> rtf_init_step_imp Ls v
                   <\<lambda>_. list_assn (rtf_init_step a v) Ls * \<up>(list_invar (rtf_init_step a v))>"
      unfolding rtf_init_step_imp_def rtf_init_step_def
      using p(1) ai(1)
      by (sep_auto heap: list_imp.list_push_front_rule[OF ai(1) a(3) ai(2)])
    ultimately show ?thesis
      by simp
  qed
  have "P {} list_empty"
    using vlist.list_empty
    by (simp add: P_def)
  note f = set_fold_imp_ruleD[OF list_vertex_fold_imp, where g = rtf_init_step
      and g_imp = "rtf_init_step_imp Ls" and P = P and R = "\<lambda> L. list_assn L Ls * \<up>(list_invar L)",
      OF this step]
  have ctx: "pr_ctx rtf.init_state =
             (list_vertex_fold rtf_init_step list_empty,
              list_first (list_vertex_fold rtf_init_step list_empty), False)"
    by (simp add: rtf.init_state_ctx rtf_init_ctx_def Let_def)
  show ?thesis
    unfolding Ci rtf_init_ctx_imp_def rtf_ctx_init_assn_def rtf_ctx_assn_def prod.case ctx
    using vlist.list_empty(1)
    by (sep_auto heap: f list_imp.list_first_rule cur_clear_rule cur_set_rule split: option.splits)
qed

end

text \<open>The imperative relabel-to-front strategy satisfies the contract of the imperative generic
      algorithm, which thus leaves a maximum flow in the backward residual capacities.\<close>

sublocale push_relabel_rtf_imp \<subseteq> rtf_imp: push_relabel_imp where select = rtf_select
  and init_ctx = rtf_init_ctx and ctx_invar = rtf_ctx_invar and select_imp = rtf_select_imp
  and init_ctx_imp = rtf_init_ctx_imp and ctx_assn = rtf_ctx_assn
  and ctx_init_assn = rtf_ctx_init_assn
proof(unfold_locales, goal_cases)
  case (1 st op c Si Ci)
  from 1 show ?case
    by (rule rtf_select_imp_rule)
next
  case (2 Si Ci)
  show ?case
    by (rule rtf_init_ctx_imp_rule)
qed

end
