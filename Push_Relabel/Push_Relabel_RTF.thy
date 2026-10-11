theory Push_Relabel_RTF
  imports
    Push_Relabel_Discharge
    Data_Structures.Fixed_Univ_List_Specs
begin

section \<open>Relabel-to-Front Push-Relabel\<close>

text \<open>The context of the strategy is a list of all vertices except source and target, and a
      cursor into it, as in the AFP. The list is kept topologically sorted with respect to the
      admissible residual edges, and all vertices before the cursor are inactive. From the
      cursor on, the first active vertex is discharged until it becomes inactive. If it was
      relabelled during its discharge, it is then moved to the front of the list; in any case the
      scan continues at its successor. When the cursor runs off the end of the list, no vertex
      is active. There is no gap heuristic.

      The search for the next active vertex runs along the list and is bounded by the number of
      vertices. The initial list is built by a fold over the vertices. Its parameter
      @{term list_vertex_fold} has the same specification as @{term vertex_fold}, but a different
      accumulator type.\<close>

subsection \<open>Topological Order of the Admissible Edges\<close>

text \<open>The pairs of vertices joined by an admissible residual edge.\<close>

definition (in flow_network_spec) "adm_pair f l a b = (\<exists> e. admissible f l e \<and> fstv e = a \<and> sndv e = b)"

context push_relabel_ops_correct
begin

text \<open>After relabelling \<open>u\<close>, every admissible residual edge not leaving \<open>u\<close> was admissible
      before, and no residual edge entering \<open>u\<close> is admissible.\<close>

lemma relabel_admissible_tail:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
          "admissible f (relabel_effect f l u) e" "fstv e \<noteq> u"
  shows "admissible f l e"
proof(rule admissible_increased_labels[OF net_assms assms(2) _ _ assms(4)])
  show "\<And> x. x \<in> \<V> \<Longrightarrow> l x \<le> relabel_effect f l u x"
    using relabel_mono[OF net_assms assms(1-3)] .
  show "relabel_effect f l u (fstv e) = l (fstv e)"
    using assms(5) by (simp add: relabel_effect_def)
qed

lemma relabel_not_admissible_head:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u" "sndv e = u"
  shows "\<not> admissible f (relabel_effect f l u) e"
proof
  assume "admissible f (relabel_effect f l u) e"
  hence e: "e \<in> \<EE>" "rcap f e > 0"
           "relabel_effect f l u (fstv e) = relabel_effect f l u (sndv e) + 1"
    by (auto elim: admissibleE)
  note inc = relabel_increases[OF net_assms assms(1-3)]
  show False
  proof(cases "fstv e = u")
    case True
    thus False
      using e(3) assms(4) by simp
  next
    case False
    have "l (fstv e) \<le> l (sndv e) + 1"
      using assms(2) e(1,2) by (auto elim: valid_labellingE)
    moreover have "relabel_effect f l u (fstv e) = l (fstv e)"
      using False by (simp add: relabel_effect_def)
    ultimately show False
      using e(3) assms(4) inc by simp
  qed
qed

lemma push_sorted:
  assumes "push_precond s t f l e" "sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) xs"
  shows "sorted_wrt (\<lambda> a b. \<not> adm_pair (push_effect f e) l b a) xs"
  by (rule sorted_wrt_mono_rel[OF _ assms(2)])
     (auto simp add: adm_pair_def dest: push_admissible[OF net_assms assms(1)])

lemma relabel_sorted:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
          "distinct xs" "sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) xs"
  shows "sorted_wrt (\<lambda> a b. \<not> adm_pair f (relabel_effect f l u) b a) (u # remove1 u xs)"
proof-
  have rm: "remove1 u xs = filter (\<lambda> y. u \<noteq> y) xs"
    by (simp add: distinct_remove1_removeAll[OF assms(4)] removeAll_filter_not_eq)
  have old: "sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) (remove1 u xs)"
    unfolding rm by (rule sorted_wrt_filter[OF assms(5)])
  have rest: "sorted_wrt (\<lambda> a b. \<not> adm_pair f (relabel_effect f l u) b a) (remove1 u xs)"
  proof(rule sorted_wrt_mono_rel[OF _ old])
    fix a b
    assume ab: "a \<in> set (remove1 u xs)" "b \<in> set (remove1 u xs)" "\<not> adm_pair f l b a"
    have "b \<noteq> u"
      using ab(2) assms(4) by simp
    thus "\<not> adm_pair f (relabel_effect f l u) b a"
      using ab(3) relabel_admissible_tail[OF assms(1-3)] by (auto simp add: adm_pair_def)
  qed
  have "\<forall> y \<in> set (remove1 u xs). \<not> adm_pair f (relabel_effect f l u) y u"
    using relabel_not_admissible_head[OF assms(1-3)] by (auto simp add: adm_pair_def)
  thus ?thesis
    using rest by simp
qed

end

subsection \<open>The Strategy\<close>

locale push_relabel_rtf_spec =
  push_relabel_ops where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar +
  vlist: fixed_univ_list \<V> list_invar list_abstract list_empty list_push_front list_move_to_front
      list_first list_next
  for fst :: "'e \<Rightarrow> 'v"
  and emap_upd :: "'emap \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'emap"
  and ex_upd :: "'exc \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'exc"
  and label_upd :: "'lab \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lab"
  and count_upd :: "'cnt \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'cnt"
  and out_invar :: "'g \<Rightarrow> bool"
  and list_invar
  and list_abstract :: "'l \<Rightarrow> 'v list"
  and list_empty list_push_front list_move_to_front list_first list_next +
  fixes list_vertex_fold :: "('l \<Rightarrow> 'v \<Rightarrow> 'l) \<Rightarrow> 'l \<Rightarrow> 'l"
begin

text \<open>The first active vertex at or after \<open>u\<close>, looking at no more than \<open>n\<close> vertices.\<close>

fun rtf_scan where
  "rtf_scan L x 0 u = None"
| "rtf_scan L x (Suc n) u =
     (if 0 < ex_get x u then Some u
      else case list_next L u of None \<Rightarrow> None | Some w \<Rightarrow> rtf_scan L x n w)"

text \<open>One discharge step on the current vertex \<open>u\<close>. The flag records whether \<open>u\<close> has been
      relabelled during its discharge.\<close>

definition "rtf_discharge L u rel fw bw l og ig =
  (let op = discharge_op False fw bw l og ig u in
   (op, (L, Some u, case op of Relabel _ \<Rightarrow> True | _ \<Rightarrow> rel)))"

text \<open>When the current vertex \<open>u\<close> has become inactive, it is moved to the front iff it was
      relabelled, and the scan continues at its successor.\<close>

definition "rtf_select ctx fw bw x l cnt og ig =
  (case ctx of
     (L, None, rel) \<Rightarrow> (Done, (L, None, rel))
   | (L, Some u, rel) \<Rightarrow>
       (if 0 < ex_get x u then rtf_discharge L u rel fw bw l og ig
        else
          (let L' = (if rel then list_move_to_front L u else L) in
           case list_next L' u of
             None \<Rightarrow> (Done, (L', None, False))
           | Some w \<Rightarrow>
               (case rtf_scan L' x num_verts w of
                  None \<Rightarrow> (Done, (L', None, False))
                | Some w' \<Rightarrow> rtf_discharge L' w' False fw bw l og ig))))"

definition "rtf_init_step = (\<lambda> L v. if v \<noteq> s \<and> v \<noteq> t then list_push_front L v else L)"

definition "rtf_init_ctx fw bw x l og ig =
  (let L = list_vertex_fold rtf_init_step list_empty in (L, list_first L, False))"

lemmas [code] = rtf_scan.simps rtf_discharge_def rtf_select_def rtf_init_step_def rtf_init_ctx_def

text \<open>The invariant for a current vertex \<open>u\<close> in the list \<open>xs\<close>. If \<open>u\<close> has not been relabelled
      during its discharge, \<open>xs\<close> is sorted topologically with respect to the admissible residual
      edges and all vertices before \<open>u\<close> are inactive. If \<open>u\<close> has been relabelled, the list
      obtained by moving \<open>u\<close> to the front is sorted.\<close>

definition "rtf_cur_invar f l xs u rel =
  (if rel
   then u \<in> set xs \<and> sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) (u # remove1 u xs)
   else sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) xs \<and>
        (\<exists> ys zs. xs = ys @ u # zs \<and> (\<forall> v \<in> set ys. \<not> active_vertex s t f v)))"

text \<open>The list holds all vertices except source and target, and no vertex is active once the
      cursor has run off the end.\<close>

definition "rtf_ctx_invar st =
  (case pr_ctx st of (L, cur, rel) \<Rightarrow>
     list_invar L \<and> set (list_abstract L) = \<V> - {s, t} \<and>
     (case cur of
        None \<Rightarrow> (\<forall> v. \<not> active_vertex s t (flow_abs st) v)
      | Some u \<Rightarrow> rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) u rel))"

end

locale push_relabel_rtf =
  push_relabel_rtf_spec where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar +
  push_relabel_ops_correct where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar
  for fst :: "'e \<Rightarrow> 'v"
  and emap_upd :: "'emap \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'emap"
  and ex_upd :: "'exc \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'exc"
  and label_upd :: "'lab \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lab"
  and count_upd :: "'cnt \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'cnt"
  and out_invar :: "'g \<Rightarrow> bool" +
  assumes list_vertex_fold:
        "\<And> g acc. \<exists> vs. distinct vs \<and> set vs = \<V> \<and> list_vertex_fold g acc = foldl g acc vs"
begin

lemma rtf_scan_props:
  assumes "list_invar L" "list_abstract L = xs @ u # ys" "length (u # ys) \<le> n"
          "\<forall> v \<in> set xs. \<not> 0 < ex_get x v"
  shows "(rtf_scan L x n u = None \<longrightarrow> (\<forall> v \<in> set (list_abstract L). \<not> 0 < ex_get x v)) \<and>
         (\<forall> w. rtf_scan L x n u = Some w \<longrightarrow> 0 < ex_get x w \<and>
              (\<exists> xs' ys'. list_abstract L = xs' @ w # ys' \<and> (\<forall> v \<in> set xs'. \<not> 0 < ex_get x v)))"
  using assms(2-4)
proof(induction ys arbitrary: xs u n)
  case Nil
  obtain m where n: "n = Suc m"
    using Nil.prems(2) by (cases n) auto
  have nx: "list_next L u = None"
    using vlist.list_next[OF assms(1) Nil.prems(1)] by simp
  show ?case
  proof(cases "0 < ex_get x u")
    case True
    thus ?thesis
      using Nil.prems(1,3) by (auto simp add: n)
  next
    case False
    thus ?thesis
      using Nil.prems(1,3) nx by (auto simp add: n)
  qed
next
  case (Cons y ys)
  obtain m where n: "n = Suc m" "length (y # ys) \<le> m"
    using Cons.prems(2) by (cases n) auto
  have nx: "list_next L u = Some y"
    using vlist.list_next[OF assms(1) Cons.prems(1)] by simp
  show ?case
  proof(cases "0 < ex_get x u")
    case True
    thus ?thesis
      using Cons.prems(1,3) by (auto simp add: n(1))
  next
    case False
    have "list_abstract L = (xs @ [u]) @ y # ys" "\<forall> v \<in> set (xs @ [u]). \<not> 0 < ex_get x v"
      using Cons.prems(1,3) False by simp_all
    from Cons.IH[OF this(1) n(2) this(2)] show ?thesis
      using False nx by (simp add: n(1))
  qed
qed

lemma rtf_discharge_props:
  assumes "invar_state st" "list_invar L" "set (list_abstract L) = \<V> - {s, t}"
          "active_vertex s t (flow_abs st) u"
          "rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) u rel"
          "rtf_discharge L u rel (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op" "rtf_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
proof-
  note inv = invar_stateD[OF assms(1)]
  have dL: "distinct (list_abstract L)"
    using vlist.list_universe[OF assms(2)] by simp
  define rel' where "rel' = (case op of Relabel _ \<Rightarrow> True | _ \<Rightarrow> rel)"
  have opd: "discharge_op False (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
   and opc: "c = (L, Some u, rel')"
    using assms(6) by (auto simp add: rtf_discharge_def Let_def rel'_def)
  note dp = discharge_op_props[OF assms(1,4) opd]
  have good: "good_op st op"
    using dp by simp
  define st' where "st' = apply_op op st"
  have ctx': "rtf_ctx_invar (st'\<lparr>pr_ctx := c\<rparr>) \<longleftrightarrow>
              rtf_cur_invar (flow_abs st') (labels_abs st') (list_abstract L) u rel'"
    using assms(2,3) by (simp add: rtf_ctx_invar_def opc)
  have push_case: "rtf_cur_invar (flow_abs st') (labels_abs st') (list_abstract L) u rel"
    if pp: "push_precond s t (flow_abs st) (labels_abs st) e" and fu: "fstv e = u"
       and fl: "flow_abs st' = push_effect (flow_abs st) e"
       and lb: "labels_abs st' = labels_abs st" for e
  proof(cases rel)
    case True
    have h: "u \<in> set (list_abstract L) \<and>
             sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) (u # remove1 u (list_abstract L))"
      using assms(5) unfolding rtf_cur_invar_def if_P[OF True] .
    show ?thesis
      unfolding rtf_cur_invar_def if_P[OF True] fl lb
      using conjunct1[OF h] push_sorted[OF pp conjunct2[OF h]] by (rule conjI)
  next
    case False
    then obtain xs ys where I: "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a)
                                  (list_abstract L)"
      "list_abstract L = xs @ u # ys" "\<forall> v \<in> set xs. \<not> active_vertex s t (flow_abs st) v"
      using assms(5) by (auto simp add: rtf_cur_invar_def)
    have sorted': "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st') (labels_abs st') b a)
                     (list_abstract L)"
      using push_sorted[OF pp I(1)] fl lb by simp
    have pre': "\<forall> v \<in> set xs. \<not> active_vertex s t (flow_abs st') v"
    proof
      fix v
      assume v: "v \<in> set xs"
      show "\<not> active_vertex s t (flow_abs st') v"
      proof
        assume "active_vertex s t (flow_abs st') v"
        hence "v = sndv e"
          using push_active[OF net_assms pp] I(3) v fl by auto
        hence "adm_pair (flow_abs st) (labels_abs st) u v"
          using pp fu by (auto simp add: adm_pair_def push_precond_def)
        moreover have "\<not> adm_pair (flow_abs st) (labels_abs st) u v"
          using I(1,2) v by (auto simp add: sorted_wrt_append)
        ultimately show False
          by simp
      qed
    qed
    show ?thesis
      using False sorted' I(2) pre' by (auto simp add: rtf_cur_invar_def)
  qed
  have inv': "rtf_cur_invar (flow_abs st') (labels_abs st') (list_abstract L) u rel'"
  proof(cases op)
    case (Push_Fwd d)
    have pp: "push_precond s t (flow_abs st) (labels_abs st) (F d)"
      using good by (simp add: Push_Fwd good_op_def)
    have "rtf_cur_invar (flow_abs st') (labels_abs st') (list_abstract L) u rel"
    proof(rule push_case[OF pp])
      show "fstv (F d) = u"
        using dp Push_Fwd by simp
      show "flow_abs st' = push_effect (flow_abs st) (F d)" "labels_abs st' = labels_abs st"
        using push_impl_props(2,3)[OF assms(1) _ pp, of op d] Push_Fwd by (simp_all add: st'_def)
    qed
    thus ?thesis
      by (simp add: rel'_def Push_Fwd)
  next
    case (Push_Bwd d)
    have pp: "push_precond s t (flow_abs st) (labels_abs st) (B d)"
      using good by (simp add: Push_Bwd good_op_def)
    have "rtf_cur_invar (flow_abs st') (labels_abs st') (list_abstract L) u rel"
    proof(rule push_case[OF pp])
      show "fstv (B d) = u"
        using dp Push_Bwd by simp
      show "flow_abs st' = push_effect (flow_abs st) (B d)" "labels_abs st' = labels_abs st"
        using push_impl_props(2,3)[OF assms(1) _ pp, of op d] Push_Bwd by (simp_all add: st'_def)
    qed
    thus ?thesis
      by (simp add: rel'_def Push_Bwd)
  next
    case (Advance u')
    have uV: "u' \<in> \<V>"
     and ex: "\<exists> e. current_res st u' = Some e \<and> \<not> admissible (flow_abs st) (labels_abs st) e"
      using good Advance by (simp_all add: good_op_def)
    from ex obtain e where e: "current_res st u' = Some e" "\<not> admissible (flow_abs st) (labels_abs st) e"
      by (elim exE conjE) (rule that)
    note ap = advance_impl_props[OF assms(1) uV e]
    show ?thesis
      using assms(5) ap(2,3) by (simp add: st'_def rel'_def Advance)
  next
    case (Relabel u')
    have u': "u' = u"
      using opd Relabel by (auto simp add: discharge_op_def Let_def split: if_splits)
    have rp: "relabel_precond s t (flow_abs st) (labels_abs st) u"
      using good Relabel u' by (simp add: good_op_def)
    note rip = relabel_impl_props[OF assms(1) rp]
    have fl: "flow_abs st' = flow_abs st"
      using rip(3) Relabel u' by (simp add: st'_def)
    have lb: "labels_abs st' = relabel_effect (flow_abs st) (labels_abs st) u"
      using rip(2) Relabel u' by (simp add: st'_def)
    define xs0 where "xs0 = (if rel then u # remove1 u (list_abstract L) else list_abstract L)"
    have uL: "u \<in> set (list_abstract L)"
      using assms(5) by (auto simp add: rtf_cur_invar_def split: if_splits)
    have d0: "distinct xs0"
      using dL by (simp add: xs0_def)
    have s0: "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) xs0"
      using assms(5) by (auto simp add: rtf_cur_invar_def xs0_def split: if_splits)
    have r0: "remove1 u xs0 = remove1 u (list_abstract L)"
      by (simp add: xs0_def)
    have "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st') (labels_abs st') b a)
            (u # remove1 u (list_abstract L))"
      using relabel_sorted[OF inv(8,9) rp d0 s0] unfolding r0 fl lb .
    thus ?thesis
      using uL by (simp add: rtf_cur_invar_def rel'_def Relabel)
  next
    case (Relabel_Gap u')
    thus ?thesis
      using opd by (simp add: discharge_op_def Let_def split: if_splits)
  qed (use dp in simp)
  show "good_op st op" "rtf_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
    using good inv' ctx' by (simp_all add: st'_def apply_op_ctx)
qed

lemma rtf_select_props:
  assumes "invar_state st" "rtf_ctx_invar st"
          "rtf_select (pr_ctx st) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op" "op \<noteq> Done \<Longrightarrow> rtf_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
proof-
  note inv = invar_stateD[OF assms(1)]
  obtain L cur rel where ctx: "pr_ctx st = (L, cur, rel)"
    by (cases "pr_ctx st") auto
  have I: "list_invar L" "set (list_abstract L) = \<V> - {s, t}"
          "case cur of None \<Rightarrow> \<forall> v. \<not> active_vertex s t (flow_abs st) v
           | Some u \<Rightarrow> rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) u rel"
    using assms(2) ctx by (simp_all add: rtf_ctx_invar_def)
  have act: "\<And> L' v. set (list_abstract L') = \<V> - {s, t} \<Longrightarrow> v \<in> set (list_abstract L') \<Longrightarrow>
               active_vertex s t (flow_abs st) v \<longleftrightarrow> 0 < ex_get (pr_excess st) v"
    using inv(6) by (auto simp add: active_vertex_def)
  have actL: "\<And> L' v. set (list_abstract L') = \<V> - {s, t} \<Longrightarrow> active_vertex s t (flow_abs st) v \<Longrightarrow>
                v \<in> set (list_abstract L')"
    by (auto simp add: active_vertex_def)
  have "good_op st op \<and> (op \<noteq> Done \<longrightarrow> rtf_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
  proof(cases cur)
    case None
    hence "op = Done" "\<forall> v. \<not> active_vertex s t (flow_abs st) v"
      using assms(3) ctx I(3) by (simp_all add: rtf_select_def)
    thus ?thesis
      by (simp add: good_op_def)
  next
    case (Some u)
    note cS = this
    have cI: "rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) u rel"
      using I(3) cS by simp
    have uL: "u \<in> set (list_abstract L)"
      using cI by (auto simp add: rtf_cur_invar_def split: if_splits)
    show ?thesis
    proof(cases "0 < ex_get (pr_excess st) u")
      case True
      have sel: "rtf_discharge L u rel (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) =
                 (op, c)"
        using assms(3) ctx cS True by (simp add: rtf_select_def)
      have au: "active_vertex s t (flow_abs st) u"
        using act[OF I(2) uL] True by simp
      show ?thesis
        using rtf_discharge_props[OF assms(1) I(1,2) au cI sel] by simp
    next
      case False
      define L' where "L' = (if rel then list_move_to_front L u else L)"
      have sel: "rtf_select (pr_ctx st) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
                   (pr_counts st) (pr_out st) (pr_in st) =
                 (case list_next L' u of
                    None \<Rightarrow> (Done, (L', None, False))
                  | Some w \<Rightarrow>
                      (case rtf_scan L' (pr_excess st) num_verts w of
                         None \<Rightarrow> (Done, (L', None, False))
                       | Some w' \<Rightarrow> rtf_discharge L' w' False (pr_fwd st) (pr_bwd st) (pr_labels st)
                                     (pr_out st) (pr_in st)))"
        unfolding L'_def using ctx cS False by (cases rel) (simp_all add: rtf_select_def Let_def)
      have L'all: "list_invar L' \<and> set (list_abstract L') = \<V> - {s, t} \<and>
        sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) (list_abstract L') \<and>
        (\<exists> xs ys. list_abstract L' = xs @ u # ys \<and> (\<forall> v \<in> set xs. \<not> 0 < ex_get (pr_excess st) v))"
      proof(cases rel)
        case True
        note mv = vlist.list_move_to_front[OF I(1) uL]
        have dL: "distinct (list_abstract L)"
          using vlist.list_universe[OF I(1)] by simp
        have abs': "list_abstract L' = u # remove1 u (list_abstract L)"
          using mv(2) by (simp add: L'_def True)
        have "list_invar L'"
          using mv(1) by (simp add: L'_def True)
        moreover have "set (list_abstract L') = \<V> - {s, t}"
          using dL uL I(2) by (auto simp add: abs')
        moreover have "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) (list_abstract L')"
          using cI unfolding rtf_cur_invar_def if_P[OF True] abs' by (rule conjunct2)
        moreover have "\<exists> xs ys. list_abstract L' = xs @ u # ys \<and> (\<forall> v \<in> set xs. \<not> 0 < ex_get (pr_excess st) v)"
          by (rule exI[of _ "[]"], rule exI[of _ "remove1 u (list_abstract L)"]) (simp add: abs')
        ultimately show ?thesis
          by (intro conjI)
      next
        case False
        have L'L: "L' = L"
          by (simp add: L'_def False)
        have cI': "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) (list_abstract L) \<and>
                   (\<exists> ys zs. list_abstract L = ys @ u # zs \<and>
                      (\<forall> v \<in> set ys. \<not> active_vertex s t (flow_abs st) v))"
          using cI unfolding rtf_cur_invar_def if_not_P[OF False] .
        then obtain xs ys where xy: "list_abstract L = xs @ u # ys"
          "\<forall> v \<in> set xs. \<not> active_vertex s t (flow_abs st) v"
          by (elim conjE exE) (rule that)
        have ex0: "\<forall> v \<in> set xs. \<not> 0 < ex_get (pr_excess st) v"
          using xy(1,2) act[OF I(2)] by auto
        have "\<exists> xs ys. list_abstract L = xs @ u # ys \<and> (\<forall> v \<in> set xs. \<not> 0 < ex_get (pr_excess st) v)"
          by (rule exI, rule exI, rule conjI[OF xy(1) ex0])
        thus ?thesis
          unfolding L'L using I(1,2) conjunct1[OF cI'] by (intro conjI)
      qed
      have L': "list_invar L'" "set (list_abstract L') = \<V> - {s, t}"
        "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) (list_abstract L')"
        "\<exists> xs ys. list_abstract L' = xs @ u # ys \<and> (\<forall> v \<in> set xs. \<not> 0 < ex_get (pr_excess st) v)"
        using L'all by simp_all
      obtain xs ys where xy0: "list_abstract L' = xs @ u # ys"
        "\<forall> v \<in> set xs. \<not> 0 < ex_get (pr_excess st) v"
        using L'(4) by (elim exE conjE) (rule that)
      have xy: "list_abstract L' = xs @ u # ys" "\<forall> v \<in> set (xs @ [u]). \<not> 0 < ex_get (pr_excess st) v"
        using xy0 False by simp_all
      have dL': "distinct (list_abstract L')"
        using vlist.list_universe[OF L'(1)] by simp
      have nx: "list_next L' u = (case ys of [] \<Rightarrow> None | y # _ \<Rightarrow> Some y)"
        using vlist.list_next[OF L'(1) xy(1)] .
      show ?thesis
      proof(cases ys)
        case Nil
        have "op = Done"
          using assms(3) sel nx Nil by simp
        moreover have "\<forall> v. \<not> active_vertex s t (flow_abs st) v"
          using xy Nil act[OF L'(2)] actL[OF L'(2)] by auto
        ultimately show ?thesis
          by (simp add: good_op_def)
      next
        case (Cons w ys')
        have len: "length (w # ys') \<le> num_verts"
        proof-
          have "length (w # ys') \<le> length (list_abstract L')"
            using xy(1) Cons by simp
          also have "\<dots> = card (\<V> - {s, t})"
            using distinct_card[OF dL'] L'(2) by simp
          also have "\<dots> \<le> card \<V>"
            by (rule card_mono[OF \<V>_finite]) auto
          finally show ?thesis
            by (simp add: num_verts)
        qed
        have xy': "list_abstract L' = (xs @ [u]) @ w # ys'"
          using xy(1) Cons by simp
        note sc = rtf_scan_props[OF L'(1) xy' len xy(2)]
        show ?thesis
        proof(cases "rtf_scan L' (pr_excess st) num_verts w")
          case None
          have "op = Done"
            using assms(3) sel nx Cons None by simp
          moreover have "\<forall> v. \<not> active_vertex s t (flow_abs st) v"
          proof
            fix v
            have nz: "\<forall> v \<in> set (list_abstract L'). \<not> 0 < ex_get (pr_excess st) v"
              using sc None by simp
            show "\<not> active_vertex s t (flow_abs st) v"
            proof
              assume a: "active_vertex s t (flow_abs st) v"
              hence "v \<in> set (list_abstract L')"
                by (rule actL[OF L'(2)])
              thus False
                using a nz act[OF L'(2)] by simp
            qed
          qed
          ultimately show ?thesis
            by (simp add: good_op_def)
        next
          case (Some w')
          have "0 < ex_get (pr_excess st) w' \<and>
                (\<exists> xs' ys'. list_abstract L' = xs' @ w' # ys' \<and> (\<forall> v \<in> set xs'. \<not> 0 < ex_get (pr_excess st) v))"
            using sc Some by simp
          then obtain xs2 ys2 where w': "0 < ex_get (pr_excess st) w'" "list_abstract L' = xs2 @ w' # ys2"
            "\<forall> v \<in> set xs2. \<not> 0 < ex_get (pr_excess st) v"
            by (elim conjE exE) (rule that)
          have sel': "rtf_discharge L' w' False (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st)
                        (pr_in st) = (op, c)"
            using assms(3) sel nx Cons Some by simp
          have aw: "active_vertex s t (flow_abs st) w'"
            using act[OF L'(2), of w'] w'(1,2) by simp
          have ina: "\<forall> v \<in> set xs2. \<not> active_vertex s t (flow_abs st) v"
            using w'(2,3) act[OF L'(2)] by auto
          have "\<exists> ys zs. list_abstract L' = ys @ w' # zs \<and> (\<forall> v \<in> set ys. \<not> active_vertex s t (flow_abs st) v)"
            by (rule exI, rule exI, rule conjI[OF w'(2) ina])
          hence cI': "rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L') w' False"
            unfolding rtf_cur_invar_def if_False using L'(3) by (intro conjI)
          show ?thesis
            using rtf_discharge_props[OF assms(1) L'(1,2) aw cI' sel'] by simp
        qed
      qed
    qed
  qed
  thus "good_op st op" "op \<noteq> Done \<Longrightarrow> rtf_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
    by simp_all
qed


lemma rtf_init_fold:
  assumes "list_invar L" "distinct vs" "set vs \<subseteq> \<V>" "set vs \<inter> set (list_abstract L) = {}"
  shows "list_invar (foldl rtf_init_step L vs) \<and>
         list_abstract (foldl rtf_init_step L vs) =
         rev (filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t) vs) @ list_abstract L"
  using assms
proof(induction vs arbitrary: L)
  case (Cons v vs)
  show ?case
  proof(cases "v \<noteq> s \<and> v \<noteq> t")
    case True
    have v: "v \<in> \<V>" "v \<notin> set (list_abstract L)"
      using Cons.prems(3,4) by auto
    have p: "list_invar (list_push_front L v)" "list_abstract (list_push_front L v) = v # list_abstract L"
      using vlist.list_push_front[OF Cons.prems(1) v] by simp_all
    have "set vs \<inter> set (list_abstract (list_push_front L v)) = {}"
      using p(2) Cons.prems(2,4) by auto
    from Cons.IH[OF p(1) _ _ this] Cons.prems(2,3) show ?thesis
      using True p(2) by (simp add: rtf_init_step_def)
  next
    case False
    have "rtf_init_step L v = L"
      using False by (auto simp add: rtf_init_step_def)
    with Cons.IH[OF Cons.prems(1)] Cons.prems(2-4) show ?thesis
      using False by auto
  qed
qed simp

lemma rtf_init_ctx_props:
  assumes "invar_state st" "\<forall> d \<in> \<E>. flow_abs st d = init_flow s d" "labels_abs st = init_labels s"
          "pr_ctx st = rtf_init_ctx (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                         (pr_in st)"
  shows "rtf_ctx_invar st"
proof-
  obtain vs where vs: "distinct vs" "set vs = \<V>"
    "list_vertex_fold rtf_init_step list_empty = foldl rtf_init_step list_empty vs"
    using list_vertex_fold by blast
  define L where "L = list_vertex_fold rtf_init_step list_empty"
  have L: "list_invar L" "list_abstract L = rev (filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t) vs)"
    using rtf_init_fold[OF vlist.list_empty(1) vs(1)] vlist.list_empty(2) vs(2,3)
    by (simp_all add: L_def)
  have set: "set (list_abstract L) = \<V> - {s, t}"
    using L(2) vs(2) by auto
  have "\<And> a b. \<not> adm_pair (flow_abs st) (labels_abs st) a b"
    using init_flow_agree(4)[OF assms(2)] assms(3) by (simp add: adm_pair_def)
  hence sorted: "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) (list_abstract L)"
    by simp
  have ctx: "pr_ctx st = (L, list_first L, False)"
    using assms(4) by (simp add: rtf_init_ctx_def L_def Let_def)
  have cur: "case list_first L of None \<Rightarrow> \<forall> v. \<not> active_vertex s t (flow_abs st) v
             | Some u \<Rightarrow> rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) u False"
  proof(cases "list_abstract L")
    case Nil
    hence "list_first L = None"
      using vlist.list_first[OF L(1)] by simp
    moreover have "\<forall> v. \<not> active_vertex s t (flow_abs st) v"
      using set Nil by (auto simp add: active_vertex_def)
    ultimately show ?thesis
      by simp
  next
    case (Cons u us)
    hence "list_first L = Some u"
      using vlist.list_first[OF L(1)] by simp
    moreover have "\<exists> ys zs. list_abstract L = ys @ u # zs \<and>
                     (\<forall> v \<in> set ys. \<not> active_vertex s t (flow_abs st) v)"
      by (rule exI[of _ "[]"], rule exI[of _ us]) (simp add: Cons)
    ultimately show ?thesis
      using sorted by (simp add: rtf_cur_invar_def)
  qed
  show ?thesis
    using L(1) set cur by (simp add: rtf_ctx_invar_def ctx)
qed

end

text \<open>The generic algorithm with the relabel-to-front strategy.\<close>

sublocale push_relabel_rtf_spec \<subseteq> rtf: push_relabel_spec where select = rtf_select
  and init_ctx = rtf_init_ctx
  by unfold_locales

text \<open>The relabel-to-front strategy satisfies the contract of the generic algorithm, which thus
      computes a maximum flow.\<close>

sublocale push_relabel_rtf \<subseteq> rtf: push_relabel where select = rtf_select
  and init_ctx = rtf_init_ctx and ctx_invar = rtf_ctx_invar
proof(unfold_locales, goal_cases)
  case (1 st op c)
  show ?case
    by (rule rtf_select_props(1)[OF 1(1,2) 1(3)[unfolded rtf.select_of_def]])
next
  case (2 st op c)
  show ?case
    by (rule rtf_select_props(2)[OF 2(1,2) 2(3)[unfolded rtf.select_of_def] 2(4)])
next
  case (3 st)
  show ?case
    by (rule rtf_init_ctx_props[OF 3])
qed

end
