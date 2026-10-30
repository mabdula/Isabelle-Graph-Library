theory Push_Relabel_HL_Imperative
  imports
    Push_Relabel_Discharge_Imperative
    Push_Relabel_HL
    Data_Structures.Fixed_Univ_Buckets_Specs_Imp
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
begin

section \<open>Imperative Highest-Label Push-Relabel\<close>

text \<open>The context of the highest-label strategy in place: the buckets of active vertices, a
      reference holding the bound on the bucket numbers in use, the current vertex in two
      references, and the handle of a structure over which an imperative vertex fold runs. The fold
      builds the initial buckets. All updates of the context work in place. The search for the
      highest non-empty bucket writes the bucket number it finds into the bound.\<close>

locale push_relabel_hl_imp_code = push_relabel_ops_imp_code fst_imp snd_imp s t num_verts emap_get_imp
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
  fixes buckets_insert_imp :: "'bki \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> unit Heap"
    and buckets_remove_imp :: "'bki \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> unit Heap"
    and buckets_pick_imp :: "'bki \<Rightarrow> nat \<Rightarrow> 'v option Heap"
    and buckets_move_imp :: "'bki \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
    and vertex_fold_imp :: "'vs \<Rightarrow> ('v \<Rightarrow> unit Heap) \<Rightarrow> unit Heap"
begin

partial_function (heap) hl_find_imp :: "'bki \<Rightarrow> nat ref \<Rightarrow> nat \<Rightarrow> 'v option Heap" where
  "hl_find_imp Bi Br k = do {
     p \<leftarrow> buckets_pick_imp Bi k;
     (case p of
        Some u \<Rightarrow> do { Br := k; return (Some u) }
      | None \<Rightarrow> if k = 0 then return None else hl_find_imp Bi Br (k - 1)) }"

text \<open>Putting an active vertex into the bucket of its label.\<close>

definition "hl_insert_imp Bi Br Si v = do {
   lv \<leftarrow> label_get_imp (pi_lab Si) v;
   buckets_insert_imp Bi v lv;
   b \<leftarrow> !Br;
   Br := max b lv }"

definition "hl_after_push_imp Bi Br Cf Cu Si u v keep = do {
   (if v \<noteq> s \<and> v \<noteq> t
    then do { x \<leftarrow> ex_get_imp (pi_ex Si) v; if x \<le> 0 then hl_insert_imp Bi Br Si v else return () }
    else return ());
   if keep then cur_set_imp Cf Cu u else cur_clear_imp Cf }"

partial_function (heap) hl_lift_imp :: "'bki \<Rightarrow> nat ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "hl_lift_imp Bi Br k j =
     (if j = 0 \<or> j \<le> k then return ()
      else do {
        p \<leftarrow> buckets_pick_imp Bi j;
        (case p of
           None \<Rightarrow> hl_lift_imp Bi Br k (j - 1)
         | Some _ \<Rightarrow> do {
             buckets_move_imp Bi j (Suc num_verts);
             b \<leftarrow> !Br;
             Br := max b (Suc num_verts);
             hl_lift_imp Bi Br k (j - 1) }) })"

definition "hl_after_relabel_imp Bi Br Cf Cu Si u = do {
   k \<leftarrow> label_get_imp (pi_lab Si) u;
   (if k < num_verts
    then do {
      c \<leftarrow> count_get_imp (pi_cnt Si) k;
      if c = 1 then do { b \<leftarrow> !Br; hl_lift_imp Bi Br k (min b (num_verts - 1)) } else return () }
    else return ());
   cur_set_imp Cf Cu u }"

definition "hl_ctx_upd_imp op Bi Br Cf Cu Si u =
  (case op of
     Push_Fwd d \<Rightarrow> do {
       c \<leftarrow> emap_get_imp (pi_fwd Si) d;
       x \<leftarrow> ex_get_imp (pi_ex Si) u;
       v \<leftarrow> snd_imp (pi_ends Si) d;
       hl_after_push_imp Bi Br Cf Cu Si u v (c < x) }
   | Push_Bwd d \<Rightarrow> do {
       c \<leftarrow> emap_get_imp (pi_bwd Si) d;
       x \<leftarrow> ex_get_imp (pi_ex Si) u;
       v \<leftarrow> fst_imp (pi_ends Si) d;
       hl_after_push_imp Bi Br Cf Cu Si u v (c < x) }
   | Relabel_Gap _ \<Rightarrow> hl_after_relabel_imp Bi Br Cf Cu Si u
   | _ \<Rightarrow> cur_set_imp Cf Cu u)"

definition "hl_discharge_imp Bi Br Cf Cu Si u = do {
   op \<leftarrow> discharge_op_imp True Si u;
   hl_ctx_upd_imp op Bi Br Cf Cu Si u;
   return op }"

definition "hl_select_imp = (\<lambda> (Bi, Br, Cf, Cu, Vi) Si. do {
   f \<leftarrow> cur_flag_imp Cf;
   if f then do { u \<leftarrow> cur_get_imp Cu; hl_discharge_imp Bi Br Cf Cu Si u }
   else do {
     b \<leftarrow> !Br;
     r \<leftarrow> hl_find_imp Bi Br b;
     (case r of
        None \<Rightarrow> return Done
      | Some u \<Rightarrow> do {
          k \<leftarrow> !Br;
          buckets_remove_imp Bi u k;
          hl_discharge_imp Bi Br Cf Cu Si u }) } })"

definition "hl_init_step_imp Bi Br Si v =
  (if v \<noteq> s \<and> v \<noteq> t
   then do { x \<leftarrow> ex_get_imp (pi_ex Si) v; if 0 < x then hl_insert_imp Bi Br Si v else return () }
   else return ())"

definition "hl_init_ctx_imp = (\<lambda> (Bi, Br, Cf, Cu, Vi) Si. do {
   Br := 0;
   vertex_fold_imp Vi (hl_init_step_imp Bi Br Si);
   cur_clear_imp Cf })"

end

text \<open>The buckets are buckets in place, and the imperative vertex fold implements the functional
      one; its own data are described by @{term vset_assn}.\<close>

locale push_relabel_hl_imp =
  push_relabel_ops_imp +
  push_relabel_hl where fst = fst and snd = snd +
  push_relabel_hl_imp_code fst_imp snd_imp s t num_verts emap_get_imp emap_upd_imp ex_get_imp ex_upd_imp
    label_get_imp label_upd_imp count_get_imp count_upd_imp out_current_imp out_has_imp
    out_move_imp out_reset_imp out_reset_to_imp in_current_imp in_has_imp in_move_imp in_reset_imp
    in_reset_to_imp gap_fold_imp edge_fold_imp buckets_insert_imp buckets_remove_imp
    buckets_pick_imp buckets_move_imp vertex_fold_imp +
  bucket_imp: fixed_univ_buckets_imp \<V> "{..<2 * card \<V>}" buckets_invar buckets_abstract
    buckets_empty buckets_insert buckets_remove buckets_pick buckets_move buckets_assn
    buckets_empty_imp buckets_insert_imp buckets_remove_imp buckets_pick_imp buckets_move_imp
  for buckets_insert_imp buckets_remove_imp buckets_pick_imp buckets_move_imp
    and vertex_fold_imp :: "'vs \<Rightarrow> _" and buckets_assn buckets_empty_imp +
  fixes vset_assn :: "'vs \<Rightarrow> assn"
  assumes bucket_vertex_fold_imp:
    "\<And> Vi. set_fold_imp_rule \<V> (vset_assn Vi) bucket_vertex_fold (vertex_fold_imp Vi)"
begin

definition "hl_ctx_assn = (\<lambda> (Bk, b, cur) (Bi, Br, Cf, Cu, Vi).
   buckets_assn Bk Bi * Br \<mapsto>\<^sub>r b * cur_assn cur Cf Cu * vset_assn Vi)"

definition "hl_ctx_init_assn = (\<lambda> (Bi, Br, Cf, Cu, Vi).
   buckets_assn buckets_empty Bi * (\<exists>\<^sub>A b. Br \<mapsto>\<^sub>r b) * (\<exists>\<^sub>A cur. cur_assn cur Cf Cu) * vset_assn Vi)"

lemma hl_ctx_assn_tuple:
  "hl_ctx_assn (Bk, b, cur) (Bi, Br, Cf, Cu, Vi) =
   buckets_assn Bk Bi * Br \<mapsto>\<^sub>r b * cur_assn cur Cf Cu * vset_assn Vi"
  by (simp add: hl_ctx_assn_def)

lemma suc_num_verts_bound: "Suc num_verts < 2 * card \<V>"
  using card_V_ge_2
  by (simp add: num_verts)

lemma hl_find_imp_rule:
  assumes "buckets_invar Bk" "k < 2 * card \<V>"
  shows "<buckets_assn Bk Bi * Br \<mapsto>\<^sub>r b> hl_find_imp Bi Br k
         <\<lambda>r. buckets_assn Bk Bi *
              Br \<mapsto>\<^sub>r (case hl_find Bk k of None \<Rightarrow> b | Some ku \<Rightarrow> prod.fst ku) *
              \<up>(r = map_option prod.snd (hl_find Bk k))>"
  using assms(2)
proof(induction k)
  case 0
  show ?case
    by (subst hl_find_imp.simps)
       (sep_auto heap: bucket_imp.buckets_pick_rule[OF assms(1) 0[folded lessThan_iff]] split: option.splits)
next
  case (Suc k)
  show ?case
    by (subst hl_find_imp.simps, cases "buckets_pick Bk (Suc k)")
       (sep_auto heap: bucket_imp.buckets_pick_rule[OF assms(1) Suc.prems[folded lessThan_iff]]
                       Suc.IH[OF Suc_lessD[OF Suc.prems]])+
qed

lemma hl_insert_imp_rule:
  assumes "label_invar (pr_labels st)" "buckets_invar Bk" "v \<in> \<V>" "buckets_abstract Bk v = None"
          "label_get (pr_labels st) v < 2 * card \<V>"
  shows "<state_assn st Si * buckets_assn Bk Bi * Br \<mapsto>\<^sub>r b> hl_insert_imp Bi Br Si v
         <\<lambda>_. state_assn st Si * buckets_assn (buckets_insert Bk v (label_get (pr_labels st) v)) Bi *
              Br \<mapsto>\<^sub>r max b (label_get (pr_labels st) v)>"
  unfolding hl_insert_imp_def
  by (sep_auto heap: label_get_state_rule[OF assms(1,3)]
                     bucket_imp.buckets_insert_rule[OF assms(2,3) assms(5)[folded lessThan_iff] assms(4)])

lemma hl_after_push_imp_rule:
  assumes "invar_state st" "buckets_invar Bk" "v \<in> \<V>"
          "v \<noteq> s \<and> v \<noteq> t \<and> ex_get (pr_excess st) v \<le> 0
           \<Longrightarrow> buckets_abstract Bk v = None"
  shows "<state_assn st Si * hl_ctx_assn (Bk, b, cur) (Bi, Br, Cf, Cu, Vi)>
           hl_after_push_imp Bi Br Cf Cu Si u v keep
         <\<lambda>_. state_assn st Si *
              hl_ctx_assn (hl_after_push Bk b u v keep (pr_excess st) (pr_labels st)) (Bi, Br, Cf, Cu, Vi)>"
proof-
  note inv = invar_basic_maps[OF assms(1)[unfolded invar_state_def, THEN conjunct1]]
  show ?thesis
  proof(cases "v \<noteq> s \<and> v \<noteq> t \<and> ex_get (pr_excess st) v \<le> 0")
    case True
    note ins = hl_insert_imp_rule[OF inv(4) assms(2,3) assms(4)[OF True] label_bound[OF assms(1,3)]]
    show ?thesis
      unfolding hl_after_push_imp_def hl_after_push_def Let_def hl_ctx_assn_tuple
      using True
      by (sep_auto heap: ex_get_state_rule[OF inv(3) assms(3)] ins cur_set_rule cur_clear_rule
                   simp: hl_ctx_assn_tuple)
  next
    case False
    show ?thesis
      unfolding hl_after_push_imp_def hl_after_push_def Let_def hl_ctx_assn_tuple
      using False
      by (sep_auto heap: ex_get_state_rule[OF inv(3) assms(3)] cur_set_rule cur_clear_rule
                   simp: hl_ctx_assn_tuple)
  qed
qed

lemma hl_lift_imp_rule:
  assumes "buckets_invar Bk" "j < num_verts"
  shows "<buckets_assn Bk Bi * Br \<mapsto>\<^sub>r b> hl_lift_imp Bi Br k j
         <\<lambda>_. buckets_assn (prod.fst (hl_lift Bk b k j)) Bi * Br \<mapsto>\<^sub>r prod.snd (hl_lift Bk b k j)>"
  using assms
proof(induction j arbitrary: Bk b)
  case 0
  show ?case
    by (subst hl_lift_imp.simps) sep_auto
next
  case (Suc j)
  have K: "Suc j \<in> {..<2 * card \<V>}" "Suc num_verts \<in> {..<2 * card \<V>}" "Suc j \<noteq> Suc num_verts"
    using Suc.prems(2) suc_num_verts_bound
    by auto
  note j = Suc_lessD[OF Suc.prems(2)]
  show ?case
  proof(cases "Suc j \<le> k")
    case True
    thus ?thesis
      by (subst hl_lift_imp.simps) sep_auto
  next
    case False
    show ?thesis
    proof(cases "buckets_pick Bk (Suc j)")
      case None
      show ?thesis
        using False
        by (subst hl_lift_imp.simps)
           (sep_auto heap: bucket_imp.buckets_pick_rule[OF Suc.prems(1) K(1)] Suc.IH[OF Suc.prems(1) j]
                     simp: None)
    next
      case (Some w)
      note mv = bucket.buckets_move(1)[OF Suc.prems(1) K]
      show ?thesis
        using False
        by (subst hl_lift_imp.simps)
           (sep_auto heap: bucket_imp.buckets_pick_rule[OF Suc.prems(1) K(1)]
                           bucket_imp.buckets_move_rule[OF Suc.prems(1) K] Suc.IH[OF mv j] simp: Some)
    qed
  qed
qed

lemma hl_after_relabel_imp_rule:
  assumes "invar_state st" "buckets_invar Bk" "u \<in> \<V>"
  shows "<state_assn st Si * hl_ctx_assn (Bk, b, cur) (Bi, Br, Cf, Cu, Vi)>
           hl_after_relabel_imp Bi Br Cf Cu Si u
         <\<lambda>_. state_assn st Si *
              hl_ctx_assn (hl_after_relabel Bk b u (pr_labels st) (pr_counts st)) (Bi, Br, Cf, Cu, Vi)>"
proof-
  note inv = invar_basic_maps[OF assms(1)[unfolded invar_state_def, THEN conjunct1]]
  define k where "k = label_get (pr_labels st) u"
  show ?thesis
  proof(cases "k < num_verts")
    case True
    note kT = True
    have kb: "label_get (pr_labels st) u < 2 * card \<V>"
      using kT num_verts
      by (simp add: k_def)
    show ?thesis
    proof(cases "count_get (pr_counts st) k = 1")
      case True
      have m: "min b (num_verts - 1) < num_verts"
        using card_V_ge_2 num_verts
        by simp
      obtain B2 b2 where h: "hl_lift Bk b k (min b (num_verts - 1)) = (B2, b2)"
        by (cases "hl_lift Bk b k (min b (num_verts - 1))") auto
      show ?thesis
        unfolding hl_after_relabel_imp_def hl_after_relabel_def Let_def hl_ctx_assn_tuple
        using kT True h
        by (sep_auto heap: label_get_state_rule[OF inv(4) assms(3)] count_get_state_rule[OF inv(5) kb]
                           hl_lift_imp_rule[OF assms(2) m] cur_set_rule simp: k_def hl_ctx_assn_tuple)
    next
      case False
      show ?thesis
        unfolding hl_after_relabel_imp_def hl_after_relabel_def Let_def hl_ctx_assn_tuple
        using kT False
        by (sep_auto heap: label_get_state_rule[OF inv(4) assms(3)] count_get_state_rule[OF inv(5) kb]
                           cur_set_rule simp: k_def hl_ctx_assn_tuple)
    qed
  next
    case False
    show ?thesis
      unfolding hl_after_relabel_imp_def hl_after_relabel_def Let_def hl_ctx_assn_tuple
      using False
      by (sep_auto heap: label_get_state_rule[OF inv(4) assms(3)] cur_set_rule simp: k_def hl_ctx_assn_tuple)
  qed
qed

lemma hl_ctx_upd_imp_rule:
  assumes "invar_state st" "buckets_invar Bk" "u \<in> \<V>" "good_op st op"
          "\<And> w. active_vertex s t (flow_abs st) w
                 \<longleftrightarrow> buckets_abstract Bk w \<noteq> None \<or> w = u"
  shows "<state_assn st Si * hl_ctx_assn (Bk, b, cur) (Bi, Br, Cf, Cu, Vi)>
           hl_ctx_upd_imp op Bi Br Cf Cu Si u
         <\<lambda>_. state_assn st Si *
              hl_ctx_assn (hl_ctx_upd op Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
                             (pr_counts st)) (Bi, Br, Cf, Cu, Vi)>"
proof-
  note inv = invar_basic_maps[OF assms(1)[unfolded invar_state_def, THEN conjunct1]]
  have none: "buckets_abstract Bk v = None"
    if "v \<in> \<V>" "v \<noteq> s \<and> v \<noteq> t \<and> ex_get (pr_excess st) v \<le> 0" for v
    using assms(1) assms(5)[of v] that
    by (auto elim!: invar_props_elims simp add: active_vertex_def)
  show ?thesis
  proof(cases op)
    case (Push_Fwd d)
    hence d: "d \<in> \<E>"
      using good_op_push_edge[of st d] assms(4)
      by simp
    note v = conjunct2[OF edge_verts[OF d]]
    show ?thesis
      unfolding Push_Fwd hl_ctx_upd_imp_def hl_ctx_upd_def pr_op.case
      by (sep_auto heap: fwd_get_state_rule[OF inv(1) d] ex_get_state_rule[OF inv(3) assms(3)]
                         snd_state_rule[OF d] hl_after_push_imp_rule[OF assms(1,2) v none[OF v]])
  next
    case (Push_Bwd d)
    hence d: "d \<in> \<E>"
      using good_op_push_edge[of st d] assms(4)
      by simp
    note v = conjunct1[OF edge_verts[OF d]]
    show ?thesis
      unfolding Push_Bwd hl_ctx_upd_imp_def hl_ctx_upd_def pr_op.case
      by (sep_auto heap: bwd_get_state_rule[OF inv(2) d] ex_get_state_rule[OF inv(3) assms(3)]
                         fst_state_rule[OF d] hl_after_push_imp_rule[OF assms(1,2) v none[OF v]])
  next
    case (Relabel_Gap w)
    from assms(1-3) show ?thesis
      unfolding Relabel_Gap hl_ctx_upd_imp_def hl_ctx_upd_def pr_op.case
      by (rule hl_after_relabel_imp_rule)
  qed (sep_auto simp: hl_ctx_upd_imp_def hl_ctx_upd_def hl_ctx_assn_tuple heap: cur_set_rule)+
qed

lemma hl_discharge_imp_rule:
  assumes "invar_state st" "buckets_invar Bk"
          "\<And> w. active_vertex s t (flow_abs st) w
                 \<longleftrightarrow> buckets_abstract Bk w \<noteq> None \<or> w = u"
          "hl_discharge Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
  shows "<state_assn st Si * hl_ctx_assn (Bk, b, cur) (Bi, Br, Cf, Cu, Vi)>
           hl_discharge_imp Bi Br Cf Cu Si u
         <\<lambda>r. state_assn st Si * hl_ctx_assn c (Bi, Br, Cf, Cu, Vi) * \<up>(r = op)>"
proof-
  have u: "active_vertex s t (flow_abs st) u" "u \<in> \<V>"
    using assms(3)[of u]
    by (simp_all add: active_vertex_def)
  have opd: "discharge_op True (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
    and c: "hl_ctx_upd op Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st) = c"
    using assms(4)
    by (auto simp add: hl_discharge_def Let_def)
  note good = conjunct1[OF discharge_op_props[OF assms(1) u(1) opd]]
  show ?thesis
    unfolding hl_discharge_imp_def
    by (sep_auto heap: discharge_op_imp_rule[OF assms(1)[unfolded invar_state_def, THEN conjunct1] u(2),
                                             where gap = True, unfolded opd]
                       hl_ctx_upd_imp_rule[OF assms(1,2) u(2) good assms(3)] simp: c)
qed

text \<open>What the context invariant gives the discharge of the current or of the highest vertex.\<close>

lemma hl_ctx_invar_cur:
  assumes "hl_ctx_invar st" "pr_ctx st = (Bk, b, cur)"
  shows "buckets_invar Bk" "b < 2 * card \<V>"
        "cur = Some u
         \<Longrightarrow> active_vertex s t (flow_abs st) w
             \<longleftrightarrow> buckets_abstract Bk w \<noteq> None \<or> w = u"
        "\<lbrakk>cur = None; buckets_abstract Bk u = Some k\<rbrakk>
         \<Longrightarrow> active_vertex s t (flow_abs st) w
             \<longleftrightarrow> buckets_abstract (buckets_remove Bk u k) w \<noteq> None \<or> w = u"
  using assms bucket.buckets_remove[of Bk u k]
  by (auto simp: hl_ctx_invar_def)

lemma hl_select_imp_rule:
  assumes "invar_state st" "hl_ctx_invar st" "hl.select_of st = (op, c)"
  shows "<state_assn st Si * hl_ctx_assn (pr_ctx st) Ci> hl_select_imp Ci Si
         <\<lambda>r. state_assn st Si * hl_ctx_assn c Ci * \<up>(r = op)>"
proof-
  obtain Bk b cur Bi Br Cf Cu Vi where ctx: "pr_ctx st = (Bk, b, cur)" and Ci: "Ci = (Bi, Br, Cf, Cu, Vi)"
    by (cases "pr_ctx st" rule: prod_cases3, cases Ci rule: prod_cases5) auto
  note I = hl_ctx_invar_cur[OF assms(2) ctx]
  have sel: "hl_select (Bk, b, cur) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
               (pr_counts st) (pr_out st) (pr_in st) = (op, c)"
    using assms(3) ctx
    by (simp add: hl.select_of_def)
  show ?thesis
  proof(cases cur)
    case (Some u)
    have "hl_discharge Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
            (pr_out st) (pr_in st) = (op, c)"
      using sel Some
      by (simp add: hl_select_def)
    note r = hl_discharge_imp_rule[OF assms(1) I(1) I(3)[OF Some] this]
    show ?thesis
      unfolding Ci ctx hl_select_imp_def prod.case Some hl_ctx_assn_tuple
      by (sep_auto heap: cur_flag_rule cur_get_rule[of "Some u" u] r[unfolded hl_ctx_assn_tuple])
  next
    case None
    note cN = this
    note find = hl_find_imp_rule[OF I(1,2)]
    show ?thesis
    proof(cases "hl_find Bk b")
      case None
      have "op = Done" "c = (Bk, b, None)"
        using sel cN None
        by (simp_all add: hl_select_def)
      thus ?thesis
        unfolding Ci ctx hl_select_imp_def prod.case cN hl_ctx_assn_tuple
        by (sep_auto heap: cur_flag_rule find simp: None hl_ctx_assn_tuple)
    next
      case (Some ku)
      then obtain k u where f: "hl_find Bk b = Some (k, u)"
        by (cases ku) auto
      have uk: "buckets_abstract Bk u = Some k"
        using I(1,2) f hl_find_props[of Bk b]
        by simp
      define B1 where "B1 = buckets_remove Bk u k"
      have "hl_discharge B1 k u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
              (pr_counts st) (pr_out st) (pr_in st) = (op, c)"
        using sel cN f
        by (simp add: hl_select_def B1_def)
      note r = hl_discharge_imp_rule[OF assms(1) bucket.buckets_remove(1)[OF I(1) uk, folded B1_def]
                                       I(4)[OF cN uk, folded B1_def] this]
      have rm_imp: "ua = u
                    \<Longrightarrow> <buckets_assn Bk Bi> buckets_remove_imp Bi ua k <\<lambda>_. buckets_assn B1 Bi>"
        for ua
        using bucket_imp.buckets_remove_rule[OF I(1) uk]
        by (simp add: B1_def)
      have r': "ua = u \<Longrightarrow>
                <state_assn st Si * (buckets_assn B1 Bi * Br \<mapsto>\<^sub>r k * cur_assn cur0 Cf Cu * vset_assn Vi)>
                  hl_discharge_imp Bi Br Cf Cu Si ua
                <\<lambda>r. state_assn st Si * hl_ctx_assn c (Bi, Br, Cf, Cu, Vi) * \<up>(r = op)>" for ua cur0
        using r[unfolded hl_ctx_assn_tuple]
        by simp
      show ?thesis
        unfolding Ci ctx hl_select_imp_def prod.case cN hl_ctx_assn_tuple
        by (sep_auto heap: cur_flag_rule find[unfolded f, simplified] rm_imp r')
    qed
  qed
qed

lemma hl_init_ctx_imp_rule:
  "<state_assn hl.init_state Si * hl_ctx_init_assn Ci> hl_init_ctx_imp Ci Si
   <\<lambda>_. state_assn hl.init_state Si * hl_ctx_assn (pr_ctx hl.init_state) Ci>"
proof-
  obtain Bi Br Cf Cu Vi where Ci: "Ci = (Bi, Br, Cf, Cu, Vi)"
    by (cases Ci) auto
  define x where "x = pr_excess hl.init_state"
  define l where "l = pr_labels hl.init_state"
  note inv = invar_basic_maps[OF hl.init_state_props(1)[unfolded invar_state_def, THEN conjunct1]]
  define P where "P = (\<lambda> W (Bk, b :: nat). buckets_invar Bk \<and>
                          (\<forall> w. buckets_abstract Bk w \<noteq> None \<longrightarrow> w \<in> W))"
  define R where "R = (\<lambda> (Bk, b). state_assn hl.init_state Si * buckets_assn Bk Bi * Br \<mapsto>\<^sub>r b)"
  have step: "P (insert v W) (hl_init_step x l a v) \<and>
              <R a> hl_init_step_imp Bi Br Si v <\<lambda>_. R (hl_init_step x l a v)>"
    if a: "P W a" "W \<subseteq> \<V>" "v \<in> \<V>" "v \<notin> W" for W a v
  proof-
    obtain Bk b where ab: "a = (Bk, b)"
      by (cases a) auto
    have aq: "buckets_invar Bk" "buckets_abstract Bk v = None"
      using a(1,4)
      by (auto simp add: P_def ab)
    note ins = hl_insert_imp_rule[OF inv(4) aq(1) a(3) aq(2) label_bound[OF hl.init_state_props(1) a(3)]]
    have "P (insert v W) (hl_init_step x l a v)"
      using aq a(1,3) hl.init_state_props(1) label_bound[of hl.init_state v] buckets_insert_lt[of Bk v]
      by (auto simp add: P_def ab hl_init_step_def l_def)
    moreover have "<R (Bk, b)> hl_init_step_imp Bi Br Si v <\<lambda>_. R (hl_init_step x l (Bk, b) v)>"
      unfolding hl_init_step_imp_def hl_init_step_def x_def l_def R_def prod.case
      by (sep_auto heap: ex_get_state_rule[OF inv(3) a(3)] ins)
    ultimately show ?thesis
      by (simp add: ab)
  qed
  have "P {} (buckets_empty, 0)"
    using bucket.buckets_empty
    by (simp add: P_def)
  note f = set_fold_imp_ruleD[OF bucket_vertex_fold_imp, where g = "hl_init_step x l"
      and g_imp = "hl_init_step_imp Bi Br Si" and P = P
      and R = R, OF this step]
  obtain Bk b where fold: "bucket_vertex_fold (hl_init_step x l) (buckets_empty, 0) = (Bk, b)"
    by (cases "bucket_vertex_fold (hl_init_step x l) (buckets_empty, 0)") auto
  have ctx: "pr_ctx hl.init_state = (Bk, b, None)"
    using fold
    by (simp only: hl.init_state_ctx) (simp add: hl_init_ctx_def x_def l_def)
  show ?thesis
    unfolding Ci hl_init_ctx_imp_def hl_ctx_init_assn_def ctx prod.case hl_ctx_assn_tuple
    by (sep_auto heap: f[unfolded fold R_def prod.case] cur_clear_rule)
qed

end

text \<open>The imperative highest-label strategy satisfies the contract of the imperative generic
      algorithm, which thus leaves a maximum flow in the backward residual capacities.\<close>

sublocale push_relabel_hl_imp \<subseteq> hl_imp: push_relabel_imp where select = hl_select
  and init_ctx = hl_init_ctx and ctx_invar = hl_ctx_invar and select_imp = hl_select_imp
  and init_ctx_imp = hl_init_ctx_imp and ctx_assn = hl_ctx_assn
  and ctx_init_assn = hl_ctx_init_assn
proof(unfold_locales, goal_cases)
  case (1 st op c Si Ci)
  from 1 show ?case
    by (rule hl_select_imp_rule)
next
  case (2 Si Ci)
  show ?case
    by (rule hl_init_ctx_imp_rule)
qed

end
