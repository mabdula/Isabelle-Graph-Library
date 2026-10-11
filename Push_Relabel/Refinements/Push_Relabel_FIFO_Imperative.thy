theory Push_Relabel_FIFO_Imperative
  imports
    Push_Relabel_Discharge_Imperative
    Push_Relabel_FIFO
    Data_Structures.Bounded_Queue_Specs_Imp
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
begin

section \<open>Imperative FIFO Push-Relabel\<close>

text \<open>The context of the FIFO strategy in place: the queue, the current vertex in two references,
      and the handle of a structure over which an imperative vertex fold runs. The fold builds the
      initial queue. All updates of the context work in place.\<close>

locale push_relabel_fifo_imp_code = push_relabel_ops_imp_code fst_imp snd_imp s t num_verts emap_get_imp
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
  fixes queue_push_imp :: "'qi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and queue_pop_imp :: "'qi \<Rightarrow> 'v Heap"
    and queue_is_empty_imp :: "'qi \<Rightarrow> bool Heap"
    and vertex_fold_imp :: "'vs \<Rightarrow> ('v \<Rightarrow> unit Heap) \<Rightarrow> unit Heap"
begin

definition "fifo_after_push_imp Qi Cf Cu Si u v keep = do {
   (if v \<noteq> s \<and> v \<noteq> t
    then do { x \<leftarrow> ex_get_imp (pi_ex Si) v; if x \<le> 0 then queue_push_imp Qi v else return () }
    else return ());
   if keep then cur_set_imp Cf Cu u else cur_clear_imp Cf }"

definition "fifo_ctx_upd_imp op Qi Cf Cu Si u =
  (case op of
     Push_Fwd d \<Rightarrow> do {
       c \<leftarrow> emap_get_imp (pi_fwd Si) d;
       x \<leftarrow> ex_get_imp (pi_ex Si) u;
       v \<leftarrow> snd_imp (pi_ends Si) d;
       fifo_after_push_imp Qi Cf Cu Si u v (c < x) }
   | Push_Bwd d \<Rightarrow> do {
       c \<leftarrow> emap_get_imp (pi_bwd Si) d;
       x \<leftarrow> ex_get_imp (pi_ex Si) u;
       v \<leftarrow> fst_imp (pi_ends Si) d;
       fifo_after_push_imp Qi Cf Cu Si u v (c < x) }
   | Advance _ \<Rightarrow> cur_set_imp Cf Cu u
   | _ \<Rightarrow> do { queue_push_imp Qi u; cur_clear_imp Cf })"

definition "fifo_discharge_imp Qi Cf Cu Si u = do {
   op \<leftarrow> discharge_op_imp True Si u;
   fifo_ctx_upd_imp op Qi Cf Cu Si u;
   return op }"

definition "fifo_select_imp = (\<lambda> (Qi, Cf, Cu, Vi) Si. do {
   f \<leftarrow> cur_flag_imp Cf;
   if f then do { u \<leftarrow> cur_get_imp Cu; fifo_discharge_imp Qi Cf Cu Si u }
   else do {
     e \<leftarrow> queue_is_empty_imp Qi;
     if e then return Done
     else do { u \<leftarrow> queue_pop_imp Qi; fifo_discharge_imp Qi Cf Cu Si u } } })"

definition "fifo_init_step_imp Qi Si v =
  (if v \<noteq> s \<and> v \<noteq> t
   then do { x \<leftarrow> ex_get_imp (pi_ex Si) v; if 0 < x then queue_push_imp Qi v else return () }
   else return ())"

definition "fifo_init_ctx_imp = (\<lambda> (Qi, Cf, Cu, Vi) Si. do {
   vertex_fold_imp Vi (fifo_init_step_imp Qi Si);
   cur_clear_imp Cf })"

end

text \<open>The queue is a bounded queue in place, and the imperative vertex fold implements the
      functional one; its own data are described by @{term vset_assn}.\<close>

locale push_relabel_fifo_imp =
  push_relabel_ops_imp +
  push_relabel_fifo where fst = fst and snd = snd +
  push_relabel_fifo_imp_code fst_imp snd_imp s t num_verts emap_get_imp emap_upd_imp ex_get_imp ex_upd_imp
    label_get_imp label_upd_imp count_get_imp count_upd_imp out_current_imp out_has_imp
    out_move_imp out_reset_imp out_reset_to_imp in_current_imp in_has_imp in_move_imp in_reset_imp
    in_reset_to_imp gap_fold_imp edge_fold_imp queue_push_imp queue_pop_imp queue_is_empty_imp
    vertex_fold_imp +
  queue_imp: bounded_queue_imp qcap queue_invar queue_abstract queue_empty queue_push queue_pop
    queue_is_empty queue_assn queue_empty_imp queue_push_imp queue_pop_imp queue_is_empty_imp
  for queue_push_imp queue_pop_imp queue_is_empty_imp
    and vertex_fold_imp :: "'vs \<Rightarrow> _" and queue_assn queue_empty_imp +
  fixes vset_assn :: "'vs \<Rightarrow> assn"
  assumes queue_vertex_fold_imp:
    "\<And> Vi. set_fold_imp_rule \<V> (vset_assn Vi) queue_vertex_fold (vertex_fold_imp Vi)"
begin

definition "fifo_ctx_assn = (\<lambda> (Q, cur) (Qi, Cf, Cu, Vi).
   queue_assn Q Qi * cur_assn cur Cf Cu * vset_assn Vi)"

definition "fifo_ctx_init_assn = (\<lambda> (Qi, Cf, Cu, Vi).
   queue_assn queue_empty Qi * (\<exists>\<^sub>A cur. cur_assn cur Cf Cu) * vset_assn Vi)"

lemma fifo_after_push_imp_rule:
  assumes "ex_invar (pr_excess st)" "queue_invar Q" "length (queue_abstract Q) < qcap" "v \<in> \<V>"
  shows "<state_assn st Si * queue_assn Q Qi * cur_assn cur Cf Cu>
           fifo_after_push_imp Qi Cf Cu Si u v keep
         <\<lambda>_. state_assn st Si * queue_assn (prod.fst (fifo_after_push Q u v keep (pr_excess st))) Qi *
              cur_assn (prod.snd (fifo_after_push Q u v keep (pr_excess st))) Cf Cu>"
  unfolding fifo_after_push_imp_def fifo_after_push_def
  by (sep_auto heap: ex_get_state_rule[OF assms(1,4)] queue_imp.queue_push_rule[OF assms(2,3)]
                     cur_set_rule cur_clear_rule)

lemma fifo_ctx_upd_imp_rule:
  assumes "invar_state st" "queue_invar Q" "length (queue_abstract Q) < qcap" "u \<in> \<V>"
          "good_op st op"
  shows "<state_assn st Si * queue_assn Q Qi * cur_assn cur Cf Cu> fifo_ctx_upd_imp op Qi Cf Cu Si u
         <\<lambda>_. state_assn st Si *
              queue_assn (prod.fst (fifo_ctx_upd op Q u (pr_fwd st) (pr_bwd st) (pr_excess st))) Qi *
              cur_assn (prod.snd (fifo_ctx_upd op Q u (pr_fwd st) (pr_bwd st) (pr_excess st))) Cf Cu>"
proof-
  note I = invar_stateD[OF assms(1)]
  show ?thesis
  proof(cases op)
    case (Push_Fwd d)
    have d: "d \<in> \<E>"
      using good_op_push_edge[of st d] assms(5) by (simp add: Push_Fwd)
    show ?thesis
      unfolding Push_Fwd fifo_ctx_upd_imp_def fifo_ctx_upd_def pr_op.case
      using edge_verts[OF d]
      by (sep_auto heap: fwd_get_state_rule[OF I(1) d] ex_get_state_rule[OF I(2) assms(4)]
                         snd_state_rule[OF d] fifo_after_push_imp_rule[OF I(2) assms(2,3)])
  next
    case (Push_Bwd d)
    have d: "d \<in> \<E>"
      using good_op_push_edge[of st d] assms(5) by (simp add: Push_Bwd)
    show ?thesis
      unfolding Push_Bwd fifo_ctx_upd_imp_def fifo_ctx_upd_def pr_op.case
      using edge_verts[OF d]
      by (sep_auto heap: bwd_get_state_rule[OF I(13) d] ex_get_state_rule[OF I(2) assms(4)]
                         fst_state_rule[OF d] fifo_after_push_imp_rule[OF I(2) assms(2,3)])
  qed (sep_auto simp: fifo_ctx_upd_imp_def fifo_ctx_upd_def
                heap: cur_set_rule cur_clear_rule queue_imp.queue_push_rule[OF assms(2,3)])+
qed

lemma fifo_discharge_imp_rule:
  assumes "invar_state st" "queue_invar Q" "distinct (u # queue_abstract Q)"
          "set (u # queue_abstract Q) = {v. active_vertex s t (flow_abs st) v}"
          "fifo_discharge Q u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
             (pr_in st) = (op, (Q', cur'))"
  shows "<state_assn st Si * queue_assn Q Qi * cur_assn cur Cf Cu> fifo_discharge_imp Qi Cf Cu Si u
         <\<lambda>r. state_assn st Si * queue_assn Q' Qi * cur_assn cur' Cf Cu * \<up>(r = op)>"
proof-
  have u: "active_vertex s t (flow_abs st) u"
    using assms(4) by auto
  hence uV: "u \<in> \<V>"
    by (simp add: active_vertex_def)
  have opd: "discharge_op True (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
    and c: "fifo_ctx_upd op Q u (pr_fwd st) (pr_bwd st) (pr_excess st) = (Q', cur')"
    using assms(5) by (auto simp add: fifo_discharge_def Let_def)
  have good: "good_op st op"
    using discharge_op_props[OF assms(1) u opd] by simp
  have "set (u # queue_abstract Q) \<subseteq> \<V>"
    using assms(4) by (auto simp add: active_vertex_def)
  note room = queue_room[OF assms(3) this]
  have basic: "invar_basic st"
    using assms(1) by (simp add: invar_state_def)
  show ?thesis
    unfolding fifo_discharge_imp_def
    by (sep_auto heap: discharge_op_imp_rule[OF basic uV, where gap = True, unfolded opd]
                       fifo_ctx_upd_imp_rule[OF assms(1,2) room uV good] simp: c)
qed

lemma fifo_select_imp_rule:
  assumes "invar_state st" "fifo_ctx_invar st" "fifo.select_of st = (op, c)"
  shows "<state_assn st Si * fifo_ctx_assn (pr_ctx st) Ci> fifo_select_imp Ci Si
         <\<lambda>r. state_assn st Si * fifo_ctx_assn c Ci * \<up>(r = op)>"
proof-
  obtain Q cur where ctx: "pr_ctx st = (Q, cur)"
    by (cases "pr_ctx st")
  obtain Qi Cf Cu Vi where Ci: "Ci = (Qi, Cf, Cu, Vi)"
    by (cases Ci) auto
  have I: "queue_invar Q" "distinct (queue_abstract Q)"
          "\<forall> w. cur = Some w \<longrightarrow> w \<notin> set (queue_abstract Q)"
          "set (queue_abstract Q) \<union> set_option cur = {v. active_vertex s t (flow_abs st) v}"
    using assms(2) ctx by (simp_all add: fifo_ctx_invar_def)
  have sel: "fifo_select (Q, cur) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
               (pr_out st) (pr_in st) = (op, c)"
    using assms(3) ctx by (simp add: fifo.select_of_def)
  obtain Q' cur' where c: "c = (Q', cur')"
    by (cases c)
  show ?thesis
  proof(cases cur)
    case (Some u)
    have dis: "fifo_discharge Q u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                 (pr_in st) = (op, (Q', cur'))"
      using sel Some c by (simp add: fifo_select_def)
    have "distinct (u # queue_abstract Q)"
         "set (u # queue_abstract Q) = {v. active_vertex s t (flow_abs st) v}"
      using I Some by auto
    note r = fifo_discharge_imp_rule[OF assms(1) I(1) this dis]
    show ?thesis
      unfolding Ci ctx c fifo_select_imp_def fifo_ctx_assn_def prod.case Some
      by (sep_auto heap: cur_flag_rule cur_get_rule[of "Some u" u] r)
  next
    case None
    show ?thesis
    proof(cases "queue_is_empty Q")
      case True
      have "op = Done" "Q' = Q" "cur' = None"
        using sel None True c by (simp_all add: fifo_select_def)
      thus ?thesis
        unfolding Ci ctx c fifo_select_imp_def fifo_ctx_assn_def prod.case None
        by (sep_auto heap: cur_flag_rule queue_imp.queue_is_empty_rule[OF I(1)] simp: True)
    next
      case False
      have ne: "queue_abstract Q \<noteq> []"
        using queue.queue_is_empty[OF I(1)] False by simp
      obtain u Q0 where pop: "queue_pop Q = (u, Q0)"
        by (cases "queue_pop Q")
      have q: "queue_invar Q0" "u # queue_abstract Q0 = queue_abstract Q"
        using queue.queue_pop[OF I(1) ne] pop ne by simp_all
      have dis: "fifo_discharge Q0 u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                   (pr_in st) = (op, (Q', cur'))"
        using sel None False pop c by (simp add: fifo_select_def)
      have "distinct (u # queue_abstract Q0)"
           "set (u # queue_abstract Q0) = {v. active_vertex s t (flow_abs st) v}"
        using I None unfolding q(2) by simp_all
      note r = fifo_discharge_imp_rule[OF assms(1) q(1) this dis]
      show ?thesis
        unfolding Ci ctx c fifo_select_imp_def fifo_ctx_assn_def prod.case None
        by (sep_auto heap: cur_flag_rule queue_imp.queue_is_empty_rule[OF I(1)]
                           queue_imp.queue_pop_rule[OF I(1) ne] r simp: False pop)
    qed
  qed
qed

lemma fifo_init_ctx_imp_rule:
  "<state_assn fifo.init_state Si * fifo_ctx_init_assn Ci> fifo_init_ctx_imp Ci Si
   <\<lambda>_. state_assn fifo.init_state Si * fifo_ctx_assn (pr_ctx fifo.init_state) Ci>"
proof-
  obtain Qi Cf Cu Vi where Ci: "Ci = (Qi, Cf, Cu, Vi)"
    by (cases Ci) auto
  define x where "x = pr_excess fifo.init_state"
  have exi: "ex_invar x"
    using invar_stateD(2)[OF fifo.init_state_props(1)] by (simp add: x_def)
  define P where "P = (\<lambda> W Q. queue_invar Q \<and> distinct (queue_abstract Q) \<and>
                          set (queue_abstract Q) = {v \<in> W. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v})"
  have p0: "P {} queue_empty"
    using queue.queue_empty by (simp add: P_def)
  have step: "P (insert v W) (fifo_init_step x a v) \<and>
              <state_assn fifo.init_state Si * queue_assn a Qi> fifo_init_step_imp Qi Si v
              <\<lambda>_. state_assn fifo.init_state Si * queue_assn (fifo_init_step x a v) Qi>"
    if a: "P W a" "W \<subseteq> \<V>" "v \<in> \<V>" "v \<notin> W" for W a v
  proof-
    have aq: "queue_invar a" "distinct (queue_abstract a)" "set (queue_abstract a) \<subseteq> W"
      using a(1) by (auto simp add: P_def)
    have "length (queue_abstract a) = card (set (queue_abstract a))"
      using distinct_card[OF aq(2)] by simp
    also have "\<dots> \<le> card W"
      by (rule card_mono[OF finite_subset[OF a(2) \<V>_finite] aq(3)])
    also have "\<dots> < card \<V>"
      by (rule psubset_card_mono[OF \<V>_finite]) (use a(2-4) in auto)
    finally have room: "length (queue_abstract a) < qcap"
      using qcap by simp
    have "P (insert v W) (fifo_init_step x a v)"
      using queue.queue_push[OF aq(1) room, of v] a(1,4) by (auto simp add: P_def fifo_init_step_def)
    moreover have "<state_assn fifo.init_state Si * queue_assn a Qi> fifo_init_step_imp Qi Si v
                   <\<lambda>_. state_assn fifo.init_state Si * queue_assn (fifo_init_step x a v) Qi>"
      unfolding fifo_init_step_imp_def fifo_init_step_def x_def
      by (sep_auto heap: ex_get_state_rule[OF exi[unfolded x_def] a(3)]
                         queue_imp.queue_push_rule[OF aq(1) room])
    ultimately show ?thesis
      by simp
  qed
  note f = set_fold_imp_ruleD[OF queue_vertex_fold_imp, where g = "fifo_init_step x"
      and g_imp = "fifo_init_step_imp Qi Si" and P = P
      and R = "\<lambda> Q. state_assn fifo.init_state Si * queue_assn Q Qi", OF p0 step]
  have ctx: "pr_ctx fifo.init_state = (queue_vertex_fold (fifo_init_step x) queue_empty, None)"
    by (simp only: fifo.init_state_ctx) (simp add: fifo_init_ctx_def x_def)
  show ?thesis
    unfolding Ci fifo_init_ctx_imp_def fifo_ctx_init_assn_def fifo_ctx_assn_def prod.case ctx
    by (sep_auto heap: f cur_clear_rule)
qed

end

text \<open>The imperative FIFO strategy satisfies the contract of the imperative generic algorithm,
      which thus leaves a maximum flow in the backward residual capacities.\<close>

sublocale push_relabel_fifo_imp \<subseteq> fifo_imp: push_relabel_imp where select = fifo_select
  and init_ctx = fifo_init_ctx and ctx_invar = fifo_ctx_invar and select_imp = fifo_select_imp
  and init_ctx_imp = fifo_init_ctx_imp and ctx_assn = fifo_ctx_assn
  and ctx_init_assn = fifo_ctx_init_assn
proof(unfold_locales, goal_cases)
  case (1 st op c Si Ci)
  show ?case
    by (rule fifo_select_imp_rule[OF 1])
next
  case (2 Si Ci)
  show ?case
    by (rule fifo_init_ctx_imp_rule)
qed

end
