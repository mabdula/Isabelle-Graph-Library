theory Push_Relabel_FIFO
  imports
    Push_Relabel_Discharge
    Data_Structures.Bounded_Queue_Specs
begin

provenance ai


section \<open>FIFO Push-Relabel with the Gap Heuristic\<close>

text \<open>The context of the strategy is a queue of active vertices and the vertex currently being
      discharged, if any. A vertex is discharged until it becomes inactive or is relabelled; in
      the latter case it goes to the rear of the queue. A vertex enters the queue when a push
      makes it active. The queue never holds more than \<open>|V|\<close> vertices.

      The initial queue is built by a fold over the vertices. Its parameter
      @{term queue_vertex_fold} has the same specification as @{term vertex_fold}, but a different
      accumulator type.\<close>

locale \<^marker>\<open>provenance ai_human\<close> push_relabel_fifo_spec =
  push_relabel_ops where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar +
  queue: bounded_queue qcap queue_invar queue_abstract queue_empty queue_push queue_pop queue_is_empty
  for fst :: "'e \<Rightarrow> 'v"
  and emap_upd :: "'emap \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'emap"
  and ex_upd :: "'exc \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'exc"
  and label_upd :: "'lab \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lab"
  and count_upd :: "'cnt \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'cnt"
  and out_invar :: "'g \<Rightarrow> bool"
  and qcap queue_invar
  and queue_abstract :: "'q \<Rightarrow> 'v list"
  and queue_empty queue_push queue_pop queue_is_empty +
  fixes queue_vertex_fold :: "('q \<Rightarrow> 'v \<Rightarrow> 'q) \<Rightarrow> 'q \<Rightarrow> 'q"
begin

text \<open>After a push from \<open>u\<close> to \<open>v\<close>: \<open>v\<close> is enqueued if it was inactive, and \<open>u\<close> stays the
      current vertex iff it keeps some excess.\<close>

definition "fifo_after_push Q u v keep x =
  (if v \<noteq> s \<and> v \<noteq> t \<and> ex_get x v \<le> 0 then queue_push Q v else Q, if keep then Some u else None)"

definition "fifo_ctx_upd op Q u fw bw x =
  (case op of
     Push_Fwd d \<Rightarrow> fifo_after_push Q u (snd d) (emap_get fw d < ex_get x u) x
   | Push_Bwd d \<Rightarrow> fifo_after_push Q u (fst d) (emap_get bw d < ex_get x u) x
   | Advance _ \<Rightarrow> (Q, Some u)
   | _ \<Rightarrow> (queue_push Q u, None))"

definition "fifo_discharge Q u fw bw x l og ig =
  (let op = discharge_op True fw bw l og ig u in (op, fifo_ctx_upd op Q u fw bw x))"

definition "fifo_select ctx fw bw x l cnt og ig =
  (case ctx of
     (Q, Some u) \<Rightarrow> fifo_discharge Q u fw bw x l og ig
   | (Q, None) \<Rightarrow>
       if queue_is_empty Q then (Done, (Q, None))
       else (case queue_pop Q of (u, Q') \<Rightarrow> fifo_discharge Q' u fw bw x l og ig))"

definition "fifo_init_step x = (\<lambda> Q v. if v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v then queue_push Q v else Q)"

definition "fifo_init_ctx fw bw x l og ig = (queue_vertex_fold (fifo_init_step x) queue_empty, None)"

lemmas [code] = fifo_after_push_def fifo_ctx_upd_def fifo_discharge_def fifo_select_def
  fifo_init_step_def fifo_init_ctx_def

text \<open>The queue and the current vertex together hold every active vertex exactly once.\<close>

definition "fifo_ctx_invar st =
  (case pr_ctx st of (Q, cur) \<Rightarrow>
     queue_invar Q \<and> distinct (queue_abstract Q) \<and> (\<forall> u. cur = Some u \<longrightarrow> u \<notin> set (queue_abstract Q)) \<and>
     set (queue_abstract Q) \<union> set_option cur = {v. active_vertex s t (flow_abs st) v})"

end

locale \<^marker>\<open>provenance ai_human\<close> push_relabel_fifo =
  push_relabel_fifo_spec where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar +
  push_relabel_ops_correct where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar
  for fst :: "'e \<Rightarrow> 'v"
  and emap_upd :: "'emap \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'emap"
  and ex_upd :: "'exc \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'exc"
  and label_upd :: "'lab \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lab"
  and count_upd :: "'cnt \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'cnt"
  and out_invar :: "'g \<Rightarrow> bool" +
  assumes qcap: "card \<V> \<le> qcap"
      and queue_vertex_fold:
        "\<And> g acc. \<exists> vs. distinct vs \<and> set vs = \<V> \<and> queue_vertex_fold g acc = foldl g acc vs"
begin

lemma queue_room:
  "\<lbrakk>distinct (u # queue_abstract Q); set (u # queue_abstract Q) \<subseteq> \<V>\<rbrakk>
   \<Longrightarrow> length (queue_abstract Q) < qcap"
  using \<V>_finite card_mono[of \<V> "set (u # queue_abstract Q)"] distinct_card[of "u # queue_abstract Q"] qcap
  by simp

lemma queue_room_active:
  "\<lbrakk>distinct (u # queue_abstract Q);
    set (u # queue_abstract Q) = {w. active_vertex s t (flow_abs st) w}\<rbrakk>
   \<Longrightarrow> length (queue_abstract Q) < qcap"
  using queue_room[of u Q]
  by (auto simp: active_vertex_def)

text \<open>After a push from \<open>u\<close> to \<open>v\<close>, the new context holds the active vertices.\<close>

lemma fifo_after_push_props:
  assumes "invar_state st" "queue_invar Q" "distinct (u # queue_abstract Q)"
          "set (u # queue_abstract Q) = {w. active_vertex s t (flow_abs st) w}" "v \<noteq> u" "v \<in> \<V>"
          "\<And> w. active_vertex s t (flow_abs st') w \<longleftrightarrow>
                 (if w = u then keep
                  else if w = v then v \<noteq> s \<and> v \<noteq> t else active_vertex s t (flow_abs st) w)"
  shows "fifo_ctx_invar (st'\<lparr>pr_ctx := fifo_after_push Q u v keep (pr_excess st)\<rparr>)"
  using assms(1-6) queue_room_active[of u Q st] queue.queue_push[of Q] active_vertex_iff[of st v]
  by (auto simp: fifo_after_push_def fifo_ctx_invar_def assms(7) set_eq_iff split: if_splits)

lemma fifo_requeue_props:
  assumes "queue_invar Q" "distinct (u # queue_abstract Q)"
          "set (u # queue_abstract Q) = {w. active_vertex s t (flow_abs st) w}"
          "c = (Q, Some u) \<or> c = (queue_push Q u, None)"
  shows "fifo_ctx_invar (st\<lparr>pr_ctx := c\<rparr>)"
  using assms queue_room_active[of u Q st] queue.queue_push[of Q]
  by (elim disjE) (simp_all add: fifo_ctx_invar_def)

text \<open>After an operation of the discharge of \<open>u\<close>, the new context holds the active vertices.\<close>

lemma fifo_ctx_upd_props:
  assumes "invar_state st" "queue_invar Q" "distinct (u # queue_abstract Q)"
          "set (u # queue_abstract Q) = {w. active_vertex s t (flow_abs st) w}" "good_op st op" "op \<noteq> Done"
          "\<forall> d. op = Push_Fwd d \<longrightarrow> fst d = u"
          "\<forall> d. op = Push_Bwd d \<longrightarrow> snd d = u"
  shows "fifo_ctx_invar
           ((apply_op op st)\<lparr>pr_ctx := fifo_ctx_upd op Q u (pr_fwd st) (pr_bwd st) (pr_excess st)\<rparr>)"
proof(cases op)
  case (Push_Fwd d)
  thus ?thesis
    using assms(5,7) push_fstv_sndv[of "flow_abs st" "labels_abs st" "F d"]
    by (simp add: fifo_ctx_upd_def)
       (rule fifo_after_push_props[OF assms(1-4)];
        auto simp: assms(1) good_op_def push_fwd_impl_active \<EE>_def snd_E_V)
next
  case (Push_Bwd d)
  thus ?thesis
    using assms(5,8) push_fstv_sndv[of "flow_abs st" "labels_abs st" "B d"]
    by (simp add: fifo_ctx_upd_def)
       (rule fifo_after_push_props[OF assms(1-4)];
        auto simp: assms(1) good_op_def push_bwd_impl_active \<EE>_def fst_E_V)
qed (use assms(4,6) apply_op_active[OF assms(1,5)] in
     \<open>simp_all add: fifo_ctx_upd_def fifo_requeue_props[OF assms(2,3)]\<close>)

lemma fifo_discharge_props:
  assumes "fifo_discharge Q u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
             (pr_in st) = (op, c)"
          "invar_state st" "queue_invar Q" "distinct (u # queue_abstract Q)"
          "set (u # queue_abstract Q) = {v. active_vertex s t (flow_abs st) v}"
  shows "good_op st op \<and>
         (op \<noteq> Done \<longrightarrow> fifo_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
  using assms discharge_op_props[OF _ _ refl, of st u True] fifo_ctx_upd_props[of st Q u]
  by (auto simp: fifo_discharge_def Let_def apply_op_ctx)

lemma fifo_select_props:
  assumes "invar_state st" "fifo_ctx_invar st"
          "fifo_select (pr_ctx st) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op \<and>
         (op \<noteq> Done \<longrightarrow> fifo_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
proof(cases "pr_ctx st")
  case (Pair Q cur)
  hence I: "queue_invar Q" "distinct (queue_abstract Q)"
           "\<forall> w. cur = Some w \<longrightarrow> w \<notin> set (queue_abstract Q)"
           "set (queue_abstract Q) \<union> set_option cur = {v. active_vertex s t (flow_abs st) v}"
    using assms(2)
    by (simp_all add: fifo_ctx_invar_def)
  show ?thesis
  proof(cases cur)
    case None
    thus ?thesis
      using Pair I assms(1,3) queue.queue_is_empty[of Q] queue.queue_pop[of Q]
            fifo_discharge_props[of "prod.snd (queue_pop Q)" "prod.fst (queue_pop Q)" st]
      by (cases "queue_abstract Q") (simp_all add: fifo_select_def good_op_def[of st Done] prod.case_eq_if)
  qed (use Pair I assms fifo_discharge_props[of Q _ st] in \<open>simp add: fifo_select_def\<close>)
qed

lemma fifo_init_fold:
  assumes "queue_invar Q"
          "length (queue_abstract Q) +
           length (filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v) vs) \<le> qcap"
  shows "queue_invar (foldl (fifo_init_step x) Q vs) \<and>
         queue_abstract (foldl (fifo_init_step x) Q vs) =
         queue_abstract Q @ filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v) vs"
  using assms
proof(induction vs arbitrary: Q)
  case (Cons v vs)
  thus ?case
    using queue.queue_push[of Q]
    by (auto simp: fifo_init_step_def)
qed simp

lemma fifo_init_room: "\<lbrakk>distinct vs; set vs = \<V>\<rbrakk> \<Longrightarrow> length (filter P vs) \<le> qcap"
  using length_filter_le[of P vs] qcap distinct_card[of vs]
  by (simp del: length_filter_le)

lemma fifo_init_ctx_props:
  assumes "invar_state st"
          "pr_ctx st = fifo_init_ctx (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                         (pr_in st)"
  shows "fifo_ctx_invar st"
  using assms queue_vertex_fold[of "fifo_init_step (pr_excess st)" queue_empty] fifo_init_room queue.queue_empty
  by (auto simp: fifo_ctx_invar_def fifo_init_ctx_def active_vertex_def fifo_init_fold elim!: invar_props_elims)

end

text \<open>The generic algorithm with the FIFO strategy.\<close>

sublocale push_relabel_fifo_spec \<subseteq> fifo: push_relabel_spec where select = fifo_select
  and init_ctx = fifo_init_ctx
  by unfold_locales

text \<open>The FIFO strategy satisfies the contract of the generic algorithm, which thus computes a
      maximum flow.\<close>

sublocale push_relabel_fifo \<subseteq> fifo: push_relabel where select = fifo_select
  and init_ctx = fifo_init_ctx and ctx_invar = fifo_ctx_invar
  by unfold_locales (simp_all add: fifo.select_of_def fifo_select_props fifo_init_ctx_props)

end
