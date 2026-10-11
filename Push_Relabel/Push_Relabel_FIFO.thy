theory Push_Relabel_FIFO
  imports
    Push_Relabel_Discharge
    Data_Structures.Bounded_Queue_Specs
begin

section \<open>FIFO Push-Relabel with the Gap Heuristic\<close>

text \<open>The context of the strategy is a queue of active vertices and the vertex currently being
      discharged, if any. A vertex is discharged until it becomes inactive or is relabelled; in
      the latter case it goes to the rear of the queue. A vertex enters the queue when a push
      makes it active. The queue never holds more than \<open>|V|\<close> vertices.

      The initial queue is built by a fold over the vertices. Its parameter
      @{term queue_vertex_fold} has the same specification as @{term vertex_fold}, but a different
      accumulator type.\<close>

locale push_relabel_fifo_spec =
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

locale push_relabel_fifo =
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
  assumes "distinct (u # queue_abstract Q)" "set (u # queue_abstract Q) \<subseteq> \<V>"
  shows "length (queue_abstract Q) < qcap"
proof-
  have "length (u # queue_abstract Q) = card (set (u # queue_abstract Q))"
    using distinct_card[OF assms(1)] by simp
  also have "\<dots> \<le> card \<V>"
    by (rule card_mono[OF \<V>_finite assms(2)])
  finally show ?thesis
    using qcap by simp
qed

lemma fifo_after_push_props:
  assumes "queue_invar Q" "distinct (u # queue_abstract Q)" "set (u # queue_abstract Q) = A"
          "A \<subseteq> \<V>" "v \<noteq> u" "v \<in> A \<longleftrightarrow> v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v"
          "\<And> w. w \<in> A' \<longleftrightarrow> (if w = u then keep else if w = v then v \<noteq> s \<and> v \<noteq> t else w \<in> A)"
          "fifo_after_push Q u v keep x = (Q', cur)"
  shows "queue_invar Q' \<and> distinct (queue_abstract Q') \<and>
         (\<forall> w. cur = Some w \<longrightarrow> w \<notin> set (queue_abstract Q')) \<and>
         set (queue_abstract Q') \<union> set_option cur = A'"
proof-
  have "set (u # queue_abstract Q) \<subseteq> \<V>"
    using assms(3,4) by simp
  note room = queue_room[OF assms(2) this]
  have cur: "cur = (if keep then Some u else None)"
    using assms(8) by (simp add: fifo_after_push_def)
  have uQ: "u \<notin> set (queue_abstract Q)" "distinct (queue_abstract Q)"
    using assms(2) by simp_all
  show ?thesis
  proof(cases "v \<noteq> s \<and> v \<noteq> t \<and> ex_get x v \<le> 0")
    case True
    have Q': "Q' = queue_push Q v"
      using True assms(8) by (simp add: fifo_after_push_def)
    have q: "queue_invar Q'" "queue_abstract Q' = queue_abstract Q @ [v]"
      using queue.queue_push[OF assms(1) room] by (simp_all add: Q')
    have vQ: "v \<notin> set (queue_abstract Q)"
      using assms(3,6) True by auto
    have "set (queue_abstract Q') \<union> set_option cur = A'"
    proof(rule set_eqI)
      fix w
      show "w \<in> set (queue_abstract Q') \<union> set_option cur \<longleftrightarrow> w \<in> A'"
        unfolding assms(7)[of w] q(2) cur using assms(3,5) uQ(1) True
        by (cases "w = u"; cases "w = v") auto
    qed
    thus ?thesis
      using q uQ vQ assms(5) by (auto simp add: cur)
  next
    case False
    have Q': "Q' = Q"
      using assms(8) unfolding fifo_after_push_def if_not_P[OF False] by simp
    have vA: "v \<in> set (queue_abstract Q) \<longleftrightarrow> v \<noteq> s \<and> v \<noteq> t"
      using assms(3,5,6) False by auto
    have "set (queue_abstract Q) \<union> set_option cur = A'"
    proof(rule set_eqI)
      fix w
      show "w \<in> set (queue_abstract Q) \<union> set_option cur \<longleftrightarrow> w \<in> A'"
        unfolding assms(7)[of w] cur using assms(3,5) uQ(1) vA
        by (cases "w = u"; cases "w = v") auto
    qed
    thus ?thesis
      using assms(1) uQ by (auto simp add: Q' cur)
  qed
qed

lemma fifo_discharge_props:
  assumes "invar_state st" "queue_invar Q" "distinct (u # queue_abstract Q)"
          "set (u # queue_abstract Q) = {v. active_vertex s t (flow_abs st) v}"
          "fifo_discharge Q u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
             (pr_in st) = (op, c)"
  shows "good_op st op" "op \<noteq> Done" "fifo_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
proof-
  note inv = invar_stateD[OF assms(1)]
  define A where "A = {v. active_vertex s t (flow_abs st) v}"
  have u: "active_vertex s t (flow_abs st) u"
    using assms(4) by auto
  have opd: "discharge_op True (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
    and c: "c = fifo_ctx_upd op Q u (pr_fwd st) (pr_bwd st) (pr_excess st)"
    using assms(5) by (auto simp add: fifo_discharge_def Let_def)
  note dp = discharge_op_props[OF assms(1) u opd]
  show "good_op st op" "op \<noteq> Done"
    using dp by simp_all
  have good: "good_op st op"
    using dp by simp
  define A' where "A' = {v. active_vertex s t (flow_abs (apply_op op st)) v}"
  have AV: "A \<subseteq> \<V>"
    by (auto simp add: A_def active_vertex_def)
  have uQ: "u \<notin> set (queue_abstract Q)" "distinct (queue_abstract Q)"
    using assms(3) by simp_all
  obtain Q' cur where c': "c = (Q', cur)"
    by (cases c)
  have same: "queue_invar Q' \<and> distinct (queue_abstract Q') \<and>
              (\<forall> w. cur = Some w \<longrightarrow> w \<notin> set (queue_abstract Q')) \<and>
              set (queue_abstract Q') \<union> set_option cur = A'"
    if "A' = A" "c = (Q, Some u) \<or> c = (queue_push Q u, None)"
    using that(2)
  proof
    assume "c = (Q, Some u)"
    thus ?thesis
      using assms(2,4) uQ that(1) c' by (auto simp add: A_def)
  next
    assume "c = (queue_push Q u, None)"
    moreover have "set (u # queue_abstract Q) \<subseteq> \<V>"
      using assms(4) AV by (simp add: A_def)
    note room = queue_room[OF assms(3) this]
    ultimately show ?thesis
      using queue.queue_push[OF assms(2)] assms(4) uQ that(1) c' by (auto simp add: A_def)
  qed
  have goal: "queue_invar Q' \<and> distinct (queue_abstract Q') \<and>
              (\<forall> w. cur = Some w \<longrightarrow> w \<notin> set (queue_abstract Q')) \<and>
              set (queue_abstract Q') \<union> set_option cur = A'"
  proof(cases op)
    case (Push_Fwd d)
    have pp: "push_precond s t (flow_abs st) (labels_abs st) (F d)"
      using good by (simp add: Push_Fwd good_op_def)
    have d: "fst d = u"
      using dp Push_Fwd by simp
    have v: "snd d \<noteq> u" "snd d \<in> \<V>"
      using push_fstv_sndv(1)[OF net_assms pp] sndv_in_V[OF net_assms push_fstv_sndv(2)[OF net_assms pp]]
      by (simp_all add: d)
    have vA: "snd d \<in> A \<longleftrightarrow> snd d \<noteq> s \<and> snd d \<noteq> t \<and> 0 < ex_get (pr_excess st) (snd d)"
      using inv(6)[OF v(2)] v(2) by (auto simp add: A_def active_vertex_def)
    have A'': "\<And> w. w \<in> A' \<longleftrightarrow>
                (if w = u then emap_get (pr_fwd st) d < ex_get (pr_excess st) u
                 else if w = snd d then snd d \<noteq> s \<and> snd d \<noteq> t else w \<in> A)"
    proof-
      fix w
      show "w \<in> A' \<longleftrightarrow>
            (if w = u then emap_get (pr_fwd st) d < ex_get (pr_excess st) u
             else if w = snd d then snd d \<noteq> s \<and> snd d \<noteq> t else w \<in> A)"
        unfolding A'_def A_def mem_Collect_eq apply_op_active[OF assms(1) good]
        by (cases "w = u") (simp_all add: Push_Fwd d)
    qed
    have "fifo_after_push Q u (snd d) (emap_get (pr_fwd st) d < ex_get (pr_excess st) u)
            (pr_excess st) = (Q', cur)"
      using c c' by (simp add: fifo_ctx_upd_def Push_Fwd)
    thus ?thesis
      using fifo_after_push_props[OF assms(2,3) _ AV v(1) vA A''] assms(4) by (simp add: A_def)
  next
    case (Push_Bwd d)
    have pp: "push_precond s t (flow_abs st) (labels_abs st) (B d)"
      using good by (simp add: Push_Bwd good_op_def)
    have d: "snd d = u"
      using dp Push_Bwd by simp
    have v: "fst d \<noteq> u" "fst d \<in> \<V>"
      using push_fstv_sndv(1)[OF net_assms pp] sndv_in_V[OF net_assms push_fstv_sndv(2)[OF net_assms pp]]
      by (simp_all add: d)
    have vA: "fst d \<in> A \<longleftrightarrow> fst d \<noteq> s \<and> fst d \<noteq> t \<and> 0 < ex_get (pr_excess st) (fst d)"
      using inv(6)[OF v(2)] v(2) by (auto simp add: A_def active_vertex_def)
    have A'': "\<And> w. w \<in> A' \<longleftrightarrow>
                (if w = u then emap_get (pr_bwd st) d < ex_get (pr_excess st) u
                 else if w = fst d then fst d \<noteq> s \<and> fst d \<noteq> t else w \<in> A)"
    proof-
      fix w
      show "w \<in> A' \<longleftrightarrow>
            (if w = u then emap_get (pr_bwd st) d < ex_get (pr_excess st) u
             else if w = fst d then fst d \<noteq> s \<and> fst d \<noteq> t else w \<in> A)"
        unfolding A'_def A_def mem_Collect_eq apply_op_active[OF assms(1) good]
        by (cases "w = u") (simp_all add: Push_Bwd d)
    qed
    have "fifo_after_push Q u (fst d) (emap_get (pr_bwd st) d < ex_get (pr_excess st) u)
            (pr_excess st) = (Q', cur)"
      using c c' by (simp add: fifo_ctx_upd_def Push_Bwd)
    thus ?thesis
      using fifo_after_push_props[OF assms(2,3) _ AV v(1) vA A''] assms(4) by (simp add: A_def)
  next
    case (Advance w)
    show ?thesis
      by (rule same) (use apply_op_active[OF assms(1) good] in
                      \<open>simp_all add: A'_def A_def Advance c fifo_ctx_upd_def\<close>)
  next
    case (Relabel w)
    show ?thesis
      by (rule same) (use apply_op_active[OF assms(1) good] in
                      \<open>simp_all add: A'_def A_def Relabel c fifo_ctx_upd_def\<close>)
  next
    case (Relabel_Gap w)
    show ?thesis
      by (rule same) (use apply_op_active[OF assms(1) good] in
                      \<open>simp_all add: A'_def A_def Relabel_Gap c fifo_ctx_upd_def\<close>)
  qed (use dp in simp)
  show "fifo_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
    using goal by (simp add: apply_op_ctx fifo_ctx_invar_def c' A'_def)
qed

lemma fifo_select_props:
  assumes "invar_state st" "fifo_ctx_invar st"
          "fifo_select (pr_ctx st) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op" "op \<noteq> Done \<Longrightarrow> fifo_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
proof-
  obtain Q cur where ctx: "pr_ctx st = (Q, cur)"
    by (cases "pr_ctx st")
  have I: "queue_invar Q" "distinct (queue_abstract Q)" "\<forall> w. cur = Some w \<longrightarrow> w \<notin> set (queue_abstract Q)"
          "set (queue_abstract Q) \<union> set_option cur = {v. active_vertex s t (flow_abs st) v}"
    using assms(2) ctx by (simp_all add: fifo_ctx_invar_def)
  have "good_op st op \<and> (op \<noteq> Done \<longrightarrow> fifo_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
  proof(cases cur)
    case (Some u)
    have dis: "fifo_discharge Q u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                 (pr_in st) = (op, c)"
      using assms(3) ctx Some by (simp add: fifo_select_def)
    have "distinct (u # queue_abstract Q)" "set (u # queue_abstract Q) = {v. active_vertex s t (flow_abs st) v}"
      using I Some by auto
    thus ?thesis
      using fifo_discharge_props[OF assms(1) I(1) _ _ dis] by simp
  next
    case None
    show ?thesis
    proof(cases "queue_is_empty Q")
      case True
      hence "queue_abstract Q = []"
        using queue.queue_is_empty[OF I(1)] by simp
      hence "\<forall> v. \<not> active_vertex s t (flow_abs st) v"
        using I(4) None by auto
      moreover have "op = Done"
        using assms(3) ctx None True by (simp add: fifo_select_def)
      ultimately show ?thesis
        by (simp add: good_op_def)
    next
      case False
      have ne: "queue_abstract Q \<noteq> []"
        using queue.queue_is_empty[OF I(1)] False by simp
      obtain u Q' where pop: "queue_pop Q = (u, Q')"
        by (cases "queue_pop Q")
      have q: "queue_invar Q'" "u # queue_abstract Q' = queue_abstract Q"
        using queue.queue_pop[OF I(1) ne] pop ne by simp_all
      have dis: "fifo_discharge Q' u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                   (pr_in st) = (op, c)"
        using assms(3) ctx None False pop by (simp add: fifo_select_def)
      have "distinct (u # queue_abstract Q')"
           "set (u # queue_abstract Q') = {v. active_vertex s t (flow_abs st) v}"
        using I None unfolding q(2) by simp_all
      thus ?thesis
        using fifo_discharge_props[OF assms(1) q(1) _ _ dis] by simp
    qed
  qed
  thus "good_op st op" "op \<noteq> Done \<Longrightarrow> fifo_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
    by simp_all
qed

lemma fifo_init_fold:
  assumes "queue_invar Q"
          "length (queue_abstract Q) + length (filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v) vs) \<le> qcap"
  shows "queue_invar (foldl (fifo_init_step x) Q vs) \<and>
         queue_abstract (foldl (fifo_init_step x) Q vs) =
         queue_abstract Q @ filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v) vs"
  using assms
proof(induction vs arbitrary: Q)
  case (Cons v vs)
  show ?case
  proof(cases "v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v")
    case True
    have room: "length (queue_abstract Q) < qcap"
      using Cons.prems(2) True by simp
    note q = queue.queue_push[OF Cons.prems(1) room, of v]
    have "queue_invar (queue_push Q v)"
         "length (queue_abstract (queue_push Q v)) +
          length (filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v) vs) \<le> qcap"
      using q Cons.prems(2) True by simp_all
    from Cons.IH[OF this] show ?thesis
      using True q by (simp add: fifo_init_step_def)
  next
    case False
    have "fifo_init_step x Q v = Q"
         "filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v) (v # vs) =
          filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v) vs"
      using False by (auto simp add: fifo_init_step_def)
    with Cons.IH[OF Cons.prems(1)] Cons.prems(2) show ?thesis
      by simp
  qed
qed simp

lemma fifo_init_ctx_props:
  assumes "invar_state st"
          "pr_ctx st = fifo_init_ctx (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                         (pr_in st)"
  shows "fifo_ctx_invar st"
proof-
  define P where "P = (\<lambda> v. v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get (pr_excess st) v)"
  obtain vs where vs: "distinct vs" "set vs = \<V>"
    "queue_vertex_fold (fifo_init_step (pr_excess st)) queue_empty =
     foldl (fifo_init_step (pr_excess st)) queue_empty vs"
    using queue_vertex_fold by blast
  have "length (filter P vs) \<le> length vs"
    by (rule length_filter_le)
  also have "\<dots> = card \<V>"
    using distinct_card[OF vs(1)] vs(2) by simp
  finally have "length (filter P vs) \<le> qcap"
    using qcap by simp
  hence f: "queue_invar (foldl (fifo_init_step (pr_excess st)) queue_empty vs)"
           "queue_abstract (foldl (fifo_init_step (pr_excess st)) queue_empty vs) = filter P vs"
    using fifo_init_fold[OF queue.queue_empty(1)] queue.queue_empty(2) by (simp_all add: P_def)
  have "set (filter P vs) = {v. active_vertex s t (flow_abs st) v}"
    using vs(2) invar_stateD(6)[OF assms(1)] by (auto simp add: P_def active_vertex_def)
  thus ?thesis
    using f vs(1) assms(2) by (simp add: fifo_ctx_invar_def fifo_init_ctx_def vs(3))
qed

end

text \<open>The generic algorithm with the FIFO strategy.\<close>

sublocale push_relabel_fifo_spec \<subseteq> fifo: push_relabel_spec where select = fifo_select
  and init_ctx = fifo_init_ctx
  by unfold_locales

text \<open>The FIFO strategy satisfies the contract of the generic algorithm, which thus computes a
      maximum flow.\<close>

sublocale push_relabel_fifo \<subseteq> fifo: push_relabel where select = fifo_select
  and init_ctx = fifo_init_ctx and ctx_invar = fifo_ctx_invar
proof(unfold_locales, goal_cases)
  case (1 st op c)
  show ?case
    by (rule fifo_select_props(1)[OF 1(1,2) 1(3)[unfolded fifo.select_of_def]])
next
  case (2 st op c)
  show ?case
    by (rule fifo_select_props(2)[OF 2(1,2) 2(3)[unfolded fifo.select_of_def] 2(4)])
next
  case (3 st)
  show ?case
    by (rule fifo_init_ctx_props[OF 3(1) 3(4)])
qed

end
