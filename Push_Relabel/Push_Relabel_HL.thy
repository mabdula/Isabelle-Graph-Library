theory Push_Relabel_HL
  imports
    Push_Relabel_Discharge
    Data_Structures.Fixed_Univ_Buckets_Specs
begin

section \<open>Highest-Label Push-Relabel with the Gap Heuristic\<close>

text \<open>The context of the strategy consists of buckets of active vertices, an upper bound \<open>b\<close>
      on the bucket numbers in use, and the vertex currently being discharged, if any. A vertex
      is put into the bucket of its label when a push makes it active. When no vertex is being
      discharged, the highest non-empty bucket at or below \<open>b\<close> is searched for, and one of its
      vertices is discharged until it becomes inactive.

      The bucket number of a vertex is always its current label. Labels of vertices in buckets
      only change by a gap relabelling, which lifts all labels strictly between the gap \<open>k\<close> and
      \<open>|V|\<close> to \<open>|V| + 1\<close>. A gap happens exactly when the current vertex is relabelled from a
      label \<open>k < |V|\<close> that no other vertex has, which the strategy reads off the label counts;
      it then moves the buckets strictly between \<open>k\<close> and \<open>|V|\<close> into bucket \<open>|V| + 1\<close>.

      The initial buckets are built by a fold over the vertices. Its parameter
      @{term bucket_vertex_fold} has the same specification as @{term vertex_fold}, but a
      different accumulator type.\<close>

locale push_relabel_hl_spec =
  push_relabel_ops where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar +
  bucket: fixed_univ_buckets \<V> "{..<2 * card \<V>}" buckets_invar buckets_abstract buckets_empty
      buckets_insert buckets_remove buckets_pick buckets_move
  for fst :: "'e \<Rightarrow> 'v"
  and emap_upd :: "'emap \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'emap"
  and ex_upd :: "'exc \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'exc"
  and label_upd :: "'lab \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lab"
  and count_upd :: "'cnt \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'cnt"
  and out_invar :: "'g \<Rightarrow> bool"
  and buckets_invar
  and buckets_abstract :: "'bk \<Rightarrow> 'v \<Rightarrow> nat option"
  and buckets_empty buckets_insert buckets_remove buckets_pick buckets_move +
  fixes bucket_vertex_fold :: "('bk \<times> nat \<Rightarrow> 'v \<Rightarrow> 'bk \<times> nat) \<Rightarrow> 'bk \<times> nat \<Rightarrow> 'bk \<times> nat"
begin

text \<open>The bucket operations with the key universe written as a bound.\<close>

lemmas buckets_universe_lt = bucket.buckets_universe[unfolded lessThan_iff]
lemmas buckets_insert_lt = bucket.buckets_insert[unfolded lessThan_iff]
lemmas buckets_pick_lt = bucket.buckets_pick[unfolded lessThan_iff]
lemmas buckets_move_lt = bucket.buckets_move[unfolded lessThan_iff]

text \<open>The highest non-empty bucket at or below \<open>k\<close>, with one of its vertices.\<close>

fun hl_find where
  "hl_find Bk 0 = (case buckets_pick Bk 0 of Some u \<Rightarrow> Some (0, u) | None \<Rightarrow> None)"
| "hl_find Bk (Suc k) =
     (case buckets_pick Bk (Suc k) of Some u \<Rightarrow> Some (Suc k, u) | None \<Rightarrow> hl_find Bk k)"

text \<open>After a push from \<open>u\<close> to \<open>v\<close>: \<open>v\<close> is put into the bucket of its label if it was inactive,
      and \<open>u\<close> stays the current vertex iff it keeps some excess.\<close>

definition "hl_after_push Bk b u v keep x l =
  (let cur = (if keep then Some u else None) in
   if v \<noteq> s \<and> v \<noteq> t \<and> ex_get x v \<le> 0
   then (buckets_insert Bk v (label_get l v), max b (label_get l v), cur)
   else (Bk, b, cur))"

text \<open>A gap at \<open>k\<close>: the non-empty buckets \<open>j\<close> with \<open>k < j\<close>, from \<open>j\<close> downwards, are moved into
      bucket \<open>|V| + 1\<close>.\<close>

fun hl_lift where
  "hl_lift Bk b k 0 = (Bk, b)"
| "hl_lift Bk b k (Suc j) =
     (if Suc j \<le> k then (Bk, b)
      else case buckets_pick Bk (Suc j) of
             None \<Rightarrow> hl_lift Bk b k j
           | Some _ \<Rightarrow> hl_lift (buckets_move Bk (Suc j) (Suc num_verts)) (max b (Suc num_verts)) k j)"

text \<open>Relabelling the current vertex \<open>u\<close> from label \<open>k\<close> causes a gap iff \<open>k < |V|\<close> and \<open>u\<close> is
      the only vertex with label \<open>k\<close>.\<close>

definition "hl_after_relabel Bk b u l cnt =
  (let k = label_get l u in
   if k < num_verts \<and> count_get cnt k = 1
   then (case hl_lift Bk b k (min b (num_verts - 1)) of (Bk', b') \<Rightarrow> (Bk', b', Some u))
   else (Bk, b, Some u))"

definition "hl_ctx_upd op Bk b u fw bw x l cnt =
  (case op of
     Push_Fwd d \<Rightarrow> hl_after_push Bk b u (snd d) (emap_get fw d < ex_get x u) x l
   | Push_Bwd d \<Rightarrow> hl_after_push Bk b u (fst d) (emap_get bw d < ex_get x u) x l
   | Relabel_Gap _ \<Rightarrow> hl_after_relabel Bk b u l cnt
   | _ \<Rightarrow> (Bk, b, Some u))"

definition "hl_discharge Bk b u fw bw x l cnt og ig =
  (let op = discharge_op True fw bw l og ig u in (op, hl_ctx_upd op Bk b u fw bw x l cnt))"

definition "hl_select ctx fw bw x l cnt og ig =
  (case ctx of
     (Bk, b, Some u) \<Rightarrow> hl_discharge Bk b u fw bw x l cnt og ig
   | (Bk, b, None) \<Rightarrow>
       (case hl_find Bk b of
          None \<Rightarrow> (Done, (Bk, b, None))
        | Some (k, u) \<Rightarrow> hl_discharge (buckets_remove Bk u k) k u fw bw x l cnt og ig))"

definition "hl_init_step x l = (\<lambda> (Bk, b) v.
  if v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v
  then (buckets_insert Bk v (label_get l v), max b (label_get l v)) else (Bk, b))"

definition "hl_init_ctx fw bw x l og ig =
  (case bucket_vertex_fold (hl_init_step x l) (buckets_empty, 0) of (Bk, b) \<Rightarrow> (Bk, b, None))"

lemmas [code] = hl_find.simps hl_after_push_def hl_lift.simps hl_after_relabel_def hl_ctx_upd_def
  hl_discharge_def hl_select_def hl_init_step_def hl_init_ctx_def

text \<open>The buckets and the current vertex together hold every active vertex exactly once, all
      bucket numbers in use are at most \<open>b\<close>, and every vertex in a bucket is in the bucket of its
      label.\<close>

definition "hl_ctx_invar st =
  (case pr_ctx st of (Bk, b, cur) \<Rightarrow>
     buckets_invar Bk \<and> b < 2 * card \<V> \<and> (\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> k \<le> b) \<and>
     (\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> k = labels_abs st v) \<and>
     (\<forall> u. cur = Some u \<longrightarrow> buckets_abstract Bk u = None) \<and>
     (\<forall> v. active_vertex s t (flow_abs st) v \<longleftrightarrow> buckets_abstract Bk v \<noteq> None \<or> cur = Some v))"

end

locale push_relabel_hl =
  push_relabel_hl_spec where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar +
  push_relabel_ops_correct where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar
  for fst :: "'e \<Rightarrow> 'v"
  and emap_upd :: "'emap \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'emap"
  and ex_upd :: "'exc \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'exc"
  and label_upd :: "'lab \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lab"
  and count_upd :: "'cnt \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'cnt"
  and out_invar :: "'g \<Rightarrow> bool" +
  assumes bucket_vertex_fold:
        "\<And> g acc. \<exists> vs. distinct vs \<and> set vs = \<V> \<and> bucket_vertex_fold g acc = foldl g acc vs"
begin

lemma label_bound:
  assumes "invar_state st" "v \<in> \<V>"
  shows "label_get (pr_labels st) v < 2 * card \<V>"
  using height_boundedD[OF invar_stateD(10)[OF assms(1)] assms(2)] card_V_ge_2[OF net_assms]
  by simp

lemma hl_find_props:
  assumes "buckets_invar Bk"
  shows "b < 2 * card \<V> \<Longrightarrow>
         (hl_find Bk b = None \<longrightarrow> (\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> b < k)) \<and>
         (\<forall> k u. hl_find Bk b = Some (k, u) \<longrightarrow> buckets_abstract Bk u = Some k \<and> k \<le> b \<and>
                  (\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j \<le> b \<longrightarrow> j \<le> k))"
proof(induction b)
  case 0
  note b = this
  show ?case
  proof(cases "buckets_pick Bk 0")
    case None
    hence nz: "\<And> v. buckets_abstract Bk v \<noteq> Some 0"
      using buckets_pick_lt(1)[OF assms(1) b] by simp
    have "\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> 0 < k"
    proof(intro allI impI)
      fix v k
      assume "buckets_abstract Bk v = Some k"
      thus "0 < k"
        using nz[of v] by (cases k) auto
    qed
    thus ?thesis
      using None by simp
  next
    case (Some u)
    thus ?thesis
      using buckets_pick_lt(2)[OF assms(1) b Some] by simp
  qed
next
  case (Suc b)
  have b: "b < 2 * card \<V>"
    using Suc.prems by simp
  note IH = Suc.IH[OF b]
  show ?case
  proof(cases "buckets_pick Bk (Suc b)")
    case (Some u)
    thus ?thesis
      using buckets_pick_lt(2)[OF assms(1) Suc.prems Some] by simp
  next
    case None
    have nb: "\<And> v. buckets_abstract Bk v \<noteq> Some (Suc b)"
      using buckets_pick_lt(1)[OF assms(1) Suc.prems] None by simp
    have f: "hl_find Bk (Suc b) = hl_find Bk b"
      using None by simp
    show ?thesis
      unfolding f using IH nb by (auto intro: Suc_lessI simp add: le_Suc_eq)
  qed
qed

text \<open>Relabelling \<open>u\<close> from label \<open>k\<close> leaves a gap at \<open>k\<close> iff \<open>k < |V|\<close> and \<open>u\<close> is the only
      vertex with label \<open>k\<close>.\<close>

lemma gap_iff_count:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "gap_precond (relabel_effect (flow_abs st) (labels_abs st) u) (labels_abs st u) \<longleftrightarrow>
         labels_abs st u < num_verts \<and> count_get (pr_counts st) (labels_abs st u) = 1"
proof-
  note inv = invar_stateD[OF assms(1)]
  define k where "k = labels_abs st u"
  define l' where "l' = relabel_effect (flow_abs st) (labels_abs st) u"
  define C where "C = {w. w \<in> \<V> \<and> labels_abs st w = k}"
  have u: "u \<in> \<V>"
    using assms(2) by (auto elim!: relabel_precondE simp add: active_vertex_def)
  have cnt: "count_get (pr_counts st) k = card C"
    using inv(7) label_bound[OF assms(1) u] by (simp add: counts_correct_def C_def k_def)
  have uC: "u \<in> C"
    using u by (simp add: C_def k_def)
  have l'w: "\<And> w. w \<noteq> u \<Longrightarrow> l' w = labels_abs st w"
    by (simp add: l'_def relabel_effect_def)
  have l'u: "k < l' u"
    using relabel_increases[OF net_assms inv(8,9) assms(2)] by (simp add: k_def l'_def)
  have "gap_precond l' k \<longleftrightarrow> k < num_verts \<and> card C = 1"
  proof
    assume gp: "gap_precond l' k"
    hence k: "k < card \<V>" "\<And> w. w \<in> \<V> \<Longrightarrow> l' w \<noteq> k"
      by (auto elim: gap_precondE)
    have "C = {u}"
    proof
      show "C \<subseteq> {u}"
      proof
        fix x
        assume x: "x \<in> C"
        show "x \<in> {u}"
        proof(rule ccontr)
          assume "x \<notin> {u}"
          hence "l' x = labels_abs st x"
            using l'w by simp
          thus False
            using x k(2)[of x] by (simp add: C_def)
        qed
      qed
      show "{u} \<subseteq> C"
        using uC by simp
    qed
    thus "k < num_verts \<and> card C = 1"
      using k(1) by (simp add: num_verts)
  next
    assume k: "k < num_verts \<and> card C = 1"
    from conjunct2[OF k] obtain x where "C = {x}"
      by (rule card_1_singletonE)
    hence C: "C = {u}"
      using uC by simp
    show "gap_precond l' k"
    proof(rule gap_precondI)
      show "k < card \<V>"
        using k by (simp add: num_verts)
      fix w
      assume w: "w \<in> \<V>"
      show "l' w \<noteq> k"
      proof(cases "w = u")
        case False
        hence "w \<notin> C"
          using C by simp
        thus ?thesis
          using w l'w[OF False] by (simp add: C_def)
      qed (use l'u in simp)
    qed
  qed
  thus ?thesis
    unfolding k_def[symmetric] l'_def[symmetric] cnt .
qed

lemma hl_lift_props:
  assumes "buckets_invar Bk" "b < 2 * card \<V>" "\<forall> w i. buckets_abstract Bk w = Some i \<longrightarrow> i \<le> b"
          "j < num_verts" "hl_lift Bk b k j = (Bk', b')"
  shows "buckets_invar Bk' \<and> b' < 2 * card \<V> \<and> (\<forall> w i. buckets_abstract Bk' w = Some i \<longrightarrow> i \<le> b') \<and>
         (\<forall> w. buckets_abstract Bk' w =
               map_option (\<lambda> i. if k < i \<and> i \<le> j then Suc num_verts else i) (buckets_abstract Bk w))"
  using assms
proof(induction j arbitrary: Bk b)
  case 0
  have "Bk' = Bk" "b' = b"
    using 0 by simp_all
  moreover have "\<forall> w. buckets_abstract Bk w =
                   map_option (\<lambda> i. if k < i \<and> i \<le> 0 then Suc num_verts else i) (buckets_abstract Bk w)"
  proof
    fix w
    show "buckets_abstract Bk w =
          map_option (\<lambda> i. if k < i \<and> i \<le> 0 then Suc num_verts else i) (buckets_abstract Bk w)"
      by (cases "buckets_abstract Bk w") auto
  qed
  ultimately show ?case
    using 0 by simp
next
  case (Suc j)
  have j: "j < num_verts"
    using Suc.prems(4) by simp
  have nb: "Suc num_verts < 2 * card \<V>"
    using card_V_ge_2[OF net_assms] by (simp add: num_verts)
  have sj: "Suc j < 2 * card \<V>"
    using Suc.prems(4) nb by simp
  show ?case
  proof(cases "Suc j \<le> k")
    case True
    have "Bk' = Bk" "b' = b"
      using Suc.prems(5) True by simp_all
    moreover have "\<forall> w. buckets_abstract Bk w =
                     map_option (\<lambda> i. if k < i \<and> i \<le> Suc j then Suc num_verts else i) (buckets_abstract Bk w)"
    proof
      fix w
      show "buckets_abstract Bk w =
            map_option (\<lambda> i. if k < i \<and> i \<le> Suc j then Suc num_verts else i) (buckets_abstract Bk w)"
        using True by (cases "buckets_abstract Bk w") auto
    qed
    ultimately show ?thesis
      using Suc.prems(1-3) by simp
  next
    case False
    show ?thesis
    proof(cases "buckets_pick Bk (Suc j)")
      case None
      have nb': "\<And> w. buckets_abstract Bk w \<noteq> Some (Suc j)"
        using buckets_pick_lt(1)[OF Suc.prems(1) sj] None by simp
      have "hl_lift Bk b k j = (Bk', b')"
        using Suc.prems(5) False None by simp
      note IH = Suc.IH[OF Suc.prems(1-3) j this]
      have "\<And> w. map_option (\<lambda> i. if k < i \<and> i \<le> j then Suc num_verts else i) (buckets_abstract Bk w) =
                 map_option (\<lambda> i. if k < i \<and> i \<le> Suc j then Suc num_verts else i) (buckets_abstract Bk w)"
      proof-
        fix w
        show "map_option (\<lambda> i. if k < i \<and> i \<le> j then Suc num_verts else i) (buckets_abstract Bk w) =
              map_option (\<lambda> i. if k < i \<and> i \<le> Suc j then Suc num_verts else i) (buckets_abstract Bk w)"
          using nb'[of w] by (cases "buckets_abstract Bk w") (auto simp add: le_Suc_eq)
      qed
      thus ?thesis
        using IH by simp
    next
      case (Some x)
      define B1 where "B1 = buckets_move Bk (Suc j) (Suc num_verts)"
      have ne: "Suc j \<noteq> Suc num_verts"
        using Suc.prems(4) by simp
      note mv = buckets_move_lt[OF Suc.prems(1) sj nb ne, folded B1_def]
      have lift: "hl_lift B1 (max b (Suc num_verts)) k j = (Bk', b')"
        using Suc.prems(5) False Some by (simp add: B1_def)
      have B1: "buckets_invar B1" "max b (Suc num_verts) < 2 * card \<V>"
               "\<forall> w i. buckets_abstract B1 w = Some i \<longrightarrow> i \<le> max b (Suc num_verts)"
        using mv Suc.prems(2,3) nb by (auto simp add: le_max_iff_disj)
      note IH = Suc.IH[OF B1 j lift]
      have "\<And> w. map_option (\<lambda> i. if k < i \<and> i \<le> j then Suc num_verts else i) (buckets_abstract B1 w) =
                 map_option (\<lambda> i. if k < i \<and> i \<le> Suc j then Suc num_verts else i) (buckets_abstract Bk w)"
      proof-
        fix w
        show "map_option (\<lambda> i. if k < i \<and> i \<le> j then Suc num_verts else i) (buckets_abstract B1 w) =
              map_option (\<lambda> i. if k < i \<and> i \<le> Suc j then Suc num_verts else i) (buckets_abstract Bk w)"
          using mv(2) False j by (cases "buckets_abstract Bk w") (auto simp add: le_Suc_eq)
      qed
      thus ?thesis
        using IH by simp
    qed
  qed
qed

lemma hl_after_relabel_props:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
          "buckets_invar Bk" "b < 2 * card \<V>"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b" "buckets_abstract Bk u = None"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k = labels_abs st w"
          "hl_after_relabel Bk b u (pr_labels st) (pr_counts st) = (Bk', b', cur)"
  shows "buckets_invar Bk' \<and> b' < 2 * card \<V> \<and> (\<forall> w k. buckets_abstract Bk' w = Some k \<longrightarrow> k \<le> b') \<and>
         (\<forall> w k. buckets_abstract Bk' w = Some k \<longrightarrow>
                   k = relabel_gap_effect (flow_abs st) (labels_abs st) u w) \<and>
         cur = Some u \<and> (\<forall> w. buckets_abstract Bk' w = None \<longleftrightarrow> buckets_abstract Bk w = None)"
proof-
  define k where "k = labels_abs st u"
  define l' where "l' = relabel_effect (flow_abs st) (labels_abs st) u"
  have l'w: "\<And> w. w \<noteq> u \<Longrightarrow> l' w = labels_abs st w"
    by (simp add: l'_def relabel_effect_def)
  have key: "\<And> w i. buckets_abstract Bk w = Some i \<Longrightarrow> w \<in> \<V> \<and> i = l' w \<and> i \<le> b"
  proof-
    fix w i
    assume wi: "buckets_abstract Bk w = Some i"
    have "w \<noteq> u"
      using wi assms(6) by auto
    thus "w \<in> \<V> \<and> i = l' w \<and> i \<le> b"
      using wi assms(5,7) buckets_universe_lt[OF assms(3) wi] l'w by auto
  qed
  note gc = gap_iff_count[OF assms(1,2), folded k_def l'_def]
  show ?thesis
  proof(cases "k < num_verts \<and> count_get (pr_counts st) k = 1")
    case True
    have eff: "relabel_gap_effect (flow_abs st) (labels_abs st) u = gap_effect l' k"
      using gc True by (simp add: relabel_gap_effect_def Let_def l'_def k_def)
    have j: "min b (num_verts - 1) < num_verts"
      using card_V_ge_2[OF net_assms] by (simp add: num_verts)
    obtain Bk1 b1 where lift: "hl_lift Bk b k (min b (num_verts - 1)) = (Bk1, b1)"
      by (cases "hl_lift Bk b k (min b (num_verts - 1))") auto
    have res: "Bk' = Bk1" "b' = b1" "cur = Some u"
      using assms(8) True lift by (simp_all add: hl_after_relabel_def Let_def k_def)
    note lp = hl_lift_props[OF assms(3-5) j lift]
    have m: "\<And> w. buckets_abstract Bk1 w =
               map_option (\<lambda> i. if k < i \<and> i \<le> min b (num_verts - 1) then Suc num_verts else i)
                 (buckets_abstract Bk w)"
      using lp by simp
    have keys: "\<forall> w i. buckets_abstract Bk1 w = Some i \<longrightarrow> i = gap_effect l' k w"
    proof(intro allI impI)
      fix w i
      assume wi: "buckets_abstract Bk1 w = Some i"
      show "i = gap_effect l' k w"
      proof(cases "buckets_abstract Bk w")
        case None
        thus ?thesis
          using wi m[of w] by simp
      next
        case (Some i0)
        have i: "i = (if k < i0 \<and> i0 \<le> min b (num_verts - 1) then Suc num_verts else i0)"
          using wi m[of w] Some by simp
        note kw = key[OF Some]
        have "i0 \<le> min b (num_verts - 1) \<longleftrightarrow> i0 < num_verts"
          using kw j by auto
        thus ?thesis
          using i kw by (auto simp add: gap_effect_def num_verts)
      qed
    qed
    have none: "\<forall> w. buckets_abstract Bk1 w = None \<longleftrightarrow> buckets_abstract Bk w = None"
      using m by simp
    show ?thesis
      using lp keys none by (simp add: res eff)
  next
    case False
    have ngp: "\<not> gap_precond l' k"
      using gc False by simp
    have eff: "relabel_gap_effect (flow_abs st) (labels_abs st) u = l'"
      unfolding relabel_gap_effect_def Let_def l'_def[symmetric] k_def[symmetric] using ngp by simp
    have "hl_after_relabel Bk b u (pr_labels st) (pr_counts st) = (Bk, b, Some u)"
      unfolding hl_after_relabel_def Let_def k_def[symmetric] if_not_P[OF False] ..
    hence res: "Bk' = Bk" "b' = b" "cur = Some u"
      using assms(8) by simp_all
    show ?thesis
      using assms(3-5) key res eff by auto
  qed
qed



lemma hl_after_push_props:
  assumes "buckets_invar Bk" "b < 2 * card \<V>" "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b"
          "buckets_abstract Bk u = None" "\<And> w. w \<in> A \<longleftrightarrow> buckets_abstract Bk w \<noteq> None \<or> w = u"
          "v \<noteq> u" "v \<in> \<V>" "v \<in> A \<longleftrightarrow> v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v"
          "label_get l v < 2 * card \<V>"
          "\<And> w. w \<in> A' \<longleftrightarrow> (if w = u then keep else if w = v then v \<noteq> s \<and> v \<noteq> t else w \<in> A)"
          "hl_after_push Bk b u v keep x l = (Bk', b', cur)"
          "\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j = label_get l w"
  shows "buckets_invar Bk' \<and> b' < 2 * card \<V> \<and> (\<forall> w k. buckets_abstract Bk' w = Some k \<longrightarrow> k \<le> b') \<and>
         (\<forall> w j. buckets_abstract Bk' w = Some j \<longrightarrow> j = label_get l w) \<and>
         (\<forall> w. cur = Some w \<longrightarrow> buckets_abstract Bk' w = None) \<and>
         (\<forall> w. w \<in> A' \<longleftrightarrow> buckets_abstract Bk' w \<noteq> None \<or> cur = Some w)"
proof-
  have cur: "cur = (if keep then Some u else None)"
    using assms(11) by (auto simp add: hl_after_push_def Let_def split: if_splits)
  show ?thesis
  proof(cases "v \<noteq> s \<and> v \<noteq> t \<and> ex_get x v \<le> 0")
    case True
    have Bk': "Bk' = buckets_insert Bk v (label_get l v)" "b' = max b (label_get l v)"
      using True assms(11) by (simp_all add: hl_after_push_def Let_def)
    have vB: "buckets_abstract Bk v = None"
      using assms(5)[of v] assms(6,8) True by auto
    note ins = buckets_insert_lt[OF assms(1,7,9) vB]
    have abs': "buckets_abstract Bk' = (buckets_abstract Bk)(v := Some (label_get l v))"
      using ins(2) by (simp add: Bk'(1))
    have A': "\<forall> w. w \<in> A' \<longleftrightarrow> buckets_abstract Bk' w \<noteq> None \<or> cur = Some w"
    proof
      fix w
      show "w \<in> A' \<longleftrightarrow> buckets_abstract Bk' w \<noteq> None \<or> cur = Some w"
        unfolding assms(10)[of w] assms(5)[of w] abs' cur using assms(4,6) True
        by (cases "w = u"; cases "w = v") auto
    qed
    have inv': "buckets_invar Bk'"
      using ins(1) by (simp add: Bk'(1))
    show ?thesis
      using inv' A' assms(2,3,4,6,9,12) unfolding abs'
      by (auto simp add: Bk'(2) cur le_max_iff_disj)
  next
    case False
    have Bk': "Bk' = Bk" "b' = b"
      using assms(11) unfolding hl_after_push_def Let_def if_not_P[OF False] by simp_all
    have vB: "buckets_abstract Bk v \<noteq> None \<longleftrightarrow> v \<noteq> s \<and> v \<noteq> t"
      using assms(5)[of v] assms(6,8) False by auto
    have A': "\<forall> w. w \<in> A' \<longleftrightarrow> buckets_abstract Bk' w \<noteq> None \<or> cur = Some w"
    proof
      fix w
      show "w \<in> A' \<longleftrightarrow> buckets_abstract Bk' w \<noteq> None \<or> cur = Some w"
        unfolding assms(10)[of w] assms(5)[of w] Bk' cur using assms(4) vB
        by (cases "w = u"; cases "w = v") auto
    qed
    show ?thesis
      using assms(1-4,12) A' by (auto simp add: Bk' cur)
  qed
qed

lemma hl_discharge_props:
  assumes "invar_state st" "buckets_invar Bk" "b < 2 * card \<V>"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b" "buckets_abstract Bk u = None"
          "\<And> w. active_vertex s t (flow_abs st) w \<longleftrightarrow> buckets_abstract Bk w \<noteq> None \<or> w = u"
          "hl_discharge Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
          "\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j = labels_abs st w"
  shows "good_op st op" "op \<noteq> Done" "hl_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
proof-
  note inv = invar_stateD[OF assms(1)]
  define A where "A = {v. active_vertex s t (flow_abs st) v}"
  have Aw: "\<And> w. w \<in> A \<longleftrightarrow> buckets_abstract Bk w \<noteq> None \<or> w = u"
    using assms(6) by (simp add: A_def)
  have u: "active_vertex s t (flow_abs st) u"
    using assms(6) by simp
  have opd: "discharge_op True (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
    and c: "c = hl_ctx_upd op Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
                  (pr_counts st)"
    using assms(7) by (auto simp add: hl_discharge_def Let_def)
  note dp = discharge_op_props[OF assms(1) u opd]
  show "good_op st op" "op \<noteq> Done"
    using dp by simp_all
  have good: "good_op st op"
    using dp by simp
  define A' where "A' = {v. active_vertex s t (flow_abs (apply_op op st)) v}"
  obtain Bk' b' cur where c': "c = (Bk', b', cur)"
    by (cases c) auto
  have goal: "buckets_invar Bk' \<and> b' < 2 * card \<V> \<and> (\<forall> w k. buckets_abstract Bk' w = Some k \<longrightarrow> k \<le> b') \<and>
              (\<forall> w j. buckets_abstract Bk' w = Some j \<longrightarrow> j = labels_abs (apply_op op st) w) \<and>
              (\<forall> w. cur = Some w \<longrightarrow> buckets_abstract Bk' w = None) \<and>
              (\<forall> w. w \<in> A' \<longleftrightarrow> buckets_abstract Bk' w \<noteq> None \<or> cur = Some w)"
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
    have "hl_after_push Bk b u (snd d) (emap_get (pr_fwd st) d < ex_get (pr_excess st) u)
            (pr_excess st) (pr_labels st) = (Bk', b', cur)"
      using c c' by (simp add: hl_ctx_upd_def Push_Fwd)
    moreover have "labels_abs (apply_op op st) = labels_abs st"
      using push_impl_props(3)[OF assms(1) _ pp, of op d] Push_Fwd by simp
    ultimately show ?thesis
      using hl_after_push_props[OF assms(2-5) Aw v vA label_bound[OF assms(1) v(2)] A'' _ assms(8)] by simp
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
    have "hl_after_push Bk b u (fst d) (emap_get (pr_bwd st) d < ex_get (pr_excess st) u)
            (pr_excess st) (pr_labels st) = (Bk', b', cur)"
      using c c' by (simp add: hl_ctx_upd_def Push_Bwd)
    moreover have "labels_abs (apply_op op st) = labels_abs st"
      using push_impl_props(3)[OF assms(1) _ pp, of op d] Push_Bwd by simp
    ultimately show ?thesis
      using hl_after_push_props[OF assms(2-5) Aw v vA label_bound[OF assms(1) v(2)] A'' _ assms(8)] by simp
  next
    case (Advance w)
    have wV: "w \<in> \<V>"
     and ex: "\<exists> e. current_res st w = Some e \<and> \<not> admissible (flow_abs st) (labels_abs st) e"
      using good Advance by (simp_all add: good_op_def)
    from ex obtain e where e: "current_res st w = Some e" "\<not> admissible (flow_abs st) (labels_abs st) e"
      by (elim exE conjE) (rule that)
    note ap = advance_impl_props[OF assms(1) wV e]
    have "c = (Bk, b, Some u)" "A' = A" "labels_abs (apply_op op st) = labels_abs st"
      using apply_op_active[OF assms(1) good] ap(3) Advance
      by (simp_all add: c hl_ctx_upd_def A'_def A_def)
    thus ?thesis
      using assms(2-5,8) Aw c' by auto
  next
    case (Relabel w)
    thus ?thesis
      using opd by (simp add: discharge_op_def Let_def split: if_splits)
  next
    case (Relabel_Gap w)
    have w: "w = u"
      using opd Relabel_Gap by (auto simp add: discharge_op_def Let_def split: if_splits)
    have rp: "relabel_precond s t (flow_abs st) (labels_abs st) u"
      using good Relabel_Gap w by (simp add: good_op_def)
    have A'A: "A' = A"
      using apply_op_active[OF assms(1) good] Relabel_Gap by (simp add: A'_def A_def)
    have lab: "labels_abs (apply_op op st) = relabel_gap_effect (flow_abs st) (labels_abs st) u"
      using relabel_gap_impl_props(2)[OF assms(1) rp] Relabel_Gap w by simp
    have "hl_after_relabel Bk b u (pr_labels st) (pr_counts st) = (Bk', b', cur)"
      using c c' by (simp add: hl_ctx_upd_def Relabel_Gap)
    note ar = hl_after_relabel_props[OF assms(1) rp assms(2-5) assms(8) this]
    show ?thesis
      using ar Aw A'A lab assms(5) by (simp add: eq_commute[of u])
  qed (use dp in simp)
  show "hl_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
    using goal by (simp add: apply_op_ctx hl_ctx_invar_def c' A'_def)
qed

lemma hl_select_props:
  assumes "invar_state st" "hl_ctx_invar st"
          "hl_select (pr_ctx st) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op" "op \<noteq> Done \<Longrightarrow> hl_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
proof-
  obtain Bk b cur where ctx: "pr_ctx st = (Bk, b, cur)"
    by (cases "pr_ctx st") auto
  have I: "buckets_invar Bk" "b < 2 * card \<V>" "\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> k \<le> b"
          "\<forall> u. cur = Some u \<longrightarrow> buckets_abstract Bk u = None"
          "\<And> v. active_vertex s t (flow_abs st) v \<longleftrightarrow> buckets_abstract Bk v \<noteq> None \<or> cur = Some v"
          "\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> k = labels_abs st v"
    using assms(2) ctx by (simp_all add: hl_ctx_invar_def)
  have "good_op st op \<and> (op \<noteq> Done \<longrightarrow> hl_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
  proof(cases cur)
    case (Some u)
    have dis: "hl_discharge Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
                 (pr_out st) (pr_in st) = (op, c)"
      using assms(3) ctx Some by (simp add: hl_select_def)
    have "buckets_abstract Bk u = None"
         "\<And> w. active_vertex s t (flow_abs st) w \<longleftrightarrow> buckets_abstract Bk w \<noteq> None \<or> w = u"
      using I(4,5) Some by auto
    thus ?thesis
      using hl_discharge_props[OF assms(1) I(1-3) _ _ dis I(6)] by simp
  next
    case None
    note cN = this
    note fp = hl_find_props[OF I(1) I(2)]
    show ?thesis
    proof(cases "hl_find Bk b")
      case None
      have "\<forall> v. \<not> active_vertex s t (flow_abs st) v"
        using fp None I(3,5) cN by fastforce
      moreover have "op = Done"
        using assms(3) ctx cN None by (simp add: hl_select_def)
      ultimately show ?thesis
        by (simp add: good_op_def)
    next
      case (Some ku)
      then obtain k u where f: "hl_find Bk b = Some (k, u)"
        by (cases ku) auto
      have uk: "buckets_abstract Bk u = Some k" "k \<le> b"
           "\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j \<le> b \<longrightarrow> j \<le> k"
        using fp f by simp_all
      define B1 where "B1 = buckets_remove Bk u k"
      note rm = bucket.buckets_remove[OF I(1) uk(1), folded B1_def]
      have dis: "hl_discharge B1 k u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
                   (pr_counts st) (pr_out st) (pr_in st) = (op, c)"
        using assms(3) ctx cN f by (simp add: hl_select_def B1_def)
      have k: "k < 2 * card \<V>"
        using uk(2) I(2) by simp
      have "\<forall> w j. buckets_abstract B1 w = Some j \<longrightarrow> j \<le> k"
           "buckets_abstract B1 u = None"
           "\<And> w. active_vertex s t (flow_abs st) w \<longleftrightarrow> buckets_abstract B1 w \<noteq> None \<or> w = u"
           "\<forall> w j. buckets_abstract B1 w = Some j \<longrightarrow> j = labels_abs st w"
        using I(3,5,6) uk rm(2) cN by auto
      thus ?thesis
        using hl_discharge_props[OF assms(1) rm(1) k _ _ _ dis] by simp
    qed
  qed
  thus "good_op st op" "op \<noteq> Done \<Longrightarrow> hl_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
    by simp_all
qed

lemma hl_init_fold:
  assumes "buckets_invar Bk" "b < 2 * card \<V>" "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b"
          "distinct vs" "set vs \<subseteq> \<V>" "\<forall> v \<in> set vs. buckets_abstract Bk v = None"
          "\<forall> v \<in> set vs. label_get l v < 2 * card \<V>"
          "foldl (hl_init_step x l) (Bk, b) vs = (Bk', b')"
          "\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j = label_get l w"
  shows "buckets_invar Bk' \<and> b' < 2 * card \<V> \<and> (\<forall> w k. buckets_abstract Bk' w = Some k \<longrightarrow> k \<le> b') \<and>
         (\<forall> w j. buckets_abstract Bk' w = Some j \<longrightarrow> j = label_get l w) \<and>
         (\<forall> w. buckets_abstract Bk' w \<noteq> None \<longleftrightarrow>
               buckets_abstract Bk w \<noteq> None \<or> (w \<in> set vs \<and> w \<noteq> s \<and> w \<noteq> t \<and> 0 < ex_get x w))"
  using assms
proof(induction vs arbitrary: Bk b)
  case Nil
  thus ?case
    by simp
next
  case (Cons v vs)
  show ?case
  proof(cases "v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v")
    case True
    define B1 where "B1 = buckets_insert Bk v (label_get l v)"
    have v: "v \<in> \<V>" "label_get l v < 2 * card \<V>" "buckets_abstract Bk v = None"
      using Cons.prems(5,6,7) by simp_all
    note ins = buckets_insert_lt[OF Cons.prems(1) v, folded B1_def]
    have step: "hl_init_step x l (Bk, b) v = (B1, max b (label_get l v))"
      using True by (simp add: hl_init_step_def B1_def)
    have "buckets_invar B1" "max b (label_get l v) < 2 * card \<V>"
         "\<forall> w k. buckets_abstract B1 w = Some k \<longrightarrow> k \<le> max b (label_get l v)"
         "distinct vs" "set vs \<subseteq> \<V>" "\<forall> w \<in> set vs. buckets_abstract B1 w = None"
         "\<forall> w \<in> set vs. label_get l w < 2 * card \<V>"
         "foldl (hl_init_step x l) (B1, max b (label_get l v)) vs = (Bk', b')"
         "\<forall> w j. buckets_abstract B1 w = Some j \<longrightarrow> j = label_get l w"
      using ins Cons.prems step by (auto simp add: le_max_iff_disj)
    from Cons.IH[OF this] show ?thesis
      using ins(2) True by auto
  next
    case False
    have step: "hl_init_step x l (Bk, b) v = (Bk, b)"
      using False by (auto simp add: hl_init_step_def)
    have "foldl (hl_init_step x l) (Bk, b) vs = (Bk', b')"
      using Cons.prems(8) step by simp
    from Cons.IH[OF Cons.prems(1-3) _ _ _ _ this Cons.prems(9)] Cons.prems(4-7) show ?thesis
      using False by auto
  qed
qed

lemma hl_init_ctx_props:
  assumes "invar_state st"
          "pr_ctx st = hl_init_ctx (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                         (pr_in st)"
  shows "hl_ctx_invar st"
proof-
  obtain vs where vs: "distinct vs" "set vs = \<V>"
    "bucket_vertex_fold (hl_init_step (pr_excess st) (pr_labels st)) (buckets_empty, 0) =
     foldl (hl_init_step (pr_excess st) (pr_labels st)) (buckets_empty, 0) vs"
    using bucket_vertex_fold by blast
  obtain Bk b where fold: "foldl (hl_init_step (pr_excess st) (pr_labels st)) (buckets_empty, 0) vs = (Bk, b)"
    by (cases "foldl (hl_init_step (pr_excess st) (pr_labels st)) (buckets_empty, 0) vs") auto
  have "0 < 2 * card \<V>"
    using card_V_ge_2[OF net_assms] by simp
  hence f: "buckets_invar Bk \<and> b < 2 * card \<V> \<and> (\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b) \<and>
            (\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j = labels_abs st w) \<and>
            (\<forall> w. buckets_abstract Bk w \<noteq> None \<longleftrightarrow>
                  (w \<in> set vs \<and> w \<noteq> s \<and> w \<noteq> t \<and> 0 < ex_get (pr_excess st) w))"
    using hl_init_fold[OF bucket.buckets_empty(1) _ _ vs(1) _ _ _ fold] bucket.buckets_empty(2) vs(2)
          label_bound[OF assms(1)] by simp
  have ctx: "pr_ctx st = (Bk, b, None)"
    using assms(2) vs(3) fold by (simp add: hl_init_ctx_def)
  show ?thesis
    using f vs(2) invar_stateD(6)[OF assms(1)] by (auto simp add: hl_ctx_invar_def ctx active_vertex_def)
qed

end

text \<open>The generic algorithm with the highest-label strategy.\<close>

sublocale push_relabel_hl_spec \<subseteq> hl: push_relabel_spec where select = hl_select
  and init_ctx = hl_init_ctx
  by unfold_locales

text \<open>The highest-label strategy satisfies the contract of the generic algorithm, which thus
      computes a maximum flow.\<close>

sublocale push_relabel_hl \<subseteq> hl: push_relabel where select = hl_select
  and init_ctx = hl_init_ctx and ctx_invar = hl_ctx_invar
proof(unfold_locales, goal_cases)
  case (1 st op c)
  show ?case
    by (rule hl_select_props(1)[OF 1(1,2) 1(3)[unfolded hl.select_of_def]])
next
  case (2 st op c)
  show ?case
    by (rule hl_select_props(2)[OF 2(1,2) 2(3)[unfolded hl.select_of_def] 2(4)])
next
  case (3 st)
  show ?case
    by (rule hl_init_ctx_props[OF 3(1) 3(4)])
qed

end

