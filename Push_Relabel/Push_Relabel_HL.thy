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
      it then moves the buckets strictly between \<open>k\<close> and \<open>|V|\<close> into
      bucket \<open>|V| + 1\<close>.

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

text \<open>After a push from \<open>u\<close> to \<open>v\<close>: \<open>v\<close> is put into the bucket of its label
      if it was inactive, and \<open>u\<close> stays the current vertex iff it keeps some excess.\<close>

definition "hl_after_push Bk b u v keep x l =
  (let cur = (if keep then Some u else None) in
   if v \<noteq> s \<and> v \<noteq> t \<and> ex_get x v \<le> 0
   then (buckets_insert Bk v (label_get l v), max b (label_get l v), cur)
   else (Bk, b, cur))"

text \<open>A gap at \<open>k\<close>: the non-empty buckets \<open>j\<close> with
      \<open>k < j\<close>, from \<open>j\<close> downwards, are moved into bucket \<open>|V| + 1\<close>.\<close>

fun hl_lift where
  "hl_lift Bk b k 0 = (Bk, b)"
| "hl_lift Bk b k (Suc j) =
     (if Suc j \<le> k then (Bk, b)
      else case buckets_pick Bk (Suc j) of
             None \<Rightarrow> hl_lift Bk b k j
           | Some _ \<Rightarrow> hl_lift (buckets_move Bk (Suc j) (Suc num_verts)) (max b (Suc num_verts)) k j)"

text \<open>Relabelling the current vertex \<open>u\<close> from label \<open>k\<close>
      causes a gap iff \<open>k < |V|\<close> and \<open>u\<close> is the only vertex with label \<open>k\<close>.\<close>

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
  "\<lbrakk>invar_state st; v \<in> \<V>\<rbrakk> \<Longrightarrow> label_get (pr_labels st) v < 2 * card \<V>"
  using card_V_ge_2 height_boundedD[of "labels_abs st" v]
  by (auto elim!: invar_props_elims)

lemma hl_find_props:
  "\<lbrakk>buckets_invar Bk; b < 2 * card \<V>\<rbrakk> \<Longrightarrow>
   (hl_find Bk b = None \<longrightarrow> (\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> b < k)) \<and>
   (\<forall> k u. hl_find Bk b = Some (k, u) \<longrightarrow>
      buckets_abstract Bk u = Some k \<and> k \<le> b \<and>
      (\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j \<le> b \<longrightarrow> j \<le> k))"
  using buckets_pick_lt[of Bk]
  by (induction b) (auto simp: le_Suc_eq split: option.splits intro: gr0I Suc_lessI)

text \<open>Relabelling \<open>u\<close> from label \<open>k\<close> leaves a gap at \<open>k\<close> iff
      \<open>k < |V|\<close> and \<open>u\<close> is the only vertex with label \<open>k\<close>.\<close>

lemma count_label_card:
  "\<lbrakk>invar_state st; u \<in> \<V>\<rbrakk> \<Longrightarrow>
   count_get (pr_counts st) (labels_abs st u) = card {w \<in> \<V>. labels_abs st w = labels_abs st u}"
  using label_bound[of st]
  by (auto simp: invar_counts_iff counts_correct_def elim!: invar_props_elims)

lemma label_class_card_one:
  "u \<in> \<V> \<Longrightarrow> card {w \<in> \<V>. l w = l u} = 1 \<longleftrightarrow> (\<forall> w \<in> \<V>. l w = l u \<longrightarrow> w = u)"
  using \<V>_finite card_le_Suc0_iff_eq[of "{w \<in> \<V>. l w = l u}"] card_gt_0_iff[of "{w \<in> \<V>. l w = l u}"]
  by (auto simp: le_Suc_eq)

lemma gap_iff_count:
  "\<lbrakk>invar_state st; relabel_precond s t (flow_abs st) (labels_abs st) u\<rbrakk> \<Longrightarrow>
   gap_precond (relabel_effect (flow_abs st) (labels_abs st) u) (labels_abs st u) \<longleftrightarrow>
   labels_abs st u < num_verts \<and> count_get (pr_counts st) (labels_abs st u) = 1"
  using relabel_increases[of "flow_abs st" "labels_abs st" u] count_label_card[of st u]
        label_class_card_one[of u "labels_abs st"]
  by (auto simp: gap_precond_def relabel_effect_def num_verts active_vertex_def
           elim!: invar_props_elims relabel_precondE)

lemma lift_bounds:
  "j < num_verts \<Longrightarrow> j < 2 * card \<V> \<and> Suc num_verts < 2 * card \<V> \<and> j \<noteq> Suc num_verts"
  using card_V_ge_2
  by (simp add: num_verts)

lemma hl_lift_props:
  "\<lbrakk>buckets_invar Bk; b < 2 * card \<V>; \<forall> w i. buckets_abstract Bk w = Some i \<longrightarrow> i \<le> b;
    j < num_verts; hl_lift Bk b k j = (Bk', b')\<rbrakk> \<Longrightarrow>
   buckets_invar Bk' \<and> b' < 2 * card \<V> \<and>
   (\<forall> w i. buckets_abstract Bk' w = Some i \<longrightarrow> i \<le> b') \<and>
   (\<forall> w. buckets_abstract Bk' w =
         map_option (\<lambda> i. if k < i \<and> i \<le> j then Suc num_verts else i) (buckets_abstract Bk w))"
proof(induction j arbitrary: Bk b)
  case (Suc j)
  note nb = lift_bounds[OF Suc.prems(4)]
  show ?case
  proof(cases "buckets_pick Bk (Suc j)")
    case None
    thus ?thesis
      using Suc.prems nb buckets_pick_lt(1)[of Bk "Suc j"] Suc.IH[of Bk b]
      by (auto simp: map_option_case le_Suc_eq split: option.split if_splits)
  next
    case (Some x)
    show ?thesis
    proof(cases "Suc j \<le> k")
      case False
      have "\<forall> w i. buckets_abstract (buckets_move Bk (Suc j) (Suc num_verts)) w = Some i \<longrightarrow>
                   i \<le> max b (Suc num_verts)"
        using Suc.prems(1,3) nb buckets_move_lt(2)[of Bk "Suc j" "Suc num_verts"]
        by (auto simp: le_max_iff_disj)
      moreover have "hl_lift (buckets_move Bk (Suc j) (Suc num_verts)) (max b (Suc num_verts)) k j = (Bk', b')"
        using False Some Suc.prems(5)
        by simp
      ultimately show ?thesis
        using False Suc.prems(1,2,4) nb buckets_move_lt[of Bk "Suc j" "Suc num_verts"]
              Suc.IH[of "buckets_move Bk (Suc j) (Suc num_verts)" "max b (Suc num_verts)"]
        by (auto simp: map_option_case le_Suc_eq le_max_iff_disj split: option.split)
    qed (use Suc.prems in \<open>auto simp: map_option_case split: option.split\<close>)
  qed
qed (auto simp: map_option_case split: option.split)

lemma min_lt_num_verts:
  "min b (num_verts - 1) < num_verts"
  using card_V_ge_2
  by (simp add: num_verts)

lemma lift_gap_effect:
  "\<lbrakk>buckets_invar Bk; \<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b; buckets_abstract Bk u = None;
    \<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k = l w; buckets_abstract Bk w = Some i\<rbrakk> \<Longrightarrow>
   (if l u < i \<and> i \<le> min b (num_verts - 1) then Suc num_verts else i) =
   gap_effect (relabel_effect f l u) (l u) w"
  using card_V_ge_2 buckets_universe_lt[of Bk]
  by (auto simp: gap_effect_def relabel_effect_def num_verts)

lemma hl_after_relabel_props:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
          "buckets_invar Bk" "b < 2 * card \<V>"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b" "buckets_abstract Bk u = None"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k = labels_abs st w"
          "hl_after_relabel Bk b u (pr_labels st) (pr_counts st) = (Bk', b', cur)"
  shows "buckets_invar Bk' \<and> b' < 2 * card \<V> \<and>
         (\<forall> w k. buckets_abstract Bk' w = Some k \<longrightarrow> k \<le> b') \<and>
         (\<forall> w k. buckets_abstract Bk' w = Some k \<longrightarrow>
                   k = relabel_gap_effect (flow_abs st) (labels_abs st) u w) \<and>
         cur = Some u \<and>
         (\<forall> w. buckets_abstract Bk' w = None \<longleftrightarrow> buckets_abstract Bk w = None)"
proof(cases "labels_abs st u < num_verts \<and> count_get (pr_counts st) (labels_abs st u) = 1")
  case True
  obtain Bk1 b1 where "hl_lift Bk b (labels_abs st u) (min b (num_verts - 1)) = (Bk1, b1)"
    by (cases "hl_lift Bk b (labels_abs st u) (min b (num_verts - 1))") auto
  note lp = hl_lift_props[OF assms(3-5) min_lt_num_verts this]
  have "i = gap_effect (relabel_effect (flow_abs st) (labels_abs st) u) (labels_abs st u) w"
    if "buckets_abstract Bk1 w = Some i" for w i
    using that lp assms(3,5-7) lift_gap_effect[of Bk b u "labels_abs st" w]
    by auto
  thus ?thesis
    using True lp assms(1,2,8) gap_iff_count[of st u] \<open>hl_lift Bk b (labels_abs st u) _ = (Bk1, b1)\<close>
    by (auto simp: hl_after_relabel_def relabel_gap_effect_def)
qed (use assms gap_iff_count[of st u] in
     \<open>auto simp: hl_after_relabel_def relabel_gap_effect_def relabel_effect_def\<close>)

text \<open>After a push from \<open>u\<close> to \<open>v\<close>, the new context holds the active vertices.\<close>

lemma bucket_iff_excess:
  "\<lbrakk>invar_state st; \<And> w. active_vertex s t (flow_abs st) w \<longleftrightarrow> buckets_abstract Bk w \<noteq> None \<or> w = u;
    v \<noteq> u; v \<in> \<V>\<rbrakk> \<Longrightarrow>
   buckets_abstract Bk v \<noteq> None \<longleftrightarrow> v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get (pr_excess st) v"
  using active_vertex_iff[of st v]
  by auto

lemma hl_after_push_props:
  assumes "invar_state st" "buckets_invar Bk" "b < 2 * card \<V>"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b" "buckets_abstract Bk u = None"
          "\<And> w. active_vertex s t (flow_abs st) w \<longleftrightarrow>
                 buckets_abstract Bk w \<noteq> None \<or> w = u"
          "\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j = labels_abs st w"
          "v \<noteq> u" "v \<in> \<V>" "labels_abs st' = labels_abs st"
          "\<And> w. active_vertex s t (flow_abs st') w \<longleftrightarrow>
                 (if w = u then keep
                  else if w = v then v \<noteq> s \<and> v \<noteq> t else active_vertex s t (flow_abs st) w)"
  shows "hl_ctx_invar (st'\<lparr>pr_ctx := hl_after_push Bk b u v keep (pr_excess st) (pr_labels st)\<rparr>)"
  using assms bucket_iff_excess[OF assms(1,6,8,9)] buckets_insert_lt[of Bk v "label_get (pr_labels st) v"]
  by (cases "v \<noteq> s \<and> v \<noteq> t \<and> ex_get (pr_excess st) v \<le> 0")
     (auto simp: hl_ctx_invar_def hl_after_push_def le_max_iff_disj label_bound)

text \<open>After an operation of the discharge of \<open>u\<close>, the new context holds the active vertices.\<close>

lemma hl_ctx_upd_props:
  assumes "invar_state st" "buckets_invar Bk" "b < 2 * card \<V>"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b" "buckets_abstract Bk u = None"
          "\<And> w. active_vertex s t (flow_abs st) w \<longleftrightarrow>
                 buckets_abstract Bk w \<noteq> None \<or> w = u"
          "\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j = labels_abs st w"
          "discharge_op True (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
  shows "hl_ctx_invar ((apply_op op st)\<lparr>pr_ctx :=
           hl_ctx_upd op Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)\<rparr>)"
proof(cases op)
  case (Push_Fwd d)
  thus ?thesis
    using assms(1,6,8) discharge_op_props[of st u True op] push_fstv_sndv[of "flow_abs st" "labels_abs st" "F d"]
          push_impl_props(3)[of st op d "F d"]
    by (simp add: hl_ctx_upd_def)
       (rule hl_after_push_props[OF assms(1-7)];
        auto simp: assms(1) good_op_def push_fwd_impl_active \<EE>_def snd_E_V)
next
  case (Push_Bwd d)
  thus ?thesis
    using assms(1,6,8) discharge_op_props[of st u True op] push_fstv_sndv[of "flow_abs st" "labels_abs st" "B d"]
          push_impl_props(3)[of st op d "B d"]
    by (simp add: hl_ctx_upd_def)
       (rule hl_after_push_props[OF assms(1-7)];
        auto simp: assms(1) good_op_def push_bwd_impl_active \<EE>_def fst_E_V)
next
  case (Advance v)
  then obtain e where "v \<in> \<V>" "current_res st v = Some e" "\<not> admissible (flow_abs st) (labels_abs st) e"
    using assms(1,6,8) discharge_op_props[of st u True op]
    by (auto simp: good_op_def)
  thus ?thesis
    using Advance assms(1-7) apply_op_active[of st op]
    by (auto simp: hl_ctx_invar_def hl_ctx_upd_def advance_impl_props(3) good_op_def)
next
  case (Relabel_Gap v)
  hence "v = u" "relabel_precond s t (flow_abs st) (labels_abs st) u"
    using assms(1,6,8) discharge_op_props[of st u True op]
    by (auto simp: discharge_op_def Let_def good_op_def split: if_splits)
  moreover obtain Bk' b' cur where "hl_after_relabel Bk b u (pr_labels st) (pr_counts st) = (Bk', b', cur)"
    by (cases "hl_after_relabel Bk b u (pr_labels st) (pr_counts st)") auto
  ultimately show ?thesis
    using Relabel_Gap assms(1,5,6) hl_after_relabel_props[OF assms(1) _ assms(2-5,7)]
          apply_op_active[OF assms(1), of op] relabel_gap_impl_props(2)[of st u]
    by (auto simp: hl_ctx_invar_def hl_ctx_upd_def good_op_def simp del: not_None_eq)
qed (use assms(1,6,8) discharge_op_props[of st u True op] in \<open>auto simp: discharge_op_def Let_def split: if_splits\<close>)

lemma hl_discharge_props:
  assumes "invar_state st" "buckets_invar Bk" "b < 2 * card \<V>"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b" "buckets_abstract Bk u = None"
          "\<And> w. active_vertex s t (flow_abs st) w \<longleftrightarrow>
                 buckets_abstract Bk w \<noteq> None \<or> w = u"
          "\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j = labels_abs st w"
          "hl_discharge Bk b u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op \<and> hl_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
  using assms discharge_op_props[of st u True] hl_ctx_upd_props[of st Bk b u]
  by (auto simp: hl_discharge_def Let_def apply_op_ctx)

lemma hl_select_find_props:
  "\<lbrakk>invar_state st; buckets_invar Bk; b < 2 * card \<V>;
    \<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> k \<le> b;
    \<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> k = labels_abs st v;
    \<And> v. active_vertex s t (flow_abs st) v \<longleftrightarrow> buckets_abstract Bk v \<noteq> None;
    hl_find Bk b = Some (k, u);
    hl_discharge (buckets_remove Bk u k) k u (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
      (pr_counts st) (pr_out st) (pr_in st) = (op, c)\<rbrakk> \<Longrightarrow>
   good_op st op \<and> hl_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
  using hl_find_props[of Bk b] bucket.buckets_remove[of Bk u k] hl_discharge_props[of st _ k u]
  by auto

lemma hl_select_props:
  assumes "invar_state st" "hl_ctx_invar st"
          "hl_select (pr_ctx st) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op \<and>
         (op \<noteq> Done \<longrightarrow> hl_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
proof(cases "pr_ctx st" rule: prod_cases3)
  case (fields Bk b cur)
  hence I: "buckets_invar Bk" "b < 2 * card \<V>"
           "\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> k \<le> b"
           "\<forall> u. cur = Some u \<longrightarrow> buckets_abstract Bk u = None"
           "\<And> v. active_vertex s t (flow_abs st) v \<longleftrightarrow>
                  buckets_abstract Bk v \<noteq> None \<or> cur = Some v"
           "\<forall> v k. buckets_abstract Bk v = Some k \<longrightarrow> k = labels_abs st v"
    using assms(2)
    by (simp_all add: hl_ctx_invar_def)
  show ?thesis
  proof(cases cur)
    case None
    show ?thesis
    proof(cases "hl_find Bk b")
      case (Some p)
      have "\<And> v. active_vertex s t (flow_abs st) v \<longleftrightarrow> buckets_abstract Bk v \<noteq> None"
        using I(5) None
        by simp
      from hl_select_find_props[OF assms(1) I(1-3,6) this] show ?thesis
        using Some fields None assms(3)
        by (cases p) (auto simp: hl_select_def)
    qed (use fields \<open>cur = None\<close> assms(3) I hl_find_props[of Bk b] in
         \<open>fastforce simp: hl_select_def good_op_def\<close>)
  next
    case (Some u)
    thus ?thesis
      using fields assms(1,3) I hl_discharge_props[of st Bk b u op c]
      by (auto simp: hl_select_def)
  qed
qed

lemma hl_init_fold:
  assumes "buckets_invar Bk" "b < 2 * card \<V>"
          "\<forall> w k. buckets_abstract Bk w = Some k \<longrightarrow> k \<le> b"
          "distinct vs" "set vs \<subseteq> \<V>" "\<forall> v \<in> set vs. buckets_abstract Bk v = None"
          "\<forall> v \<in> set vs. label_get l v < 2 * card \<V>"
          "foldl (hl_init_step x l) (Bk, b) vs = (Bk', b')"
          "\<forall> w j. buckets_abstract Bk w = Some j \<longrightarrow> j = label_get l w"
  shows "buckets_invar Bk' \<and> b' < 2 * card \<V> \<and>
         (\<forall> w k. buckets_abstract Bk' w = Some k \<longrightarrow> k \<le> b') \<and>
         (\<forall> w j. buckets_abstract Bk' w = Some j \<longrightarrow> j = label_get l w) \<and>
         (\<forall> w. buckets_abstract Bk' w \<noteq> None \<longleftrightarrow>
               buckets_abstract Bk w \<noteq> None \<or>
               (w \<in> set vs \<and> w \<noteq> s \<and> w \<noteq> t \<and> 0 < ex_get x w))"
  using assms
proof(induction vs arbitrary: Bk b)
  case (Cons v vs)
  show ?case
  proof(cases "v \<noteq> s \<and> v \<noteq> t \<and> 0 < ex_get x v")
    case True
    let ?B = "buckets_insert Bk v (label_get l v)"
    have "buckets_invar ?B" "max b (label_get l v) < 2 * card \<V>"
         "\<forall> w k. buckets_abstract ?B w = Some k \<longrightarrow> k \<le> max b (label_get l v)"
         "distinct vs" "set vs \<subseteq> \<V>" "\<forall> w \<in> set vs. buckets_abstract ?B w = None"
         "\<forall> w \<in> set vs. label_get l w < 2 * card \<V>"
         "foldl (hl_init_step x l) (?B, max b (label_get l v)) vs = (Bk', b')"
         "\<forall> w j. buckets_abstract ?B w = Some j \<longrightarrow> j = label_get l w"
      using True Cons.prems buckets_insert_lt[of Bk v "label_get l v"]
      by (auto simp: hl_init_step_def le_max_iff_disj)
    from Cons.IH[OF this] show ?thesis
      using True Cons.prems(1,5-7) buckets_insert_lt[of Bk v "label_get l v"]
      by auto
  next
    case False
    hence "foldl (hl_init_step x l) (Bk, b) vs = (Bk', b')"
      using Cons.prems(8)
      by (auto simp: hl_init_step_def)
    from Cons.IH[OF Cons.prems(1-3) _ _ _ _ this Cons.prems(9)] show ?thesis
      using False Cons.prems(4-7)
      by auto
  qed
qed simp

lemma hl_init_ctx_props:
  assumes "invar_state st"
          "pr_ctx st = hl_init_ctx (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                         (pr_in st)"
  shows "hl_ctx_invar st"
proof-
  obtain vs where "distinct vs" "set vs = \<V>"
    "bucket_vertex_fold (hl_init_step (pr_excess st) (pr_labels st)) (buckets_empty, 0) =
     foldl (hl_init_step (pr_excess st) (pr_labels st)) (buckets_empty, 0) vs"
    using bucket_vertex_fold
    by blast
  moreover obtain Bk b where "foldl (hl_init_step (pr_excess st) (pr_labels st)) (buckets_empty, 0) vs = (Bk, b)"
    by (cases "foldl (hl_init_step (pr_excess st) (pr_labels st)) (buckets_empty, 0) vs") auto
  ultimately show ?thesis
    using assms card_V_ge_2 bucket.buckets_empty hl_init_fold[of buckets_empty 0 vs "pr_labels st" "pr_excess st" Bk b]
    by (auto simp: hl_ctx_invar_def hl_init_ctx_def active_vertex_def label_bound elim!: invar_props_elims)
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
  by unfold_locales (simp_all add: hl.select_of_def hl_select_props hl_init_ctx_props)

end
