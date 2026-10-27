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

text \<open>After relabelling \<open>u\<close>, every admissible residual edge not leaving \<open>u\<close> was
      admissible before, and no residual edge entering \<open>u\<close> is admissible.\<close>

lemma relabel_admissible_tail:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u;
    admissible f (relabel_effect f l u) e; fstv e \<noteq> u\<rbrakk>
   \<Longrightarrow> admissible f l e"
  by (rule admissible_increased_labels[where l' = "relabel_effect f l u"])
     (use relabel_mono[of f l u] in \<open>auto simp: relabel_effect_def fun_upd_def\<close>)

lemma relabel_not_admissible_head:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u; sndv e = u\<rbrakk>
   \<Longrightarrow> \<not> admissible f (relabel_effect f l u) e"
  using relabel_increases[of f l u]
  by (cases "fstv e = u") (auto simp: relabel_effect_def elim!: admissibleE valid_labellingE)

lemma push_sorted:
  assumes "push_precond s t f l e" "sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) xs"
  shows "sorted_wrt (\<lambda> a b. \<not> adm_pair (push_effect f e) l b a) xs"
  using assms(2)
  by (rule sorted_wrt_mono_rel[rotated]) (use assms(1) in \<open>auto simp: adm_pair_def dest: push_admissible\<close>)

lemma relabel_sorted_filter:
  assumes "is_preflow s f" "valid_labelling s t f l" "relabel_precond s t f l u"
          "sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) xs"
  shows "sorted_wrt (\<lambda> a b. \<not> adm_pair f (relabel_effect f l u) b a) (filter (\<lambda> y. u \<noteq> y) xs)"
  using sorted_wrt_filter[OF assms(4)]
  by (rule sorted_wrt_mono_rel[rotated]) (use assms(1-3) in \<open>auto simp: adm_pair_def dest: relabel_admissible_tail\<close>)

lemma relabel_sorted:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u; distinct xs;
    sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) xs\<rbrakk> \<Longrightarrow>
   sorted_wrt (\<lambda> a b. \<not> adm_pair f (relabel_effect f l u) b a) (u # remove1 u xs)"
  using relabel_sorted_filter[of f l u xs] relabel_not_admissible_head[of f l u]
  by (auto simp: distinct_remove1_removeAll removeAll_filter_not_eq adm_pair_def)

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

text \<open>The first active vertex at or after \<open>u\<close>, looking at no more than \<open>n\<close>
      vertices.\<close>

fun rtf_scan where
  "rtf_scan L x 0 u = None"
| "rtf_scan L x (Suc n) u =
     (if 0 < ex_get x u then Some u
      else case list_next L u of None \<Rightarrow> None | Some w \<Rightarrow> rtf_scan L x n w)"

text \<open>One discharge step on the current vertex \<open>u\<close>. The flag records whether \<open>u\<close> has
      been relabelled during its discharge.\<close>

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

text \<open>The invariant for a current vertex \<open>u\<close> in the list \<open>xs\<close>. If \<open>u\<close> has
      not been relabelled during its discharge, \<open>xs\<close> is sorted topologically with respect to
      the admissible residual edges and all vertices before \<open>u\<close> are inactive. If \<open>u\<close> has
      been relabelled, the list obtained by moving \<open>u\<close> to the front is sorted.\<close>

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
  shows "(rtf_scan L x n u = None \<longrightarrow>
            (\<forall> v \<in> set (list_abstract L). \<not> 0 < ex_get x v)) \<and>
         (\<forall> w. rtf_scan L x n u = Some w \<longrightarrow> 0 < ex_get x w \<and>
              (\<exists> xs' ys'. list_abstract L = xs' @ w # ys' \<and>
                 (\<forall> v \<in> set xs'. \<not> 0 < ex_get x v)))"
  using assms(2-4)
proof(induction ys arbitrary: xs u n)
  case Nil
  thus ?case
    using assms(1) vlist.list_next[of L xs u "[]"]
    by (cases n) auto
next
  case (Cons y ys)
  obtain m where "n = Suc m" "length (y # ys) \<le> m"
    using Cons.prems(2)
    by (cases n) auto
  moreover have "list_next L u = Some y"
    using assms(1) Cons.prems(1) vlist.list_next[of L xs u "y # ys"]
    by simp
  ultimately show ?case
  proof(cases "0 < ex_get x u")
    case False
    thus ?thesis
      using Cons.prems(1,3) Cons.IH[of "xs @ [u]" y m] \<open>n = Suc m\<close> \<open>length (y # ys) \<le> m\<close>
            \<open>list_next L u = Some y\<close>
      by simp
  qed (use Cons.prems(1,3) in auto)
qed

text \<open>A push from the current vertex and a relabel of it preserve the invariant of the cursor.\<close>

lemma push_adm_pair:
  "\<lbrakk>push_precond s t f l e; fstv e = u\<rbrakk> \<Longrightarrow> adm_pair f l u (sndv e)"
  by (auto simp: adm_pair_def push_precond_def)

lemma rtf_cur_invar_push:
  assumes "push_precond s t f l e" "fstv e = u" "rtf_cur_invar f l xs u rel"
  shows "rtf_cur_invar (push_effect f e) l xs u rel"
proof(cases rel)
  case False
  then obtain ys zs where "xs = ys @ u # zs" "\<forall> v \<in> set ys. \<not> active_vertex s t f v"
                          "\<forall> v \<in> set ys. \<not> adm_pair f l u v"
    using assms(3)
    by (auto simp: rtf_cur_invar_def sorted_wrt_append)
  thus ?thesis
    using False assms push_sorted[of f l e xs] push_active[of f l e] push_adm_pair[of f l e u]
    by (auto simp: rtf_cur_invar_def)
qed (use assms push_sorted[of f l e "u # remove1 u xs"] in \<open>simp add: rtf_cur_invar_def\<close>)

lemma rtf_cur_invar_relabel:
  "\<lbrakk>is_preflow s f; valid_labelling s t f l; relabel_precond s t f l u; distinct xs;
    rtf_cur_invar f l xs u rel\<rbrakk>
   \<Longrightarrow> rtf_cur_invar f (relabel_effect f l u) xs u True"
  using relabel_sorted[of f l u "u # remove1 u xs"] relabel_sorted[of f l u xs]
  by (auto simp: rtf_cur_invar_def split: if_splits)

lemma rtf_discharge_props:
  assumes "invar_state st" "active_vertex s t (flow_abs st) u" "distinct xs"
          "rtf_cur_invar (flow_abs st) (labels_abs st) xs u rel"
          "discharge_op False (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = op"
  shows "rtf_cur_invar (flow_abs (apply_op op st)) (labels_abs (apply_op op st)) xs u
           (case op of Relabel _ \<Rightarrow> True | _ \<Rightarrow> rel)"
proof(cases op)
  case (Push_Fwd d)
  thus ?thesis
    using assms discharge_op_props[of st u False op] push_impl_props(2,3)[of st op d "F d"]
    by (auto simp: good_op_def intro: rtf_cur_invar_push)
next
  case (Push_Bwd d)
  thus ?thesis
    using assms discharge_op_props[of st u False op] push_impl_props(2,3)[of st op d "B d"]
    by (auto simp: good_op_def intro: rtf_cur_invar_push)
next
  case (Advance v)
  then obtain e where "v \<in> \<V>" "current_res st v = Some e" "\<not> admissible (flow_abs st) (labels_abs st) e"
    using assms discharge_op_props[of st u False op]
    by (auto simp: good_op_def)
  thus ?thesis
    using Advance assms(1,4)
    by (simp add: advance_impl_props(2,3))
next
  case (Relabel v)
  hence "v = u"
    using assms(5)
    by (auto simp: discharge_op_def Let_def split: if_splits)
  thus ?thesis
    using Relabel assms discharge_op_props[of st u False op] relabel_impl_props(2,3)[of st u]
    by (auto simp: good_op_def intro: rtf_cur_invar_relabel elim!: invar_props_elims)
qed (use assms discharge_op_props[of st u False op] in \<open>auto simp: discharge_op_def Let_def split: if_splits\<close>)

lemma rtf_discharge_ctx:
  assumes "invar_state st" "list_invar L" "set (list_abstract L) = \<V> - {s, t}"
          "active_vertex s t (flow_abs st) u"
          "rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) u rel"
          "rtf_discharge L u rel (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op \<and> rtf_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
  using assms discharge_op_props[of st u False] vlist.list_universe[of L] rtf_discharge_props[of st u _ rel]
  by (auto simp: rtf_discharge_def Let_def apply_op_ctx rtf_ctx_invar_def)

lemma rtf_active_iff:
  "\<lbrakk>invar_state st; set (list_abstract L) = \<V> - {s, t}\<rbrakk>
   \<Longrightarrow> active_vertex s t (flow_abs st) v \<longleftrightarrow>
       v \<in> set (list_abstract L) \<and> 0 < ex_get (pr_excess st) v"
  by (auto simp: active_vertex_def elim!: invar_props_elims)

text \<open>When the discharge of the current vertex \<open>u\<close> ends, the list after the optional move to the
      front is sorted and has no active vertex before \<open>u\<close>.\<close>

lemma rtf_move_props:
  assumes "list_invar L" "set (list_abstract L) = \<V> - {s, t}" "rtf_cur_invar f l (list_abstract L) u rel"
          "L' = (if rel then list_move_to_front L u else L)"
  shows "list_invar L' \<and> set (list_abstract L') = \<V> - {s, t} \<and>
         sorted_wrt (\<lambda> a b. \<not> adm_pair f l b a) (list_abstract L') \<and>
         (\<exists> xs ys. list_abstract L' = xs @ u # ys \<and>
            (\<forall> v \<in> set xs. \<not> active_vertex s t f v))"
  using assms vlist.list_move_to_front[of L u] vlist.list_universe[of L]
  by (cases rel) (auto simp: rtf_cur_invar_def Cons_eq_append_conv)

text \<open>The scan for the next active vertex after \<open>u\<close>.\<close>

lemma rtf_next_props:
  assumes "invar_state st"
          "list_invar L \<and> set (list_abstract L) = \<V> - {s, t} \<and>
           sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) (list_abstract L) \<and>
           (\<exists> xs ys. list_abstract L = xs @ u # ys \<and>
              (\<forall> v \<in> set xs. \<not> active_vertex s t (flow_abs st) v))"
          "\<not> 0 < ex_get (pr_excess st) u"
          "(case list_next L u of
              None \<Rightarrow> (Done, (L, None, False))
            | Some w \<Rightarrow>
                (case rtf_scan L (pr_excess st) num_verts w of
                   None \<Rightarrow> (Done, (L, None, False))
                 | Some w' \<Rightarrow> rtf_discharge L w' False (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st)
                                (pr_in st))) = (op, c)"
  shows "good_op st op \<and>
         (op \<noteq> Done \<longrightarrow> rtf_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
proof-
  obtain xs ys where L: "list_invar L" "set (list_abstract L) = \<V> - {s, t}"
      "sorted_wrt (\<lambda> a b. \<not> adm_pair (flow_abs st) (labels_abs st) b a) (list_abstract L)"
      "list_abstract L = xs @ u # ys" "\<forall> v \<in> set xs. \<not> active_vertex s t (flow_abs st) v"
      "\<And> v. active_vertex s t (flow_abs st) v \<longleftrightarrow> v \<in> set (list_abstract L) \<and> 0 < ex_get (pr_excess st) v"
    using assms(1,2) rtf_active_iff[of st L]
    by blast
  have "\<forall> v \<in> set (xs @ [u]). \<not> 0 < ex_get (pr_excess st) v"
    using L(4-6) assms(3)
    by auto
  moreover have "length (list_abstract L) \<le> num_verts"
    using L(1,2) distinct_card[of "list_abstract L"] vlist.list_universe[of L] \<V>_finite
          card_mono[of \<V> "\<V> - {s, t}"]
    by (auto simp: num_verts)
  ultimately show ?thesis
  proof(cases ys)
    case (Cons w ys')
    have "list_abstract L = (xs @ [u]) @ w # ys'" "length (w # ys') \<le> num_verts"
      using L(4) Cons \<open>length (list_abstract L) \<le> num_verts\<close>
      by auto
    note scan =
      rtf_scan_props[OF L(1) this \<open>\<forall> v \<in> set (xs @ [u]). \<not> 0 < ex_get (pr_excess st) v\<close>]
    show ?thesis
    proof(cases "rtf_scan L (pr_excess st) num_verts w")
      case (Some w')
      with scan have "active_vertex s t (flow_abs st) w'"
                     "rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) w' False"
        using L(3,6)
        by (auto simp: rtf_cur_invar_def)
      moreover have "rtf_discharge L w' False (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) = (op, c)"
        using assms(4) Some Cons L(1,4) vlist.list_next[of L xs u ys]
        by simp
      ultimately show ?thesis
        using assms(1) L(1,2) rtf_discharge_ctx[of st L]
        by blast
    qed (use assms(4) Cons scan L(1,4,6) vlist.list_next[of L xs u ys] in \<open>auto simp: good_op_def\<close>)
  qed (use assms(3,4) L(1,4,6) vlist.list_next[of L xs u ys] in \<open>auto simp: good_op_def\<close>)
qed

lemma rtf_select_props:
  assumes "invar_state st" "rtf_ctx_invar st"
          "rtf_select (pr_ctx st) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st)
             (pr_out st) (pr_in st) = (op, c)"
  shows "good_op st op \<and>
         (op \<noteq> Done \<longrightarrow> rtf_ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
proof-
  obtain L cur rel where ctx: "pr_ctx st = (L, cur, rel)" "list_invar L" "set (list_abstract L) = \<V> - {s, t}"
    using assms(2)
    by (cases "pr_ctx st") (auto simp: rtf_ctx_invar_def)
  show ?thesis
  proof(cases cur)
    case (Some u)
    hence cI: "rtf_cur_invar (flow_abs st) (labels_abs st) (list_abstract L) u rel"
      using assms(2) ctx(1)
      by (simp add: rtf_ctx_invar_def)
    show ?thesis
    proof(cases "0 < ex_get (pr_excess st) u")
      case True
      moreover have "u \<in> set (list_abstract L)"
        using cI
        by (auto simp: rtf_cur_invar_def split: if_splits)
      ultimately show ?thesis
        using assms ctx Some cI rtf_discharge_ctx[of st L u rel] rtf_active_iff[of st L]
        by (simp add: rtf_select_def)
    next
      case False
      thus ?thesis
        using assms(3) ctx(1) Some rtf_next_props[OF assms(1) rtf_move_props[OF ctx(2,3) cI refl] False]
        by (simp add: rtf_select_def Let_def)
    qed
  qed (use assms(2,3) ctx(1) in \<open>simp add: rtf_select_def rtf_ctx_invar_def good_op_def\<close>)
qed

lemma rtf_init_fold:
  assumes "list_invar L" "distinct vs" "set vs \<subseteq> \<V>" "set vs \<inter> set (list_abstract L) = {}"
  shows "list_invar (foldl rtf_init_step L vs) \<and>
         list_abstract (foldl rtf_init_step L vs) =
         rev (filter (\<lambda> v. v \<noteq> s \<and> v \<noteq> t) vs) @ list_abstract L"
  using assms
  by (induction vs arbitrary: L) (auto simp: rtf_init_step_def vlist.list_push_front)

lemma rtf_init_ctx_props:
  assumes "invar_state st" "\<forall> d \<in> \<E>. flow_abs st d = init_flow s d" "labels_abs st = init_labels s"
          "pr_ctx st = rtf_init_ctx (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_out st)
                         (pr_in st)"
  shows "rtf_ctx_invar st"
proof-
  define L where "L = list_vertex_fold rtf_init_step list_empty"
  obtain vs where "distinct vs" "set vs = \<V>" "L = foldl rtf_init_step list_empty vs"
    using list_vertex_fold[of rtf_init_step list_empty]
    by (auto simp: L_def)
  hence "list_invar L" "set (list_abstract L) = \<V> - {s, t}"
    using rtf_init_fold[of list_empty vs] vlist.list_empty
    by auto
  thus ?thesis
    using assms(2-4) vlist.list_first[of L] init_flow_agree(4)[of "flow_abs st"]
    by (cases "list_abstract L")
       (auto simp: rtf_ctx_invar_def rtf_init_ctx_def L_def[symmetric] rtf_cur_invar_def adm_pair_def
                   active_vertex_def Cons_eq_append_conv)
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
  by unfold_locales (simp_all add: rtf.select_of_def rtf_select_props rtf_init_ctx_props)

end
