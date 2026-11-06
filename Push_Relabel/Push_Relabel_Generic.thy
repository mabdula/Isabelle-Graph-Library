theory Push_Relabel_Generic
  imports
    Push_Relabel_Basic
    Data_Structures.Fixed_Univ_Map_Specs
    Directed_Set_Graphs.Edge_Iterators
begin

named_theorems call_cond_elims
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems termination_intros
section \<open>The Generic Push-Relabel Algorithm on Abstract Data Types\<close>

subsection \<open>State and Operations\<close>

text \<open>The state of the algorithm consists of the forward and backward residual capacities
      (two maps on the edges; the backward residual capacity of an edge is its flow), the
      excesses, the labels, the number of vertices carrying each label (for the gap heuristic),
      an iterator over the outgoing and one over the ingoing edges of every vertex, and an
      opaque context owned by the strategy. All maps are total maps on fixed universes.

      The residual edges leaving a vertex \<open>u\<close> are the forward copies of the edges leaving \<open>u\<close>,
      followed by the backward copies of the edges entering \<open>u\<close>. The current residual edge of
      \<open>u\<close> is taken from the outgoing iterator as long as it has edges left, and from the ingoing
      iterator afterwards.

      In every iteration, the strategy @{term select} looks at the state and decides on one
      operation: push forward or backward along an edge, advance to the next residual edge of a
      vertex, relabel a vertex (optionally followed by a gap relabelling) or stop. The operations
      themselves are implemented here once, on the abstract data types, and never construct
      residual edges. The contract of the strategy is stated in terms of the mathematical objects
      of @{theory Push_Relabel.Push_Relabel_Basic}.\<close>

datatype ('e, 'v) pr_op = Push_Fwd 'e | Push_Bwd 'e | Advance 'v | Relabel 'v | Relabel_Gap 'v | Done

record ('emap, 'exc, 'lab, 'cnt, 'g, 'ctx) pr_state =
  pr_fwd :: 'emap
  pr_bwd :: 'emap
  pr_excess :: 'exc
  pr_labels :: 'lab
  pr_counts :: 'cnt
  pr_out :: 'g
  pr_in :: 'g
  pr_ctx :: 'ctx

locale push_relabel_ops =
  flow_network_spec where fst = fst +
  edge_map: fixed_univ_map \<E> emap_invar emap_upd emap_get +
  ex_map: fixed_univ_map \<V> ex_invar ex_upd ex_get +
  label_map: fixed_univ_map \<V> label_invar label_upd label_get +
  count_map: fixed_univ_map "{..<2 * card \<V>}" count_invar count_upd count_get +
  bidirectional_iterator where fst = fst and snd = snd
      and out_invar = out_invar and out_abstract = out_abstract
      and out_current = out_current and out_has = out_has
      and out_iterated = out_iterated and out_remaining = out_remaining
      and out_move = out_move and out_reset = out_reset
      and in_invar = in_invar and in_abstract = in_abstract
      and in_current = in_current and in_has = in_has
      and in_iterated = in_iterated and in_remaining = in_remaining
      and in_move = in_move and in_reset = in_reset +
  outr: indexed_iterable_set_reset_to where idx_invar = out_invar and idx_abstract = out_abstract
      and idx_current = out_current and idx_has = out_has and idx_iterated = out_iterated
      and idx_remaining = out_remaining and idx_move = out_move and idx_reset = out_reset
      and K = \<V> and idx_reset_to = out_reset_to +
  inr: indexed_iterable_set_reset_to where idx_invar = in_invar and idx_abstract = in_abstract
      and idx_current = in_current and idx_has = in_has and idx_iterated = in_iterated
      and idx_remaining = in_remaining and idx_move = in_move and idx_reset = in_reset
      and K = \<V> and idx_reset_to = in_reset_to
  for fst :: "'e \<Rightarrow> 'v"
  and emap_invar and emap_upd :: "'emap \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'emap" and emap_get
  and ex_invar and ex_upd :: "'exc \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'exc" and ex_get
  and label_invar and label_upd :: "'lab \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lab" and label_get
  and count_invar and count_upd :: "'cnt \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'cnt" and count_get
  and out_invar :: "'g \<Rightarrow> bool" and out_abstract out_current out_has out_iterated out_remaining
  and out_move out_reset
  and in_invar :: "'g \<Rightarrow> bool" and in_abstract in_current in_has in_iterated in_remaining
  and in_move in_reset
  and out_reset_to :: "'g \<Rightarrow> 'v \<Rightarrow> 'e \<Rightarrow> 'g" and in_reset_to :: "'g \<Rightarrow> 'v \<Rightarrow> 'e \<Rightarrow> 'g" +
  fixes s t :: 'v
    and caps :: 'emap
    and num_verts :: nat
    and gap_fold :: "'lab \<Rightarrow> nat \<Rightarrow> ('lab \<times> 'cnt \<times> 'g \<times> 'g \<Rightarrow> 'v \<Rightarrow> 'lab \<times> 'cnt \<times> 'g \<times> 'g)
                     \<Rightarrow> 'lab \<times> 'cnt \<times> 'g \<times> 'g \<Rightarrow> 'lab \<times> 'cnt \<times> 'g \<times> 'g"
    and edge_fold :: "('emap \<times> 'emap \<times> 'exc \<Rightarrow> 'e \<Rightarrow> 'emap \<times> 'emap \<times> 'exc)
                      \<Rightarrow> 'emap \<times> 'emap \<times> 'exc \<Rightarrow> 'emap \<times> 'emap \<times> 'exc"
    and emap_init :: 'emap
    and ex_init :: 'exc
    and label_init :: 'lab
    and count_init :: 'cnt
    and out_init in_init :: 'g

text \<open>The strategy is a separate parameter, so that strategies can be defined on top of the
      operations and invariants without referring to themselves.\<close>

locale push_relabel_spec =
  push_relabel_ops where fst = fst and emap_upd = emap_upd and ex_upd = ex_upd
      and label_upd = label_upd and count_upd = count_upd and out_invar = out_invar
  for fst :: "'e \<Rightarrow> 'v"
  and emap_upd :: "'emap \<Rightarrow> 'e \<Rightarrow> real \<Rightarrow> 'emap"
  and ex_upd :: "'exc \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'exc"
  and label_upd :: "'lab \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lab"
  and count_upd :: "'cnt \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'cnt"
  and out_invar :: "'g \<Rightarrow> bool" +
  fixes select :: "'ctx \<Rightarrow> 'emap \<Rightarrow> 'emap \<Rightarrow> 'exc \<Rightarrow> 'lab \<Rightarrow> 'cnt \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> ('e, 'v) pr_op \<times> 'ctx"
    and init_ctx :: "'emap \<Rightarrow> 'emap \<Rightarrow> 'exc \<Rightarrow> 'lab \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'ctx"

context push_relabel_ops
begin

subsubsection \<open>Operations\<close>

text \<open>Admissibility of the forward and of the backward copy of an edge.\<close>

definition "admissible_fwd_impl fw l d =
  (emap_get fw d > 0 \<and> label_get l (fst d) = label_get l (snd d) + 1)"

definition "admissible_bwd_impl bw l d =
  (emap_get bw d > 0 \<and> label_get l (snd d) = label_get l (fst d) + 1)"

text \<open>Sending \<open>\<delta>\<close> units of flow along an edge (backwards if \<open>\<delta>\<close> is
      negative) changes both residual capacities of the edge and the excesses of its two endpoints.\<close>

definition "augment_impl d \<delta> fw bw x =
  (let fw' = emap_upd fw d (emap_get fw d - \<delta>);
       bw' = emap_upd bw d (emap_get bw d + \<delta>);
       x1 = ex_upd x (fst d) (ex_get x (fst d) - \<delta>);
       x' = ex_upd x1 (snd d) (ex_get x1 (snd d) + \<delta>)
   in (fw', bw', x'))"

definition "push_fwd_impl d st =
  (let fw = pr_fwd st; bw = pr_bwd st; x = pr_excess st;
       \<gamma> = min (ex_get x (fst d)) (emap_get fw d) in
   case augment_impl d \<gamma> fw bw x of
     (fw', bw', x') \<Rightarrow> st\<lparr>pr_fwd := fw', pr_bwd := bw', pr_excess := x'\<rparr>)"

definition "push_bwd_impl d st =
  (let fw = pr_fwd st; bw = pr_bwd st; x = pr_excess st;
       \<gamma> = min (ex_get x (snd d)) (emap_get bw d) in
   case augment_impl d (- \<gamma>) fw bw x of
     (fw', bw', x') \<Rightarrow> st\<lparr>pr_fwd := fw', pr_bwd := bw', pr_excess := x'\<rparr>)"

text \<open>Advancing passes the current residual edge of a vertex and then all following residual
      edges that are not admissible, so that the next operation on the vertex is a push or a
      relabelling. Both directions are skipped by instances of the same function.\<close>

partial_function (tailrec) skip_scan ::
  "('g \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> ('g \<Rightarrow> 'v \<Rightarrow> 'e) \<Rightarrow> ('g \<Rightarrow> 'v \<Rightarrow> 'g) \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow> 'v \<Rightarrow> 'g \<Rightarrow> 'g"
  where
  "skip_scan has cur move adm u C =
     (if has C u \<and> \<not> adm (cur C u) then skip_scan has cur move adm u (move C u) else C)"

definition "skip_impl u st =
  (let og = skip_scan out_has out_current out_move (admissible_fwd_impl (pr_fwd st) (pr_labels st))
              u (pr_out st) in
   if out_has og u then st\<lparr>pr_out := og\<rparr>
   else st\<lparr>pr_out := og, pr_in := skip_scan in_has in_current in_move
                                   (admissible_bwd_impl (pr_bwd st) (pr_labels st)) u (pr_in st)\<rparr>)"

definition "move_impl u st =
  (if out_has (pr_out st) u then st\<lparr>pr_out := out_move (pr_out st) u\<rparr>
   else st\<lparr>pr_in := in_move (pr_in st) u\<rparr>)"

definition "advance_impl u st = skip_impl u (move_impl u st)"

text \<open>Changing the label of a vertex also updates the counts.\<close>

definition "change_label l cnt v k' =
  (let k = label_get l v; cnt1 = count_upd cnt k (count_get cnt k - 1)
   in (label_upd l v k', count_upd cnt1 k' (count_get cnt1 k' + 1)))"

text \<open>The new label of a vertex is the minimum label over the residual edges leaving it. It is
      computed by one scan over the outgoing edges (forward residual capacities, heads) and one
      over the ingoing edges (backward residual capacities, tails). Both scans are instances of
      the same function, which is parametrised by the iterator operations, the residual
      capacity map and the endpoint function. Together with the minimum, a scan keeps the edge
      at which the minimum was improved last, i.e. the first edge reaching the final minimum.

      Afterwards, the current residual edge of the vertex is the first one reaching the minimum,
      which is admissible after the relabelling; all residual edges before it lead to larger
      labels and stay inadmissible. If the ingoing scan improved the minimum of the outgoing
      one, the outgoing iterator stays exhausted and the ingoing one is set to that edge;
      otherwise the outgoing iterator is set to the edge and the ingoing one is reset.\<close>

partial_function (tailrec) min_scan ::
  "('g \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> ('g \<Rightarrow> 'v \<Rightarrow> 'e) \<Rightarrow> ('g \<Rightarrow> 'v \<Rightarrow> 'g) \<Rightarrow> 'emap \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow> 'lab
   \<Rightarrow> 'v \<Rightarrow> 'g \<Rightarrow> (nat \<times> 'e) option \<Rightarrow> 'g \<times> (nat \<times> 'e) option" where
  "min_scan has cur move r endp l u C mb =
     (if has C u
      then (let d = cur C u in
            if emap_get r d > 0
            then (let k = label_get l (endp d) in
                  if (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> k < k')
                  then min_scan has cur move r endp l u (move C u) (Some (k, d))
                  else min_scan has cur move r endp l u (move C u) mb)
            else min_scan has cur move r endp l u (move C u) mb)
      else (C, mb))"

definition "new_label fw bw l og ig u =
  (case min_scan out_has out_current out_move fw snd l u (out_reset og u) None of (og1, mb1) \<Rightarrow>
   case min_scan in_has in_current in_move bw fst l u (in_reset ig u) mb1 of (ig1, mb2) \<Rightarrow>
   case the mb2 of (m, d) \<Rightarrow>
     (if (case mb1 of None \<Rightarrow> True | Some (m1, _) \<Rightarrow> m < m1)
      then (og1, in_reset_to ig1 u d, m + 1)
      else (out_reset_to og1 u d, in_reset ig1 u, m + 1)))"

definition "relabel_impl u st =
  (case new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u of
     (og', ig', k') \<Rightarrow>
     (case change_label (pr_labels st) (pr_counts st) u k' of (l', cnt') \<Rightarrow>
        st\<lparr>pr_labels := l', pr_counts := cnt', pr_out := og', pr_in := ig'\<rparr>))"

text \<open>Gap relabelling: all vertices with labels strictly between \<open>k\<close> and the number of
      vertices are lifted above the source. Their iterators are reset. Only these vertices are
      visited: @{term gap_fold} enumerates them from the label map.\<close>

definition "gap_step k = (\<lambda> (l, cnt, og, ig) v.
  (let lv = label_get l v in
   if k < lv \<and> lv < num_verts
   then (case change_label l cnt v (num_verts + 1) of
           (l', cnt') \<Rightarrow> (l', cnt', out_reset og v, in_reset ig v))
   else (l, cnt, og, ig)))"

definition "gap_impl k st =
  (case gap_fold (pr_labels st) k (gap_step k) (pr_labels st, pr_counts st, pr_out st, pr_in st)
   of (l, cnt, og, ig) \<Rightarrow> st\<lparr>pr_labels := l, pr_counts := cnt, pr_out := og, pr_in := ig\<rparr>)"

definition "relabel_gap_impl u st =
  (let k = label_get (pr_labels st) u; st' = relabel_impl u st in
   if k < num_verts \<and> count_get (pr_counts st') k = 0 then gap_impl k st' else st')"

fun apply_op where
  "apply_op (Push_Fwd d) st = push_fwd_impl d st"
| "apply_op (Push_Bwd d) st = push_bwd_impl d st"
| "apply_op (Advance u) st = advance_impl u st"
| "apply_op (Relabel u) st = relabel_impl u st"
| "apply_op (Relabel_Gap u) st = relabel_gap_impl u st"
| "apply_op Done st = st"

text \<open>The operations do not touch the context of the strategy.\<close>

lemma relabel_impl_ctx: "relabel_impl u (st\<lparr>pr_ctx := c\<rparr>)
                         = (relabel_impl u st)\<lparr>pr_ctx := c\<rparr>"
  by (simp add: relabel_impl_def split: prod.splits)

lemma gap_impl_ctx: "gap_impl k (st\<lparr>pr_ctx := c\<rparr>) = (gap_impl k st)\<lparr>pr_ctx := c\<rparr>"
  by (simp add: gap_impl_def split: prod.splits)

lemma apply_op_ctx: "apply_op op (st\<lparr>pr_ctx := c\<rparr>) = (apply_op op st)\<lparr>pr_ctx := c\<rparr>"
  by (cases op)
     (simp_all add: push_fwd_impl_def push_bwd_impl_def advance_impl_def skip_impl_def move_impl_def
                    relabel_gap_impl_def relabel_impl_ctx gap_impl_ctx Let_def split: prod.splits)

end


context push_relabel_spec
begin

subsubsection \<open>The Loop\<close>

definition "select_of st =
  select (pr_ctx st) (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st) (pr_counts st) (pr_out st)
    (pr_in st)"

function (domintros) push_relabel_loop where
  "push_relabel_loop st =
     (case select_of st of (op, c) \<Rightarrow>
        if op = Done then st\<lparr>pr_ctx := c\<rparr>
        else push_relabel_loop (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"
  by pat_completeness auto

partial_function (tailrec) push_relabel_loop_impl where
  "push_relabel_loop_impl st =
     (case select_of st of (op, c) \<Rightarrow>
        if op = Done then st\<lparr>pr_ctx := c\<rparr>
        else push_relabel_loop_impl (apply_op op (st\<lparr>pr_ctx := c\<rparr>)))"

lemma push_relabel_loop_impl_same:
  "push_relabel_loop_dom st \<Longrightarrow> push_relabel_loop_impl st = push_relabel_loop st"
  apply(induction rule: push_relabel_loop.pinduct)
  apply(subst push_relabel_loop_impl.simps)
  apply(subst push_relabel_loop.psimps)
  by (auto split: prod.splits)

definition "push_relabel_upd st = (case select_of st of (op, c) \<Rightarrow> apply_op op (st\<lparr>pr_ctx := c\<rparr>))"

definition "push_relabel_ret st = st\<lparr>pr_ctx := prod.snd (select_of st)\<rparr>"

definition "push_relabel_ret_cond st = (prod.fst (select_of st) = Done)"

definition "push_relabel_upd_cond st = (prod.fst (select_of st) \<noteq> Done)"

lemma push_relabel_cases:
  "\<lbrakk>push_relabel_ret_cond st \<Longrightarrow> P; push_relabel_upd_cond st \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: push_relabel_ret_cond_def push_relabel_upd_cond_def)

lemma push_relabel_upd_cond[call_cond_elims]:
  "\<lbrakk>push_relabel_upd_cond st; \<And> op c. \<lbrakk>select_of st = (op, c); op \<noteq> Done\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (cases "select_of st") (auto simp: push_relabel_upd_cond_def)

lemma push_relabel_ret_cond[call_cond_elims]:
  "\<lbrakk>push_relabel_ret_cond st; \<And> c. select_of st = (Done, c) \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (cases "select_of st") (auto simp: push_relabel_ret_cond_def)

lemma push_relabel_domintros:
  "push_relabel_ret_cond st \<Longrightarrow> push_relabel_loop_dom st"
  "\<lbrakk>push_relabel_upd_cond st; push_relabel_loop_dom (push_relabel_upd st)\<rbrakk>
   \<Longrightarrow> push_relabel_loop_dom st"
  by (cases "select_of st";
      auto intro: push_relabel_loop.domintros simp: push_relabel_ret_cond_def push_relabel_upd_def)+

lemma push_relabel_simps:
  "push_relabel_ret_cond st \<Longrightarrow> push_relabel_loop st = push_relabel_ret st"
  "\<lbrakk>push_relabel_loop_dom st; push_relabel_upd_cond st\<rbrakk>
   \<Longrightarrow> push_relabel_loop st = push_relabel_loop (push_relabel_upd st)"
  by (cases "select_of st";
      simp add: push_relabel_loop.psimps push_relabel_domintros(1) push_relabel_ret_cond_def
                push_relabel_ret_def push_relabel_upd_cond_def push_relabel_upd_def)+

lemma push_relabel_induct[consumes 1]:
  assumes "push_relabel_loop_dom st"
          "\<And> st. \<lbrakk>push_relabel_loop_dom st;
                   push_relabel_upd_cond st \<Longrightarrow> P (push_relabel_upd st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  using assms(1)
proof(induction rule: push_relabel_loop.pinduct)
  case (1 st)
  thus ?case
    by (cases "select_of st") (auto intro: assms(2) simp: push_relabel_upd_cond_def push_relabel_upd_def)
qed

end

context push_relabel_ops
begin

subsubsection \<open>Initialisation\<close>

text \<open>The residual capacities are initialised from the capacities in one pass over the edges.
      All edges leaving the source (except self-loops) are saturated in the same pass.\<close>

definition "init_step = (\<lambda> (fw, bw, x) d.
  (let c = emap_get caps d in
   if fst d = s \<and> snd d \<noteq> s
   then (let x1 = ex_upd x s (ex_get x s - c)
         in (emap_upd fw d 0, emap_upd bw d c, ex_upd x1 (snd d) (ex_get x1 (snd d) + c)))
   else (emap_upd fw d c, emap_upd bw d 0, x)))"

end

context push_relabel_spec
begin

definition "init_state =
  (case edge_fold init_step (emap_init, emap_init, ex_init) of (fw, bw, x) \<Rightarrow>
     (let l = label_upd label_init s num_verts;
          cnt = count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1
      in \<lparr>pr_fwd = fw, pr_bwd = bw, pr_excess = x, pr_labels = l, pr_counts = cnt,
          pr_out = out_init, pr_in = in_init, pr_ctx = init_ctx fw bw x l out_init in_init\<rparr>))"

definition "push_relabel = pr_bwd (push_relabel_loop_impl init_state)"

lemmas [code] = admissible_fwd_impl_def admissible_bwd_impl_def augment_impl_def push_fwd_impl_def
  push_bwd_impl_def skip_scan.simps skip_impl_def move_impl_def advance_impl_def
  change_label_def min_scan.simps new_label_def relabel_impl_def gap_step_def gap_impl_def
  relabel_gap_impl_def apply_op.simps select_of_def push_relabel_loop_impl.simps init_step_def
  init_state_def push_relabel_def

end

context push_relabel_ops
begin

subsubsection \<open>Abstraction and Invariants\<close>

abbreviation "flow_abs st \<equiv> emap_get (pr_bwd st)"
abbreviation "labels_abs st \<equiv> label_get (pr_labels st)"

text \<open>The residual edges of a vertex that its iterators have already passed.\<close>

definition "iterated_res st u = F ` out_iterated (pr_out st) u \<union> B ` in_iterated (pr_in st) u"

text \<open>The current residual edge of a vertex, if any.\<close>

definition "current_res st u =
  (if out_has (pr_out st) u then Some (F (out_current (pr_out st) u))
   else if in_has (pr_in st) u then Some (B (in_current (pr_in st) u))
   else None)"

definition "invar_basic st =
  (emap_invar (pr_fwd st) \<and> emap_invar (pr_bwd st) \<and> ex_invar (pr_excess st) \<and>
   label_invar (pr_labels st) \<and> count_invar (pr_counts st) \<and>
   out_graph_inv (pr_out st) \<and> in_graph_inv (pr_in st))"

definition "invar_excess st = (\<forall> v \<in> \<V>. ex_get (pr_excess st) v = ex (flow_abs st) v)"

definition "invar_counts st =
  (\<forall> k < 2 * card \<V>. count_get (pr_counts st) k = card {v. v \<in> \<V> \<and> labels_abs st v = k})"

text \<open>Forward and backward residual capacities add up to the capacity.\<close>

definition "res_correct fw bw =
  (\<forall> d \<in> \<E>. \<u> d = ereal (emap_get fw d + emap_get bw d))"

definition "invar_res st = res_correct (pr_fwd st) (pr_bwd st)"

definition "invar_flow st = is_preflow s (flow_abs st)"

definition "invar_labels st =
  (valid_labelling s t (flow_abs st) (labels_abs st) \<and> height_bounded (labels_abs st))"

definition "invar_iterated st =
  (\<forall> u \<in> \<V>. \<forall> e \<in> iterated_res st u. \<not> admissible (flow_abs st) (labels_abs st) e)"

definition "invar_state st =
  (invar_basic st \<and> invar_excess st \<and> invar_counts st \<and> invar_res st \<and> invar_flow st \<and>
   invar_labels st \<and> invar_iterated st)"

text \<open>The contract of the strategy: every operation it requests is applicable.\<close>

definition "good_op st op =
  (case op of
     Push_Fwd d \<Rightarrow> push_precond s t (flow_abs st) (labels_abs st) (F d)
   | Push_Bwd d \<Rightarrow> push_precond s t (flow_abs st) (labels_abs st) (B d)
   | Advance u \<Rightarrow> u \<in> \<V> \<and> (\<exists> e. current_res st u = Some e \<and>
                                   \<not> admissible (flow_abs st) (labels_abs st) e)
   | Relabel u \<Rightarrow> relabel_precond s t (flow_abs st) (labels_abs st) u
   | Relabel_Gap u \<Rightarrow> relabel_precond s t (flow_abs st) (labels_abs st) u
   | Done \<Rightarrow> (\<forall> v. \<not> active_vertex s t (flow_abs st) v))"

end

subsection \<open>Locale for Proofs\<close>

text \<open>The facts about the operations do not depend on the strategy.\<close>

locale push_relabel_ops_correct =
  push_relabel_ops where fst = fst +
  flow_network where fst = fst
  for fst :: "'e \<Rightarrow> 'v" +
  assumes s_in_V: "s \<in> \<V>"
      and t_in_V: "t \<in> \<V>"
      and s_neq_t: "s \<noteq> t"
      and caps: "emap_invar caps" "\<And> d. d \<in> \<E> \<Longrightarrow> ereal (emap_get caps d) = \<u> d"
      and num_verts: "num_verts = card \<V>"
      and gap_fold:
        "\<And> l k g acc. label_invar l \<Longrightarrow>
           \<exists> vs. distinct vs \<and> set vs = {v. v \<in> \<V> \<and> k < label_get l v \<and> label_get l v < card \<V>} \<and>
                 gap_fold l k g acc = foldl g acc vs"
      and edge_fold:
        "\<And> g acc. \<exists> es. distinct es \<and> set es = \<E> \<and> edge_fold g acc = foldl g acc es"
      and init_adts:
        "emap_invar emap_init"
        "ex_invar ex_init" "ex_get ex_init = (\<lambda> v. 0)"
        "label_invar label_init" "label_get label_init = (\<lambda> v. 0)"
        "count_invar count_init" "count_get count_init = (\<lambda> k. 0)"
        "out_graph_inv out_init" "in_graph_inv in_init"

text \<open>The contract of the strategy, with an invariant @{term ctx_invar} of its own.\<close>

locale push_relabel =
  push_relabel_spec where fst = fst +
  push_relabel_ops_correct where fst = fst
  for fst :: "'e \<Rightarrow> 'v" +
  fixes ctx_invar :: "(_, _, _, _, _, _) pr_state \<Rightarrow> bool"
  assumes select:
        "\<And> st op c. \<lbrakk>invar_state st; ctx_invar st; select_of st = (op, c)\<rbrakk> \<Longrightarrow> good_op st op"
        "\<And> st op c. \<lbrakk>invar_state st; ctx_invar st; select_of st = (op, c); op \<noteq> Done\<rbrakk>
                    \<Longrightarrow> ctx_invar (apply_op op (st\<lparr>pr_ctx := c\<rparr>))"
      and init_ctx:
        "\<And> st. \<lbrakk>invar_state st; \<forall> d \<in> \<E>. flow_abs st d = init_flow s d; labels_abs st = init_labels s;
                pr_ctx st = init_ctx (pr_fwd st) (pr_bwd st) (pr_excess st) (pr_labels st)
                                     (pr_out st) (pr_in st)\<rbrakk>
               \<Longrightarrow> ctx_invar st"

context push_relabel_ops_correct
begin

sublocale push_relabel_network fst snd create_edge \<u> \<E> s t
  by unfold_locales (auto simp: s_in_V t_in_V s_neq_t simp flip: caps(2))

subsubsection \<open>Invariants\<close>

lemma finite_delta: "finite (\<delta>\<^sup>+ u)" "finite (\<delta>\<^sup>- u)"
  using finite_E by (auto simp: delta_plus_def delta_minus_def)

text \<open>The iterators abstract to the edges leaving and entering each vertex.\<close>

lemma out_graph_inv_props:
  "\<lbrakk>out_graph_inv og; \<lbrakk>out_invar og; \<forall> v \<in> \<V>. out_abstract og v = \<delta>\<^sup>+ v\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (simp add: out_graph_inv_def)

lemma out_graph_inv_intro[invar_props_intros]:
  "\<lbrakk>out_invar og; \<forall> v \<in> \<V>. out_abstract og v = \<delta>\<^sup>+ v\<rbrakk>
   \<Longrightarrow> out_graph_inv og"
  by (simp add: out_graph_inv_def)

lemma in_graph_inv_props:
  "\<lbrakk>in_graph_inv ig; \<lbrakk>in_invar ig; \<forall> v \<in> \<V>. in_abstract ig v = \<delta>\<^sup>- v\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (simp add: in_graph_inv_def)

lemma in_graph_inv_intro[invar_props_intros]:
  "\<lbrakk>in_invar ig; \<forall> v \<in> \<V>. in_abstract ig v = \<delta>\<^sup>- v\<rbrakk>
   \<Longrightarrow> in_graph_inv ig"
  by (simp add: in_graph_inv_def)

lemma out_graph_inv_delta:
  assumes "out_graph_inv og" "u \<in> \<V>"
  shows "out_invar og" "out_abstract og u = \<delta>\<^sup>+ u" "out_iterated og u \<subseteq> \<delta>\<^sup>+ u"
        "out_remaining og u \<subseteq> \<delta>\<^sup>+ u" "finite (out_remaining og u)"
        "out_has og u \<Longrightarrow> out_current og u \<in> \<delta>\<^sup>+ u"
  using assms outg.idx_partition_union[of og u] outg.idx_has[of og u] outg.idx_current[of og u]
  by (auto simp: out_graph_inv_def intro: finite_subset[OF _ finite_delta(1)])

lemma in_graph_inv_delta:
  assumes "in_graph_inv ig" "u \<in> \<V>"
  shows "in_invar ig" "in_abstract ig u = \<delta>\<^sup>- u" "in_iterated ig u \<subseteq> \<delta>\<^sup>- u"
        "in_remaining ig u \<subseteq> \<delta>\<^sup>- u" "finite (in_remaining ig u)"
        "in_has ig u \<Longrightarrow> in_current ig u \<in> \<delta>\<^sup>- u"
  using assms ing.idx_partition_union[of ig u] ing.idx_has[of ig u] ing.idx_current[of ig u]
  by (auto simp: in_graph_inv_def intro: finite_subset[OF _ finite_delta(2)])

text \<open>One elimination and one introduction rule per invariant.\<close>

lemma invar_basic_props[invar_props_elims]:
  "\<lbrakk>invar_basic st;
    \<lbrakk>emap_invar (pr_fwd st); emap_invar (pr_bwd st); ex_invar (pr_excess st);
     label_invar (pr_labels st); count_invar (pr_counts st); out_graph_inv (pr_out st);
     in_graph_inv (pr_in st)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (simp add: invar_basic_def)

lemma invar_basic_intro[invar_props_intros]:
  "\<lbrakk>emap_invar (pr_fwd st); emap_invar (pr_bwd st); ex_invar (pr_excess st); label_invar (pr_labels st);
    count_invar (pr_counts st); out_graph_inv (pr_out st); in_graph_inv (pr_in st)\<rbrakk>
   \<Longrightarrow> invar_basic st"
  by (simp add: invar_basic_def)

lemma invar_excess_props[invar_props_elims]:
  "\<lbrakk>invar_excess st; (\<forall> v \<in> \<V>. ex_get (pr_excess st) v = ex (flow_abs st) v) \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (simp add: invar_excess_def)

lemma invar_excess_intro[invar_props_intros]:
  "\<forall> v \<in> \<V>. ex_get (pr_excess st) v = ex (flow_abs st) v \<Longrightarrow> invar_excess st"
  by (simp add: invar_excess_def)

lemma invar_counts_props[invar_props_elims]:
  "\<lbrakk>invar_counts st;
    (\<forall> k < 2 * card \<V>. count_get (pr_counts st) k = card {v. v \<in> \<V> \<and> labels_abs st v = k})
    \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (simp add: invar_counts_def)

lemma invar_counts_intro[invar_props_intros]:
  "\<forall> k < 2 * card \<V>. count_get (pr_counts st) k = card {v. v \<in> \<V> \<and> labels_abs st v = k}
   \<Longrightarrow> invar_counts st"
  by (simp add: invar_counts_def)

lemma invar_res_props[invar_props_elims]:
  "\<lbrakk>invar_res st; res_correct (pr_fwd st) (pr_bwd st) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: invar_res_def)

lemma invar_res_intro[invar_props_intros]: "res_correct (pr_fwd st) (pr_bwd st) \<Longrightarrow> invar_res st"
  by (simp add: invar_res_def)

lemma invar_flow_props[invar_props_elims]:
  "\<lbrakk>invar_flow st; is_preflow s (flow_abs st) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: invar_flow_def)

lemma invar_flow_intro[invar_props_intros]: "is_preflow s (flow_abs st) \<Longrightarrow> invar_flow st"
  by (simp add: invar_flow_def)

lemma invar_labels_props[invar_props_elims]:
  "\<lbrakk>invar_labels st;
    \<lbrakk>valid_labelling s t (flow_abs st) (labels_abs st); height_bounded (labels_abs st)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (simp add: invar_labels_def)

lemma invar_labels_intro[invar_props_intros]:
  "\<lbrakk>valid_labelling s t (flow_abs st) (labels_abs st); height_bounded (labels_abs st)\<rbrakk>
   \<Longrightarrow> invar_labels st"
  by (simp add: invar_labels_def)

lemma invar_iterated_props[invar_props_elims]:
  "\<lbrakk>invar_iterated st;
    (\<forall> u \<in> \<V>. \<forall> e \<in> iterated_res st u. \<not> admissible (flow_abs st) (labels_abs st) e)
    \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (simp add: invar_iterated_def)

lemma invar_iterated_intro[invar_props_intros]:
  "\<forall> u \<in> \<V>. \<forall> e \<in> iterated_res st u. \<not> admissible (flow_abs st) (labels_abs st) e
   \<Longrightarrow> invar_iterated st"
  by (simp add: invar_iterated_def)

lemma invar_state_props[invar_props_elims]:
  "\<lbrakk>invar_state st;
    \<lbrakk>invar_basic st; invar_excess st; invar_counts st; invar_res st; invar_flow st; invar_labels st;
     invar_iterated st\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (simp add: invar_state_def)

lemma invar_state_intro[invar_props_intros]:
  "\<lbrakk>invar_basic st; invar_excess st; invar_counts st; invar_res st; invar_flow st; invar_labels st;
    invar_iterated st\<rbrakk>
   \<Longrightarrow> invar_state st"
  by (simp add: invar_state_def)

subsubsection \<open>Residual Capacities and Augmentation\<close>

lemma rcap_fwd: "\<lbrakk>res_correct fw bw; d \<in> \<E>\<rbrakk> \<Longrightarrow> rcap (emap_get bw) (F d)
                 = ereal (emap_get fw d)"
  by (simp add: res_correct_def)

lemma admissible_fwd_impl:
  "\<lbrakk>res_correct fw bw; d \<in> \<E>\<rbrakk>
   \<Longrightarrow> admissible_fwd_impl fw l d \<longleftrightarrow> admissible (emap_get bw) (label_get l) (F d)"
  by (simp only: admissible_fwd_impl_def admissible_def rcap_fwd) (auto simp: \<EE>_def)

lemma admissible_bwd_impl:
  "d \<in> \<E> \<Longrightarrow> admissible_bwd_impl bw l d
   \<longleftrightarrow> admissible (emap_get bw) (label_get l) (B d)"
  by (auto simp: admissible_bwd_impl_def admissible_def \<EE>_def)

text \<open>Sending flow forward along an edge augments its forward copy, sending it backward
      augments its backward copy.\<close>

lemma oedge_props:
  "e \<in> \<EE> \<Longrightarrow> oedge e \<in> \<E> \<and> fst (oedge e) \<in> \<V> \<and> snd (oedge e) \<in> \<V>"
  using o_edge_res
  by (auto intro: fst_E_V snd_E_V)

lemma augment_impl_props:
  assumes "emap_invar fw" "emap_invar bw" "ex_invar x" "e \<in> \<EE>"
          "\<forall> v \<in> \<V>. ex_get x v = ex (emap_get bw) v" "res_correct fw bw"
          "augment_impl (oedge e) (case e of F _ \<Rightarrow> \<gamma> | B _ \<Rightarrow> - \<gamma>) fw bw x
           = (fw', bw', x')"
  shows "emap_invar fw'" "emap_invar bw'" "ex_invar x'"
        "emap_get bw' = augment_edge (emap_get bw) \<gamma> e"
        "\<forall> v \<in> \<V>. ex_get x' v = ex (emap_get bw') v" "res_correct fw' bw'"
proof-
  show "emap_invar fw'" "emap_invar bw'" "ex_invar x'" "res_correct fw' bw'"
    using assms oedge_props[of e]
    by (auto simp: augment_impl_def Let_def res_correct_def edge_map.fixed_univ_map_upd
                   edge_map.fixed_univ_map_upd_invar ex_map.fixed_univ_map_upd_invar)
  show "emap_get bw' = augment_edge (emap_get bw) \<gamma> e"
    using assms(2,4,7) oedge_props[of e]
    by (cases e) (auto simp: augment_impl_def Let_def edge_map.fixed_univ_map_upd)
  thus "\<forall> v \<in> \<V>. ex_get x' v = ex (emap_get bw') v"
    using assms(3,4,5,7) oedge_props[of e] ex_augment_edge[OF assms(4), of "emap_get bw" \<gamma>]
    by (cases e)
       (auto simp: augment_impl_def Let_def ex_map.fixed_univ_map_upd ex_map.fixed_univ_map_upd_invar
             simp del: augment_edge.simps)
qed


subsubsection \<open>Labels and Counts\<close>

definition "counts_correct l cnt =
  (\<forall> k < 2 * card \<V>. count_get cnt k = card {w. w \<in> \<V> \<and> label_get l w = k})"

lemma invar_counts_iff: "invar_counts st = counts_correct (pr_labels st) (pr_counts st)"
  by (simp add: invar_counts_def counts_correct_def)

lemma card_label_class_update:
  assumes "v \<in> \<V>"
  shows "card {w. w \<in> \<V> \<and> ((label_get l)(v := k')) w = j} =
         card {w. w \<in> \<V> \<and> label_get l w = j} - (if label_get l v = j then 1 else 0)
         + (if k' = j then 1 else 0)"
proof(cases "k' = j")
  case True
  hence "{w. w \<in> \<V> \<and> ((label_get l)(v := k')) w = j}
         = insert v ({w. w \<in> \<V> \<and> label_get l w = j} - {v})"
    using assms by auto
  thus ?thesis
    using True assms \<V>_finite by (simp add: card_Diff_singleton_if del: insert_Diff_single)
next
  case False
  hence "{w. w \<in> \<V> \<and> ((label_get l)(v := k')) w = j} = {w. w \<in> \<V> \<and> label_get l w = j} - {v}"
    by auto
  thus ?thesis
    using False assms \<V>_finite by (simp add: card_Diff_singleton_if)
qed

lemma change_label_props:
  assumes "label_invar l" "count_invar cnt" "v \<in> \<V>" "label_get l v < 2 * card \<V>"
          "k' < 2 * card \<V>" "counts_correct l cnt" "change_label l cnt v k' = (l', cnt')"
  shows "label_invar l'" "count_invar cnt'" "label_get l' = (label_get l)(v := k')"
        "counts_correct l' cnt'"
proof-
  define cnt1 where "cnt1 = count_upd cnt (label_get l v) (count_get cnt (label_get l v) - 1)"
  show "label_invar l'" "count_invar cnt'" "label_get l' = (label_get l)(v := k')"
    using assms(1-5,7)
    by (auto simp: change_label_def Let_def label_map.fixed_univ_map_upd_invar label_map.fixed_univ_map_upd
                   count_map.fixed_univ_map_upd_invar)
  moreover have "count_invar cnt1"
    "count_get cnt1 = (count_get cnt)(label_get l v := count_get cnt (label_get l v) - 1)"
    "cnt' = count_upd cnt1 k' (count_get cnt1 k' + 1)" "count_get cnt (label_get l v) \<ge> 1"
    using assms(2-4,6,7) \<V>_finite
    by (auto simp: cnt1_def change_label_def Let_def count_map.fixed_univ_map_upd_invar
                   count_map.fixed_univ_map_upd counts_correct_def Suc_le_eq card_gt_0_iff)
  ultimately show "counts_correct l' cnt'"
    using assms(5,6) card_label_class_update[OF assms(3)]
    by (auto simp: counts_correct_def count_map.fixed_univ_map_upd)
qed


subsubsection \<open>Computing New Labels\<close>

definition "scan_labels r endp l S = {label_get l (endp d) | d. d \<in> S \<and> emap_get r d > 0}"

definition "min_opt X = (if X = {} then None else Some (Min X))"

lemma scan_labels_empty[simp]: "scan_labels r endp l {} = {}"
  by (simp add: scan_labels_def)

lemma scan_labels_finite: "finite S \<Longrightarrow> finite (scan_labels r endp l S)"
  by (rule finite_subset[of _ "(\<lambda> d. label_get l (endp d)) ` S"]) (auto simp: scan_labels_def)

lemma scan_labels_insert:
  "scan_labels r endp l (insert d S) =
   (if emap_get r d > 0 then insert (label_get l (endp d)) (scan_labels r endp l S)
    else scan_labels r endp l S)"
  by (auto simp add: scan_labels_def)

text \<open>One step of a scan: the pair improves iff the current edge is residual and leads to a
      smaller label.\<close>

lemma min_scan_step:
  "has C u \<Longrightarrow> min_scan has cur move r endp l u C mb =
     min_scan has cur move r endp l u (move C u)
       (if 0 < emap_get r (cur C u) \<and>
           (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> label_get l (endp (cur C u)) < k')
        then Some (label_get l (endp (cur C u)), cur C u) else mb)"
  by (subst min_scan.simps) (simp add: Let_def)

lemma min_opt_step:
  "\<lbrakk>finite X; map_option prod.fst mb = min_opt X\<rbrakk> \<Longrightarrow>
   map_option prod.fst
     (if 0 < emap_get r d \<and> (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> k < k') then Some (k, d) else mb)
   = min_opt (if 0 < emap_get r d then insert k X else X)"
  by (cases mb) (auto simp: min_opt_def min_def split: if_splits simp del: Min_ge_iff Min_gr_iff)

text \<open>One lemma for both scans: it is stated for an arbitrary iterator. Besides the minimum, the
      scan either keeps the initial pair or returns an edge \<open>d\<close> reaching the minimum, together
      with a state of the iterator in which \<open>d\<close> is current and all edges passed since the start
      of the scan are not residual or lead to larger labels.\<close>

lemma min_scan_props:
  assumes "indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move
                                    it_reset \<V>"
      and "it_invar C" "u \<in> \<V>" "finite (it_remaining C u)" "finite X"
          "map_option prod.fst mb = min_opt X"
          "min_scan has cur move r endp l u C mb = (C', mb')"
  shows "it_invar C'" "\<forall> w. it_abstract C' w = it_abstract C w"
        "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w
         \<and> it_remaining C' w = it_remaining C w"
        "map_option prod.fst mb' = min_opt (X \<union> scan_labels r endp l (it_remaining C u))"
        "mb' = mb \<or>
         (\<exists> d C''. mb' = Some (label_get l (endp d), d) \<and>
            (case mb of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d) < k) \<and>
            it_invar C'' \<and> it_abstract C'' u = it_abstract C u \<and> has C'' u \<and> cur C'' u = d \<and>
            it_iterated C u \<subseteq> it_iterated C'' u \<and>
            (\<forall> d' \<in> it_iterated C'' u - it_iterated C u.
               0 < emap_get r d' \<longrightarrow> label_get l (endp d) < label_get l (endp d')))"
proof-
  interpret it: indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move
                                     it_reset \<V>
    by (rule assms(1))
  have "it_invar C' \<and> (\<forall> w. it_abstract C' w = it_abstract C w) \<and>
        (\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w
          \<and> it_remaining C' w = it_remaining C w) \<and>
        map_option prod.fst mb' = min_opt (X \<union> scan_labels r endp l (it_remaining C u)) \<and>
        (mb' = mb \<or>
         (\<exists> d C''. mb' = Some (label_get l (endp d), d) \<and>
            (case mb of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d) < k) \<and>
            it_invar C'' \<and> it_abstract C'' u = it_abstract C u \<and> has C'' u \<and> cur C'' u = d \<and>
            it_iterated C u \<subseteq> it_iterated C'' u \<and>
            (\<forall> d' \<in> it_iterated C'' u - it_iterated C u.
               0 < emap_get r d' \<longrightarrow> label_get l (endp d) < label_get l (endp d'))))"
    (is "?A \<and> ?B \<and> ?C \<and> ?D \<and> ?E")
    using assms(2-)
  proof(induction "card (it_remaining C u)" arbitrary: C mb X rule: less_induct)
    case less
    show ?case
    proof(cases "has C u")
      case True
      let ?X1 = "if 0 < emap_get r (cur C u) then insert (label_get l (endp (cur C u))) X else X"
      let ?imp = "0 < emap_get r (cur C u) \<and>
                  (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> label_get l (endp (cur C u)) < k')"
      have rem: "it_remaining C u \<noteq> {}" "cur C u \<in> it_remaining C u"
        using less.prems(1,2) True
        by (auto simp: it.idx_has it.idx_current)
      note mv = less.prems(1,2) rem(1)
      have "card (it_remaining (move C u) u) < card (it_remaining C u)" "it_invar (move C u)"
           "finite (it_remaining (move C u) u)" "finite ?X1"
        using mv less.prems(3,4) rem(2)
        by (simp_all add: it.idx_move_remaining it.idx_move_invar card_gt_0_iff)
      note IH = less.hyps[OF this(1,2) less.prems(2) this(3,4) min_opt_step[OF less.prems(4,5)]
                             less.prems(6)[unfolded min_scan_step[of has C u, OF True]]]
      have "mb' = mb \<or>
            (\<exists> d C''. mb' = Some (label_get l (endp d), d) \<and>
               (case mb of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d) < k) \<and>
               it_invar C'' \<and> it_abstract C'' u = it_abstract C u \<and> has C'' u \<and> cur C'' u = d \<and>
               it_iterated C u \<subseteq> it_iterated C'' u \<and>
               (\<forall> d' \<in> it_iterated C'' u - it_iterated C u.
                  0 < emap_get r d' \<longrightarrow> label_get l (endp d) < label_get l (endp d')))"
        using IH[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
      proof(elim disjE exE conjE, goal_cases)
        case 1
        thus ?case
          using True less.prems(1) by (cases ?imp) (auto intro!: exI[of _ "cur C u"] exI[of _ C])
      next
        case (2 d' C'')
        have "(case mb of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d') < k) \<and>
              (0 < emap_get r (cur C u) \<longrightarrow> label_get l (endp d') < label_get l (endp (cur C u)))"
          using 2(2) by (cases ?imp) (auto split: option.splits prod.splits)
        thus ?case
          using 2 mv
          by (intro disjI2 exI[of _ d'] exI[of _ C'']) (auto simp: it.idx_move_iterated it.idx_move_abstract)
      qed
      moreover have "?X1 \<union> scan_labels r endp l (it_remaining (move C u) u) =
                     X \<union> scan_labels r endp l (it_remaining C u)"
        using rem(2) mv
        by (auto simp: it.idx_move_remaining scan_labels_insert scan_labels_def)
      ultimately show ?thesis
        using IH mv
        by (elim conjE) (intro conjI, simp_all add: it.idx_move_abstract it.idx_move_iterated_other
                                                    it.idx_move_remaining_other)
    qed (insert less.prems, simp add: min_scan.simps it.idx_has)
  qed
  thus ?A ?B ?C ?D ?E
    by simp_all
qed

lemma min_opt_empty: "map_option prod.fst None = min_opt {}"
  by (simp add: min_opt_def)

text \<open>A scan from a reset iterator passes all edges of the vertex. If it improves the pair, setting
      the iterator to the improving edge passes only edges that are not residual or lead to larger
      labels.\<close>

lemma min_scan_reset_props:
  assumes "indexed_iterable_set_reset_to it_invar it_abstract cur has it_iterated it_remaining move
                                             it_reset \<V> reset_to"
      and "it_invar C" "u \<in> \<V>" "it_abstract C u = A" "finite A" "finite X"
          "map_option prod.fst mb = min_opt X"
          "min_scan has cur move r endp l u (it_reset C u) mb = (C', mb')"
  shows "it_invar C'" "\<forall> w. it_abstract C' w = it_abstract C w"
        "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w"
        "it_iterated C' u \<subseteq> A"
        "map_option prod.fst mb' = min_opt (X \<union> scan_labels r endp l A)"
        "\<lbrakk>mb' = Some (k, d); mb' \<noteq> mb\<rbrakk> \<Longrightarrow>
           k = label_get l (endp d) \<and> (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> k < k') \<and>
           d \<in> A \<and> it_invar (reset_to C' u d) \<and>
           (\<forall> w. it_abstract (reset_to C' u d) w = it_abstract C w) \<and>
           (\<forall> w. w \<noteq> u \<longrightarrow> it_iterated (reset_to C' u d) w = it_iterated C w) \<and>
           (\<forall> d' \<in> it_iterated (reset_to C' u d) u.
              0 < emap_get r d' \<longrightarrow> k < label_get l (endp d'))"
proof-
  interpret it: indexed_iterable_set_reset_to it_invar it_abstract cur has it_iterated it_remaining move
                                              it_reset \<V> reset_to
    by (rule assms(1))
  have "finite (it_remaining (it_reset C u) u)"
    using assms(2-5) by (simp add: it.idx_reset_remaining)
  note sc = min_scan_props[OF it.indexed_iterable_set_axioms it.idx_reset_invar[OF assms(2,3)] assms(3) this
                              assms(6-8)]
  show "it_invar C'" "\<forall> w. it_abstract C' w = it_abstract C w"
       "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w" "it_iterated C' u \<subseteq> A"
       "map_option prod.fst mb' = min_opt (X \<union> scan_labels r endp l A)"
    using sc(1-4) assms(2-4) it.idx_partition_union[OF sc(1) assms(3)]
    by (auto simp: it.idx_reset_abstract it.idx_reset_iterated_other it.idx_reset_remaining)
  assume "mb' = Some (k, d)" "mb' \<noteq> mb"
  then obtain C'' where "k = label_get l (endp d)"
    "case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> k < k'"
    "it_invar C''" "it_abstract C'' u = it_abstract C u" "has C'' u" "cur C'' u = d"
    "\<forall> d' \<in> it_iterated C'' u. 0 < emap_get r d' \<longrightarrow> k < label_get l (endp d')"
    using sc(5) assms(2,3) by (auto simp: it.idx_reset_abstract it.idx_reset_iterated)
  moreover hence "d \<in> A"
    using assms(3,4) it.idx_has[of C'' u] it.idx_current[of C'' u] it.idx_partition_union[of C'' u]
    by auto
  ultimately show "k = label_get l (endp d) \<and> (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> k < k') \<and>
           d \<in> A \<and> it_invar (reset_to C' u d) \<and>
           (\<forall> w. it_abstract (reset_to C' u d) w = it_abstract C w) \<and>
           (\<forall> w. w \<noteq> u \<longrightarrow> it_iterated (reset_to C' u d) w = it_iterated C w) \<and>
           (\<forall> d' \<in> it_iterated (reset_to C' u d) u.
              0 < emap_get r d' \<longrightarrow> k < label_get l (endp d'))"
    using sc(1-3) assms(2-4) it.idx_reset_to_like[of C' u C'' d]
    by (auto simp: it.idx_reset_to_invar it.idx_reset_to_abstract it.idx_reset_to_iterated_other
                   it.idx_reset_abstract it.idx_reset_iterated_other)
qed

lemma invar_stateD:
  assumes "invar_state st"
  shows "emap_invar (pr_fwd st)" "ex_invar (pr_excess st)" "label_invar (pr_labels st)"
        "count_invar (pr_counts st)" "out_invar (pr_out st)"
        "\<And> v. v \<in> \<V> \<Longrightarrow> ex_get (pr_excess st) v = ex (flow_abs st) v"
        "counts_correct (pr_labels st) (pr_counts st)"
        "is_preflow s (flow_abs st)"
        "valid_labelling s t (flow_abs st) (labels_abs st)" "height_bounded (labels_abs st)"
        "\<And> u. u \<in> \<V> \<Longrightarrow> out_abstract (pr_out st) u = \<delta>\<^sup>+ u"
        "\<And> u e. \<lbrakk>u \<in> \<V>; e \<in> iterated_res st u\<rbrakk>
         \<Longrightarrow> \<not> admissible (flow_abs st) (labels_abs st) e"
        "emap_invar (pr_bwd st)" "res_correct (pr_fwd st) (pr_bwd st)"
        "in_invar (pr_in st)" "\<And> u. u \<in> \<V> \<Longrightarrow> in_abstract (pr_in st) u = \<delta>\<^sup>- u"
  using assms
  by (auto simp add: invar_state_def invar_basic_def invar_excess_def invar_counts_iff
                     invar_res_def invar_flow_def invar_labels_def invar_iterated_def
                     out_graph_inv_def in_graph_inv_def)

lemma invar_stateI:
  assumes "emap_invar (pr_fwd st)" "ex_invar (pr_excess st)" "label_invar (pr_labels st)"
          "count_invar (pr_counts st)" "out_invar (pr_out st)"
          "\<And> v. v \<in> \<V> \<Longrightarrow> ex_get (pr_excess st) v = ex (flow_abs st) v"
          "counts_correct (pr_labels st) (pr_counts st)"
          "is_preflow s (flow_abs st)"
          "valid_labelling s t (flow_abs st) (labels_abs st)" "height_bounded (labels_abs st)"
          "\<And> u. u \<in> \<V> \<Longrightarrow> out_abstract (pr_out st) u = \<delta>\<^sup>+ u"
          "\<And> u e. \<lbrakk>u \<in> \<V>; e \<in> iterated_res st u\<rbrakk>
           \<Longrightarrow> \<not> admissible (flow_abs st) (labels_abs st) e"
          "emap_invar (pr_bwd st)" "res_correct (pr_fwd st) (pr_bwd st)"
          "in_invar (pr_in st)" "\<And> u. u \<in> \<V> \<Longrightarrow> in_abstract (pr_in st) u = \<delta>\<^sup>- u"
  shows "invar_state st"
  using assms
  by (auto simp add: invar_state_def invar_basic_def invar_excess_def invar_counts_iff
                     invar_res_def invar_flow_def invar_labels_def invar_iterated_def
                     out_graph_inv_def in_graph_inv_def)
lemma invar_state_ctx: "invar_state (st\<lparr>pr_ctx := c\<rparr>) = invar_state st"
  by (simp add: invar_state_def invar_basic_def invar_excess_def invar_counts_def invar_res_def
                invar_flow_def invar_labels_def invar_iterated_def iterated_res_def)

lemma good_op_ctx: "good_op (st\<lparr>pr_ctx := c\<rparr>) op = good_op st op"
proof-
  have "flow_abs (st\<lparr>pr_ctx := c\<rparr>) = flow_abs st"
       "labels_abs (st\<lparr>pr_ctx := c\<rparr>) = labels_abs st"
       "current_res (st\<lparr>pr_ctx := c\<rparr>) = current_res st"
    by (simp_all add: current_res_def fun_eq_iff)
  thus ?thesis
    unfolding good_op_def by (simp only:)
qed

text \<open>The residual edges leaving a vertex are exactly the forward copies of its outgoing and
      the backward copies of its ingoing edges, so the two scans compute the new label.\<close>

lemma scan_labels_relabel_labels:
  assumes "res_correct fw bw"
  shows "scan_labels fw snd l (\<delta>\<^sup>+ u) \<union> scan_labels bw fst l (\<delta>\<^sup>- u) =
         relabel_labels (emap_get bw) (label_get l) u"
proof(intro equalityI subsetI)
  fix x
  assume "x \<in> scan_labels fw snd l (\<delta>\<^sup>+ u) \<union> scan_labels bw fst l (\<delta>\<^sup>- u)"
  then obtain d where "d \<in> \<E>" "(fst d = u \<and> 0 < emap_get fw d \<and> x = label_get l (snd d)) \<or>
                                  (snd d = u \<and> 0 < emap_get bw d \<and> x = label_get l (fst d))"
    by (auto simp: scan_labels_def delta_plus_def delta_minus_def)
  thus "x \<in> relabel_labels (emap_get bw) (label_get l) u"
    using rcap_fwd[OF assms] unfolding relabel_labels_def by (elim disjE) (force simp: \<EE>_def)+
next
  fix x
  assume "x \<in> relabel_labels (emap_get bw) (label_get l) u"
  then obtain e where "e \<in> \<EE>" "fstv e = u" "rcap (emap_get bw) e > 0" "x = label_get l (sndv e)"
    unfolding relabel_labels_def by blast
  thus "x \<in> scan_labels fw snd l (\<delta>\<^sup>+ u) \<union> scan_labels bw fst l (\<delta>\<^sup>- u)"
    using rcap_fwd[OF assms] o_edge_res[of e]
    by (cases e) (auto simp: scan_labels_def delta_plus_def delta_minus_def)
qed


lemma new_label_props:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
          "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = (og', ig', k')"
  shows "out_invar og'" "in_invar ig'"
        "\<And> w. out_abstract og' w = out_abstract (pr_out st) w"
        "\<And> w. in_abstract ig' w = in_abstract (pr_in st) w"
        "\<And> d. \<lbrakk>d \<in> out_iterated og' u; 0 < emap_get (pr_fwd st) d\<rbrakk>
         \<Longrightarrow> k' \<le> labels_abs st (snd d)"
        "\<And> d. \<lbrakk>d \<in> in_iterated ig' u; 0 < emap_get (pr_bwd st) d\<rbrakk>
         \<Longrightarrow> k' \<le> labels_abs st (fst d)"
        "\<And> w. w \<noteq> u \<Longrightarrow> out_iterated og' w = out_iterated (pr_out st) w"
        "\<And> w. w \<noteq> u \<Longrightarrow> in_iterated ig' w = in_iterated (pr_in st) w"
        "k' = relabel_effect (flow_abs st) (labels_abs st) u u"
        "\<exists> og1 mb1 ig1 M d.
           min_scan out_has out_current out_move (pr_fwd st) snd (pr_labels st) u
             (out_reset (pr_out st) u) None = (og1, mb1) \<and>
           min_scan in_has in_current in_move (pr_bwd st) fst (pr_labels st) u
             (in_reset (pr_in st) u) mb1 = (ig1, Some (M, d)) \<and>
           (if (case mb1 of None \<Rightarrow> True | Some (m1, _) \<Rightarrow> M < m1)
            then d \<in> in_abstract ig1 u else d \<in> out_abstract og1 u)"
proof-
  have I: "out_invar (pr_out st)" "out_abstract (pr_out st) u = \<delta>\<^sup>+ u" "in_invar (pr_in st)"
          "in_abstract (pr_in st) u = \<delta>\<^sup>- u" "res_correct (pr_fwd st) (pr_bwd st)"
          "is_preflow s (flow_abs st)" "active_vertex s t (flow_abs st) u"
    using assms(1,2)
    by (auto elim!: invar_props_elims relabel_precondE active_vertexE simp: out_graph_inv_delta in_graph_inv_delta)
  hence u: "u \<in> \<V>"
    by (auto elim: active_vertexE)
  obtain og1 mb1 where scan1:
    "min_scan out_has out_current out_move (pr_fwd st) snd (pr_labels st) u (out_reset (pr_out st) u) None
     = (og1, mb1)"
    by fastforce
  obtain ig1 mb2 where scan2:
    "min_scan in_has in_current in_move (pr_bwd st) fst (pr_labels st) u (in_reset (pr_in st) u) mb1
     = (ig1, mb2)"
    by fastforce
  note scan = scan1 scan2
  note sc1 = min_scan_reset_props[OF outr.indexed_iterable_set_reset_to_axioms I(1) u I(2) finite_delta(1)
                                     finite.emptyI min_opt_empty scan(1)]
  have "finite ({} \<union> scan_labels (pr_fwd st) snd (pr_labels st) (\<delta>\<^sup>+ u))"
    by (simp add: scan_labels_finite finite_delta)
  note sc2 = min_scan_reset_props[OF inr.indexed_iterable_set_reset_to_axioms I(3) u I(4) finite_delta(2) this
                                     sc1(5) scan(2)]
  define M where "M = Min (relabel_labels (flow_abs st) (labels_abs st) u)"
  have "map_option prod.fst mb2 = Some M"
    using sc2(5) I(5-7)
    by (simp add: min_opt_def M_def relabel_labels_nonempty scan_labels_relabel_labels)
  then obtain d where mb2: "mb2 = Some (M, d)"
    by auto
  define cnd where "cnd = (case mb1 of None \<Rightarrow> True | Some (m1, _) \<Rightarrow> M < m1)"
  have res: "(og', ig', k') = (if cnd then (og1, in_reset_to ig1 u d, M + 1)
                               else (out_reset_to og1 u d, in_reset ig1 u, M + 1))"
    using scan mb2 assms(3) by (simp add: new_label_def cnd_def)
  thus "k' = relabel_effect (flow_abs st) (labels_abs st) u u"
    by (simp add: relabel_effect_def M_def split: if_splits)
  have "out_invar og' \<and> in_invar ig' \<and> (\<forall> w. out_abstract og' w = out_abstract (pr_out st) w) \<and>
        (\<forall> w. in_abstract ig' w = in_abstract (pr_in st) w) \<and>
        (\<forall> d'. d' \<in> out_iterated og' u \<longrightarrow> 0 < emap_get (pr_fwd st) d'
          \<longrightarrow> k' \<le> labels_abs st (snd d')) \<and>
        (\<forall> d'. d' \<in> in_iterated ig' u \<longrightarrow> 0 < emap_get (pr_bwd st) d'
          \<longrightarrow> k' \<le> labels_abs st (fst d')) \<and>
        (\<forall> w. w \<noteq> u \<longrightarrow> out_iterated og' w = out_iterated (pr_out st) w) \<and>
        (\<forall> w. w \<noteq> u \<longrightarrow> in_iterated ig' w = in_iterated (pr_in st) w) \<and>
        (if cnd then d \<in> in_abstract ig1 u else d \<in> out_abstract og1 u)"
  proof(cases cnd)
    case True
    hence "mb2 \<noteq> mb1"
      using mb2 by (cases mb1) (auto simp: cnd_def)
    note w = sc2(6)[OF mb2 this]
    have "\<forall> d' \<in> out_iterated og1 u. 0 < emap_get (pr_fwd st) d'
            \<longrightarrow> M < labels_abs st (snd d')"
    proof(intro ballI impI)
      fix d'
      assume "d' \<in> out_iterated og1 u" "0 < emap_get (pr_fwd st) d'"
      hence "labels_abs st (snd d') \<in> scan_labels (pr_fwd st) snd (pr_labels st) (\<delta>\<^sup>+ u)"
        using sc1(4) by (auto simp: scan_labels_def)
      moreover hence "Min (scan_labels (pr_fwd st) snd (pr_labels st) (\<delta>\<^sup>+ u))
                      \<le> labels_abs st (snd d')"
        by (simp add: scan_labels_finite finite_delta)
      ultimately show "M < labels_abs st (snd d')"
        using True sc1(5) by (cases mb1) (auto simp: cnd_def min_opt_def split: if_splits)
    qed
    thus ?thesis
      using True res w sc1(1-3) sc2(2) I(4)
      by (auto simp: Suc_le_eq)
  next
    case False
    hence "mb1 = Some (M, d)" "mb1 \<noteq> None"
      using sc2(6)[OF mb2] mb2 by (cases mb1; auto simp: cnd_def)+
    note w = sc1(6)[OF this]
    show ?thesis
      using False res sc1(1-3) w sc2(1-3) I(2) u
      by (auto simp: Suc_le_eq ing.idx_reset_invar ing.idx_reset_abstract ing.idx_reset_iterated
                     ing.idx_reset_iterated_other)
  qed
  thus "out_invar og'" "in_invar ig'"
       "\<And> w. out_abstract og' w = out_abstract (pr_out st) w"
       "\<And> w. in_abstract ig' w = in_abstract (pr_in st) w"
       "\<And> d. \<lbrakk>d \<in> out_iterated og' u; 0 < emap_get (pr_fwd st) d\<rbrakk>
        \<Longrightarrow> k' \<le> labels_abs st (snd d)"
       "\<And> d. \<lbrakk>d \<in> in_iterated ig' u; 0 < emap_get (pr_bwd st) d\<rbrakk>
        \<Longrightarrow> k' \<le> labels_abs st (fst d)"
       "\<And> w. w \<noteq> u \<Longrightarrow> out_iterated og' w = out_iterated (pr_out st) w"
       "\<And> w. w \<noteq> u \<Longrightarrow> in_iterated ig' w = in_iterated (pr_in st) w"
       "\<exists> og1 mb1 ig1 M d.
          min_scan out_has out_current out_move (pr_fwd st) snd (pr_labels st) u
            (out_reset (pr_out st) u) None = (og1, mb1) \<and>
          min_scan in_has in_current in_move (pr_bwd st) fst (pr_labels st) u
            (in_reset (pr_in st) u) mb1 = (ig1, Some (M, d)) \<and>
          (if (case mb1 of None \<Rightarrow> True | Some (m1, _) \<Rightarrow> M < m1)
           then d \<in> in_abstract ig1 u else d \<in> out_abstract og1 u)"
    using scan mb2 by (auto simp: cnd_def)
qed

subsubsection \<open>Invariants are Preserved by the Operations\<close>

lemma iterated_res_props:
  assumes "invar_state st" "u \<in> \<V>" "e \<in> iterated_res st u"
  shows "fstv e = u" "e \<in> \<EE>"
  using assms out_graph_inv_delta(3)[of "pr_out st" u] in_graph_inv_delta(3)[of "pr_in st" u]
  by (auto elim!: invar_props_elims simp: iterated_res_def delta_plus_def delta_minus_def \<EE>_def)

text \<open>If labels only increase, flows do not change, and every vertex whose label changed has
      its iterators reset, then no passed residual edge is admissible.\<close>

lemma iterated_invar_label_increase:
  assumes "invar_state st" "flow_abs st' = flow_abs st"
          "\<And> x. x \<in> \<V> \<Longrightarrow> labels_abs st x \<le> labels_abs st' x"
          "u \<in> \<V>" "labels_abs st' u = labels_abs st u" "e \<in> iterated_res st u"
  shows "\<not> admissible (flow_abs st') (labels_abs st') e"
using assms iterated_res_props[OF assms(1,4,6)]
        admissible_increased_labels[of "flow_abs st" "labels_abs st" "labels_abs st'" e]
  by (auto elim!: invar_props_elims)

text \<open>Before and after relabelling, the label of the vertex is below \<open>2 |V|\<close>.\<close>

lemma relabel_bounds:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "label_get (pr_labels st) u < 2 * card \<V>"
        "relabel_effect (flow_abs st) (labels_abs st) u u < 2 * card \<V>"
proof-
  have "u \<in> \<V>" "is_preflow s (flow_abs st)" "valid_labelling s t (flow_abs st) (labels_abs st)"
       "height_bounded (labels_abs st)"
    using assms by (auto elim!: invar_props_elims relabel_precondE active_vertexE)
  thus "label_get (pr_labels st) u < 2 * card \<V>"
       "relabel_effect (flow_abs st) (labels_abs st) u u < 2 * card \<V>"
    using relabel_preserves_height_bounded[of "flow_abs st" "labels_abs st" u] assms(2) cardV_0
    by (fastforce dest: height_boundedD)+
qed

lemma relabel_impl_props:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "invar_state (relabel_impl u st)"
        "labels_abs (relabel_impl u st) = relabel_effect (flow_abs st) (labels_abs st) u"
        "pr_fwd (relabel_impl u st) = pr_fwd st \<and> pr_bwd (relabel_impl u st) = pr_bwd st"
        "pr_excess (relabel_impl u st) = pr_excess st"
        "pr_ctx (relabel_impl u st) = pr_ctx st"
        "\<And> w. w \<noteq> u \<Longrightarrow> iterated_res (relabel_impl u st) w = iterated_res st w"
proof-
  obtain og' ig' k' where
    nl: "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = (og', ig', k')"
    by (cases "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u") auto
  obtain l' cnt' where cl: "change_label (pr_labels st) (pr_counts st) u k' = (l', cnt')"
    by (cases "change_label (pr_labels st) (pr_counts st) u k'") auto
  note nlp = new_label_props[OF assms nl]
  have I: "u \<in> \<V>" "label_invar (pr_labels st)" "count_invar (pr_counts st)"
          "counts_correct (pr_labels st) (pr_counts st)" "is_preflow s (flow_abs st)"
          "valid_labelling s t (flow_abs st) (labels_abs st)" "height_bounded (labels_abs st)"
          "out_graph_inv (pr_out st)" "in_graph_inv (pr_in st)" "res_correct (pr_fwd st) (pr_bwd st)"
          "label_get (pr_labels st) u < 2 * card \<V>" "k' < 2 * card \<V>"
    using assms nlp(9)
    by (auto elim!: invar_props_elims relabel_precondE active_vertexE simp: counts_correct_def relabel_bounds)
  note clp = change_label_props[OF I(2,3,1,11,12,4) cl]
  have st': "relabel_impl u st = st\<lparr>pr_labels := l', pr_counts := cnt', pr_out := og', pr_in := ig'\<rparr>"
    using nl cl by (simp add: relabel_impl_def)
  have labels: "label_get l' = relabel_effect (flow_abs st) (labels_abs st) u"
    using clp(3) nlp(9) by (simp add: relabel_effect_def)
  show "labels_abs (relabel_impl u st) = relabel_effect (flow_abs st) (labels_abs st) u"
       "pr_fwd (relabel_impl u st) = pr_fwd st \<and> pr_bwd (relabel_impl u st) = pr_bwd st"
       "pr_excess (relabel_impl u st) = pr_excess st" "pr_ctx (relabel_impl u st) = pr_ctx st"
       "\<And> w. w \<noteq> u \<Longrightarrow> iterated_res (relabel_impl u st) w = iterated_res st w"
    using nlp(7,8) by (simp_all add: st' labels iterated_res_def)
  have "invar_iterated (relabel_impl u st)"
  proof(unfold invar_iterated_def, intro ballI)
    fix w e
    assume w: "w \<in> \<V>" "e \<in> iterated_res (relabel_impl u st) w"
    thus "\<not> admissible (flow_abs (relabel_impl u st)) (labels_abs (relabel_impl u st)) e"
    proof(cases "w = u")
      text \<open>The passed residual edges of \<open>u\<close> lead to labels at least the new label of
        \<open>u\<close>.\<close>
      case True
      hence "e \<in> iterated_res (relabel_impl u st) u"
        using w(2) by simp
      hence "\<not> admissible (flow_abs st) (relabel_effect (flow_abs st) (labels_abs st) u) e"
        using nlp(5,6,9) outg.idx_partition_union[OF nlp(1) I(1)] ing.idx_partition_union[OF nlp(2) I(1)]
              nlp(3,4)[of u] out_graph_inv_delta(2)[OF I(8,1)] in_graph_inv_delta(2)[OF I(9,1)] rcap_fwd[OF I(10)]
        by (fastforce simp: st' iterated_res_def admissible_def relabel_effect_def delta_plus_def
                            delta_minus_def split: if_splits)
      thus ?thesis
        by (simp add: st' labels)
    next
      case False
      thus ?thesis
        using w(1) w(2)
              I(5,6) assms relabel_mono
        by (intro iterated_invar_label_increase[where st = st])
           (simp_all add: st' labels iterated_res_def nlp(7,8) relabel_effect_def)
    qed
  qed
  moreover have "invar_basic st" "invar_excess st" "invar_res st" "invar_flow st"
    using assms(1) by (auto elim: invar_state_props)
  hence "invar_basic (relabel_impl u st)" "invar_excess (relabel_impl u st)" "invar_res (relabel_impl u st)"
        "invar_flow (relabel_impl u st)"
    using clp(1,2) nlp(1-4) I(1)
    by (auto simp: st' invar_basic_def invar_excess_def invar_res_def invar_flow_def out_graph_inv_def
                   in_graph_inv_def)
  moreover have "invar_counts (relabel_impl u st)" "invar_labels (relabel_impl u st)"
    using clp(4) I(5-7) assms(2)
    by (simp_all add: st' labels invar_counts_def invar_labels_def counts_correct_def relabel_preserves_valid
                      relabel_preserves_height_bounded)
  ultimately show "invar_state (relabel_impl u st)"
    by (simp add: invar_state_def)
qed

lemma gap_fold_props:
  assumes "distinct vs" "set vs \<subseteq> \<V>" "label_invar l" "count_invar cnt" "out_invar og"
          "in_invar ig" "counts_correct l cnt" "\<forall> w \<in> \<V>. label_get l w < 2 * card \<V>"
          "foldl (gap_step k) (l, cnt, og, ig) vs = (l', cnt', og', ig')"
  shows "label_invar l' \<and> count_invar cnt' \<and> out_invar og' \<and> in_invar ig' \<and>
         counts_correct l' cnt' \<and> (\<forall> w \<in> \<V>. label_get l' w < 2 * card \<V>) \<and>
         label_get l' = (\<lambda> w. if w \<in> set vs \<and> k < label_get l w \<and> label_get l w < num_verts
                             then num_verts + 1 else label_get l w) \<and>
         (\<forall> w. out_abstract og' w = out_abstract og w) \<and>
         (\<forall> w. in_abstract ig' w = in_abstract ig w) \<and>
         (\<forall> w. out_iterated og' w =
               (if w \<in> set vs \<and> k < label_get l w \<and> label_get l w < num_verts then {}
                else out_iterated og w)) \<and>
         (\<forall> w. in_iterated ig' w =
               (if w \<in> set vs \<and> k < label_get l w \<and> label_get l w < num_verts then {}
                else in_iterated ig w))"
  using assms
proof(induction vs arbitrary: l cnt og ig)
  case (Cons v vs)
  show ?case
  proof(cases "k < label_get l v \<and> label_get l v < num_verts")
    case True
    obtain l1 cnt1 where cl: "change_label l cnt v (num_verts + 1) = (l1, cnt1)"
      by (cases "change_label l cnt v (num_verts + 1)") auto
    have "v \<in> \<V>" "num_verts + 1 < 2 * card \<V>"
      using Cons.prems(2) card_V_ge_2 by (simp_all add: num_verts)
    note clp = change_label_props[OF Cons.prems(3,4) this(1) _ this(2) Cons.prems(7) cl]
    have "foldl (gap_step k) (l1, cnt1, out_reset og v, in_reset ig v) vs = (l', cnt', og', ig')"
      using True cl Cons.prems(9) by (simp add: gap_step_def Let_def)
    hence "label_invar l' \<and> count_invar cnt' \<and> out_invar og' \<and> in_invar ig' \<and>
         counts_correct l' cnt' \<and> (\<forall> w \<in> \<V>. label_get l' w < 2 * card \<V>) \<and>
         label_get l' = (\<lambda> w. if w \<in> set vs \<and> k < label_get l1 w \<and> label_get l1 w < num_verts
                             then num_verts + 1 else label_get l1 w) \<and>
         (\<forall> w. out_abstract og' w = out_abstract (out_reset og v) w) \<and>
         (\<forall> w. in_abstract ig' w = in_abstract (in_reset ig v) w) \<and>
         (\<forall> w. out_iterated og' w =
               (if w \<in> set vs \<and> k < label_get l1 w \<and> label_get l1 w < num_verts then {}
                else out_iterated (out_reset og v) w)) \<and>
         (\<forall> w. in_iterated ig' w =
               (if w \<in> set vs \<and> k < label_get l1 w \<and> label_get l1 w < num_verts then {}
                else in_iterated (in_reset ig v) w))"
      using Cons.prems(1-8) Cons.prems(2) card_V_ge_2 clp
      by (intro Cons.IH) (auto simp: outg.idx_reset_invar ing.idx_reset_invar num_verts)
    thus ?thesis
      using True Cons.prems(1,5,6,8) Cons.prems(2) clp(3)
      by (auto simp: outg.idx_reset_abstract outg.idx_reset_iterated outg.idx_reset_iterated_other
                     ing.idx_reset_abstract ing.idx_reset_iterated ing.idx_reset_iterated_other)
  next
    case False
    hence "foldl (gap_step k) (l, cnt, og, ig) vs = (l', cnt', og', ig')"
      using Cons.prems(9) by (auto simp: gap_step_def Let_def)
    thus ?thesis
      using Cons.IH[OF _ _ Cons.prems(3-8)] Cons.prems(1,2) False by auto
  qed
qed simp

lemma relabel_gap_impl_props:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "invar_state (relabel_gap_impl u st)"
        "labels_abs (relabel_gap_impl u st) = relabel_gap_effect (flow_abs st) (labels_abs st) u"
        "pr_fwd (relabel_gap_impl u st) = pr_fwd st \<and> pr_bwd (relabel_gap_impl u st) = pr_bwd st"
        "pr_excess (relabel_gap_impl u st) = pr_excess st"
        "pr_ctx (relabel_gap_impl u st) = pr_ctx st"
proof-
  define k where "k = labels_abs st u"
  define st' where "st' = relabel_impl u st"
  define l' where "l' = relabel_effect (flow_abs st) (labels_abs st) u"
  note rp = relabel_impl_props[OF assms, folded st'_def l'_def]
  have I: "is_preflow s (flow_abs st)" "valid_labelling s t (flow_abs st) (labels_abs st)"
          "height_bounded (labels_abs st)" "label_invar (pr_labels st')" "count_invar (pr_counts st')"
          "out_graph_inv (pr_out st')" "in_graph_inv (pr_in st')" "counts_correct (pr_labels st') (pr_counts st')"
          "height_bounded (labels_abs st')"
    using assms(1) rp(1) by (auto elim!: invar_props_elims simp: counts_correct_def)
  show "pr_fwd (relabel_gap_impl u st) = pr_fwd st \<and> pr_bwd (relabel_gap_impl u st) = pr_bwd st"
       "pr_excess (relabel_gap_impl u st) = pr_excess st"
       "pr_ctx (relabel_gap_impl u st) = pr_ctx st"
    using rp(3,4,5)
    by (auto simp: relabel_gap_impl_def gap_impl_def Let_def st'_def[symmetric] split: prod.splits)
  have cnt: "count_get (pr_counts st') k = card {w. w \<in> \<V> \<and> l' w = k}" if "k < num_verts"
    using I(8) rp(2) that by (simp add: counts_correct_def num_verts)
  have "invar_state (relabel_gap_impl u st) \<and>
        labels_abs (relabel_gap_impl u st) = relabel_gap_effect (flow_abs st) (labels_abs st) u"
  proof(cases "k < num_verts \<and> count_get (pr_counts st') k = 0")
    case True
    obtain vs where vs: "distinct vs"
      "set vs = {v. v \<in> \<V> \<and> k < label_get (pr_labels st') v \<and> label_get (pr_labels st') v < card \<V>}"
      "gap_fold (pr_labels st') k (gap_step k) (pr_labels st', pr_counts st', pr_out st', pr_in st') =
       foldl (gap_step k) (pr_labels st', pr_counts st', pr_out st', pr_in st') vs"
      using gap_fold[OF I(4), of k "gap_step k" "(pr_labels st', pr_counts st', pr_out st', pr_in st')"]
      by blast
    obtain l'' cnt'' og'' ig'' where fold:
      "foldl (gap_step k) (pr_labels st', pr_counts st', pr_out st', pr_in st') vs = (l'', cnt'', og'', ig'')"
      by (cases "foldl (gap_step k) (pr_labels st', pr_counts st', pr_out st', pr_in st') vs") auto
    have "set vs \<subseteq> \<V>" "\<forall> w \<in> \<V>. label_get (pr_labels st') w < 2 * card \<V>"
      using vs(2) height_boundedD[OF I(9)] cardV_0 by fastforce+
    note gf = gap_fold_props[OF vs(1) this(1) I(4,5) _ _ I(8) this(2) fold, simplified vs(2) num_verts]
    have res: "relabel_gap_impl u st = st'\<lparr>pr_labels := l'', pr_counts := cnt'',
                 pr_out := og'', pr_in := ig''\<rparr>"
      using True vs(3) fold by (simp add: relabel_gap_impl_def gap_impl_def Let_def k_def st'_def)
    have labels: "label_get l'' = gap_effect l' k"
      using gf I(6,7) rp(2) by (auto simp: gap_effect_def num_verts out_graph_inv_def in_graph_inv_def)
    have "gap_precond l' k"
      using True cnt \<V>_finite by (auto intro!: gap_precondI simp: num_verts)
    hence eff: "relabel_gap_effect (flow_abs st) (labels_abs st) u = gap_effect l' k"
      by (simp add: relabel_gap_effect_def l'_def k_def)
    have gf_it: "iterated_res (relabel_gap_impl u st) w =
                 (if w \<in> \<V> \<and> k < l' w \<and> l' w < num_verts then {} else iterated_res st' w)" for w
      using gf I(6,7) rp(2) unfolding res
      by (simp add: iterated_res_def num_verts out_graph_inv_def in_graph_inv_def)
    have "invar_iterated (relabel_gap_impl u st)"
    proof(unfold invar_iterated_def, intro ballI)
      fix w e
      assume w: "w \<in> \<V>" "e \<in> iterated_res (relabel_gap_impl u st) w"
      hence "\<not> (k < l' w \<and> l' w < card \<V>)" "e \<in> iterated_res st' w"
        using gf_it[of w] by (auto simp: num_verts split: if_splits)
      thus "\<not> admissible (flow_abs (relabel_gap_impl u st)) (labels_abs (relabel_gap_impl u st)) e"
        by (intro iterated_invar_label_increase[OF rp(1) _ _ w(1)])
           (simp_all add: res labels rp(2) gap_effect_def)
    qed
    moreover have "invar_basic st'" "invar_excess st'" "invar_res st'" "invar_flow st'"
      using rp(1) by (auto elim: invar_state_props)
    hence "invar_basic (relabel_gap_impl u st)" "invar_excess (relabel_gap_impl u st)"
          "invar_res (relabel_gap_impl u st)" "invar_flow (relabel_gap_impl u st)"
      using gf I(6,7)
      by (auto simp: res invar_basic_def invar_excess_def invar_res_def invar_flow_def out_graph_inv_def
                     in_graph_inv_def)
    moreover have "invar_counts (relabel_gap_impl u st)"
      using gf I(6,7) by (simp add: res invar_counts_def counts_correct_def out_graph_inv_def in_graph_inv_def)
    moreover have "invar_labels (relabel_gap_impl u st)"
      using I(1-3) assms(2) rp(3)
      by (simp add: res labels eff[symmetric] invar_labels_def relabel_gap_preserves_valid
                    relabel_gap_preserves_height_bounded)
    ultimately show ?thesis
      using labels eff by (simp add: invar_state_def res)
  next
    case False
    hence "relabel_gap_impl u st = st'"
      by (auto simp: relabel_gap_impl_def Let_def k_def st'_def)
    moreover have "\<not> gap_precond l' k"
      using False cnt by (auto simp: gap_precond_def num_verts card_gt_0_iff)
    ultimately show ?thesis
      using rp(1,2) by (simp add: relabel_gap_effect_def l'_def k_def)
  qed
  thus "invar_state (relabel_gap_impl u st)"
       "labels_abs (relabel_gap_impl u st) = relabel_gap_effect (flow_abs st) (labels_abs st) u"
    by simp_all
qed

text \<open>A forward push along \<open>d\<close> pushes along @{term "F d"},
  a backward push along @{term "B d"}.\<close>

lemma push_impl_props:
  assumes "invar_state st" "(op = Push_Fwd d \<and> e = F d) \<or> (op = Push_Bwd d \<and> e = B d)"
          "push_precond s t (flow_abs st) (labels_abs st) e"
  shows "invar_state (apply_op op st)"
        "flow_abs (apply_op op st) = push_effect (flow_abs st) e"
        "pr_labels (apply_op op st) = pr_labels st" "pr_counts (apply_op op st) = pr_counts st"
        "pr_out (apply_op op st) = pr_out st" "pr_in (apply_op op st) = pr_in st"
        "pr_ctx (apply_op op st) = pr_ctx st"
proof-
  have I: "emap_invar (pr_fwd st)" "emap_invar (pr_bwd st)" "ex_invar (pr_excess st)"
          "\<forall> v \<in> \<V>. ex_get (pr_excess st) v = ex (flow_abs st) v" "res_correct (pr_fwd st) (pr_bwd st)"
          "is_preflow s (flow_abs st)" "valid_labelling s t (flow_abs st) (labels_abs st)"
    using assms(1) by (auto elim!: invar_props_elims)
  have e: "e \<in> \<EE>" "fstv e \<in> \<V>" "d \<in> \<E>"
    using assms(2,3) o_edge_res[of e] by (auto elim!: push_precondE admissibleE active_vertexE)
  obtain fw' bw' x' where
    aug: "augment_impl (oedge e)
            (case e of F _ \<Rightarrow> push_amount (flow_abs st) e | B _ \<Rightarrow> - push_amount (flow_abs st) e)
            (pr_fwd st) (pr_bwd st) (pr_excess st) = (fw', bw', x')"
    by (cases "augment_impl (oedge e) (case e of F _ \<Rightarrow> push_amount (flow_abs st) e
                                                | B _ \<Rightarrow> - push_amount (flow_abs st) e)
                 (pr_fwd st) (pr_bwd st) (pr_excess st)") auto
  have st': "apply_op op st = st\<lparr>pr_fwd := fw', pr_bwd := bw', pr_excess := x'\<rparr>"
    using assms(2) aug I(4) e(2) rcap_fwd[OF I(5) e(3)]
    by (auto simp: push_fwd_impl_def push_bwd_impl_def Let_def push_amount_def)
  note ap = augment_impl_props[OF I(1-3) e(1) I(4,5) aug]
  have "emap_get bw' = push_effect (flow_abs st) e"
    using ap(4)
    by (simp add: push_effect_def)
  thus "flow_abs (apply_op op st) = push_effect (flow_abs st) e"
       "pr_labels (apply_op op st) = pr_labels st" "pr_counts (apply_op op st) = pr_counts st"
       "pr_out (apply_op op st) = pr_out st" "pr_in (apply_op op st) = pr_in st"
       "pr_ctx (apply_op op st) = pr_ctx st"
    by (simp_all add: st')
  have "invar_basic st" "invar_counts st" "height_bounded (labels_abs st)"
       "\<forall> u \<in> \<V>. \<forall> e \<in> iterated_res st u. \<not> admissible (flow_abs st) (labels_abs st) e"
    using assms(1) by (auto elim!: invar_props_elims)
  hence "invar_basic (apply_op op st)" "invar_counts (apply_op op st)" "invar_labels (apply_op op st)"
        "invar_iterated (apply_op op st)"
    using ap(1-3) push_preserves_valid[OF I(7) assms(3)] ap(4)[folded push_effect_def]
    by (auto simp: st' invar_basic_def invar_counts_def invar_labels_def invar_iterated_def
                   iterated_res_def dest: push_admissible[OF assms(3)])
  moreover have "invar_excess (apply_op op st)" "invar_res (apply_op op st)" "invar_flow (apply_op op st)"
    using ap(5,6) push_preserves_preflow[OF I(6) assms(3)] ap(4)[folded push_effect_def]
    by (simp_all add: st' invar_excess_def invar_res_def invar_flow_def)
  ultimately show "invar_state (apply_op op st)"
    by (simp add: invar_state_def)
qed


text \<open>The number of edges the two iterators of a vertex have not yet passed.\<close>

definition "remaining_count st u = card (out_remaining (pr_out st) u) + card (in_remaining (pr_in st) u)"

text \<open>Changing only the iterators preserves the invariants if the new iterators are valid and no
      newly passed residual edge is admissible.\<close>

lemma invar_state_iterators:
  assumes "invar_state st" "pr_fwd st' = pr_fwd st" "pr_bwd st' = pr_bwd st" "pr_excess st' = pr_excess st"
          "pr_labels st' = pr_labels st" "pr_counts st' = pr_counts st" "out_graph_inv (pr_out st')"
          "in_graph_inv (pr_in st')"
          "\<forall> w \<in> \<V>. \<forall> e \<in> iterated_res st' w.
             \<not> admissible (flow_abs st) (labels_abs st) e"
  shows "invar_state st'"
  using assms
  by (simp add: invar_state_def invar_basic_def invar_excess_def invar_counts_def invar_res_def invar_flow_def
                invar_labels_def invar_iterated_def)

lemma invar_state_iterators_update:
  assumes "invar_state st" "out_graph_inv og" "in_graph_inv ig"
          "\<And> w d. \<lbrakk>w \<in> \<V>; d \<in> out_iterated og w - out_iterated (pr_out st) w\<rbrakk>
           \<Longrightarrow> \<not> admissible_fwd_impl (pr_fwd st) (pr_labels st) d"
          "\<And> w d. \<lbrakk>w \<in> \<V>; d \<in> in_iterated ig w - in_iterated (pr_in st) w\<rbrakk>
           \<Longrightarrow> \<not> admissible_bwd_impl (pr_bwd st) (pr_labels st) d"
  shows "invar_state (st\<lparr>pr_out := og, pr_in := ig\<rparr>)"
  using assms out_graph_inv_delta(3)[OF assms(2)] in_graph_inv_delta(3)[OF assms(3)]
  by (intro invar_state_iterators[OF assms(1)];
      auto elim!: invar_state_props invar_res_props invar_iterated_props simp: iterated_res_def;
      fastforce simp: delta_plus_def delta_minus_def admissible_fwd_impl admissible_bwd_impl)


lemma iterator_move_iterated:
  assumes "indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move it_reset \<V>"
          "it_invar C" "u \<in> \<V>" "has C u"
  shows "it_iterated (move C u) w = (if w = u then insert (cur C u) (it_iterated C w) else it_iterated C w)"
proof-
  interpret it: indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move it_reset \<V>
    by (rule assms(1))
  show ?thesis
    using assms(2-)
    by (cases "w = u") (auto simp: it.idx_has it.idx_move_iterated it.idx_move_iterated_other)
qed

lemma move_impl_props:
  assumes "invar_state st" "u \<in> \<V>" "current_res st u = Some e"
          "\<not> admissible (flow_abs st) (labels_abs st) e"
  shows "invar_state (move_impl u st)"
        "pr_fwd (move_impl u st) = pr_fwd st \<and> pr_bwd (move_impl u st) = pr_bwd st"
        "pr_labels (move_impl u st) = pr_labels st" "pr_ctx (move_impl u st) = pr_ctx st"
        "remaining_count (move_impl u st) u < remaining_count st u"
        "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (move_impl u st) w = remaining_count st w"
proof-
  have I: "out_invar (pr_out st)" "finite (out_remaining (pr_out st) u)" "in_invar (pr_in st)"
          "finite (in_remaining (pr_in st) u)" "out_graph_inv (pr_out st)" "in_graph_inv (pr_in st)"
          "res_correct (pr_fwd st) (pr_bwd st)"
    using assms(1,2)
    by (auto elim!: invar_props_elims simp: out_graph_inv_delta in_graph_inv_delta)
  note iterated = iterator_move_iterated[OF outg.indexed_iterable_set_axioms I(1) assms(2)]
                  iterator_move_iterated[OF ing.indexed_iterable_set_axioms I(3) assms(2)]
  have "invar_state (st\<lparr>
          pr_out := if out_has (pr_out st) u then out_move (pr_out st) u else pr_out st,
          pr_in := if out_has (pr_out st) u then pr_in st else in_move (pr_in st) u\<rparr>)"
    using assms I outg.idx_current[of "pr_out st" u] ing.idx_current[of "pr_in st" u]
          out_graph_inv_delta(6)[of "pr_out st" u] in_graph_inv_delta(6)[of "pr_in st" u]
    by (intro invar_state_iterators_update;
        auto simp: out_graph_inv_def in_graph_inv_def current_res_def outg.idx_has ing.idx_has
                   outg.idx_move_invar ing.idx_move_invar outg.idx_move_abstract ing.idx_move_abstract
                   iterated admissible_fwd_impl admissible_bwd_impl
                   delta_plus_def delta_minus_def
             split: if_splits)
  thus "invar_state (move_impl u st)"
    by (auto simp: move_impl_def split: if_splits)
  show "pr_fwd (move_impl u st) = pr_fwd st \<and> pr_bwd (move_impl u st) = pr_bwd st"
       "pr_labels (move_impl u st) = pr_labels st" "pr_ctx (move_impl u st) = pr_ctx st"
       "remaining_count (move_impl u st) u < remaining_count st u"
       "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (move_impl u st) w = remaining_count st w"
    using assms(2,3) I outg.idx_current[of "pr_out st" u] ing.idx_current[of "pr_in st" u]
    by (auto simp: move_impl_def current_res_def remaining_count_def outg.idx_has ing.idx_has
                   outg.idx_move_remaining ing.idx_move_remaining outg.idx_move_remaining_other
                   ing.idx_move_remaining_other card_gt_0_iff split: if_splits)
qed

text \<open>Skipping inadmissible edges: the scan stops at the first admissible edge or at the end of
      the edges; all passed edges are inadmissible and the remaining edges do not grow.\<close>

lemma skip_scan_props:
  assumes "indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move
                                    it_reset \<V>"
      and "it_invar C" "u \<in> \<V>" "finite (it_remaining C u)"
          "skip_scan has cur move adm u C = C'"
  shows "it_invar C'" "\<forall> w. it_abstract C' w = it_abstract C w"
        "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w
         \<and> it_remaining C' w = it_remaining C w"
        "\<forall> d \<in> it_iterated C' u - it_iterated C u. \<not> adm d"
        "card (it_remaining C' u) \<le> card (it_remaining C u)"
proof-
  interpret it: indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move
                                     it_reset \<V>
    by (rule assms(1))
  have "it_invar C' \<and> (\<forall> w. it_abstract C' w = it_abstract C w) \<and>
        (\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w
          \<and> it_remaining C' w = it_remaining C w) \<and>
        (\<forall> d \<in> it_iterated C' u - it_iterated C u. \<not> adm d) \<and>
        card (it_remaining C' u) \<le> card (it_remaining C u)"
    using assms(2-)
  proof(induction "card (it_remaining C u)" arbitrary: C rule: less_induct)
    case less
    show ?case
    proof(cases "has C u \<and> \<not> adm (cur C u)")
      case True
      have "card (it_remaining (move C u) u) < card (it_remaining C u)"
           "it_invar (move C u)" "finite (it_remaining (move C u) u)"
           "skip_scan has cur move adm u (move C u) = C'"
        using less.prems True it.idx_current[of C u]
        by (auto simp: it.idx_has it.idx_move_remaining it.idx_move_invar card_gt_0_iff
                          skip_scan.simps[of has cur move adm u C])
      from less.hyps[OF this(1,2) less.prems(2) this(3,4)] this
      show ?thesis
        using less.prems(1,2) True
        by (auto simp: it.idx_has it.idx_move_abstract it.idx_move_iterated it.idx_move_iterated_other
                       it.idx_move_remaining_other)
    next
      case False
      with less.prems(1,4) show ?thesis
        by (subst (asm) skip_scan.simps) auto
    qed
  qed
  thus "it_invar C'" "\<forall> w. it_abstract C' w = it_abstract C w"
       "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w
          \<and> it_remaining C' w = it_remaining C w"
       "\<forall> d \<in> it_iterated C' u - it_iterated C u. \<not> adm d"
       "card (it_remaining C' u) \<le> card (it_remaining C u)"
    by simp_all
qed

lemma skip_impl_props:
  assumes "invar_state st" "u \<in> \<V>"
  shows "invar_state (skip_impl u st)"
        "pr_fwd (skip_impl u st) = pr_fwd st \<and> pr_bwd (skip_impl u st) = pr_bwd st"
        "pr_labels (skip_impl u st) = pr_labels st" "pr_ctx (skip_impl u st) = pr_ctx st"
        "remaining_count (skip_impl u st) u \<le> remaining_count st u"
        "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (skip_impl u st) w = remaining_count st w"
proof-
  have I: "out_invar (pr_out st)" "out_abstract (pr_out st) u = \<delta>\<^sup>+ u"
          "finite (out_remaining (pr_out st) u)"
          "in_invar (pr_in st)" "in_abstract (pr_in st) u = \<delta>\<^sup>- u" "finite (in_remaining (pr_in st) u)"
          "out_graph_inv (pr_out st)" "in_graph_inv (pr_in st)"
          "\<forall> w \<in> \<V>. \<forall> e \<in> iterated_res st w. \<not> admissible (flow_abs st) (labels_abs st) e"
          "res_correct (pr_fwd st) (pr_bwd st)"
    using assms by (auto elim!: invar_props_elims simp: out_graph_inv_delta in_graph_inv_delta)
  define og where "og = skip_scan out_has out_current out_move
                          (admissible_fwd_impl (pr_fwd st) (pr_labels st)) u (pr_out st)"
  define ig where "ig = (if out_has og u then pr_in st
                         else skip_scan in_has in_current in_move
                                (admissible_bwd_impl (pr_bwd st) (pr_labels st)) u (pr_in st))"
  have st': "skip_impl u st = st\<lparr>pr_out := og, pr_in := ig\<rparr>"
    by (cases "out_has og u") (simp_all add: skip_impl_def Let_def og_def[symmetric] ig_def)
  note so = skip_scan_props[OF outg.indexed_iterable_set_axioms I(1) assms(2) I(3) og_def[symmetric]]
  have si: "in_invar ig" "\<forall> w. in_abstract ig w = in_abstract (pr_in st) w"
           "\<forall> w. w \<noteq> u \<longrightarrow> in_iterated ig w = in_iterated (pr_in st) w \<and>
                            in_remaining ig w = in_remaining (pr_in st) w"
           "\<forall> d \<in> in_iterated ig u - in_iterated (pr_in st) u.
              \<not> admissible_bwd_impl (pr_bwd st) (pr_labels st) d"
           "card (in_remaining ig u) \<le> card (in_remaining (pr_in st) u)"
    using skip_scan_props[where adm = "admissible_bwd_impl (pr_bwd st) (pr_labels st)",
                          OF ing.indexed_iterable_set_axioms I(4) assms(2) I(6) refl] I(4)
    by (auto simp: ig_def)
  show "pr_fwd (skip_impl u st) = pr_fwd st \<and> pr_bwd (skip_impl u st) = pr_bwd st"
       "pr_labels (skip_impl u st) = pr_labels st" "pr_ctx (skip_impl u st) = pr_ctx st"
       "remaining_count (skip_impl u st) u \<le> remaining_count st u"
       "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (skip_impl u st) w = remaining_count st w"
    using so(3,5) si(3,5) by (simp_all add: st' remaining_count_def)
  show "invar_state (skip_impl u st)"
    unfolding st'
    using assms so si I(7,8)
    by (intro invar_state_iterators_update)
       (auto simp: out_graph_inv_def in_graph_inv_def)
qed

text \<open>Advancing moves past the current inadmissible edge and then skips all following
      inadmissible edges.\<close>

lemma advance_impl_props:
  assumes "invar_state st" "u \<in> \<V>" "current_res st u = Some e"
          "\<not> admissible (flow_abs st) (labels_abs st) e"
  shows "invar_state (advance_impl u st)"
        "pr_fwd (advance_impl u st) = pr_fwd st \<and> pr_bwd (advance_impl u st) = pr_bwd st"
        "pr_labels (advance_impl u st) = pr_labels st" "pr_ctx (advance_impl u st) = pr_ctx st"
        "remaining_count (advance_impl u st) u < remaining_count st u"
        "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (advance_impl u st) w = remaining_count st w"
  using move_impl_props[OF assms] skip_impl_props[of "move_impl u st" u] assms(2)
  by (auto simp: advance_impl_def intro: le_less_trans)

subsubsection \<open>Termination\<close>

text \<open>The number of edges not yet passed by any iterator.\<close>

definition "remaining_measure st = (\<Sum> v \<in> \<V>. remaining_count st v)"

text \<open>Relabelling decreases the first component, saturating pushes decrease the second,
      non-saturating pushes the second or the third, and advancing decreases the fourth.\<close>

definition "pr_measure =
  measures [\<lambda> st. label_measure (labels_abs st),
            \<lambda> st. admissible_count (flow_abs st) (labels_abs st),
            \<lambda> st. active_potential s t (flow_abs st) (labels_abs st),
            remaining_measure]"

lemma wf_pr_measure: "wf pr_measure"
  by (simp add: pr_measure_def)

lemma pr_measure_ctx: "(st', st\<lparr>pr_ctx := c\<rparr>) \<in> pr_measure
                       \<longleftrightarrow> (st', st) \<in> pr_measure"
  by (simp add: pr_measure_def remaining_measure_def remaining_count_def)

lemma push_measure:
  "\<lbrakk>push_precond s t (flow_abs st) (labels_abs st) e; flow_abs st' = push_effect (flow_abs st) e;
    labels_abs st' = labels_abs st\<rbrakk>
   \<Longrightarrow> (st', st) \<in> pr_measure"
  using push_saturating_admissible_count[of "flow_abs st" "labels_abs st" e]
        push_nonsaturating_active_potential[of "flow_abs st" "labels_abs st" e]
        push_admissible_count_mono[of "flow_abs st" "labels_abs st" e]
  by (cases "real_of_ereal (rcap (flow_abs st) e) \<le> ex (flow_abs st) (fstv e)") (auto simp: pr_measure_def)

lemma label_measure_step:
  "label_measure (labels_abs st') < label_measure (labels_abs st) \<Longrightarrow> (st', st) \<in> pr_measure"
  by (simp add: pr_measure_def)

lemma advance_measure:
  assumes "invar_state st" "u \<in> \<V>" "current_res st u = Some e"
          "\<not> admissible (flow_abs st) (labels_abs st) e"
  shows "(advance_impl u st, st) \<in> pr_measure"
proof-
  note ap = advance_impl_props[OF assms]
  have "remaining_count (advance_impl u st) w \<le> remaining_count st w" for w
    using ap(5,6) by (cases "w = u") auto
  hence "remaining_measure (advance_impl u st) < remaining_measure st"
    unfolding remaining_measure_def using ap(5) assms(2) \<V>_finite by (intro sum_strict_mono_ex1) auto
  thus ?thesis
    using ap(2,3) by (simp add: pr_measure_def)
qed


text \<open>Every operation the strategy may request preserves the invariants and decreases the measure.\<close>

lemma invar_state_labelling:
  "invar_state st \<Longrightarrow>
   is_preflow s (flow_abs st) \<and> valid_labelling s t (flow_abs st) (labels_abs st) \<and>
   height_bounded (labels_abs st)"
  by (auto elim!: invar_props_elims)

lemma apply_op_props:
  assumes "invar_state st" "good_op st op" "op \<noteq> Done"
  shows "invar_state (apply_op op st)" "(apply_op op st, st) \<in> pr_measure"
proof-
  have "invar_state (apply_op op st) \<and> (apply_op op st, st) \<in> pr_measure"
  proof(cases op)
    case (Push_Fwd d)
    hence "push_precond s t (flow_abs st) (labels_abs st) (F d)"
      using assms(2) by (simp add: good_op_def)
    from push_impl_props[OF assms(1) _ this, of op d] push_measure[OF this] show ?thesis
      using Push_Fwd
      by simp
  next
    case (Push_Bwd d)
    hence "push_precond s t (flow_abs st) (labels_abs st) (B d)"
      using assms(2) by (simp add: good_op_def)
    from push_impl_props[OF assms(1) _ this, of op d] push_measure[OF this] show ?thesis
      using Push_Bwd
      by simp
  next
    case (Advance u)
    then obtain e where "u \<in> \<V>" "current_res st u = Some e" "\<not> admissible (flow_abs st) (labels_abs st) e"
      using assms(2) by (auto simp: good_op_def)
    thus ?thesis
      using Advance assms(1)
      by (auto intro: advance_impl_props(1) advance_measure)
  next
    case (Relabel u)
    hence "relabel_precond s t (flow_abs st) (labels_abs st) u"
      using assms(2) by (simp add: good_op_def)
    thus ?thesis
      using Relabel assms(1) invar_state_labelling[of st]
      by (auto intro!: relabel_impl_props(1) label_measure_step simp: relabel_impl_props(2) relabel_label_measure)
  next
    case (Relabel_Gap u)
    hence "relabel_precond s t (flow_abs st) (labels_abs st) u"
      using assms(2) by (simp add: good_op_def)
    thus ?thesis
      using Relabel_Gap assms(1) invar_state_labelling[of st]
      by (auto intro!: relabel_gap_impl_props(1) label_measure_step
               simp: relabel_gap_impl_props(2) relabel_gap_label_measure)
  qed (use assms(3) in simp)
  thus "invar_state (apply_op op st)" "(apply_op op st, st) \<in> pr_measure"
    by simp_all
qed

end

context push_relabel
begin

subsubsection \<open>Invariants, Termination and Correctness of the Loop\<close>

lemma invar_state_holds_upd[invar_holds_intros]:
  "\<lbrakk>push_relabel_upd_cond st; invar_state st; ctx_invar st\<rbrakk>
   \<Longrightarrow> invar_state (push_relabel_upd st)"
  by (elim push_relabel_upd_cond)
     (auto intro!: apply_op_props(1) simp: push_relabel_upd_def invar_state_ctx good_op_ctx select(1))

lemma ctx_invar_holds_upd[invar_holds_intros]:
  "\<lbrakk>push_relabel_upd_cond st; invar_state st; ctx_invar st\<rbrakk>
   \<Longrightarrow> ctx_invar (push_relabel_upd st)"
  by (elim push_relabel_upd_cond) (simp add: push_relabel_upd_def select(2))

lemma invar_state_holds_ret[invar_holds_intros]:
  "\<lbrakk>push_relabel_ret_cond st; invar_state st\<rbrakk> \<Longrightarrow> invar_state (push_relabel_ret st)"
  by (simp add: push_relabel_ret_def invar_state_ctx)

lemma ret_1_no_active[ret_holds_intros]:
  "\<lbrakk>push_relabel_ret_cond st; invar_state st; ctx_invar st\<rbrakk>
   \<Longrightarrow> \<not> active_vertex s t (flow_abs (push_relabel_ret st)) v"
  by (elim push_relabel_ret_cond)
     (insert select(1)[of st Done], auto simp: push_relabel_ret_def good_op_def)

lemma call_1_terminates[termination_intros]:
  "\<lbrakk>push_relabel_upd_cond st; invar_state st; ctx_invar st\<rbrakk> \<Longrightarrow> (push_relabel_upd st, st) \<in> pr_measure"
  by (elim push_relabel_upd_cond, subst pr_measure_ctx[symmetric])
     (auto intro!: apply_op_props(2) simp: push_relabel_upd_def invar_state_ctx good_op_ctx select(1))

lemma push_relabel_loop_terminates[termination_intros]:
  assumes "invar_state st" "ctx_invar st"
  shows "push_relabel_loop_dom st"
  using assms
proof(induction rule: wf_induct_rule[OF wf_pr_measure])
  case IH: (1 st)
  thus ?case
    by (cases rule: push_relabel_cases[of st])
       (auto intro: push_relabel_domintros IH(1) invar_holds_intros termination_intros)
qed

lemma invar_state_holds[invar_holds_intros]:
  assumes "push_relabel_loop_dom st" "invar_state st" "ctx_invar st"
  shows "invar_state (push_relabel_loop st)"
  using assms
proof(induction rule: push_relabel_induct)
  case IH: (1 st)
  show ?case
    by (rule push_relabel_cases[of st]) (auto intro!: IH(2-) invar_holds_intros simp: push_relabel_simps IH(1))
qed

lemma push_relabel_loop_no_active[ret_holds_intros]:
  assumes "push_relabel_loop_dom st" "invar_state st" "ctx_invar st"
  shows "\<not> active_vertex s t (flow_abs (push_relabel_loop st)) v"
  using assms
proof(induction rule: push_relabel_induct)
  case IH: (1 st)
  show ?case
    by (rule push_relabel_cases[of st])
       (simp_all add: push_relabel_simps IH ret_1_no_active invar_state_holds_upd ctx_invar_holds_upd)
qed

text \<open>The loop computes a maximum flow from every state satisfying the invariants.\<close>

lemma push_relabel_loop_max_flow:
  assumes "invar_state st" "ctx_invar st"
  shows "is_max_flow s t (flow_abs (push_relabel_loop st))"
proof-
  have "invar_state (push_relabel_loop st)" "\<And> v. \<not> active_vertex s t (flow_abs (push_relabel_loop st)) v"
    using assms
    by (simp_all add: invar_state_holds push_relabel_loop_no_active push_relabel_loop_terminates)
  thus ?thesis
    by (auto elim!: invar_props_elims intro: no_active_max_flow)
qed

end


context push_relabel_ops_correct
begin

subsubsection \<open>Initialisation\<close>

text \<open>After the edges in \<open>D\<close> have been processed, the maps agree with the initial flow on
      \<open>D\<close> and the excesses are those of the initial flow restricted to \<open>D\<close>.\<close>

definition "init_inv D fw bw x =
  (emap_invar fw \<and> emap_invar bw \<and> ex_invar x \<and>
   (\<forall> d \<in> D. emap_get bw d = init_flow s d \<and> \<u> d = ereal (emap_get fw d + emap_get bw d)) \<and>
   (\<forall> v \<in> \<V>. ex_get x v = (\<Sum> d \<in> \<delta>\<^sup>- v \<inter> D. init_flow s d) - (\<Sum> d \<in> \<delta>\<^sup>+ v \<inter> D. init_flow s d)))"

lemma sum_Int_insert:
  "\<lbrakk>finite A; d \<notin> D\<rbrakk> \<Longrightarrow> (\<Sum> e \<in> A \<inter> insert d D. g e)
   = (\<Sum> e \<in> A \<inter> D. g e) + (if d \<in> A then g d else 0)"
  by (simp add: Int_insert_right add.commute)

lemma delta_mem_iff:
  "d \<in> \<E> \<Longrightarrow> (d \<in> \<delta>\<^sup>- v \<longleftrightarrow> snd d = v) \<and> (d \<in> \<delta>\<^sup>+ v \<longleftrightarrow> fst d = v)"
  by (auto simp: delta_minus_def delta_plus_def)

lemma init_step_inv:
  assumes "init_inv D fw bw x" "d \<in> \<E>" "d \<notin> D" "init_step (fw, bw, x) d = (fw', bw', x')"
  shows "init_inv (insert d D) fw' bw' x'"
proof-
  define c where "c = emap_get caps d"
  have c: "\<u> d = ereal c"
    using assms(2) by (simp add: c_def caps(2))
  have I: "emap_invar fw" "emap_invar bw" "ex_invar x"
          "\<forall> e \<in> D. emap_get bw e = init_flow s e \<and> \<u> e = ereal (emap_get fw e + emap_get bw e)"
          "\<forall> v \<in> \<V>. ex_get x v = (\<Sum> e \<in> \<delta>\<^sup>- v \<inter> D. init_flow s e)
           - (\<Sum> e \<in> \<delta>\<^sup>+ v \<inter> D. init_flow s e)"
    using assms(1) by (simp_all add: init_inv_def)
  show ?thesis
  proof(cases "fst d = s \<and> snd d \<noteq> s")
    case True
    define x1 where "x1 = ex_upd x s (ex_get x s - c)"
    have "fw' = emap_upd fw d 0" "bw' = emap_upd bw d c" "x' = ex_upd x1 (snd d) (ex_get x1 (snd d) + c)"
      using assms(4) True
      by (auto simp: init_step_def Let_def c_def x1_def)
    moreover have "ex_invar x1" "ex_get x1 = (ex_get x)(s := ex_get x s - c)"
      using I(3) s_in_V
      by (simp_all add: x1_def ex_map.fixed_univ_map_upd_invar ex_map.fixed_univ_map_upd)
    moreover have "init_flow s d = c" "s \<noteq> snd d"
      using True assms(2) c
      by (auto simp: init_flow_def)
    ultimately show ?thesis
      using I assms(2,3) c True fst_E_V snd_E_V delta_mem_iff[of d]
      by (simp add: init_inv_def sum_Int_insert finite_delta edge_map.fixed_univ_map_upd_invar
                    ex_map.fixed_univ_map_upd_invar edge_map.fixed_univ_map_upd ex_map.fixed_univ_map_upd)
  next
    case False
    have "fw' = emap_upd fw d c" "bw' = emap_upd bw d 0" "x' = x"
      using assms(4) False
      by (auto simp: init_step_def Let_def c_def)
    moreover have "init_flow s d = 0"
      using False
      by (auto simp: init_flow_def)
    ultimately show ?thesis
      using I assms(2,3) c delta_mem_iff[of d]
      by (simp add: init_inv_def sum_Int_insert finite_delta edge_map.fixed_univ_map_upd_invar
                    edge_map.fixed_univ_map_upd)
  qed
qed

lemma init_fold_inv:
  assumes "init_inv D fw bw x" "distinct ds" "set ds \<subseteq> \<E>" "set ds \<inter> D = {}"
          "foldl init_step (fw, bw, x) ds = (fw', bw', x')"
  shows "init_inv (D \<union> set ds) fw' bw' x'"
  using assms
proof(induction ds arbitrary: D fw bw x)
  case (Cons d ds)
  obtain fw1 bw1 x1 where step: "init_step (fw, bw, x) d = (fw1, bw1, x1)"
    by (cases "init_step (fw, bw, x) d") auto
  have "init_inv (insert d D) fw1 bw1 x1"
    using Cons.prems(1,3,4) step by (intro init_step_inv) auto
  hence "init_inv (insert d D \<union> set ds) fw' bw' x'"
    using Cons.prems(2-5) step by (intro Cons.IH) auto
  thus ?case
    by simp
qed simp

text \<open>Every flow that agrees with the initial flow on the edges is an initial preflow.\<close>

lemma init_rcap_agree:
  "\<lbrakk>\<forall> d \<in> \<E>. f d = init_flow s d; e \<in> \<EE>\<rbrakk> \<Longrightarrow> rcap f e = rcap (init_flow s) e"
  by (auto simp: \<EE>_def)

lemma init_flow_agree:
  assumes "\<forall> d \<in> \<E>. f d = init_flow s d"
  shows "\<And> v. ex f v = ex (init_flow s) v" "is_preflow s f"
        "valid_labelling s t f (init_labels s)" "\<And> e. \<not> admissible f (init_labels s) e"
proof-
  show "\<And> v. ex f v = ex (init_flow s) v"
    using assms
    by (auto intro: sum.cong simp: ex_def delta_minus_def delta_plus_def)
  thus "is_preflow s f"
    using init_flow_preflow assms
    by (simp add: is_preflow_def isuflow_def)
  show "valid_labelling s t f (init_labels s)"
    using init_labels_valid assms init_rcap_agree[of f]
    by (simp add: valid_labelling_def)
  show "\<not> admissible f (init_labels s) e" for e
    using init_not_admissible[of e] assms init_rcap_agree[of f e]
    by (cases "e \<in> \<EE>") (auto simp: admissible_def)
qed


text \<open>The pass over the edges computes the initial flow, its residual capacities and its excesses.\<close>

lemma init_edge_fold:
  obtains fw bw x where "edge_fold init_step (emap_init, emap_init, ex_init) = (fw, bw, x)"
    "emap_invar fw" "emap_invar bw" "ex_invar x" "\<forall> d \<in> \<E>. emap_get bw d = init_flow s d"
    "res_correct fw bw" "\<forall> v \<in> \<V>. ex_get x v = ex (emap_get bw) v"
proof-
  obtain es where es: "distinct es" "set es = \<E>"
    "edge_fold init_step (emap_init, emap_init, ex_init) = foldl init_step (emap_init, emap_init, ex_init) es"
    using edge_fold by blast
  obtain fw bw x where fold: "foldl init_step (emap_init, emap_init, ex_init) es = (fw, bw, x)"
    by (cases "foldl init_step (emap_init, emap_init, ex_init) es") auto
  have "init_inv {} emap_init emap_init ex_init"
    using init_adts by (simp add: init_inv_def)
  hence "init_inv \<E> fw bw x"
    using init_fold_inv[of "{}", OF _ es(1) _ _ fold] es(2) by simp
  moreover have "\<delta>\<^sup>- v \<inter> \<E> = \<delta>\<^sup>- v" "\<delta>\<^sup>+ v \<inter> \<E> = \<delta>\<^sup>+ v"
    for v
    by (auto simp: delta_minus_def delta_plus_def)
  ultimately show ?thesis
    using that es(3) fold init_flow_agree(1)[of "emap_get bw"]
    by (auto simp: init_inv_def res_correct_def ex_def)
qed

text \<open>The source is labelled with the number of vertices, all other vertices with 0.\<close>

lemma init_labels_counts:
  "label_invar (label_upd label_init s num_verts)"
  "label_get (label_upd label_init s num_verts) = init_labels s"
  "count_invar (count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1)"
  "counts_correct (label_upd label_init s num_verts) (count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1)"
proof-
  show "label_invar (label_upd label_init s num_verts)"
       "label_get (label_upd label_init s num_verts) = init_labels s"
    using init_adts(4,5) s_in_V
    by (simp_all add: init_labels_def num_verts label_map.fixed_univ_map_upd_invar label_map.fixed_univ_map_upd)
  moreover have "card \<V> \<ge> 2"
    using card_V_ge_2 .
  ultimately have "{w. w \<in> \<V> \<and> label_get (label_upd label_init s num_verts) w = k}
                   = (if k = card \<V> then {s} else if k = 0 then \<V> - {s} else {})" for k
    using s_in_V by (auto simp: init_labels_def)
  moreover have "count_invar (count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1)"
    "count_get (count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1)
     = ((\<lambda> k. 0)(0 := card \<V> - 1))(card \<V> := 1)"
    using init_adts(6,7) card_V_ge_2
    by (simp_all add: num_verts count_map.fixed_univ_map_upd_invar count_map.fixed_univ_map_upd)
  ultimately show "count_invar (count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1)"
    "counts_correct (label_upd label_init s num_verts) (count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1)"
    using \<V>_finite s_in_V card_V_ge_2 by (auto simp: counts_correct_def)
qed

end

context push_relabel
begin

lemma init_state_props: "invar_state init_state" "ctx_invar init_state" "push_relabel_loop_dom init_state"
proof-
  obtain fw bw x where fold: "edge_fold init_step (emap_init, emap_init, ex_init) = (fw, bw, x)"
    "emap_invar fw" "emap_invar bw" "ex_invar x" "\<forall> d \<in> \<E>. emap_get bw d = init_flow s d"
    "res_correct fw bw" "\<forall> v \<in> \<V>. ex_get x v = ex (emap_get bw) v"
    by (rule init_edge_fold)
  hence st: "init_state = \<lparr>pr_fwd = fw, pr_bwd = bw, pr_excess = x, pr_labels = label_upd label_init s num_verts,
                          pr_counts = count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1,
                          pr_out = out_init, pr_in = in_init,
                          pr_ctx = init_ctx fw bw x (label_upd label_init s num_verts) out_init in_init\<rparr>"
    by (simp add: init_state_def Let_def)
  have "invar_state init_state"
    using fold(2-) init_labels_counts init_adts(8,9) init_flow_agree(2-)[OF fold(5)]
          init_labels_height_bounded
    by (simp add: st invar_state_def invar_basic_def invar_excess_def invar_counts_def invar_res_def
                  invar_flow_def invar_labels_def invar_iterated_def counts_correct_def)
  moreover hence "ctx_invar init_state"
    using init_ctx fold(5) init_labels_counts(2) by (simp add: st)
  ultimately show "invar_state init_state" "ctx_invar init_state" "push_relabel_loop_dom init_state"
    by (simp_all add: push_relabel_loop_terminates)
qed

subsubsection \<open>Correctness\<close>

lemma push_relabel_correct: "is_max_flow s t (emap_get push_relabel)"
  using init_state_props
  by (simp add: push_relabel_def push_relabel_loop_max_flow push_relabel_loop_impl_same)

end

end
