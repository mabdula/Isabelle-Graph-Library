theory Push_Relabel_Generic
  imports
    Push_Relabel_Basic
    Data_Structures.Fixed_Univ_Map_Specs
    Data_Structures.Iterable_Set_Specs
    Data_Structures.Iterable_Set_Reset_To_Specs
begin

section \<open>The Generic Push-Relabel Algorithm on Abstract Data Types\<close>

subsection \<open>Iterators over Outgoing and Ingoing Edges\<close>

text \<open>REDUNDANT: the two locales below are verbatim copies of @{text outgoing_edge_iterator} and
      @{text ingoing_edge_iterator} from \<open>Mincost_Flow_Algorithms/Acyclic_Flow.thy\<close>, which must
      not be imported here. They should be moved to a common place and unified with that copy.\<close>

locale outgoing_edge_iterator =
  multigraph_spec where fst = fst +
  outg: indexed_iterable_set where
      idx_invar     = out_invar and
      idx_abstract  = out_abstract and
      idx_current   = out_current and
      idx_has       = out_has and
      idx_iterated  = out_iterated and
      idx_remaining = out_remaining and
      idx_move      = out_move and
      idx_reset     = out_reset and
      K = \<V>
  for fst :: "'e \<Rightarrow> 'v"
  and out_invar     :: "'g \<Rightarrow> bool"
  and out_abstract  :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and out_current   :: "'g \<Rightarrow> 'v \<Rightarrow> 'e"
  and out_has       :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
  and out_iterated  :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and out_remaining :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and out_move      :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
  and out_reset     :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
begin

text \<open>The collection @{term og} implements the outgoing adjacency iff it is well-formed and
      abstracts, at every vertex, to that vertex's outgoing edges.\<close>

definition "out_graph_inv og \<longleftrightarrow>
   out_invar og \<and> (\<forall>v \<in> \<V>. out_abstract og v = \<delta>\<^sup>+ v)"

end

locale ingoing_edge_iterator =
  multigraph_spec where fst = fst +
  ing: indexed_iterable_set where
      idx_invar     = in_invar and
      idx_abstract  = in_abstract and
      idx_current   = in_current and
      idx_has       = in_has and
      idx_iterated  = in_iterated and
      idx_remaining = in_remaining and
      idx_move      = in_move and
      idx_reset     = in_reset and
      K = \<V>
  for fst :: "'e \<Rightarrow> 'v"
  and in_invar     :: "'g \<Rightarrow> bool"
  and in_abstract  :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and in_current   :: "'g \<Rightarrow> 'v \<Rightarrow> 'e"
  and in_has       :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
  and in_iterated  :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and in_remaining :: "'g \<Rightarrow> 'v \<Rightarrow> 'e set"
  and in_move      :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
  and in_reset     :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
begin

text \<open>The collection @{term ig} implements the ingoing adjacency iff it is well-formed and
      abstracts, at every vertex, to that vertex's ingoing edges.\<close>

definition "in_graph_inv ig \<longleftrightarrow>
   in_invar ig \<and> (\<forall>v \<in> \<V>. in_abstract ig v = \<delta>\<^sup>- v)"

end

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
      of @{theory Draft.Push_Relabel_Basic}.\<close>

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
  outgoing_edge_iterator where fst = fst and snd = snd
      and out_invar = out_invar and out_abstract = out_abstract
      and out_current = out_current and out_has = out_has
      and out_iterated = out_iterated and out_remaining = out_remaining
      and out_move = out_move and out_reset = out_reset +
  ingoing_edge_iterator where fst = fst and snd = snd
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

text \<open>Sending \<open>\<delta>\<close> units of flow along an edge (backwards if \<open>\<delta>\<close> is negative) changes both
      residual capacities of the edge and the excesses of its two endpoints.\<close>

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

lemma relabel_impl_ctx: "relabel_impl u (st\<lparr>pr_ctx := c\<rparr>) = (relabel_impl u st)\<lparr>pr_ctx := c\<rparr>"
  by (simp add: relabel_impl_def split: prod.splits)

lemma gap_impl_ctx: "gap_impl k (st\<lparr>pr_ctx := c\<rparr>) = (gap_impl k st)\<lparr>pr_ctx := c\<rparr>"
  by (simp add: gap_impl_def split: prod.splits)

lemma apply_op_ctx: "apply_op op (st\<lparr>pr_ctx := c\<rparr>) = (apply_op op st)\<lparr>pr_ctx := c\<rparr>"
proof(cases op)
  case (Relabel_Gap u)
  show ?thesis
    by (simp add: Relabel_Gap relabel_gap_impl_def Let_def relabel_impl_ctx gap_impl_ctx)
qed (simp_all add: push_fwd_impl_def push_bwd_impl_def advance_impl_def skip_impl_def move_impl_def
                   relabel_impl_ctx Let_def split: prod.splits)

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
  assumes "push_relabel_loop_dom st"
  shows "push_relabel_loop_impl st = push_relabel_loop st"
  apply(induction rule: push_relabel_loop.pinduct[OF assms])
  apply(subst push_relabel_loop_impl.simps)
  apply(subst push_relabel_loop.psimps)
  by (auto split: prod.splits)

definition "push_relabel_upd st = (case select_of st of (op, c) \<Rightarrow> apply_op op (st\<lparr>pr_ctx := c\<rparr>))"

definition "push_relabel_ret st = st\<lparr>pr_ctx := prod.snd (select_of st)\<rparr>"

definition "push_relabel_ret_cond st = (prod.fst (select_of st) = Done)"

definition "push_relabel_upd_cond st = (prod.fst (select_of st) \<noteq> Done)"

lemma push_relabel_cases:
  "\<lbrakk>push_relabel_ret_cond st \<Longrightarrow> P; push_relabel_upd_cond st \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: push_relabel_ret_cond_def push_relabel_upd_cond_def)

lemma push_relabel_domintros:
  "push_relabel_ret_cond st \<Longrightarrow> push_relabel_loop_dom st"
  "\<lbrakk>push_relabel_upd_cond st; push_relabel_loop_dom (push_relabel_upd st)\<rbrakk>
   \<Longrightarrow> push_relabel_loop_dom st"
proof-
  obtain op c where sel: "select_of st = (op, c)"
    by (cases "select_of st") auto
  show "push_relabel_loop_dom st" if "push_relabel_ret_cond st"
    using sel that by (intro push_relabel_loop.domintros[of st]) (simp add: push_relabel_ret_cond_def)
  show "push_relabel_loop_dom st"
    if "push_relabel_upd_cond st" "push_relabel_loop_dom (push_relabel_upd st)"
    using sel that by (intro push_relabel_loop.domintros[of st]) (simp add: push_relabel_upd_def)
qed

lemma push_relabel_simps:
  "push_relabel_ret_cond st \<Longrightarrow> push_relabel_loop st = push_relabel_ret st"
  "\<lbrakk>push_relabel_loop_dom st; push_relabel_upd_cond st\<rbrakk>
   \<Longrightarrow> push_relabel_loop st = push_relabel_loop (push_relabel_upd st)"
proof-
  obtain op c where sel: "select_of st = (op, c)"
    by (cases "select_of st") auto
  show "push_relabel_loop st = push_relabel_ret st" if "push_relabel_ret_cond st"
    using sel that push_relabel_loop.psimps[OF push_relabel_domintros(1)[OF that]]
    by (simp add: push_relabel_ret_cond_def push_relabel_ret_def)
  show "push_relabel_loop st = push_relabel_loop (push_relabel_upd st)"
    if "push_relabel_loop_dom st" "push_relabel_upd_cond st"
    using sel that push_relabel_loop.psimps[OF that(1)]
    by (simp add: push_relabel_upd_cond_def push_relabel_upd_def)
qed

lemma push_relabel_induct:
  assumes "push_relabel_loop_dom st"
          "\<And> st. \<lbrakk>push_relabel_loop_dom st; push_relabel_upd_cond st \<Longrightarrow> P (push_relabel_upd st)\<rbrakk>
                  \<Longrightarrow> P st"
  shows "P st"
proof(induction rule: push_relabel_loop.pinduct[OF assms(1)])
  case (1 st)
  obtain op c where sel: "select_of st = (op, c)"
    by (cases "select_of st") auto
  show ?case
  proof(rule assms(2)[OF 1(1)])
    assume "push_relabel_upd_cond st"
    hence "op \<noteq> Done"
      using sel by (simp add: push_relabel_upd_cond_def)
    thus "P (push_relabel_upd st)"
      using 1(2)[OF sel[symmetric]] sel by (simp add: push_relabel_upd_def)
  qed
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

lemma finite_capacities: "\<forall> e \<in> \<E>. \<u> e < PInfty"
proof
  fix e
  assume "e \<in> \<E>"
  thus "\<u> e < PInfty"
    using caps(2)[of e] by force
qed

lemmas net_assms = s_in_V t_in_V s_neq_t finite_capacities

subsubsection \<open>Residual Capacities and Augmentation\<close>

lemma finite_delta: "finite (\<delta>\<^sup>+ u)" "finite (\<delta>\<^sup>- u)"
  using finite_E by (auto simp add: delta_plus_def delta_minus_def)

lemma rcap_fwd:
  assumes "res_correct fw bw" "d \<in> \<E>"
  shows "rcap (emap_get bw) (F d) = ereal (emap_get fw d)"
proof-
  have "\<u> d = ereal (emap_get fw d + emap_get bw d)"
    using assms by (simp add: res_correct_def)
  thus ?thesis
    by simp
qed

lemma admissible_fwd_impl:
  "\<lbrakk>res_correct fw bw; d \<in> \<E>\<rbrakk>
   \<Longrightarrow> admissible_fwd_impl fw l d \<longleftrightarrow> admissible (emap_get bw) (label_get l) (F d)"
  by (simp only: admissible_fwd_impl_def admissible_def rcap_fwd) (auto simp add: \<EE>_def)

lemma admissible_bwd_impl:
  "d \<in> \<E> \<Longrightarrow> admissible_bwd_impl bw l d \<longleftrightarrow> admissible (emap_get bw) (label_get l) (B d)"
  by (auto simp add: admissible_bwd_impl_def admissible_def \<EE>_def)
   
text \<open>Sending flow forward along an edge augments its forward copy, sending it backward
      augments its backward copy.\<close>

lemma augment_impl_props:
  assumes "emap_invar fw" "emap_invar bw" "ex_invar x" "e \<in> \<EE>"
          "\<forall> v \<in> \<V>. ex_get x v = ex (emap_get bw) v" "res_correct fw bw"
          "augment_impl (oedge e) (case e of F _ \<Rightarrow> \<gamma> | B _ \<Rightarrow> - \<gamma>) fw bw x = (fw', bw', x')"
  shows "emap_invar fw'" "emap_invar bw'" "ex_invar x'"
        "emap_get bw' = augment_edge (emap_get bw) \<gamma> e"
        "\<forall> v \<in> \<V>. ex_get x' v = ex (emap_get bw') v" "res_correct fw' bw'"
proof-
  define d where "d = oedge e"
  define \<delta> where "\<delta> = (case e of F _ \<Rightarrow> \<gamma> | B _ \<Rightarrow> - \<gamma>)"
  have d: "d \<in> \<E>"
    using assms(4) o_edge_res by (simp add: d_def)
  have uv: "fst d \<in> \<V>" "snd d \<in> \<V>"
    using d by (auto intro: fst_E_V snd_E_V)
  define x1 where "x1 = ex_upd x (fst d) (ex_get x (fst d) - \<delta>)"
  have fw': "fw' = emap_upd fw d (emap_get fw d - \<delta>)"
   and bw': "bw' = emap_upd bw d (emap_get bw d + \<delta>)"
   and x': "x' = ex_upd x1 (snd d) (ex_get x1 (snd d) + \<delta>)"
    using assms(7) by (auto simp add: augment_impl_def Let_def d_def \<delta>_def x1_def)
  show "emap_invar fw'" "emap_invar bw'"
    using edge_map.fixed_univ_map_upd_invar[OF assms(1) d] edge_map.fixed_univ_map_upd_invar[OF assms(2) d]
    by (simp_all add: fw' bw')
  have fw'_get: "emap_get fw' = (emap_get fw)(d := emap_get fw d - \<delta>)"
    using edge_map.fixed_univ_map_upd[OF assms(1) d] by (simp add: fw')
  have bw'_get: "emap_get bw' = (emap_get bw)(d := emap_get bw d + \<delta>)"
    using edge_map.fixed_univ_map_upd[OF assms(2) d] by (simp add: bw')
  have x1: "ex_invar x1" "ex_get x1 = (ex_get x)(fst d := ex_get x (fst d) - \<delta>)"
    using ex_map.fixed_univ_map_upd_invar[OF assms(3) uv(1)] ex_map.fixed_univ_map_upd[OF assms(3) uv(1)]
    by (simp_all add: x1_def)
  show "ex_invar x'"
    using ex_map.fixed_univ_map_upd_invar[OF x1(1) uv(2)] by (simp add: x')
  have x'_get: "ex_get x' = (ex_get x1)(snd d := ex_get x1 (snd d) + \<delta>)"
    using ex_map.fixed_univ_map_upd[OF x1(1) uv(2)] by (simp add: x')
  show aug: "emap_get bw' = augment_edge (emap_get bw) \<gamma> e"
    unfolding bw'_get by (cases e) (auto simp add: d_def \<delta>_def)
  show "\<forall> v \<in> \<V>. ex_get x' v = ex (emap_get bw') v"
  proof
    fix v
    assume v: "v \<in> \<V>"
    have "ex (emap_get bw') v =
          ex (emap_get bw) v - (if v = fstv e then \<gamma> else 0) + (if v = sndv e then \<gamma> else 0)"
      unfolding aug by (rule ex_augment_edge[OF net_assms assms(4)])
    thus "ex_get x' v = ex (emap_get bw') v"
      using assms(5) v by (cases e) (auto simp add: x'_get x1(2) d_def \<delta>_def)
  qed
  show "res_correct fw' bw'"
    using assms(6) by (simp add: res_correct_def fw'_get bw'_get)
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
proof-
  define A where "A = {w. w \<in> \<V> \<and> label_get l w = j}"
  have fin: "finite A"
    using \<V>_finite by (simp add: A_def)
  have eq: "{w. w \<in> \<V> \<and> ((label_get l)(v := k')) w = j} =
            (A - {v}) \<union> (if k' = j then {v} else {})"
    using assms by (auto simp add: A_def)
  have vA: "v \<in> A \<longleftrightarrow> label_get l v = j"
    using assms by (simp add: A_def)
  have "card (A - {v}) = card A - (if label_get l v = j then 1 else 0)"
    using fin vA by simp
  moreover have "card ((A - {v}) \<union> (if k' = j then {v} else {})) =
                 card (A - {v}) + (if k' = j then 1 else 0)"
  proof(cases "k' = j")
    case True
    have "card (insert v (A - {v})) = Suc (card (A - {v}))"
      using fin by (intro card_insert_disjoint) auto
    thus ?thesis
      using True by simp
  qed simp
  ultimately show ?thesis
    unfolding eq A_def[symmetric] by simp
qed

lemma change_label_props:
  assumes "label_invar l" "count_invar cnt" "v \<in> \<V>" "label_get l v < 2 * card \<V>"
          "k' < 2 * card \<V>" "counts_correct l cnt" "change_label l cnt v k' = (l', cnt')"
  shows "label_invar l'" "count_invar cnt'" "label_get l' = (label_get l)(v := k')"
        "counts_correct l' cnt'"
proof-
  define k where "k = label_get l v"
  define cnt1 where "cnt1 = count_upd cnt k (count_get cnt k - 1)"
  have l': "l' = label_upd l v k'" and cnt': "cnt' = count_upd cnt1 k' (count_get cnt1 k' + 1)"
    using assms(7) by (auto simp add: change_label_def Let_def k_def cnt1_def)
  have k: "k \<in> {..<2 * card \<V>}" "k' \<in> {..<2 * card \<V>}"
    using assms(4,5) by (auto simp add: k_def)
  show "label_invar l'"
    using label_map.fixed_univ_map_upd_invar[OF assms(1,3)] by (simp add: l')
  show l'_get: "label_get l' = (label_get l)(v := k')"
    using label_map.fixed_univ_map_upd[OF assms(1,3)] by (simp add: l')
  have cnt1: "count_invar cnt1" "count_get cnt1 = (count_get cnt)(k := count_get cnt k - 1)"
    using count_map.fixed_univ_map_upd_invar[OF assms(2) k(1)]
          count_map.fixed_univ_map_upd[OF assms(2) k(1)] by (simp_all add: cnt1_def)
  show "count_invar cnt'"
    using count_map.fixed_univ_map_upd_invar[OF cnt1(1) k(2)] by (simp add: cnt')
  have cnt'_get: "count_get cnt' = (count_get cnt1)(k' := count_get cnt1 k' + 1)"
    using count_map.fixed_univ_map_upd[OF cnt1(1) k(2)] by (simp add: cnt')
  have pos: "count_get cnt k \<ge> 1"
  proof-
    have "v \<in> {w. w \<in> \<V> \<and> label_get l w = k}"
      using assms(3) by (simp add: k_def)
    hence "card {w. w \<in> \<V> \<and> label_get l w = k} \<ge> 1"
      using \<V>_finite by (metis (no_types, lifting) One_nat_def Suc_leI card_gt_0_iff empty_iff
                          finite_subset mem_Collect_eq subsetI)
    thus ?thesis
      using assms(6) k(1) by (simp add: counts_correct_def)
  qed
  show "counts_correct l' cnt'"
    unfolding counts_correct_def
  proof(intro allI impI)
    fix j
    assume j: "j < 2 * card \<V>"
    have old: "count_get cnt j = card {w. w \<in> \<V> \<and> label_get l w = j}"
      using assms(6) j by (simp add: counts_correct_def)
    show "count_get cnt' j = card {w. w \<in> \<V> \<and> label_get l' w = j}"
      unfolding l'_get card_label_class_update[OF assms(3)] old[symmetric]
      using pos by (auto simp add: cnt'_get cnt1(2) k_def)
  qed
qed

subsubsection \<open>Computing New Labels\<close>

definition "scan_labels r endp l S = {label_get l (endp d) | d. d \<in> S \<and> emap_get r d > 0}"

definition "min_opt X = (if X = {} then None else Some (Min X))"

lemma scan_labels_empty[simp]: "scan_labels r endp l {} = {}"
  by (simp add: scan_labels_def)

lemma scan_labels_finite: "finite S \<Longrightarrow> finite (scan_labels r endp l S)"
proof-
  assume "finite S"
  moreover have "scan_labels r endp l S \<subseteq> (\<lambda> d. label_get l (endp d)) ` S"
    by (auto simp add: scan_labels_def)
  ultimately show ?thesis
    using finite_subset by blast
qed

lemma scan_labels_insert:
  "scan_labels r endp l (insert d S) =
   (if emap_get r d > 0 then insert (label_get l (endp d)) (scan_labels r endp l S)
    else scan_labels r endp l S)"
  by (auto simp add: scan_labels_def)

text \<open>One lemma for both scans: it is stated for an arbitrary iterator. Besides the minimum, the
      scan either keeps the initial pair or returns an edge \<open>d\<close> reaching the minimum, together
      with a state of the iterator in which \<open>d\<close> is current and all edges passed since the start
      of the scan are not residual or lead to larger labels.\<close>

lemma min_scan_props:
  assumes it: "indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move
                                    it_reset \<V>"
      and "it_invar C" "u \<in> \<V>" "finite (it_remaining C u)" "finite X"
          "map_option prod.fst mb = min_opt X"
          "min_scan has cur move r endp l u C mb = (C', mb')"
  shows "it_invar C'" "\<forall> w. it_abstract C' w = it_abstract C w"
        "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w \<and> it_remaining C' w = it_remaining C w"
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
    by (rule it)
  have main:
    "it_invar C' \<and> (\<forall> w. it_abstract C' w = it_abstract C w) \<and>
     (\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w \<and> it_remaining C' w = it_remaining C w) \<and>
     map_option prod.fst mb' = min_opt (X \<union> scan_labels r endp l (it_remaining C u)) \<and>
     (mb' = mb \<or>
      (\<exists> d C''. mb' = Some (label_get l (endp d), d) \<and>
         (case mb of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d) < k) \<and>
         it_invar C'' \<and> it_abstract C'' u = it_abstract C u \<and> has C'' u \<and> cur C'' u = d \<and>
         it_iterated C u \<subseteq> it_iterated C'' u \<and>
         (\<forall> d' \<in> it_iterated C'' u - it_iterated C u.
            0 < emap_get r d' \<longrightarrow> label_get l (endp d) < label_get l (endp d'))))"
    using assms(2-)
  proof(induction "card (it_remaining C u)" arbitrary: C mb X rule: less_induct)
    case less
    show ?case
    proof(cases "has C u")
      case False
      hence rem: "it_remaining C u = {}"
        using it.idx_has[OF less.prems(1,2)] by simp
      have "min_scan has cur move r endp l u C mb = (C, mb)"
        using False by (simp add: min_scan.simps)
      hence "C' = C" "mb' = mb"
        using less.prems(6) by auto
      thus ?thesis
        using less.prems(1,5) rem by simp
    next
      case True
      define d where "d = cur C u"
      define imp where
        "imp = (0 < emap_get r d \<and> (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> label_get l (endp d) < k'))"
      define mb1 where "mb1 = (if imp then Some (label_get l (endp d), d) else mb)"
      define X1 where
        "X1 = (if emap_get r d > 0 then insert (label_get l (endp d)) X else X)"
      have rem: "it_remaining C u \<noteq> {}"
        using it.idx_has[OF less.prems(1,2)] True by simp
      have dR: "d \<in> it_remaining C u"
        using it.idx_current[OF less.prems(1,2) rem] by (simp add: d_def)
      have step: "min_scan has cur move r endp l u C mb = min_scan has cur move r endp l u (move C u) mb1"
        using True unfolding mb1_def imp_def d_def by (subst min_scan.simps) (simp add: Let_def)
      have C1: "it_invar (move C u)" "it_remaining (move C u) u = it_remaining C u - {d}"
        using it.idx_move_invar[OF less.prems(1,2)]
              it.idx_move_remaining[OF less.prems(1,2) rem] by (simp_all add: d_def)
      have itm: "it_iterated (move C u) u = it_iterated C u \<union> {d}"
        using it.idx_move_iterated[OF less.prems(1,2) rem] by (simp add: d_def)
      have abs1: "it_abstract (move C u) u = it_abstract C u"
        using it.idx_move_abstract[OF less.prems(1,2) rem] .
      have card: "card (it_remaining (move C u) u) < card (it_remaining C u)"
        unfolding C1(2) using less.prems(3) dR by (rule card_Diff1_less)
      have m1: "map_option prod.fst mb1 = min_opt X1"
      proof(cases imp)
        case True
        hence p: "0 < emap_get r d"
                 "case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> label_get l (endp d) < k'"
          by (simp_all add: imp_def)
        show ?thesis
        proof(cases "mb = None")
          case True
          hence "X = {}"
            using less.prems(5) by (simp add: min_opt_def split: if_splits)
          thus ?thesis
            using \<open>imp\<close> p(1) by (simp add: mb1_def X1_def min_opt_def)
        next
          case False
          then obtain a where "mb = Some a"
            by auto
          moreover obtain k' e' where "a = (k', e')"
            by (cases a)
          ultimately have a: "mb = Some (k', e')"
            by simp
          hence X: "X \<noteq> {}" "k' = Min X"
            using less.prems(5) by (simp_all add: min_opt_def split: if_splits)
          have lt: "label_get l (endp d) < k'"
            using p(2) a by simp
          have mn: "Min (insert (label_get l (endp d)) X) = label_get l (endp d)"
            using Min_insert[OF less.prems(4) X(1)] lt X(2) by (simp add: min_def)
          thus ?thesis
            using \<open>imp\<close> p(1) by (simp add: mb1_def X1_def min_opt_def)
        qed
      next
        case False
        show ?thesis
        proof(cases "0 < emap_get r d")
          case True
          hence "mb \<noteq> None"
            using False by (cases mb) (auto simp add: imp_def)
          then obtain a where "mb = Some a"
            by auto
          moreover obtain k' e' where "a = (k', e')"
            by (cases a)
          ultimately have a: "mb = Some (k', e')"
            by simp
          have k': "k' \<le> label_get l (endp d)"
            using a True False by (simp add: imp_def)
          have X: "X \<noteq> {}" "k' = Min X"
            using less.prems(5) a by (simp_all add: min_opt_def split: if_splits)
          have mn: "Min (insert (label_get l (endp d)) X) = k'"
            using Min_insert[OF less.prems(4) X(1)] k' X(2) by (simp add: min_def)
          show ?thesis
            using False True a mn by (simp add: mb1_def X1_def min_opt_def)
        next
          case nr: False
          thus ?thesis
            using False less.prems(5) by (simp add: mb1_def X1_def)
        qed
      qed
      have fin: "finite (it_remaining (move C u) u)" "finite X1"
        using less.prems(3,4) by (simp_all add: C1(2) X1_def)
      have sc: "min_scan has cur move r endp l u (move C u) mb1 = (C', mb')"
        using step less.prems(6) by simp
      note IH = less.hyps[OF card C1(1) less.prems(2) fin m1 sc]
      have remC: "it_remaining C u = insert d (it_remaining (move C u) u)"
        using dR by (auto simp add: C1(2))
      hence lab: "X1 \<union> scan_labels r endp l (it_remaining (move C u) u) =
                  X \<union> scan_labels r endp l (it_remaining C u)"
        by (auto simp add: X1_def scan_labels_insert)
      have IHd: "mb' = mb1 \<or>
        (\<exists> d' C''. mb' = Some (label_get l (endp d'), d') \<and>
           (case mb1 of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d') < k) \<and>
           it_invar C'' \<and> it_abstract C'' u = it_abstract (move C u) u \<and> has C'' u \<and> cur C'' u = d' \<and>
           it_iterated (move C u) u \<subseteq> it_iterated C'' u \<and>
           (\<forall> d'' \<in> it_iterated C'' u - it_iterated (move C u) u.
              0 < emap_get r d'' \<longrightarrow> label_get l (endp d') < label_get l (endp d'')))"
        using IH by (elim conjE)
      have disj: "mb' = mb \<or>
        (\<exists> d' C''. mb' = Some (label_get l (endp d'), d') \<and>
           (case mb of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d') < k) \<and>
           it_invar C'' \<and> it_abstract C'' u = it_abstract C u \<and> has C'' u \<and> cur C'' u = d' \<and>
           it_iterated C u \<subseteq> it_iterated C'' u \<and>
           (\<forall> d'' \<in> it_iterated C'' u - it_iterated C u.
              0 < emap_get r d'' \<longrightarrow> label_get l (endp d') < label_get l (endp d'')))"
      proof(cases imp)
        case True
        hence p: "0 < emap_get r d"
                 "case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> label_get l (endp d) < k'"
          by (simp_all add: imp_def)
        from IHd show ?thesis
        proof
          assume "mb' = mb1"
          hence "mb' = Some (label_get l (endp d), d)"
            using True by (simp add: mb1_def)
          thus ?thesis
            using p(2) less.prems(1) \<open>has C u\<close>
            by (intro disjI2 exI[of _ d] exI[of _ C]) (simp add: d_def)
        next
          assume "\<exists> d' C''. mb' = Some (label_get l (endp d'), d') \<and>
            (case mb1 of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d') < k) \<and>
            it_invar C'' \<and> it_abstract C'' u = it_abstract (move C u) u \<and> has C'' u \<and> cur C'' u = d' \<and>
            it_iterated (move C u) u \<subseteq> it_iterated C'' u \<and>
            (\<forall> d'' \<in> it_iterated C'' u - it_iterated (move C u) u.
               0 < emap_get r d'' \<longrightarrow> label_get l (endp d') < label_get l (endp d''))"
          then obtain d' C'' where h: "mb' = Some (label_get l (endp d'), d')"
            "case mb1 of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d') < k"
            "it_invar C''" "it_abstract C'' u = it_abstract (move C u) u" "has C'' u" "cur C'' u = d'"
            "it_iterated (move C u) u \<subseteq> it_iterated C'' u"
            "\<forall> d'' \<in> it_iterated C'' u - it_iterated (move C u) u.
               0 < emap_get r d'' \<longrightarrow> label_get l (endp d') < label_get l (endp d'')"
            by blast
          have lt: "label_get l (endp d') < label_get l (endp d)"
            using h(2) True by (simp add: mb1_def)
          have "case mb of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d') < k"
            using p(2) lt by (auto split: option.splits)
          moreover have "\<forall> d'' \<in> it_iterated C'' u - it_iterated C u.
                           0 < emap_get r d'' \<longrightarrow> label_get l (endp d') < label_get l (endp d'')"
            using h(8) lt itm by auto
          moreover have "it_iterated C u \<subseteq> it_iterated C'' u"
            using h(7) itm by auto
          ultimately show ?thesis
            using h(1,3-6) abs1 by (intro disjI2 exI[of _ d'] exI[of _ C'']) simp
        qed
      next
        case False
        have mb1: "mb1 = mb"
          using False by (simp add: mb1_def)
        from IHd show ?thesis
        proof
          assume "mb' = mb1"
          thus ?thesis
            using mb1 by simp
        next
          assume "\<exists> d' C''. mb' = Some (label_get l (endp d'), d') \<and>
            (case mb1 of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d') < k) \<and>
            it_invar C'' \<and> it_abstract C'' u = it_abstract (move C u) u \<and> has C'' u \<and> cur C'' u = d' \<and>
            it_iterated (move C u) u \<subseteq> it_iterated C'' u \<and>
            (\<forall> d'' \<in> it_iterated C'' u - it_iterated (move C u) u.
               0 < emap_get r d'' \<longrightarrow> label_get l (endp d') < label_get l (endp d''))"
          then obtain d' C'' where h: "mb' = Some (label_get l (endp d'), d')"
            "case mb1 of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d') < k"
            "it_invar C''" "it_abstract C'' u = it_abstract (move C u) u" "has C'' u" "cur C'' u = d'"
            "it_iterated (move C u) u \<subseteq> it_iterated C'' u"
            "\<forall> d'' \<in> it_iterated C'' u - it_iterated (move C u) u.
               0 < emap_get r d'' \<longrightarrow> label_get l (endp d') < label_get l (endp d'')"
            by blast
          have "\<forall> d'' \<in> it_iterated C'' u - it_iterated C u.
                  0 < emap_get r d'' \<longrightarrow> label_get l (endp d') < label_get l (endp d'')"
          proof(intro ballI impI)
            fix d''
            assume d'': "d'' \<in> it_iterated C'' u - it_iterated C u" "0 < emap_get r d''"
            show "label_get l (endp d') < label_get l (endp d'')"
            proof(cases "d'' = d")
              case True
              hence "mb \<noteq> None"
                using False d''(2) by (cases mb) (auto simp add: imp_def)
              then obtain a where "mb = Some a"
                by auto
              moreover obtain k' e' where "a = (k', e')"
                by (cases a)
              ultimately have a: "mb = Some (k', e')"
                by simp
              have "k' \<le> label_get l (endp d)"
                using False d''(2) True a by (simp add: imp_def)
              moreover have "label_get l (endp d') < k'"
                using h(2) a mb1 by simp
              ultimately show ?thesis
                using True by simp
            next
              case False
              thus ?thesis
                using d'' h(8) itm by auto
            qed
          qed
          moreover have "it_iterated C u \<subseteq> it_iterated C'' u"
            using h(7) itm by auto
          ultimately show ?thesis
            using h(1-6) mb1 abs1 by (intro disjI2 exI[of _ d'] exI[of _ C'']) simp
        qed
      qed
      have "it_invar C' \<and> (\<forall> w. it_abstract C' w = it_abstract C w) \<and>
            (\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w \<and> it_remaining C' w = it_remaining C w) \<and>
            map_option prod.fst mb' = min_opt (X \<union> scan_labels r endp l (it_remaining C u))"
        using IH lab it.idx_move_abstract[OF less.prems(1,2) rem]
              it.idx_move_iterated_other[OF less.prems(1,2) rem]
              it.idx_move_remaining_other[OF less.prems(1,2) rem]
        by simp
      with disj show ?thesis
        by (elim conjE) (intro conjI)
    qed
  qed
  show "it_invar C'"
    using main by (elim conjE)
  show "\<forall> w. it_abstract C' w = it_abstract C w"
    using main by (elim conjE)
  show "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w \<and> it_remaining C' w = it_remaining C w"
    using main by (elim conjE)
  show "map_option prod.fst mb' = min_opt (X \<union> scan_labels r endp l (it_remaining C u))"
    using main by (elim conjE)
  show "mb' = mb \<or>
         (\<exists> d C''. mb' = Some (label_get l (endp d), d) \<and>
            (case mb of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get l (endp d) < k) \<and>
            it_invar C'' \<and> it_abstract C'' u = it_abstract C u \<and> has C'' u \<and> cur C'' u = d \<and>
            it_iterated C u \<subseteq> it_iterated C'' u \<and>
            (\<forall> d' \<in> it_iterated C'' u - it_iterated C u.
               0 < emap_get r d' \<longrightarrow> label_get l (endp d) < label_get l (endp d')))"
    using main by (elim conjE)
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
        "\<And> u e. \<lbrakk>u \<in> \<V>; e \<in> iterated_res st u\<rbrakk> \<Longrightarrow> \<not> admissible (flow_abs st) (labels_abs st) e"
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
          "\<And> u e. \<lbrakk>u \<in> \<V>; e \<in> iterated_res st u\<rbrakk> \<Longrightarrow> \<not> admissible (flow_abs st) (labels_abs st) e"
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
  have eqs: "flow_abs (st\<lparr>pr_ctx := c\<rparr>) = flow_abs st" "labels_abs (st\<lparr>pr_ctx := c\<rparr>) = labels_abs st"
            "current_res (st\<lparr>pr_ctx := c\<rparr>) = current_res st"
    by (simp_all add: current_res_def fun_eq_iff)
  show ?thesis
    unfolding good_op_def by (simp only: eqs)
qed


text \<open>The residual edges leaving a vertex are exactly the forward copies of its outgoing and
      the backward copies of its ingoing edges, so the two scans compute the new label.\<close>

lemma scan_labels_relabel_labels:
  assumes "res_correct fw bw"
  shows "scan_labels fw snd l (\<delta>\<^sup>+ u) \<union> scan_labels bw fst l (\<delta>\<^sup>- u) =
         relabel_labels (emap_get bw) (label_get l) u"
proof-
  have Fpos: "rcap (emap_get bw) (F d) > 0 \<longleftrightarrow> emap_get fw d > 0" if "d \<in> \<E>" for d
    using rcap_fwd[OF assms that] by simp
  have Bpos: "rcap (emap_get bw) (B d) > 0 \<longleftrightarrow> emap_get bw d > 0" for d
    by simp
  show ?thesis
  proof(intro equalityI subsetI)
    fix x
    assume "x \<in> scan_labels fw snd l (\<delta>\<^sup>+ u) \<union> scan_labels bw fst l (\<delta>\<^sup>- u)"
    then consider (fwd) d where "d \<in> \<E>" "fst d = u" "emap_get fw d > 0" "x = label_get l (snd d)"
                | (bwd) d where "d \<in> \<E>" "snd d = u" "emap_get bw d > 0" "x = label_get l (fst d)"
      by (auto simp add: scan_labels_def delta_plus_def delta_minus_def)
    thus "x \<in> relabel_labels (emap_get bw) (label_get l) u"
    proof cases
      case fwd
      hence "F d \<in> \<EE>" "fstv (F d) = u" "rcap (emap_get bw) (F d) > 0"
            "x = label_get l (sndv (F d))"
        using Fpos[OF fwd(1)] by (auto simp add: \<EE>_def)
      thus ?thesis
        unfolding relabel_labels_def by blast
    next
      case bwd
      hence "B d \<in> \<EE>" "fstv (B d) = u" "rcap (emap_get bw) (B d) > 0"
            "x = label_get l (sndv (B d))"
        using Bpos by (auto simp add: \<EE>_def)
      thus ?thesis
        unfolding relabel_labels_def by blast
    qed
  next
    fix x
    assume "x \<in> relabel_labels (emap_get bw) (label_get l) u"
    then obtain e where e: "e \<in> \<EE>" "fstv e = u" "rcap (emap_get bw) e > 0"
                           "x = label_get l (sndv e)"
      unfolding relabel_labels_def by blast
    have d: "oedge e \<in> \<E>"
      using e(1) o_edge_res by blast
    show "x \<in> scan_labels fw snd l (\<delta>\<^sup>+ u) \<union> scan_labels bw fst l (\<delta>\<^sup>- u)"
    proof(cases e)
      case (F d')
      thus ?thesis
        using e d Fpos[of d'] by (auto simp add: scan_labels_def delta_plus_def)
    next
      case (B d')
      thus ?thesis
        using e d by (auto simp add: scan_labels_def delta_minus_def)
    qed
  qed
qed

lemma new_label_props:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
          "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = (og', ig', k')"
  shows "out_invar og'" "in_invar ig'"
        "\<And> w. out_abstract og' w = out_abstract (pr_out st) w"
        "\<And> w. in_abstract ig' w = in_abstract (pr_in st) w"
        "\<And> d. \<lbrakk>d \<in> out_iterated og' u; 0 < emap_get (pr_fwd st) d\<rbrakk> \<Longrightarrow> k' \<le> labels_abs st (snd d)"
        "\<And> d. \<lbrakk>d \<in> in_iterated ig' u; 0 < emap_get (pr_bwd st) d\<rbrakk> \<Longrightarrow> k' \<le> labels_abs st (fst d)"
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
  note inv = invar_stateD[OF assms(1)]
  have act: "active_vertex s t (flow_abs st) u"
    using assms(2) by (auto elim: relabel_precondE)
  hence u: "u \<in> \<V>"
    by (auto elim: active_vertexE)
  define og0 where "og0 = out_reset (pr_out st) u"
  define ig0 where "ig0 = in_reset (pr_in st) u"
  define S1 where "S1 = scan_labels (pr_fwd st) snd (pr_labels st) (\<delta>\<^sup>+ u)"
  define S2 where "S2 = scan_labels (pr_bwd st) fst (pr_labels st) (\<delta>\<^sup>- u)"
  obtain og1 mb1 where
    scan1: "min_scan out_has out_current out_move (pr_fwd st) snd (pr_labels st) u og0 None = (og1, mb1)"
    by (cases "min_scan out_has out_current out_move (pr_fwd st) snd (pr_labels st) u og0 None") auto
  obtain ig1 mb2 where
    scan2: "min_scan in_has in_current in_move (pr_bwd st) fst (pr_labels st) u ig0 mb1 = (ig1, mb2)"
    by (cases "min_scan in_has in_current in_move (pr_bwd st) fst (pr_labels st) u ig0 mb1") auto
  have og0: "out_invar og0" "out_remaining og0 u = \<delta>\<^sup>+ u" "out_iterated og0 u = {}"
            "\<And> w. out_abstract og0 w = out_abstract (pr_out st) w"
            "\<And> w. w \<noteq> u \<Longrightarrow> out_iterated og0 w = out_iterated (pr_out st) w"
    using outg.idx_reset_invar[OF inv(5) u] outg.idx_reset_remaining[OF inv(5) u] inv(11)[OF u]
          outg.idx_reset_iterated[OF inv(5) u] outg.idx_reset_abstract[OF inv(5) u]
          outg.idx_reset_iterated_other[OF inv(5) u]
    by (simp_all add: og0_def)
  have ig0: "in_invar ig0" "in_remaining ig0 u = \<delta>\<^sup>- u" "in_iterated ig0 u = {}"
            "\<And> w. in_abstract ig0 w = in_abstract (pr_in st) w"
            "\<And> w. w \<noteq> u \<Longrightarrow> in_iterated ig0 w = in_iterated (pr_in st) w"
    using ing.idx_reset_invar[OF inv(15) u] ing.idx_reset_remaining[OF inv(15) u] inv(16)[OF u]
          ing.idx_reset_iterated[OF inv(15) u] ing.idx_reset_abstract[OF inv(15) u]
          ing.idx_reset_iterated_other[OF inv(15) u]
    by (simp_all add: ig0_def)
  have fin1: "finite (out_remaining og0 u)" "finite S1"
    using og0(2) finite_delta(1) scan_labels_finite[OF finite_delta(1)] by (simp_all add: S1_def)
  have fin2: "finite (in_remaining ig0 u)"
    using ig0(2) finite_delta(2) by simp
  have e0: "map_option prod.fst None = min_opt {}"
    by (simp add: min_opt_def)
  note sc1 = min_scan_props[OF outg.indexed_iterable_set_axioms og0(1) u fin1(1) finite.emptyI e0 scan1]
  have m1: "map_option prod.fst mb1 = min_opt S1"
    using sc1(4) og0(2) by (simp add: S1_def)
  note sc2 = min_scan_props[OF ing.indexed_iterable_set_axioms ig0(1) u fin2 fin1(2) m1 scan2]
  have m2: "map_option prod.fst mb2 = min_opt (S1 \<union> S2)"
    using sc2(4) ig0(2) by (simp add: S2_def)
  define M where "M = Min (relabel_labels (flow_abs st) (labels_abs st) u)"
  have ne: "S1 \<union> S2 \<noteq> {}" "M = Min (S1 \<union> S2)"
    using relabel_labels_nonempty[OF net_assms inv(8) act] scan_labels_relabel_labels[OF inv(14)]
    by (simp_all add: S1_def S2_def M_def)
  have mo: "map_option prod.fst mb2 = Some M"
    using m2 unfolding min_opt_def if_not_P[OF ne(1)] ne(2) .
  define d where "d = prod.snd (the mb2)"
  have mb2: "mb2 = Some (M, d)"
    using mo by (cases mb2) (simp_all add: d_def prod_eq_iff)
  define cnd where "cnd = (case mb1 of None \<Rightarrow> True | Some (m1, _) \<Rightarrow> M < m1)"
  have res: "(og', ig', k') = (if cnd then (og1, in_reset_to ig1 u d, M + 1)
                               else (out_reset_to og1 u d, in_reset ig1 u, M + 1))"
    using scan1 scan2 mb2 assms(3) by (simp add: new_label_def og0_def ig0_def cnd_def)
  have k'M: "k' = M + 1"
    using res by (simp split: if_splits)
  show "k' = relabel_effect (flow_abs st) (labels_abs st) u u"
    by (simp add: k'M relabel_effect_def M_def)
  have og1: "out_invar og1" "\<And> w. out_abstract og1 w = out_abstract (pr_out st) w"
            "\<And> w. w \<noteq> u \<Longrightarrow> out_iterated og1 w = out_iterated (pr_out st) w"
    using sc1(1-3) og0(4,5) by auto
  have ig1: "in_invar ig1" "\<And> w. in_abstract ig1 w = in_abstract (pr_in st) w"
            "\<And> w. w \<noteq> u \<Longrightarrow> in_iterated ig1 w = in_iterated (pr_in st) w"
    using sc2(1-3) ig0(4,5) by auto
  have main:
    "out_invar og' \<and> in_invar ig' \<and> (\<forall> w. out_abstract og' w = out_abstract (pr_out st) w) \<and>
     (\<forall> w. in_abstract ig' w = in_abstract (pr_in st) w) \<and>
     (\<forall> d'. d' \<in> out_iterated og' u \<longrightarrow> 0 < emap_get (pr_fwd st) d' \<longrightarrow> k' \<le> labels_abs st (snd d')) \<and>
     (\<forall> d'. d' \<in> in_iterated ig' u \<longrightarrow> 0 < emap_get (pr_bwd st) d' \<longrightarrow> k' \<le> labels_abs st (fst d')) \<and>
     (\<forall> w. w \<noteq> u \<longrightarrow> out_iterated og' w = out_iterated (pr_out st) w) \<and>
     (\<forall> w. w \<noteq> u \<longrightarrow> in_iterated ig' w = in_iterated (pr_in st) w) \<and>
     (if cnd then d \<in> in_abstract ig1 u else d \<in> out_abstract og1 u)"
  proof(cases cnd)
    case True
    have res': "og' = og1" "ig' = in_reset_to ig1 u d"
      using res True by simp_all
    have "mb2 \<noteq> mb1"
      using True mb2 by (auto simp add: cnd_def)
    then obtain d2 C2 where c2: "mb2 = Some (label_get (pr_labels st) (fst d2), d2)"
      "in_invar C2" "in_abstract C2 u = in_abstract ig0 u" "in_has C2 u" "in_current C2 u = d2"
      "\<forall> d' \<in> in_iterated C2 u - in_iterated ig0 u.
         0 < emap_get (pr_bwd st) d' \<longrightarrow> label_get (pr_labels st) (fst d2) < label_get (pr_labels st) (fst d')"
      using sc2(5) by (elim disjE exE conjE) (simp, (rule that; assumption))
    have d2: "d2 = d" "M = label_get (pr_labels st) (fst d2)"
      using c2(1) mb2 by simp_all
    have abs2: "in_abstract C2 u = in_abstract ig1 u"
      using c2(3) ig0(4) ig1(2) by simp
    have dA: "d \<in> in_abstract ig1 u"
    proof-
      have "in_remaining C2 u \<noteq> {}"
        using ing.idx_has[OF c2(2) u] c2(4) by simp
      hence "d \<in> in_remaining C2 u"
        using ing.idx_current[OF c2(2) u] c2(5) d2(1) by simp
      thus ?thesis
        using ing.idx_partition_union[OF c2(2) u] abs2 by auto
    qed
    have it2: "in_iterated ig' u = in_iterated C2 u"
      using inr.idx_reset_to_like[OF ig1(1) u c2(2) abs2 c2(4)] c2(5) d2(1) by (simp add: res')
    show ?thesis
    proof(intro conjI)
      show "out_invar og'"
        using og1(1) by (simp add: res')
      show "in_invar ig'"
        using inr.idx_reset_to_invar[OF ig1(1) u dA] by (simp add: res')
      show "\<forall> w. out_abstract og' w = out_abstract (pr_out st) w"
        using og1(2) by (simp add: res')
      show "\<forall> w. in_abstract ig' w = in_abstract (pr_in st) w"
        using inr.idx_reset_to_abstract[OF ig1(1) u dA] ig1(2) by (simp add: res')
      show "\<forall> d'. d' \<in> out_iterated og' u \<longrightarrow> 0 < emap_get (pr_fwd st) d' \<longrightarrow>
                  k' \<le> labels_abs st (snd d')"
      proof(intro allI impI)
        fix d'
        assume d': "d' \<in> out_iterated og' u" "0 < emap_get (pr_fwd st) d'"
        have "d' \<in> \<delta>\<^sup>+ u"
          using outg.idx_partition_union[OF og1(1) u] og1(2)[of u] inv(11)[OF u] d'(1)
          by (auto simp add: res')
        hence inS: "labels_abs st (snd d') \<in> S1"
          using d'(2) by (auto simp add: S1_def scan_labels_def)
        hence S1: "S1 \<noteq> {}" "Min S1 \<le> labels_abs st (snd d')"
          using fin1(2) by auto
        define e1 where "e1 = prod.snd (the mb1)"
        have "mb1 = Some (Min S1, e1)"
          using m1 S1(1) by (cases mb1) (simp_all add: min_opt_def prod_eq_iff e1_def)
        hence "M < Min S1"
          using True by (simp add: cnd_def)
        thus "k' \<le> labels_abs st (snd d')"
          using S1(2) k'M by simp
      qed
      show "\<forall> d'. d' \<in> in_iterated ig' u \<longrightarrow> 0 < emap_get (pr_bwd st) d' \<longrightarrow>
                  k' \<le> labels_abs st (fst d')"
        using c2(6) it2 ig0(3) d2(2) k'M by auto
      show "\<forall> w. w \<noteq> u \<longrightarrow> out_iterated og' w = out_iterated (pr_out st) w"
        using og1(3) by (simp add: res')
      show "\<forall> w. w \<noteq> u \<longrightarrow> in_iterated ig' w = in_iterated (pr_in st) w"
        using inr.idx_reset_to_iterated_other[OF ig1(1) u dA] ig1(3) by (simp add: res')
      show "if cnd then d \<in> in_abstract ig1 u else d \<in> out_abstract og1 u"
        using dA True by simp
    qed
  next
    case False
    have res': "og' = out_reset_to og1 u d" "ig' = in_reset ig1 u"
      using res False by simp_all
    have "mb2 = mb1"
    proof(rule ccontr)
      assume "mb2 \<noteq> mb1"
      then obtain d2 where c2: "mb2 = Some (label_get (pr_labels st) (fst d2), d2)"
        "case mb1 of None \<Rightarrow> True | Some (k, _) \<Rightarrow> label_get (pr_labels st) (fst d2) < k"
        using sc2(5) by (elim disjE exE conjE) (simp, (rule that; assumption))
      have "M = label_get (pr_labels st) (fst d2)"
        using c2(1) unfolding mb2 by simp
      hence "cnd"
        using c2(2) by (cases mb1) (auto simp add: cnd_def)
      thus False
        using False by simp
    qed
    hence mb1: "mb1 = Some (M, d)"
      using mb2 by simp
    then obtain d1 C1 where c1: "mb1 = Some (label_get (pr_labels st) (snd d1), d1)"
      "out_invar C1" "out_abstract C1 u = out_abstract og0 u" "out_has C1 u" "out_current C1 u = d1"
      "\<forall> d' \<in> out_iterated C1 u - out_iterated og0 u.
         0 < emap_get (pr_fwd st) d' \<longrightarrow> label_get (pr_labels st) (snd d1) < label_get (pr_labels st) (snd d')"
      using sc1(5) mb1 by (elim disjE exE conjE) (simp, (rule that; assumption))
    have d1: "d1 = d" "M = label_get (pr_labels st) (snd d1)"
      using c1(1) mb1 by simp_all
    have abs1: "out_abstract C1 u = out_abstract og1 u"
      using c1(3) og0(4) og1(2) by simp
    have dA: "d \<in> out_abstract og1 u"
    proof-
      have "out_remaining C1 u \<noteq> {}"
        using outg.idx_has[OF c1(2) u] c1(4) by simp
      hence "d \<in> out_remaining C1 u"
        using outg.idx_current[OF c1(2) u] c1(5) d1(1) by simp
      thus ?thesis
        using outg.idx_partition_union[OF c1(2) u] abs1 by auto
    qed
    have it1: "out_iterated og' u = out_iterated C1 u"
      using outr.idx_reset_to_like[OF og1(1) u c1(2) abs1 c1(4)] c1(5) d1(1) by (simp add: res')
    show ?thesis
    proof(intro conjI)
      show "out_invar og'"
        using outr.idx_reset_to_invar[OF og1(1) u dA] by (simp add: res')
      show "in_invar ig'"
        using ing.idx_reset_invar[OF ig1(1) u] by (simp add: res')
      show "\<forall> w. out_abstract og' w = out_abstract (pr_out st) w"
        using outr.idx_reset_to_abstract[OF og1(1) u dA] og1(2) by (simp add: res')
      show "\<forall> w. in_abstract ig' w = in_abstract (pr_in st) w"
        using ing.idx_reset_abstract[OF ig1(1) u] ig1(2) by (simp add: res')
      show "\<forall> d'. d' \<in> out_iterated og' u \<longrightarrow> 0 < emap_get (pr_fwd st) d' \<longrightarrow>
                  k' \<le> labels_abs st (snd d')"
        using c1(6) it1 og0(3) d1(2) k'M by auto
      show "\<forall> d'. d' \<in> in_iterated ig' u \<longrightarrow> 0 < emap_get (pr_bwd st) d' \<longrightarrow>
                  k' \<le> labels_abs st (fst d')"
        using ing.idx_reset_iterated[OF ig1(1) u] by (simp add: res')
      show "\<forall> w. w \<noteq> u \<longrightarrow> out_iterated og' w = out_iterated (pr_out st) w"
        using outr.idx_reset_to_iterated_other[OF og1(1) u dA] og1(3) by (simp add: res')
      show "\<forall> w. w \<noteq> u \<longrightarrow> in_iterated ig' w = in_iterated (pr_in st) w"
        using ing.idx_reset_iterated_other[OF ig1(1) u] ig1(3) by (simp add: res')
      show "if cnd then d \<in> in_abstract ig1 u else d \<in> out_abstract og1 u"
        using dA False by simp
    qed
  qed
  show "out_invar og'" "in_invar ig'"
    using main by simp_all
  show "\<And> w. out_abstract og' w = out_abstract (pr_out st) w"
       "\<And> w. in_abstract ig' w = in_abstract (pr_in st) w"
    using main by simp_all
  show "\<And> d. \<lbrakk>d \<in> out_iterated og' u; 0 < emap_get (pr_fwd st) d\<rbrakk> \<Longrightarrow> k' \<le> labels_abs st (snd d)"
       "\<And> d. \<lbrakk>d \<in> in_iterated ig' u; 0 < emap_get (pr_bwd st) d\<rbrakk> \<Longrightarrow> k' \<le> labels_abs st (fst d)"
    using main by simp_all
  show "\<And> w. w \<noteq> u \<Longrightarrow> out_iterated og' w = out_iterated (pr_out st) w"
       "\<And> w. w \<noteq> u \<Longrightarrow> in_iterated ig' w = in_iterated (pr_in st) w"
    using main by simp_all
  show "\<exists> og1 mb1 ig1 M d.
          min_scan out_has out_current out_move (pr_fwd st) snd (pr_labels st) u
            (out_reset (pr_out st) u) None = (og1, mb1) \<and>
          min_scan in_has in_current in_move (pr_bwd st) fst (pr_labels st) u
            (in_reset (pr_in st) u) mb1 = (ig1, Some (M, d)) \<and>
          (if (case mb1 of None \<Rightarrow> True | Some (m1, _) \<Rightarrow> M < m1)
           then d \<in> in_abstract ig1 u else d \<in> out_abstract og1 u)"
    using scan1 scan2 main[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                           THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
    by (intro exI conjI) (simp_all add: og0_def ig0_def mb2 cnd_def)
qed

subsubsection \<open>Invariants are Preserved by the Operations\<close>

lemma iterated_res_props:
  assumes "invar_state st" "u \<in> \<V>" "e \<in> iterated_res st u"
  shows "fstv e = u" "e \<in> \<EE>"
proof-
  note inv = invar_stateD[OF assms(1)]
  have out: "out_iterated (pr_out st) u \<subseteq> \<delta>\<^sup>+ u"
    using outg.idx_partition_union[OF inv(5) assms(2)] inv(11)[OF assms(2)] by blast
  have inn: "in_iterated (pr_in st) u \<subseteq> \<delta>\<^sup>- u"
    using ing.idx_partition_union[OF inv(15) assms(2)] inv(16)[OF assms(2)] by blast
  show "fstv e = u" "e \<in> \<EE>"
    using assms(3) out inn
    by (auto simp add: iterated_res_def delta_plus_def delta_minus_def \<EE>_def)
qed

text \<open>If labels only increase, flows do not change, and every vertex whose label changed has
      its iterators reset, then no passed residual edge is admissible.\<close>

lemma iterated_invar_label_increase:
  assumes "invar_state st" "flow_abs st' = flow_abs st"
          "\<And> x. x \<in> \<V> \<Longrightarrow> labels_abs st x \<le> labels_abs st' x"
          "u \<in> \<V>" "labels_abs st' u = labels_abs st u" "e \<in> iterated_res st u"
  shows "\<not> admissible (flow_abs st') (labels_abs st') e"
proof
  assume adm: "admissible (flow_abs st') (labels_abs st') e"
  note inv = invar_stateD[OF assms(1)]
  note same = assms(5,6)
  have "fstv e = u"
    using iterated_res_props[OF assms(1,4) same(2)] by simp
  hence "admissible (flow_abs st) (labels_abs st) e"
    using admissible_increased_labels[OF net_assms inv(9) assms(3)] same(1) adm
    by (simp add: assms(2))
  thus False
    using inv(12)[OF assms(4) same(2)] by simp
qed

text \<open>Before and after relabelling, the label of the vertex is below \<open>2 |V|\<close>.\<close>

lemma relabel_bounds:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "label_get (pr_labels st) u < 2 * card \<V>"
        "relabel_effect (flow_abs st) (labels_abs st) u u < 2 * card \<V>"
proof-
  note inv = invar_stateD[OF assms(1)]
  have u: "u \<in> \<V>"
    using assms(2) by (auto elim!: relabel_precondE active_vertexE)
  have hb: "height_bounded (relabel_effect (flow_abs st) (labels_abs st) u)"
    using relabel_preserves_height_bounded[OF net_assms inv(8,9) assms(2) inv(10)] .
  show "label_get (pr_labels st) u < 2 * card \<V>"
       "relabel_effect (flow_abs st) (labels_abs st) u u < 2 * card \<V>"
    using height_boundedD[OF inv(10) u] height_boundedD[OF hb u] cardV_0 by auto
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
  note inv = invar_stateD[OF assms(1)]
  have u: "u \<in> \<V>"
    using assms(2) by (auto elim!: relabel_precondE active_vertexE)
  obtain og' ig' k' where
    nl: "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = (og', ig', k')"
    by (cases "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u") auto
  obtain l' cnt' where cl: "change_label (pr_labels st) (pr_counts st) u k' = (l', cnt')"
    by (cases "change_label (pr_labels st) (pr_counts st) u k'") auto
  note nlp = new_label_props[OF assms nl]
  have st': "relabel_impl u st = st\<lparr>pr_labels := l', pr_counts := cnt', pr_out := og', pr_in := ig'\<rparr>"
    using nl cl by (simp add: relabel_impl_def)
  have hb: "height_bounded (relabel_effect (flow_abs st) (labels_abs st) u)"
    using relabel_preserves_height_bounded[OF net_assms inv(8,9) assms(2) inv(10)] .
  have bounds: "label_get (pr_labels st) u < 2 * card \<V>" "k' < 2 * card \<V>"
    using relabel_bounds[OF assms] nlp(9) by simp_all
  note clp = change_label_props[OF inv(3,4) u bounds inv(7) cl]
  have labels: "label_get l' = relabel_effect (flow_abs st) (labels_abs st) u"
    using clp(3) nlp(9) by (simp add: relabel_effect_def)
  show "labels_abs (relabel_impl u st) = relabel_effect (flow_abs st) (labels_abs st) u"
    by (simp add: st' labels)
  show "pr_fwd (relabel_impl u st) = pr_fwd st \<and> pr_bwd (relabel_impl u st) = pr_bwd st"
       "pr_excess (relabel_impl u st) = pr_excess st" "pr_ctx (relabel_impl u st) = pr_ctx st"
    by (simp_all add: st')
  show it_w: "\<And> w. w \<noteq> u \<Longrightarrow> iterated_res (relabel_impl u st) w = iterated_res st w"
    using nlp(7,8) by (simp add: st' iterated_res_def)
  have nadm_u: "\<not> admissible (flow_abs (relabel_impl u st)) (labels_abs (relabel_impl u st)) e"
    if e: "e \<in> iterated_res (relabel_impl u st) u" for e
  proof
    assume adm: "admissible (flow_abs (relabel_impl u st)) (labels_abs (relabel_impl u st)) e"
    define l1 where "l1 = relabel_effect (flow_abs st) (labels_abs st) u"
    have ad: "0 < rcap (flow_abs st) e" "l1 (fstv e) = l1 (sndv e) + 1"
      using adm by (auto elim!: admissibleE simp add: st' labels l1_def)
    have l1u: "l1 u = k'" and l1w: "\<And> w. w \<noteq> u \<Longrightarrow> l1 w = labels_abs st w"
      using nlp(9) by (simp_all add: l1_def relabel_effect_def)
    have key: "False" if "l1 u = l1 w + 1" "k' \<le> labels_abs st w" for w
    proof(cases "w = u")
      case True
      thus False
        using that(1) by simp
    next
      case False
      thus False
        using that l1u l1w[OF False] by simp
    qed
    from e consider (f) d where "d \<in> out_iterated og' u" "e = F d"
                  | (b) d where "d \<in> in_iterated ig' u" "e = B d"
      by (auto simp add: st' iterated_res_def)
    thus False
    proof cases
      case f
      have "d \<in> \<delta>\<^sup>+ u"
        using outg.idx_partition_union[OF nlp(1) u] nlp(3)[of u] inv(11)[OF u] f(1) by blast
      hence d: "d \<in> \<E>" "fst d = u"
        by (simp_all add: delta_plus_def)
      have "0 < emap_get (pr_fwd st) d"
        using ad(1) rcap_fwd[OF inv(14) d(1)] f(2) by simp
      thus False
        using key[of "snd d"] nlp(5)[OF f(1)] ad(2) d(2) f(2) by simp
    next
      case b
      have "d \<in> \<delta>\<^sup>- u"
        using ing.idx_partition_union[OF nlp(2) u] nlp(4)[of u] inv(16)[OF u] b(1) by blast
      hence d: "d \<in> \<E>" "snd d = u"
        by (simp_all add: delta_minus_def)
      have "0 < emap_get (pr_bwd st) d"
        using ad(1) b(2) by simp
      thus False
        using key[of "fst d"] nlp(6)[OF b(1)] ad(2) d(2) b(2) by simp
    qed
  qed
  show "invar_state (relabel_impl u st)"
  proof(rule invar_stateI)
    show "valid_labelling s t (flow_abs (relabel_impl u st)) (labels_abs (relabel_impl u st))"
      using relabel_preserves_valid[OF net_assms inv(8,9) assms(2)] by (simp add: st' labels)
    show "height_bounded (labels_abs (relabel_impl u st))"
      using hb by (simp add: st' labels)
    fix w e
    assume w: "w \<in> \<V>" and e: "e \<in> iterated_res (relabel_impl u st) w"
    show "\<not> admissible (flow_abs (relabel_impl u st)) (labels_abs (relabel_impl u st)) e"
    proof(cases "w = u")
      case True
      thus ?thesis
        using nadm_u e by simp
    next
      case False
      have "e \<in> iterated_res st w"
        using e it_w[OF False] by simp
      moreover have "labels_abs (relabel_impl u st) w = labels_abs st w"
        using False by (simp add: st' labels relabel_effect_def)
      ultimately show ?thesis
        using relabel_mono[OF net_assms inv(8,9) assms(2)]
        by (intro iterated_invar_label_increase[OF assms(1) _ _ w]) (simp_all add: st' labels)
    qed
  qed (use inv clp nlp in \<open>simp_all add: st'\<close>)
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
  case Nil
  thus ?case by simp
next
  case (Cons v vs)
  have v: "v \<in> \<V>" "v \<notin> set vs"
    using Cons.prems(1,2) by auto
  have n: "num_verts + 1 < 2 * card \<V>"
    using card_V_ge_2[OF net_assms] by (simp add: num_verts)
  show ?case
  proof(cases "k < label_get l v \<and> label_get l v < num_verts")
    case True
    obtain l1 cnt1 where cl: "change_label l cnt v (num_verts + 1) = (l1, cnt1)"
      by (cases "change_label l cnt v (num_verts + 1)") auto
    define og1 where "og1 = out_reset og v"
    define ig1 where "ig1 = in_reset ig v"
    have step: "gap_step k (l, cnt, og, ig) v = (l1, cnt1, og1, ig1)"
      using True cl by (simp add: gap_step_def og1_def ig1_def Let_def)
    note clp = change_label_props[OF Cons.prems(3,4) v(1) _ n Cons.prems(7) cl]
    have l1: "label_invar l1" "count_invar cnt1" "label_get l1 = (label_get l)(v := num_verts + 1)"
             "counts_correct l1 cnt1"
      using clp Cons.prems(8) v(1) by auto
    have og1: "out_invar og1" "\<And> w. out_abstract og1 w = out_abstract og w" "out_iterated og1 v = {}"
              "\<And> w. w \<noteq> v \<Longrightarrow> out_iterated og1 w = out_iterated og w"
      using outg.idx_reset_invar[OF Cons.prems(5) v(1)]
            outg.idx_reset_abstract[OF Cons.prems(5) v(1)]
            outg.idx_reset_iterated[OF Cons.prems(5) v(1)]
            outg.idx_reset_iterated_other[OF Cons.prems(5) v(1)]
      by (simp_all add: og1_def)
    have ig1: "in_invar ig1" "\<And> w. in_abstract ig1 w = in_abstract ig w" "in_iterated ig1 v = {}"
              "\<And> w. w \<noteq> v \<Longrightarrow> in_iterated ig1 w = in_iterated ig w"
      using ing.idx_reset_invar[OF Cons.prems(6) v(1)]
            ing.idx_reset_abstract[OF Cons.prems(6) v(1)]
            ing.idx_reset_iterated[OF Cons.prems(6) v(1)]
            ing.idx_reset_iterated_other[OF Cons.prems(6) v(1)]
      by (simp_all add: ig1_def)
    have bnd: "\<forall> w \<in> \<V>. label_get l1 w < 2 * card \<V>"
      using Cons.prems(8) n by (simp add: l1(3))
    have IH: "label_invar l' \<and> count_invar cnt' \<and> out_invar og' \<and> in_invar ig' \<and>
              counts_correct l' cnt' \<and> (\<forall> w \<in> \<V>. label_get l' w < 2 * card \<V>) \<and>
              label_get l' = (\<lambda> w. if w \<in> set vs \<and> k < label_get l1 w \<and> label_get l1 w < num_verts
                                  then num_verts + 1 else label_get l1 w) \<and>
              (\<forall> w. out_abstract og' w = out_abstract og1 w) \<and>
              (\<forall> w. in_abstract ig' w = in_abstract ig1 w) \<and>
              (\<forall> w. out_iterated og' w =
                    (if w \<in> set vs \<and> k < label_get l1 w \<and> label_get l1 w < num_verts then {}
                     else out_iterated og1 w)) \<and>
              (\<forall> w. in_iterated ig' w =
                    (if w \<in> set vs \<and> k < label_get l1 w \<and> label_get l1 w < num_verts then {}
                     else in_iterated ig1 w))"
      using Cons.prems(1,2,9) l1 og1(1) ig1(1) bnd step
      by (intro Cons.IH) auto
    show ?thesis
      using IH True v(2) og1(2,3,4) ig1(2,3,4) by (auto simp add: l1(3))
  next
    case False
    have step: "gap_step k (l, cnt, og, ig) v = (l, cnt, og, ig)"
      using False by (auto simp add: gap_step_def Let_def)
    have IH: "label_invar l' \<and> count_invar cnt' \<and> out_invar og' \<and> in_invar ig' \<and>
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
      using Cons.prems step by (intro Cons.IH) auto
    show ?thesis
      using IH False by auto
  qed
qed

lemma relabel_gap_impl_props:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "invar_state (relabel_gap_impl u st)"
        "labels_abs (relabel_gap_impl u st) = relabel_gap_effect (flow_abs st) (labels_abs st) u"
        "pr_fwd (relabel_gap_impl u st) = pr_fwd st \<and> pr_bwd (relabel_gap_impl u st) = pr_bwd st"
        "pr_excess (relabel_gap_impl u st) = pr_excess st"
        "pr_ctx (relabel_gap_impl u st) = pr_ctx st"
proof-
  note inv = invar_stateD[OF assms(1)]
  define k where "k = labels_abs st u"
  define st' where "st' = relabel_impl u st"
  define l' where "l' = relabel_effect (flow_abs st) (labels_abs st) u"
  note rp = relabel_impl_props[OF assms, folded st'_def l'_def]
  note inv' = invar_stateD[OF rp(1)]
  show "pr_fwd (relabel_gap_impl u st) = pr_fwd st \<and> pr_bwd (relabel_gap_impl u st) = pr_bwd st"
       "pr_excess (relabel_gap_impl u st) = pr_excess st"
       "pr_ctx (relabel_gap_impl u st) = pr_ctx st"
    using rp(3,4,5)
    by (auto simp add: relabel_gap_impl_def gap_impl_def Let_def st'_def[symmetric] split: prod.splits)
  have main: "invar_state (relabel_gap_impl u st) \<and>
        labels_abs (relabel_gap_impl u st) = relabel_gap_effect (flow_abs st) (labels_abs st) u"
  proof(cases "k < num_verts \<and> count_get (pr_counts st') k = 0")
    case True
    have none: "\<And> w. w \<in> \<V> \<Longrightarrow> l' w \<noteq> k"
    proof-
      fix w
      assume w: "w \<in> \<V>"
      have "k < 2 * card \<V>"
        using True by (simp add: num_verts)
      hence "card {w. w \<in> \<V> \<and> labels_abs st' w = k} = 0"
        using inv'(7) True by (simp add: counts_correct_def)
      thus "l' w \<noteq> k"
        using \<V>_finite w rp(2) by auto
    qed
    have gp: "gap_precond l' k"
      using True none by (auto intro: gap_precondI simp add: num_verts)
    obtain vs where vs: "distinct vs"
      "set vs = {v. v \<in> \<V> \<and> k < label_get (pr_labels st') v \<and> label_get (pr_labels st') v < card \<V>}"
      "gap_fold (pr_labels st') k (gap_step k) (pr_labels st', pr_counts st', pr_out st', pr_in st') =
       foldl (gap_step k) (pr_labels st', pr_counts st', pr_out st', pr_in st') vs"
      using gap_fold[OF inv'(3)] by blast
    obtain l'' cnt'' og'' ig'' where fold:
      "foldl (gap_step k) (pr_labels st', pr_counts st', pr_out st', pr_in st') vs = (l'', cnt'', og'', ig'')"
      by (cases "foldl (gap_step k) (pr_labels st', pr_counts st', pr_out st', pr_in st') vs") auto
    have bnd: "\<forall> w \<in> \<V>. label_get (pr_labels st') w < 2 * card \<V>"
      using height_boundedD[OF inv'(10)] cardV_0 by fastforce
    have vsV: "set vs \<subseteq> \<V>"
      using vs(2) by blast
    note gf = gap_fold_props[OF vs(1) vsV inv'(3,4,5,15,7) bnd fold, simplified vs(2) num_verts]
    have res: "relabel_gap_impl u st = st'\<lparr>pr_labels := l'', pr_counts := cnt'', pr_out := og'', pr_in := ig''\<rparr>"
      using True vs(3) fold by (simp add: relabel_gap_impl_def gap_impl_def Let_def k_def st'_def)
    have labels: "label_get l'' = gap_effect l' k"
      using gf rp(2) by (auto simp add: gap_effect_def num_verts)
    have eff: "relabel_gap_effect (flow_abs st) (labels_abs st) u = gap_effect l' k"
      using gp by (simp add: relabel_gap_effect_def l'_def k_def)
    have inv_res: "invar_state (relabel_gap_impl u st)"
    proof(rule invar_stateI)
      show "valid_labelling s t (flow_abs (relabel_gap_impl u st)) (labels_abs (relabel_gap_impl u st))"
        using relabel_gap_preserves_valid[OF net_assms inv(8,9) assms(2)] rp(3)
        by (simp add: res labels eff[symmetric])
      show "height_bounded (labels_abs (relabel_gap_impl u st))"
        using relabel_gap_preserves_height_bounded[OF net_assms inv(8,9) assms(2) inv(10)]
        by (simp add: res labels eff[symmetric])
      have gf_it: "\<And> w. iterated_res (relabel_gap_impl u st) w =
                    (if w \<in> \<V> \<and> k < l' w \<and> l' w < num_verts then {} else iterated_res st' w)"
        using gf rp(2) unfolding res by (simp add: iterated_res_def num_verts)
      fix w e
      assume w: "w \<in> \<V>" and e: "e \<in> iterated_res (relabel_gap_impl u st) w"
      have np: "\<not> (w \<in> \<V> \<and> k < l' w \<and> l' w < num_verts)"
        using e gf_it[of w] by auto
      have e': "e \<in> iterated_res st' w"
        using e unfolding gf_it[of w] if_not_P[OF np] .
      have lw: "label_get l'' w = l' w"
        using np unfolding labels gap_effect_def num_verts[symmetric] by simp
      show "\<not> admissible (flow_abs (relabel_gap_impl u st)) (labels_abs (relabel_gap_impl u st)) e"
      proof(rule iterated_invar_label_increase[OF rp(1) _ _ w _ e'])
        show "flow_abs (relabel_gap_impl u st) = flow_abs st'"
          by (simp add: res)
        show "\<And> x. x \<in> \<V> \<Longrightarrow> labels_abs st' x \<le> labels_abs (relabel_gap_impl u st) x"
          by (simp add: res labels rp(2) gap_effect_def)
        show "labels_abs (relabel_gap_impl u st) w = labels_abs st' w"
          using lw by (simp add: res rp(2))
      qed
    qed (use inv' gf rp(3,4) in \<open>auto simp add: res\<close>)
    show ?thesis
      using inv_res by (simp add: res labels eff)
  next
    case False
    have "relabel_gap_impl u st =
          (if k < num_verts \<and> count_get (pr_counts st') k = 0 then gap_impl k st' else st')"
      by (simp add: relabel_gap_impl_def Let_def k_def st'_def)
    hence res: "relabel_gap_impl u st = st'"
      unfolding if_not_P[OF False] .
    have "\<not> gap_precond l' k"
    proof
      assume gp: "gap_precond l' k"
      hence k: "k < num_verts" "\<forall> w \<in> \<V>. l' w \<noteq> k"
        by (auto elim: gap_precondE simp add: num_verts)
      have "k < 2 * card \<V>"
        using k(1) by (simp add: num_verts)
      hence "count_get (pr_counts st') k = card {w. w \<in> \<V> \<and> l' w = k}"
        using inv'(7) rp(2) by (simp add: counts_correct_def)
      also have "\<dots> = 0"
      proof-
        have e: "{w. w \<in> \<V> \<and> l' w = k} = {}"
          using k(2) by blast
        show ?thesis
          unfolding e by simp
      qed
      finally show False
        using False k(1) by simp
    qed
    hence "relabel_gap_effect (flow_abs st) (labels_abs st) u = l'"
      by (simp add: relabel_gap_effect_def l'_def k_def)
    thus ?thesis
      using rp(1,2) by (simp add: res)
  qed
  thus "invar_state (relabel_gap_impl u st)"
       "labels_abs (relabel_gap_impl u st) = relabel_gap_effect (flow_abs st) (labels_abs st) u"
    by simp_all
qed

text \<open>A forward push along \<open>d\<close> pushes along @{term "F d"}, a backward push along @{term "B d"}.\<close>

lemma push_impl_props:
  assumes "invar_state st" "(op = Push_Fwd d \<and> e = F d) \<or> (op = Push_Bwd d \<and> e = B d)"
          "push_precond s t (flow_abs st) (labels_abs st) e"
  shows "invar_state (apply_op op st)"
        "flow_abs (apply_op op st) = push_effect (flow_abs st) e"
        "pr_labels (apply_op op st) = pr_labels st" "pr_counts (apply_op op st) = pr_counts st"
        "pr_out (apply_op op st) = pr_out st" "pr_in (apply_op op st) = pr_in st"
        "pr_ctx (apply_op op st) = pr_ctx st"
proof-
  note inv = invar_stateD[OF assms(1)]
  have e: "e \<in> \<EE>" "fstv e \<in> \<V>"
    using assms(3) by (auto elim!: push_precondE admissibleE active_vertexE)
  have d: "d \<in> \<E>" "oedge e = d"
    using e(1) o_edge_res[of e] assms(2) by auto
  define \<gamma> where "\<gamma> = push_amount (flow_abs st) e"
  define \<delta> where "\<delta> = (case e of F _ \<Rightarrow> \<gamma> | B _ \<Rightarrow> - \<gamma>)"
  obtain fw' bw' x' where aug: "augment_impl d \<delta> (pr_fwd st) (pr_bwd st) (pr_excess st) = (fw', bw', x')"
    by (cases "augment_impl d \<delta> (pr_fwd st) (pr_bwd st) (pr_excess st)") auto
  have st': "apply_op op st = st\<lparr>pr_fwd := fw', pr_bwd := bw', pr_excess := x'\<rparr>"
    using assms(2)
  proof
    assume op: "op = Push_Fwd d \<and> e = F d"
    have "min (ex_get (pr_excess st) (fst d)) (emap_get (pr_fwd st) d) = \<gamma>"
      using inv(6)[of "fst d"] e(2) rcap_fwd[OF inv(14) d(1)] op by (simp add: \<gamma>_def push_amount_def)
    thus ?thesis
      using aug op by (simp add: push_fwd_impl_def Let_def \<delta>_def)
  next
    assume op: "op = Push_Bwd d \<and> e = B d"
    have "min (ex_get (pr_excess st) (snd d)) (emap_get (pr_bwd st) d) = \<gamma>"
      using inv(6)[of "snd d"] e(2) op by (simp add: \<gamma>_def push_amount_def)
    thus ?thesis
      using aug op by (simp add: push_bwd_impl_def Let_def \<delta>_def)
  qed
  have aug': "augment_impl (oedge e) (case e of F _ \<Rightarrow> \<gamma> | B _ \<Rightarrow> - \<gamma>) (pr_fwd st) (pr_bwd st)
                (pr_excess st) = (fw', bw', x')"
    using aug by (simp add: d(2) \<delta>_def)
  note ap = augment_impl_props[OF inv(1) inv(13) inv(2) e(1) _ inv(14) aug']
  have flow: "emap_get bw' = push_effect (flow_abs st) e"
    using ap(4) inv(6) by (simp add: push_effect_def \<gamma>_def)
  show "flow_abs (apply_op op st) = push_effect (flow_abs st) e"
    by (simp add: st' flow)
  show "pr_labels (apply_op op st) = pr_labels st" "pr_counts (apply_op op st) = pr_counts st"
       "pr_out (apply_op op st) = pr_out st" "pr_in (apply_op op st) = pr_in st"
       "pr_ctx (apply_op op st) = pr_ctx st"
    by (simp_all add: st')
  show "invar_state (apply_op op st)"
  proof(rule invar_stateI)
    show "is_preflow s (flow_abs (apply_op op st))"
      using push_preserves_preflow[OF net_assms inv(8) assms(3)] by (simp add: st' flow)
    show "valid_labelling s t (flow_abs (apply_op op st)) (labels_abs (apply_op op st))"
      using push_preserves_valid[OF net_assms inv(9) assms(3)] by (simp add: st' flow)
    fix w a
    assume w: "w \<in> \<V>" "a \<in> iterated_res (apply_op op st) w"
    have "a \<in> iterated_res st w"
      using w(2) by (simp add: st' iterated_res_def)
    thus "\<not> admissible (flow_abs (apply_op op st)) (labels_abs (apply_op op st)) a"
      using push_admissible[OF net_assms assms(3), of a] inv(12)[OF w(1)]
      by (auto simp add: st' flow)
  qed (use inv ap in \<open>simp_all add: st'\<close>)
qed


text \<open>The number of edges the two iterators of a vertex have not yet passed.\<close>

definition "remaining_count st u = card (out_remaining (pr_out st) u) + card (in_remaining (pr_in st) u)"

lemma move_impl_props:
  assumes "invar_state st" "u \<in> \<V>" "current_res st u = Some e"
          "\<not> admissible (flow_abs st) (labels_abs st) e"
  shows "invar_state (move_impl u st)"
        "pr_fwd (move_impl u st) = pr_fwd st \<and> pr_bwd (move_impl u st) = pr_bwd st"
        "pr_labels (move_impl u st) = pr_labels st" "pr_ctx (move_impl u st) = pr_ctx st"
        "remaining_count (move_impl u st) u < remaining_count st u"
        "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (move_impl u st) w = remaining_count st w"
proof-
  note inv = invar_stateD[OF assms(1)]
  have fin: "finite (out_remaining (pr_out st) u)" "finite (in_remaining (pr_in st) u)"
    using outg.idx_partition_union[OF inv(5) assms(2)] ing.idx_partition_union[OF inv(15) assms(2)]
          inv(11)[OF assms(2)] inv(16)[OF assms(2)] finite_delta
    by (metis finite_Un)+
  show "pr_fwd (move_impl u st) = pr_fwd st \<and> pr_bwd (move_impl u st) = pr_bwd st"
       "pr_labels (move_impl u st) = pr_labels st" "pr_ctx (move_impl u st) = pr_ctx st"
    by (simp_all add: move_impl_def)
  have main: "invar_state (move_impl u st) \<and>
              remaining_count (move_impl u st) u < remaining_count st u \<and>
              (\<forall> w. w \<noteq> u \<longrightarrow> remaining_count (move_impl u st) w = remaining_count st w)"
  proof(cases "out_has (pr_out st) u")
    case True
    define og where "og = pr_out st"
    have st': "move_impl u st = st\<lparr>pr_out := out_move og u\<rparr>"
      using True by (simp add: move_impl_def og_def)
    have e: "e = F (out_current og u)"
      using assms(3) True by (simp add: current_res_def og_def)
    have rem: "out_remaining og u \<noteq> {}"
      using outg.idx_has[OF inv(5) assms(2)] True by (simp add: og_def)
    have cur: "out_current og u \<in> out_remaining og u"
      using outg.idx_current[OF inv(5) assms(2)] rem by (simp add: og_def)
    note mv = outg.idx_move_invar[OF inv(5) assms(2)] outg.idx_move_abstract[OF inv(5) assms(2) rem[unfolded og_def]]
              outg.idx_move_remaining[OF inv(5) assms(2) rem[unfolded og_def]]
              outg.idx_move_iterated[OF inv(5) assms(2) rem[unfolded og_def]]
              outg.idx_move_remaining_other[OF inv(5) assms(2) rem[unfolded og_def]]
              outg.idx_move_iterated_other[OF inv(5) assms(2) rem[unfolded og_def]]
    have "card (out_remaining og u - {out_current og u}) < card (out_remaining og u)"
      using fin(1) cur by (intro card_Diff1_less) (simp_all add: og_def)
    hence dec: "remaining_count (move_impl u st) u < remaining_count st u"
      using mv(3) by (simp add: st' remaining_count_def og_def)
    have other: "\<forall> w. w \<noteq> u \<longrightarrow> remaining_count (move_impl u st) w = remaining_count st w"
      using mv(5) by (simp add: st' remaining_count_def og_def)
    have "invar_state (move_impl u st)"
    proof(rule invar_stateI)
      fix w d
      assume w: "w \<in> \<V>" "d \<in> iterated_res (move_impl u st) w"
      show "\<not> admissible (flow_abs (move_impl u st)) (labels_abs (move_impl u st)) d"
      proof(cases "w = u")
        case True
        thus ?thesis
          using w inv(12) assms(4) mv(4) by (auto simp add: st' e iterated_res_def og_def)
      next
        case False
        thus ?thesis
          using w inv(12) mv(6) by (auto simp add: st' iterated_res_def og_def)
      qed
    qed (use inv mv in \<open>simp_all add: st' og_def\<close>)
    thus ?thesis
      using dec other by simp
  next
    case False
    define ig where "ig = pr_in st"
    have st': "move_impl u st = st\<lparr>pr_in := in_move ig u\<rparr>"
      using False by (simp add: move_impl_def ig_def)
    have has: "in_has ig u" and e: "e = B (in_current ig u)"
      using assms(3) False by (simp_all add: current_res_def ig_def split: if_splits)
    have rem: "in_remaining ig u \<noteq> {}"
      using ing.idx_has[OF inv(15) assms(2)] has by (simp add: ig_def)
    have cur: "in_current ig u \<in> in_remaining ig u"
      using ing.idx_current[OF inv(15) assms(2)] rem by (simp add: ig_def)
    note mv = ing.idx_move_invar[OF inv(15) assms(2)] ing.idx_move_abstract[OF inv(15) assms(2) rem[unfolded ig_def]]
              ing.idx_move_remaining[OF inv(15) assms(2) rem[unfolded ig_def]]
              ing.idx_move_iterated[OF inv(15) assms(2) rem[unfolded ig_def]]
              ing.idx_move_remaining_other[OF inv(15) assms(2) rem[unfolded ig_def]]
              ing.idx_move_iterated_other[OF inv(15) assms(2) rem[unfolded ig_def]]
    have "card (in_remaining ig u - {in_current ig u}) < card (in_remaining ig u)"
      using fin(2) cur by (intro card_Diff1_less) (simp_all add: ig_def)
    hence dec: "remaining_count (move_impl u st) u < remaining_count st u"
      using mv(3) by (simp add: st' remaining_count_def ig_def)
    have other: "\<forall> w. w \<noteq> u \<longrightarrow> remaining_count (move_impl u st) w = remaining_count st w"
      using mv(5) by (simp add: st' remaining_count_def ig_def)
    have "invar_state (move_impl u st)"
    proof(rule invar_stateI)
      fix w d
      assume w: "w \<in> \<V>" "d \<in> iterated_res (move_impl u st) w"
      show "\<not> admissible (flow_abs (move_impl u st)) (labels_abs (move_impl u st)) d"
      proof(cases "w = u")
        case True
        thus ?thesis
          using w inv(12) assms(4) mv(4) by (auto simp add: st' e iterated_res_def ig_def)
      next
        case False
        thus ?thesis
          using w inv(12) mv(6) by (auto simp add: st' iterated_res_def ig_def)
      qed
    qed (use inv mv in \<open>simp_all add: st' ig_def\<close>)
    thus ?thesis
      using dec other by simp
  qed
  thus "invar_state (move_impl u st)"
       "remaining_count (move_impl u st) u < remaining_count st u"
       "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (move_impl u st) w = remaining_count st w"
    by simp_all
qed

text \<open>Skipping inadmissible edges: the scan stops at the first admissible edge or at the end of
      the edges; all passed edges are inadmissible and the remaining edges do not grow.\<close>

lemma skip_scan_props:
  assumes it: "indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move
                                    it_reset \<V>"
      and "it_invar C" "u \<in> \<V>" "finite (it_remaining C u)"
          "skip_scan has cur move adm u C = C'"
  shows "it_invar C'" "\<forall> w. it_abstract C' w = it_abstract C w"
        "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w \<and> it_remaining C' w = it_remaining C w"
        "\<forall> d \<in> it_iterated C' u - it_iterated C u. \<not> adm d"
        "card (it_remaining C' u) \<le> card (it_remaining C u)"
proof-
  interpret it: indexed_iterable_set it_invar it_abstract cur has it_iterated it_remaining move
                                     it_reset \<V>
    by (rule it)
  have main:
    "it_invar C' \<and> (\<forall> w. it_abstract C' w = it_abstract C w) \<and>
     (\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w \<and> it_remaining C' w = it_remaining C w) \<and>
     (\<forall> d \<in> it_iterated C' u - it_iterated C u. \<not> adm d) \<and>
     card (it_remaining C' u) \<le> card (it_remaining C u)"
    using assms(2-)
  proof(induction "card (it_remaining C u)" arbitrary: C rule: less_induct)
    case less
    show ?case
    proof(cases "has C u \<and> \<not> adm (cur C u)")
      case False
      have "skip_scan has cur move adm u C = C"
        by (subst skip_scan.simps) (simp only: if_not_P[OF False])
      hence "C' = C"
        using less.prems(4) by simp
      thus ?thesis
        using less.prems(1) by simp
    next
      case True
      define d where "d = cur C u"
      have rem: "it_remaining C u \<noteq> {}"
        using it.idx_has[OF less.prems(1,2)] True by simp
      have dR: "d \<in> it_remaining C u"
        using it.idx_current[OF less.prems(1,2) rem] by (simp add: d_def)
      have step: "skip_scan has cur move adm u C = skip_scan has cur move adm u (move C u)"
        by (subst skip_scan.simps) (simp only: if_P[OF True])
      have C1: "it_invar (move C u)" "it_remaining (move C u) u = it_remaining C u - {d}"
        using it.idx_move_invar[OF less.prems(1,2)]
              it.idx_move_remaining[OF less.prems(1,2) rem] by (simp_all add: d_def)
      have itm: "it_iterated (move C u) u = it_iterated C u \<union> {d}"
        using it.idx_move_iterated[OF less.prems(1,2) rem] by (simp add: d_def)
      have card: "card (it_remaining (move C u) u) < card (it_remaining C u)"
        unfolding C1(2) using less.prems(3) dR by (rule card_Diff1_less)
      have fin: "finite (it_remaining (move C u) u)"
        using less.prems(3) by (simp add: C1(2))
      have sc: "skip_scan has cur move adm u (move C u) = C'"
        using step less.prems(4) by simp
      note IH = less.hyps[OF card C1(1) less.prems(2) fin sc]
      have nd: "\<not> adm d"
        using True by (simp add: d_def)
      show ?thesis
        using IH it.idx_move_abstract[OF less.prems(1,2) rem]
              it.idx_move_iterated_other[OF less.prems(1,2) rem]
              it.idx_move_remaining_other[OF less.prems(1,2) rem] itm nd card
        by auto
    qed
  qed
  thus "it_invar C'" "\<forall> w. it_abstract C' w = it_abstract C w"
       "\<forall> w. w \<noteq> u \<longrightarrow> it_iterated C' w = it_iterated C w \<and> it_remaining C' w = it_remaining C w"
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
  note inv = invar_stateD[OF assms(1)]
  have fin: "finite (out_remaining (pr_out st) u)" "finite (in_remaining (pr_in st) u)"
    using outg.idx_partition_union[OF inv(5) assms(2)] ing.idx_partition_union[OF inv(15) assms(2)]
          inv(11)[OF assms(2)] inv(16)[OF assms(2)] finite_delta
    by (metis finite_Un)+
  define og where "og = skip_scan out_has out_current out_move
                          (admissible_fwd_impl (pr_fwd st) (pr_labels st)) u (pr_out st)"
  define ig where "ig = (if out_has og u then pr_in st
                         else skip_scan in_has in_current in_move
                                (admissible_bwd_impl (pr_bwd st) (pr_labels st)) u (pr_in st))"
  have st': "skip_impl u st = st\<lparr>pr_out := og, pr_in := ig\<rparr>"
    by (cases "out_has og u") (simp_all add: skip_impl_def Let_def og_def[symmetric] ig_def)
  note so = skip_scan_props[OF outg.indexed_iterable_set_axioms inv(5) assms(2) fin(1) og_def[symmetric]]
  have si0: "in_invar ig \<and> (\<forall> w. in_abstract ig w = in_abstract (pr_in st) w) \<and>
             (\<forall> w. w \<noteq> u \<longrightarrow> in_iterated ig w = in_iterated (pr_in st) w \<and>
                              in_remaining ig w = in_remaining (pr_in st) w) \<and>
             (\<forall> d \<in> in_iterated ig u - in_iterated (pr_in st) u.
                \<not> admissible_bwd_impl (pr_bwd st) (pr_labels st) d) \<and>
             card (in_remaining ig u) \<le> card (in_remaining (pr_in st) u)"
  proof(cases "out_has og u")
    case True
    thus ?thesis
      using inv(15) by (simp add: ig_def)
  next
    case False
    hence "skip_scan in_has in_current in_move (admissible_bwd_impl (pr_bwd st) (pr_labels st)) u
             (pr_in st) = ig"
      by (simp add: ig_def)
    note si = skip_scan_props[OF ing.indexed_iterable_set_axioms inv(15) assms(2) fin(2) this]
    show ?thesis
      using si by simp
  qed
  hence si: "in_invar ig" "\<forall> w. in_abstract ig w = in_abstract (pr_in st) w"
            "\<forall> w. w \<noteq> u \<longrightarrow> in_iterated ig w = in_iterated (pr_in st) w \<and>
                             in_remaining ig w = in_remaining (pr_in st) w"
            "\<forall> d \<in> in_iterated ig u - in_iterated (pr_in st) u.
               \<not> admissible_bwd_impl (pr_bwd st) (pr_labels st) d"
            "card (in_remaining ig u) \<le> card (in_remaining (pr_in st) u)"
    by simp_all
  show "pr_fwd (skip_impl u st) = pr_fwd st \<and> pr_bwd (skip_impl u st) = pr_bwd st"
       "pr_labels (skip_impl u st) = pr_labels st" "pr_ctx (skip_impl u st) = pr_ctx st"
    by (simp_all add: st')
  show "remaining_count (skip_impl u st) u \<le> remaining_count st u"
    using so(5) si(5) by (simp add: st' remaining_count_def)
  show "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (skip_impl u st) w = remaining_count st w"
    using so(3) si(3) by (simp add: st' remaining_count_def)
  have nadm: "\<not> admissible (flow_abs st) (labels_abs st) e"
    if w: "w \<in> \<V>" and e: "e \<in> iterated_res (skip_impl u st) w" for w e
  proof(cases "e \<in> iterated_res st w")
    case True
    thus ?thesis
      using inv(12)[OF w] by simp
  next
    case False
    have wu: "w = u"
    proof(rule ccontr)
      assume "w \<noteq> u"
      hence "iterated_res (skip_impl u st) w = iterated_res st w"
        using so(3) si(3) by (simp add: st' iterated_res_def)
      thus False
        using e False by simp
    qed
    from e False consider (f) d where "d \<in> out_iterated og u - out_iterated (pr_out st) u" "e = F d"
                        | (b) d where "d \<in> in_iterated ig u - in_iterated (pr_in st) u" "e = B d"
      by (auto simp add: st' iterated_res_def wu)
    thus ?thesis
    proof cases
      case f
      have "d \<in> \<delta>\<^sup>+ u"
        using outg.idx_partition_union[OF so(1) assms(2)] so(2) inv(11)[OF assms(2)] f(1) by blast
      hence "d \<in> \<E>"
        by (simp add: delta_plus_def)
      thus ?thesis
        using so(4) f admissible_fwd_impl[OF inv(14)] by auto
    next
      case b
      have "d \<in> \<delta>\<^sup>- u"
        using ing.idx_partition_union[OF si(1) assms(2)] si(2) inv(16)[OF assms(2)] b(1) by blast
      hence "d \<in> \<E>"
        by (simp add: delta_minus_def)
      thus ?thesis
        using si(4) b admissible_bwd_impl by auto
    qed
  qed
  show "invar_state (skip_impl u st)"
  proof(rule invar_stateI)
    fix w e
    assume w: "w \<in> \<V>" and e: "e \<in> iterated_res (skip_impl u st) w"
    show "\<not> admissible (flow_abs (skip_impl u st)) (labels_abs (skip_impl u st)) e"
      using nadm[OF w e] by (simp add: st')
  qed (use inv so si in \<open>simp_all add: st'\<close>)
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
proof-
  note mp = move_impl_props[OF assms]
  note sp = skip_impl_props[OF mp(1) assms(2)]
  have adv: "advance_impl u st = skip_impl u (move_impl u st)"
    by (simp add: advance_impl_def)
  show "invar_state (advance_impl u st)"
    using sp(1) by (simp add: adv)
  show "pr_fwd (advance_impl u st) = pr_fwd st \<and> pr_bwd (advance_impl u st) = pr_bwd st"
    using sp(2) mp(2) by (simp add: adv)
  show "pr_labels (advance_impl u st) = pr_labels st" "pr_ctx (advance_impl u st) = pr_ctx st"
    using sp(3,4) mp(3,4) by (simp_all add: adv)
  show "remaining_count (advance_impl u st) u < remaining_count st u"
    using le_less_trans[OF sp(5) mp(5)] by (simp add: adv)
  show "\<And> w. w \<noteq> u \<Longrightarrow> remaining_count (advance_impl u st) w = remaining_count st w"
    using sp(6) mp(6) by (simp add: adv)
qed


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

lemma pr_measure_ctx: "(st', st\<lparr>pr_ctx := c\<rparr>) \<in> pr_measure \<longleftrightarrow> (st', st) \<in> pr_measure"
  by (simp add: pr_measure_def remaining_measure_def remaining_count_def)

lemma push_measure:
  assumes "push_precond s t (flow_abs st) (labels_abs st) e"
          "flow_abs st' = push_effect (flow_abs st) e" "labels_abs st' = labels_abs st"
  shows "(st', st) \<in> pr_measure"
proof(cases "real_of_ereal (rcap (flow_abs st) e) \<le> ex (flow_abs st) (fstv e)")
  case True
  thus ?thesis
    using push_saturating_admissible_count[OF net_assms assms(1) True] assms(2,3)
    by (simp add: pr_measure_def)
next
  case False
  hence "ex (flow_abs st) (fstv e) < real_of_ereal (rcap (flow_abs st) e)"
    by simp
  thus ?thesis
    using push_nonsaturating_active_potential[OF net_assms assms(1)]
          push_admissible_count_mono[OF net_assms assms(1)] assms(2,3)
    by (auto simp add: pr_measure_def)
qed

lemma label_measure_step:
  "label_measure (labels_abs st') < label_measure (labels_abs st) \<Longrightarrow> (st', st) \<in> pr_measure"
  by (simp add: pr_measure_def)

lemma advance_measure:
  assumes "invar_state st" "u \<in> \<V>" "current_res st u = Some e"
          "\<not> admissible (flow_abs st) (labels_abs st) e"
  shows "(advance_impl u st, st) \<in> pr_measure"
proof-
  note ap = advance_impl_props[OF assms]
  have "remaining_measure (advance_impl u st) < remaining_measure st"
    unfolding remaining_measure_def
  proof(rule sum_strict_mono_ex1[OF \<V>_finite])
    show "\<forall> w \<in> \<V>. remaining_count (advance_impl u st) w \<le> remaining_count st w"
    proof
      fix w
      show "remaining_count (advance_impl u st) w \<le> remaining_count st w"
        using ap(5,6) by (cases "w = u") auto
    qed
    show "\<exists> w \<in> \<V>. remaining_count (advance_impl u st) w < remaining_count st w"
      using ap(5) assms(2) by blast
  qed
  thus ?thesis
    using ap(2,3) by (simp add: pr_measure_def)
qed

end

context push_relabel
begin

lemma push_relabel_upd_props:
  assumes "invar_state st" "ctx_invar st" "push_relabel_upd_cond st"
  shows "invar_state (push_relabel_upd st)" "ctx_invar (push_relabel_upd st)"
        "(push_relabel_upd st, st) \<in> pr_measure"
proof-
  obtain op c where sel: "select_of st = (op, c)"
    by (cases "select_of st") auto
  have op: "op \<noteq> Done"
    using assms(3) sel by (simp add: push_relabel_upd_cond_def)
  define st0 where "st0 = st\<lparr>pr_ctx := c\<rparr>"
  have upd: "push_relabel_upd st = apply_op op st0"
    using sel by (simp add: push_relabel_upd_def st0_def)
  show "ctx_invar (push_relabel_upd st)"
    using select(2)[OF assms(1,2) sel op] by (simp add: upd st0_def)
  have inv0: "invar_state st0"
    using assms(1) by (simp add: st0_def invar_state_ctx)
  have eqs: "flow_abs st0 = flow_abs st" "labels_abs st0 = labels_abs st"
            "current_res st0 = current_res st"
    by (simp_all add: st0_def current_res_def fun_eq_iff)
  have good: "good_op st0 op"
    using select(1)[OF assms(1,2) sel] by (cases op) (simp_all add: good_op_def eqs)
  note inv = invar_stateD[OF inv0]
  have "invar_state (apply_op op st0) \<and> (apply_op op st0, st0) \<in> pr_measure"
  proof(cases op)
    case (Push_Fwd d)
    have pre: "push_precond s t (flow_abs st0) (labels_abs st0) (F d)"
      using good by (simp add: Push_Fwd good_op_def)
    note pp = push_impl_props[OF inv0 disjI1[OF conjI[OF Push_Fwd refl]] pre]
    show ?thesis
      using pp(1,3) push_measure[OF pre pp(2)] by simp
  next
    case (Push_Bwd d)
    have pre: "push_precond s t (flow_abs st0) (labels_abs st0) (B d)"
      using good by (simp add: Push_Bwd good_op_def)
    note pp = push_impl_props[OF inv0 disjI2[OF conjI[OF Push_Bwd refl]] pre]
    show ?thesis
      using pp(1,3) push_measure[OF pre pp(2)] by simp
  next
    case (Advance u)
    then obtain e where e: "u \<in> \<V>" "current_res st0 u = Some e"
                           "\<not> admissible (flow_abs st0) (labels_abs st0) e"
      using good by (auto simp add: good_op_def)
    show ?thesis
      using advance_impl_props(1)[OF inv0 e] advance_measure[OF inv0 e] by (simp add: Advance)
  next
    case (Relabel u)
    have pre: "relabel_precond s t (flow_abs st0) (labels_abs st0) u"
      using good by (simp add: Relabel good_op_def)
    note rp = relabel_impl_props[OF inv0 pre]
    have "label_measure (labels_abs (relabel_impl u st0)) < label_measure (labels_abs st0)"
      using relabel_label_measure[OF net_assms inv(8,9) pre inv(10)] rp(2) by simp
    thus ?thesis
      using rp(1) label_measure_step by (simp add: Relabel)
  next
    case (Relabel_Gap u)
    have pre: "relabel_precond s t (flow_abs st0) (labels_abs st0) u"
      using good by (simp add: Relabel_Gap good_op_def)
    note rp = relabel_gap_impl_props[OF inv0 pre]
    have "label_measure (labels_abs (relabel_gap_impl u st0)) < label_measure (labels_abs st0)"
      using relabel_gap_label_measure[OF net_assms inv(8,9) pre inv(10)] rp(2) by simp
    thus ?thesis
      using rp(1) label_measure_step by (simp add: Relabel_Gap)
  qed (use op in simp)
  hence i: "invar_state (apply_op op st0)" and m: "(apply_op op st0, st0) \<in> pr_measure"
    by simp_all
  show "invar_state (push_relabel_upd st)"
    using i by (simp add: upd)
  have "(apply_op op st0, st) \<in> pr_measure"
    using m unfolding st0_def pr_measure_ctx .
  thus "(push_relabel_upd st, st) \<in> pr_measure"
    by (simp add: upd st0_def)
qed

text \<open>The loop terminates, preserves the invariants and stops without active vertices.\<close>

lemma push_relabel_loop_props:
  assumes "invar_state st" "ctx_invar st"
  shows "push_relabel_loop_dom st" "invar_state (push_relabel_loop st)"
        "\<And> v. \<not> active_vertex s t (flow_abs (push_relabel_loop st)) v"
proof-
  have "push_relabel_loop_dom st \<and> invar_state (push_relabel_loop st) \<and>
        (\<forall> v. \<not> active_vertex s t (flow_abs (push_relabel_loop st)) v)"
    using assms
  proof(induction st rule: wf_induct[OF wf_pr_measure])
    case (1 st)
    show ?case
    proof(rule push_relabel_cases[of st])
      assume ret: "push_relabel_ret_cond st"
      obtain op c where sel: "select_of st = (op, c)"
        by (cases "select_of st") auto
      have "op = Done"
        using ret sel by (simp add: push_relabel_ret_cond_def)
      hence "\<forall> v. \<not> active_vertex s t (flow_abs st) v"
        using select(1)[OF 1(2,3) sel] by (simp add: good_op_def)
      moreover have "push_relabel_loop st = st\<lparr>pr_ctx := c\<rparr>"
        using push_relabel_simps(1)[OF ret] sel by (simp add: push_relabel_ret_def)
      ultimately show ?thesis
        using push_relabel_domintros(1)[OF ret] 1(2) by (simp add: invar_state_ctx)
    next
      assume upd: "push_relabel_upd_cond st"
      note up = push_relabel_upd_props[OF 1(2,3) upd]
      have IH: "push_relabel_loop_dom (push_relabel_upd st) \<and>
                invar_state (push_relabel_loop (push_relabel_upd st)) \<and>
                (\<forall> v. \<not> active_vertex s t (flow_abs (push_relabel_loop (push_relabel_upd st))) v)"
        using 1(1)[rule_format, OF up(3) up(1,2)] .
      hence dom: "push_relabel_loop_dom st"
        using push_relabel_domintros(2)[OF upd] by blast
      show ?thesis
        using IH dom push_relabel_simps(2)[OF dom upd] by simp
    qed
  qed
  thus "push_relabel_loop_dom st" "invar_state (push_relabel_loop st)"
       "\<And> v. \<not> active_vertex s t (flow_abs (push_relabel_loop st)) v"
    by simp_all
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
  assumes "finite A" "d \<notin> D"
  shows "(\<Sum> e \<in> A \<inter> insert d D. g e) = (\<Sum> e \<in> A \<inter> D. g e) + (if d \<in> A then g d else 0)"
proof(cases "d \<in> A")
  case True
  hence "A \<inter> insert d D = insert d (A \<inter> D)"
    by blast
  thus ?thesis
    using True assms by (simp add: add.commute)
next
  case False
  hence "A \<inter> insert d D = A \<inter> D"
    by blast
  thus ?thesis
    using False by simp
qed

lemma init_step_inv:
  assumes "init_inv D fw bw x" "d \<in> \<E>" "d \<notin> D" "init_step (fw, bw, x) d = (fw', bw', x')"
  shows "init_inv (insert d D) fw' bw' x'"
proof-
  define c where "c = emap_get caps d"
  have c: "\<u> d = ereal c"
    using caps(2)[OF assms(2)] by (simp add: c_def)
  have uv: "fst d \<in> \<V>" "snd d \<in> \<V>"
    using assms(2) by (auto intro: fst_E_V snd_E_V)
  have I: "emap_invar fw" "emap_invar bw" "ex_invar x"
          "\<forall> e \<in> D. emap_get bw e = init_flow s e \<and> \<u> e = ereal (emap_get fw e + emap_get bw e)"
          "\<forall> v \<in> \<V>. ex_get x v = (\<Sum> e \<in> \<delta>\<^sup>- v \<inter> D. init_flow s e) - (\<Sum> e \<in> \<delta>\<^sup>+ v \<inter> D. init_flow s e)"
    using assms(1) by (simp_all add: init_inv_def)
  have sums: "\<And> v. (\<Sum> e \<in> \<delta>\<^sup>- v \<inter> insert d D. init_flow s e) =
                    (\<Sum> e \<in> \<delta>\<^sup>- v \<inter> D. init_flow s e) + (if snd d = v then init_flow s d else 0)"
             "\<And> v. (\<Sum> e \<in> \<delta>\<^sup>+ v \<inter> insert d D. init_flow s e) =
                    (\<Sum> e \<in> \<delta>\<^sup>+ v \<inter> D. init_flow s e) + (if fst d = v then init_flow s d else 0)"
  proof-
    have mem: "\<And> v. d \<in> \<delta>\<^sup>- v \<longleftrightarrow> snd d = v" "\<And> v. d \<in> \<delta>\<^sup>+ v \<longleftrightarrow> fst d = v"
      using assms(2) by (auto simp add: delta_minus_def delta_plus_def)
    fix v
    show "(\<Sum> e \<in> \<delta>\<^sup>- v \<inter> insert d D. init_flow s e) =
          (\<Sum> e \<in> \<delta>\<^sup>- v \<inter> D. init_flow s e) + (if snd d = v then init_flow s d else 0)"
         "(\<Sum> e \<in> \<delta>\<^sup>+ v \<inter> insert d D. init_flow s e) =
          (\<Sum> e \<in> \<delta>\<^sup>+ v \<inter> D. init_flow s e) + (if fst d = v then init_flow s d else 0)"
      unfolding sum_Int_insert[OF finite_delta(2) assms(3)] sum_Int_insert[OF finite_delta(1) assms(3)]
                mem by simp_all
  qed
  show ?thesis
  proof(cases "fst d = s \<and> snd d \<noteq> s")
    case True
    define x1 where "x1 = ex_upd x s (ex_get x s - c)"
    have st: "fw' = emap_upd fw d 0" "bw' = emap_upd bw d c"
             "x' = ex_upd x1 (snd d) (ex_get x1 (snd d) + c)"
      using assms(4) True by (auto simp add: init_step_def Let_def c_def x1_def)
    have f: "init_flow s d = c"
      using True assms(2) c by (simp add: init_flow_def)
    have x1: "ex_invar x1" "ex_get x1 = (ex_get x)(s := ex_get x s - c)"
      using ex_map.fixed_univ_map_upd_invar[OF I(3) s_in_V] ex_map.fixed_univ_map_upd[OF I(3) s_in_V]
      by (simp_all add: x1_def)
    have invs: "emap_invar fw'" "emap_invar bw'" "ex_invar x'"
      using edge_map.fixed_univ_map_upd_invar[OF I(1) assms(2)]
            edge_map.fixed_univ_map_upd_invar[OF I(2) assms(2)]
            ex_map.fixed_univ_map_upd_invar[OF x1(1) uv(2)] by (simp_all add: st)
    have get: "emap_get fw' = (emap_get fw)(d := 0)" "emap_get bw' = (emap_get bw)(d := c)"
              "ex_get x' = (ex_get x1)(snd d := ex_get x1 (snd d) + c)"
      using edge_map.fixed_univ_map_upd[OF I(1) assms(2)] edge_map.fixed_univ_map_upd[OF I(2) assms(2)]
            ex_map.fixed_univ_map_upd[OF x1(1) uv(2)] by (simp_all add: st)
    have flows: "\<forall> e \<in> insert d D. emap_get bw' e = init_flow s e \<and>
                                   \<u> e = ereal (emap_get fw' e + emap_get bw' e)"
      using I(4) c f assms(3) by (auto simp add: get)
    have exs: "\<forall> v \<in> \<V>. ex_get x' v = (\<Sum> e \<in> \<delta>\<^sup>- v \<inter> insert d D. init_flow s e) -
                                      (\<Sum> e \<in> \<delta>\<^sup>+ v \<inter> insert d D. init_flow s e)"
      using I(5) True f by (auto simp add: get x1(2) sums)
    show ?thesis
      using invs flows exs by (simp add: init_inv_def)
  next
    case False
    have st: "fw' = emap_upd fw d c" "bw' = emap_upd bw d 0" "x' = x"
      using assms(4) False by (auto simp add: init_step_def Let_def c_def)
    have f: "init_flow s d = 0"
      using False by (auto simp add: init_flow_def)
    have invs: "emap_invar fw'" "emap_invar bw'" "ex_invar x'"
      using edge_map.fixed_univ_map_upd_invar[OF I(1) assms(2)]
            edge_map.fixed_univ_map_upd_invar[OF I(2) assms(2)] I(3) by (simp_all add: st)
    have get: "emap_get fw' = (emap_get fw)(d := c)" "emap_get bw' = (emap_get bw)(d := 0)"
      using edge_map.fixed_univ_map_upd[OF I(1) assms(2)] edge_map.fixed_univ_map_upd[OF I(2) assms(2)]
      by (simp_all add: st)
    have flows: "\<forall> e \<in> insert d D. emap_get bw' e = init_flow s e \<and>
                                   \<u> e = ereal (emap_get fw' e + emap_get bw' e)"
      using I(4) c f assms(3) by (auto simp add: get)
    have exs: "\<forall> v \<in> \<V>. ex_get x' v = (\<Sum> e \<in> \<delta>\<^sup>- v \<inter> insert d D. init_flow s e) -
                                      (\<Sum> e \<in> \<delta>\<^sup>+ v \<inter> insert d D. init_flow s e)"
      using I(5) f by (simp add: st sums)
    show ?thesis
      using invs flows exs by (simp add: init_inv_def)
  qed
qed

lemma init_fold_inv:
  assumes "init_inv D fw bw x" "distinct ds" "set ds \<subseteq> \<E>" "set ds \<inter> D = {}"
          "foldl init_step (fw, bw, x) ds = (fw', bw', x')"
  shows "init_inv (D \<union> set ds) fw' bw' x'"
  using assms
proof(induction ds arbitrary: D fw bw x)
  case Nil
  thus ?case
    by simp
next
  case (Cons d ds)
  obtain fw1 bw1 x1 where step: "init_step (fw, bw, x) d = (fw1, bw1, x1)"
    by (cases "init_step (fw, bw, x) d") auto
  have "init_inv (insert d D) fw1 bw1 x1"
    using Cons.prems(3,4) by (intro init_step_inv[OF Cons.prems(1) _ _ step]) auto
  hence "init_inv (insert d D \<union> set ds) fw' bw' x'"
    using Cons.prems(2-5) step by (intro Cons.IH) auto
  thus ?case
    by simp
qed

text \<open>Every flow that agrees with the initial flow on the edges is an initial preflow.\<close>

lemma init_flow_agree:
  assumes "\<forall> d \<in> \<E>. f d = init_flow s d"
  shows "\<And> v. ex f v = ex (init_flow s) v" "is_preflow s f"
        "valid_labelling s t f (init_labels s)" "\<And> e. \<not> admissible f (init_labels s) e"
proof-
  show ex: "\<And> v. ex f v = ex (init_flow s) v"
  proof-
    fix v
    have "sum f (\<delta>\<^sup>- v) = sum (init_flow s) (\<delta>\<^sup>- v)" "sum f (\<delta>\<^sup>+ v) = sum (init_flow s) (\<delta>\<^sup>+ v)"
      using assms by (auto intro: sum.cong simp add: delta_minus_def delta_plus_def)
    thus "ex f v = ex (init_flow s) v"
      by (simp add: ex_def)
  qed
  have rc: "\<And> e. e \<in> \<EE> \<Longrightarrow> rcap f e = rcap (init_flow s) e"
    using assms by (auto simp add: \<EE>_def)
  show "is_preflow s f"
    using init_flow_preflow[OF net_assms] assms ex by (simp add: is_preflow_def isuflow_def)
  show "valid_labelling s t f (init_labels s)"
    using init_labels_valid[OF net_assms] rc by (simp add: valid_labelling_def)
  fix e
  show "\<not> admissible f (init_labels s) e"
    using init_not_admissible[OF net_assms, of e] rc[of e]
    by (cases "e \<in> \<EE>") (auto simp add: admissible_def)
qed

end

context push_relabel
begin

lemma init_state_props: "invar_state init_state" "ctx_invar init_state"
proof-
  obtain es where es: "distinct es" "set es = \<E>"
    "edge_fold init_step (emap_init, emap_init, ex_init) = foldl init_step (emap_init, emap_init, ex_init) es"
    using edge_fold by blast
  obtain fw bw x where fold: "foldl init_step (emap_init, emap_init, ex_init) es = (fw, bw, x)"
    by (cases "foldl init_step (emap_init, emap_init, ex_init) es") auto
  have I0: "init_inv {} emap_init emap_init ex_init"
    using init_adts by (simp add: init_inv_def)
  have "init_inv \<E> fw bw x"
    using init_fold_inv[OF I0 es(1) _ _ fold] es(2) by simp
  hence I: "emap_invar fw" "emap_invar bw" "ex_invar x" "\<forall> d \<in> \<E>. emap_get bw d = init_flow s d"
           "res_correct fw bw"
           "\<forall> v \<in> \<V>. ex_get x v = (\<Sum> d \<in> \<delta>\<^sup>- v \<inter> \<E>. init_flow s d) - (\<Sum> d \<in> \<delta>\<^sup>+ v \<inter> \<E>. init_flow s d)"
    by (auto simp add: init_inv_def res_correct_def)
  note agree = init_flow_agree[OF I(4)]
  have "\<And> v. \<delta>\<^sup>- v \<inter> \<E> = \<delta>\<^sup>- v" "\<And> v. \<delta>\<^sup>+ v \<inter> \<E> = \<delta>\<^sup>+ v"
    by (auto simp add: delta_minus_def delta_plus_def)
  hence exs: "\<And> v. v \<in> \<V> \<Longrightarrow> ex_get x v = ex (emap_get bw) v"
    using I(6) agree(1) by (simp add: ex_def)
  define l where "l = label_upd label_init s num_verts"
  define cnt where "cnt = count_upd (count_upd count_init 0 (num_verts - 1)) num_verts 1"
  have n: "card \<V> \<ge> 2"
    using card_V_ge_2[OF net_assms] .
  have l: "label_invar l" "label_get l = init_labels s"
    using label_map.fixed_univ_map_upd_invar[OF init_adts(4) s_in_V]
          label_map.fixed_univ_map_upd[OF init_adts(4) s_in_V] init_adts(5)
    by (simp_all add: l_def init_labels_def num_verts)
  have k: "(0::nat) \<in> {..<2 * card \<V>}" "num_verts \<in> {..<2 * card \<V>}"
    using n by (simp_all add: num_verts)
  have cnt: "count_invar cnt" "count_get cnt = ((\<lambda> k. 0)(0 := card \<V> - 1))(card \<V> := 1)"
    using count_map.fixed_univ_map_upd_invar[OF count_map.fixed_univ_map_upd_invar[OF init_adts(6) k(1)] k(2)]
          count_map.fixed_univ_map_upd[OF count_map.fixed_univ_map_upd_invar[OF init_adts(6) k(1)] k(2)]
          count_map.fixed_univ_map_upd[OF init_adts(6) k(1)] init_adts(7)
    by (simp_all add: cnt_def num_verts)
  have cc: "counts_correct l cnt"
    unfolding counts_correct_def
  proof(intro allI impI)
    fix k
    assume "k < 2 * card \<V>"
    show "count_get cnt k = card {w. w \<in> \<V> \<and> label_get l w = k}"
    proof(cases "k = card \<V>")
      case True
      have "{w. w \<in> \<V> \<and> label_get l w = k} = {s}"
        using True s_in_V n by (auto simp add: l(2) init_labels_def)
      thus ?thesis
        using True by (simp add: cnt(2))
    next
      case False
      note F = this
      show ?thesis
      proof(cases "k = 0")
        case True
        have "{w. w \<in> \<V> \<and> label_get l w = k} = \<V> - {s}"
          using True n by (auto simp add: l(2) init_labels_def)
        thus ?thesis
          using True F \<V>_finite s_in_V by (simp add: cnt(2))
      next
        case False
        have e: "{w. w \<in> \<V> \<and> label_get l w = k} = {}"
          using False F by (auto simp add: l(2) init_labels_def)
        show ?thesis
          unfolding e using False F by (simp add: cnt(2))
      qed
    qed
  qed
  have st: "init_state = \<lparr>pr_fwd = fw, pr_bwd = bw, pr_excess = x, pr_labels = l, pr_counts = cnt,
                          pr_out = out_init, pr_in = in_init,
                          pr_ctx = init_ctx fw bw x l out_init in_init\<rparr>"
    using es(3) fold by (simp add: init_state_def Let_def l_def cnt_def)
  have og: "out_invar out_init" "\<And> u. u \<in> \<V> \<Longrightarrow> out_abstract out_init u = \<delta>\<^sup>+ u"
    using init_adts(8) by (simp_all add: out_graph_inv_def)
  have ig: "in_invar in_init" "\<And> u. u \<in> \<V> \<Longrightarrow> in_abstract in_init u = \<delta>\<^sup>- u"
    using init_adts(9) by (simp_all add: in_graph_inv_def)
  show inv: "invar_state init_state"
    by (rule invar_stateI)
       (use I exs l cnt(1) cc og ig agree init_labels_height_bounded[OF net_assms] in \<open>simp_all add: st\<close>)
  show "ctx_invar init_state"
    using init_ctx[OF inv] I(4) l(2) by (simp add: st)
qed

subsubsection \<open>Correctness\<close>

theorem push_relabel_correct: "is_max_flow s t (emap_get push_relabel)"
proof-
  note lp = push_relabel_loop_props[OF init_state_props]
  have "push_relabel = pr_bwd (push_relabel_loop init_state)"
    using push_relabel_loop_impl_same[OF lp(1)] by (simp add: push_relabel_def)
  moreover have "is_max_flow s t (flow_abs (push_relabel_loop init_state))"
    using no_active_max_flow[OF net_assms invar_stateD(8)[OF lp(2)] invar_stateD(9)[OF lp(2)] lp(3)] .
  ultimately show ?thesis
    by simp
qed

end

end
