theory Push_Relabel_Generic_Imperative
  imports
    Push_Relabel_Generic
    Data_Structures.Fixed_Univ_Map_Specs_Imp
    Data_Structures.Iterable_Set_Reset_To_Specs_Imp
    Data_Structures.Real_Embedding
begin

section \<open>Imperative Refinement of the Generic Push-Relabel Algorithm\<close>

text \<open>The operations of @{locale push_relabel_ops} are implemented once more, now on imperative
      data structures given by their Hoare triples: the residual capacities, the capacities and
      the excesses are maps whose values are read into the reals by an embedding @{term h}, the
      labels and the counts are maps holding natural numbers, and the outgoing and ingoing edges
      are indexed iterators with jumping. The endpoints of an edge are read from a data structure
      as well, by @{term fst_imp} and @{term snd_imp}. All operations work in place; the handles of the data
      structures are fixed when the algorithm starts and never change. Nothing is allocated.

      The programs follow the functional operations step by step, so every Hoare triple says that
      a program computes its functional counterpart.\<close>

record ('fi, 'xi, 'li, 'ci, 'gi, 'ei, 'e) pr_imp =
  pi_fwd :: 'fi
  pi_bwd :: 'fi
  pi_caps :: 'fi
  pi_ex :: 'xi
  pi_lab :: 'li
  pi_cnt :: 'ci
  pi_out :: 'gi
  pi_in :: 'gi
  pi_ends :: 'ei
  pi_mf :: "bool ref"
  pi_mk :: "nat ref"
  pi_md :: "'e ref"

subsection \<open>The Programs\<close>

text \<open>The code locale fixes only the imperative operations of the data structures, so that it
      can be interpreted globally.\<close>

locale push_relabel_ops_imp_code =
  fixes fst_imp snd_imp :: "'ei \<Rightarrow> 'e::heap \<Rightarrow> 'v::heap Heap"
    and s t :: 'v
    and num_verts :: nat
    and emap_get_imp :: "'fi \<Rightarrow> 'e \<Rightarrow> 'n::{linordered_idom, heap} Heap"
    and emap_upd_imp :: "'fi \<Rightarrow> 'e \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and ex_get_imp :: "'xi \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and ex_upd_imp :: "'xi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and label_get_imp :: "'li \<Rightarrow> 'v \<Rightarrow> nat Heap"
    and label_upd_imp :: "'li \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> unit Heap"
    and count_get_imp :: "'ci \<Rightarrow> nat \<Rightarrow> nat Heap"
    and count_upd_imp :: "'ci \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
    and out_current_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e Heap"
    and out_has_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and out_move_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and out_reset_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and out_reset_to_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e \<Rightarrow> unit Heap"
    and in_current_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e Heap"
    and in_has_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and in_move_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and in_reset_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and in_reset_to_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e \<Rightarrow> unit Heap"
    and gap_fold_imp :: "'li \<Rightarrow> nat \<Rightarrow> ('v \<Rightarrow> unit Heap) \<Rightarrow> unit Heap"
    and edge_fold_imp :: "'gi \<Rightarrow> ('e \<Rightarrow> unit Heap) \<Rightarrow> unit Heap"
begin

definition "admissible_fwd_imp Ei Fi Li d = do {
   c \<leftarrow> emap_get_imp Fi d;
   if 0 < c then do {
     u \<leftarrow> fst_imp Ei d;
     v \<leftarrow> snd_imp Ei d;
     a \<leftarrow> label_get_imp Li u;
     b \<leftarrow> label_get_imp Li v;
     return (a = b + 1) }
   else return False }"

definition "admissible_bwd_imp Ei Bi Li d = do {
   c \<leftarrow> emap_get_imp Bi d;
   if 0 < c then do {
     u \<leftarrow> fst_imp Ei d;
     v \<leftarrow> snd_imp Ei d;
     a \<leftarrow> label_get_imp Li v;
     b \<leftarrow> label_get_imp Li u;
     return (a = b + 1) }
   else return False }"

text \<open>The endpoints \<open>u\<close> and \<open>v\<close> of \<open>d\<close> are read once by the caller.\<close>

definition "augment_imp d u v \<delta> Si = do {
   a \<leftarrow> emap_get_imp (pi_fwd Si) d;
   emap_upd_imp (pi_fwd Si) d (a - \<delta>);
   b \<leftarrow> emap_get_imp (pi_bwd Si) d;
   emap_upd_imp (pi_bwd Si) d (b + \<delta>);
   x \<leftarrow> ex_get_imp (pi_ex Si) u;
   ex_upd_imp (pi_ex Si) u (x - \<delta>);
   y \<leftarrow> ex_get_imp (pi_ex Si) v;
   ex_upd_imp (pi_ex Si) v (y + \<delta>) }"

definition "push_fwd_imp d Si = do {
   u \<leftarrow> fst_imp (pi_ends Si) d;
   v \<leftarrow> snd_imp (pi_ends Si) d;
   x \<leftarrow> ex_get_imp (pi_ex Si) u;
   c \<leftarrow> emap_get_imp (pi_fwd Si) d;
   augment_imp d u v (min x c) Si }"

definition "push_bwd_imp d Si = do {
   u \<leftarrow> fst_imp (pi_ends Si) d;
   v \<leftarrow> snd_imp (pi_ends Si) d;
   x \<leftarrow> ex_get_imp (pi_ex Si) v;
   c \<leftarrow> emap_get_imp (pi_bwd Si) d;
   augment_imp d u v (- min x c) Si }"

partial_function (heap) skip_scan_imp ::
  "('gi \<Rightarrow> 'v \<Rightarrow> bool Heap) \<Rightarrow> ('gi \<Rightarrow> 'v \<Rightarrow> 'e Heap) \<Rightarrow> ('gi \<Rightarrow> 'v \<Rightarrow> unit Heap) \<Rightarrow>
   ('e \<Rightarrow> bool Heap) \<Rightarrow> 'v \<Rightarrow> 'gi \<Rightarrow> unit Heap" where
  "skip_scan_imp has cur move adm u Ci = do {
     b \<leftarrow> has Ci u;
     if b then do {
       e \<leftarrow> cur Ci u;
       a \<leftarrow> adm e;
       if a then return () else do { move Ci u; skip_scan_imp has cur move adm u Ci } }
     else return () }"

definition "skip_imp u Si = do {
   skip_scan_imp out_has_imp out_current_imp out_move_imp
     (admissible_fwd_imp (pi_ends Si) (pi_fwd Si) (pi_lab Si)) u (pi_out Si);
   b \<leftarrow> out_has_imp (pi_out Si) u;
   if b then return ()
   else skip_scan_imp in_has_imp in_current_imp in_move_imp
          (admissible_bwd_imp (pi_ends Si) (pi_bwd Si) (pi_lab Si)) u (pi_in Si) }"

definition "move_imp u Si = do {
   b \<leftarrow> out_has_imp (pi_out Si) u;
   if b then out_move_imp (pi_out Si) u else in_move_imp (pi_in Si) u }"

definition "advance_imp u Si = do { move_imp u Si; skip_imp u Si }"

definition "change_label_imp v k' Si = do {
   k \<leftarrow> label_get_imp (pi_lab Si) v;
   c \<leftarrow> count_get_imp (pi_cnt Si) k;
   count_upd_imp (pi_cnt Si) k (c - 1);
   label_upd_imp (pi_lab Si) v k';
   c' \<leftarrow> count_get_imp (pi_cnt Si) k';
   count_upd_imp (pi_cnt Si) k' (c' + 1) }"

text \<open>A relabelling scan improves the minimum held in the references of the state in place.\<close>

definition "min_set_imp Si k d = do { pi_mf Si := True; pi_mk Si := k; pi_md Si := d }"

partial_function (heap) min_scan_imp ::
  "('gi \<Rightarrow> 'v \<Rightarrow> bool Heap) \<Rightarrow> ('gi \<Rightarrow> 'v \<Rightarrow> 'e Heap) \<Rightarrow> ('gi \<Rightarrow> 'v \<Rightarrow> unit Heap) \<Rightarrow> 'fi \<Rightarrow>
   ('e \<Rightarrow> 'v Heap) \<Rightarrow> 'v \<Rightarrow> 'gi \<Rightarrow> ('fi, 'xi, 'li, 'ci, 'gi, 'ei, 'e) pr_imp \<Rightarrow> unit Heap" where
  "min_scan_imp has cur move Ri endp u Ci Si = do {
     b \<leftarrow> has Ci u;
     if b then do {
       d \<leftarrow> cur Ci u;
       r \<leftarrow> emap_get_imp Ri d;
       if 0 < r then do {
         w \<leftarrow> endp d;
         k \<leftarrow> label_get_imp (pi_lab Si) w;
         move Ci u;
         f \<leftarrow> !(pi_mf Si);
         k' \<leftarrow> !(pi_mk Si);
         if \<not> f \<or> k < k'
         then do { min_set_imp Si k d; min_scan_imp has cur move Ri endp u Ci Si }
         else min_scan_imp has cur move Ri endp u Ci Si }
       else do { move Ci u; min_scan_imp has cur move Ri endp u Ci Si } }
     else return () }"

definition "new_label_imp u Si = do {
   out_reset_imp (pi_out Si) u;
   pi_mf Si := False;
   min_scan_imp out_has_imp out_current_imp out_move_imp (pi_fwd Si) (snd_imp (pi_ends Si)) u
     (pi_out Si) Si;
   f1 \<leftarrow> !(pi_mf Si);
   m1 \<leftarrow> !(pi_mk Si);
   in_reset_imp (pi_in Si) u;
   min_scan_imp in_has_imp in_current_imp in_move_imp (pi_bwd Si) (fst_imp (pi_ends Si)) u
     (pi_in Si) Si;
   m \<leftarrow> !(pi_mk Si);
   d \<leftarrow> !(pi_md Si);
   if \<not> f1 \<or> m < m1
   then do { in_reset_to_imp (pi_in Si) u d; return (m + 1) }
   else do { out_reset_to_imp (pi_out Si) u d; in_reset_imp (pi_in Si) u; return (m + 1) } }"

definition "relabel_imp u Si = do { k' \<leftarrow> new_label_imp u Si; change_label_imp u k' Si }"

definition "gap_step_imp k Si v = do {
   lv \<leftarrow> label_get_imp (pi_lab Si) v;
   if k < lv \<and> lv < num_verts
   then do { change_label_imp v (num_verts + 1) Si; out_reset_imp (pi_out Si) v;
             in_reset_imp (pi_in Si) v }
   else return () }"

definition "gap_imp k Si = gap_fold_imp (pi_lab Si) k (gap_step_imp k Si)"

definition "relabel_gap_imp u Si = do {
   k \<leftarrow> label_get_imp (pi_lab Si) u;
   relabel_imp u Si;
   if k < num_verts
   then do { c \<leftarrow> count_get_imp (pi_cnt Si) k; if c = 0 then gap_imp k Si else return () }
   else return () }"

fun apply_op_imp where
  "apply_op_imp (Push_Fwd d) Si = push_fwd_imp d Si"
| "apply_op_imp (Push_Bwd d) Si = push_bwd_imp d Si"
| "apply_op_imp (Advance u) Si = advance_imp u Si"
| "apply_op_imp (Relabel u) Si = relabel_imp u Si"
| "apply_op_imp (Relabel_Gap u) Si = relabel_gap_imp u Si"
| "apply_op_imp Done Si = return ()"

definition "init_step_imp Si d = do {
   c \<leftarrow> emap_get_imp (pi_caps Si) d;
   u \<leftarrow> fst_imp (pi_ends Si) d;
   v \<leftarrow> snd_imp (pi_ends Si) d;
   if u = s \<and> v \<noteq> s
   then do {
     x \<leftarrow> ex_get_imp (pi_ex Si) s;
     ex_upd_imp (pi_ex Si) s (x - c);
     emap_upd_imp (pi_fwd Si) d 0;
     emap_upd_imp (pi_bwd Si) d c;
     y \<leftarrow> ex_get_imp (pi_ex Si) v;
     ex_upd_imp (pi_ex Si) v (y + c) }
   else do { emap_upd_imp (pi_fwd Si) d c; emap_upd_imp (pi_bwd Si) d 0 } }"

definition "init_imp Si = do {
   edge_fold_imp (pi_out Si) (init_step_imp Si);
   label_upd_imp (pi_lab Si) s num_verts;
   count_upd_imp (pi_cnt Si) 0 (num_verts - 1);
   count_upd_imp (pi_cnt Si) num_verts 1 }"

end

text \<open>The loop: the strategy decides on the next operation by @{term select_imp}, which updates
      its context @{term Ci} in place.\<close>

locale push_relabel_imp_code = push_relabel_ops_imp_code fst_imp snd_imp s t num_verts emap_get_imp
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
  fixes select_imp :: "'xc \<Rightarrow> ('fi, 'xi, 'li, 'ci, 'gi, 'ei, 'e) pr_imp \<Rightarrow> ('e, 'v) pr_op Heap"
    and init_ctx_imp :: "'xc \<Rightarrow> ('fi, 'xi, 'li, 'ci, 'gi, 'ei, 'e) pr_imp \<Rightarrow> unit Heap"
begin

partial_function (heap) push_relabel_loop_imp where
  "push_relabel_loop_imp Ci Si = do {
     op \<leftarrow> select_imp Ci Si;
     if op = Done then return ()
     else do { apply_op_imp op Si; push_relabel_loop_imp Ci Si } }"

definition "push_relabel_imp Ci Si = do {
   init_imp Si;
   init_ctx_imp Ci Si;
   push_relabel_loop_imp Ci Si }"

end

subsection \<open>Correctness of the Operations\<close>

text \<open>The data structures are given by their specifications. The map on the edges holds both
      residual capacities and the capacities, the map on the vertices the excesses; their values
      are read by @{term h}. The labels and counts are stored as they are.

      The enumeration of the vertices of a gap is specified in terms of the label map alone: if
      the step @{term g} changes the label map of the accumulator only by lifting the visited
      vertex to a label of at least the number of vertices, and @{term g_imp} implements it with
      a frame @{term R} for the rest of the accumulator, then @{term gap_fold_imp} implements
      @{term gap_fold}. Likewise, @{term edge_fold_imp} implements @{term edge_fold} for every
      step that preserves some invariant; it may read the outgoing iterator.\<close>

locale push_relabel_ops_imp =
  push_relabel_ops_correct where fst = fst and snd = snd +
  real_embedding h +
  push_relabel_ops_imp_code fst_imp snd_imp s t num_verts emap_get_imp emap_upd_imp ex_get_imp ex_upd_imp
    label_get_imp label_upd_imp count_get_imp count_upd_imp out_current_imp out_has_imp
    out_move_imp out_reset_imp out_reset_to_imp in_current_imp in_has_imp in_move_imp in_reset_imp
    in_reset_to_imp gap_fold_imp edge_fold_imp +
  emap_imp: fixed_univ_map_imp \<E> emap_invar emap_upd emap_get h emap_assn emap_upd_imp emap_get_imp +
  ex_imp: fixed_univ_map_imp \<V> ex_invar ex_upd ex_get h ex_assn ex_upd_imp ex_get_imp +
  label_imp: fixed_univ_map_imp \<V> label_invar label_upd label_get "id :: nat \<Rightarrow> nat" label_assn
    label_upd_imp label_get_imp +
  count_imp: fixed_univ_map_imp "{..<2 * card \<V>}" count_invar count_upd count_get
    "id :: nat \<Rightarrow> nat" count_assn count_upd_imp count_get_imp +
  out_imp: indexed_iterable_set_reset_to_imp out_invar out_abstract out_current out_has out_iterated
    out_remaining out_move out_reset \<V> out_assn out_current_imp out_has_imp out_move_imp
    out_reset_imp out_reset_to out_reset_to_imp +
  in_imp: indexed_iterable_set_reset_to_imp in_invar in_abstract in_current in_has in_iterated
    in_remaining in_move in_reset \<V> in_assn in_current_imp in_has_imp in_move_imp
    in_reset_imp in_reset_to in_reset_to_imp
  for fst snd :: "'e::heap \<Rightarrow> 'v::heap" and fst_imp snd_imp :: "'ei \<Rightarrow> 'e \<Rightarrow> 'v Heap"
  and h :: "'n::{linordered_idom, heap} \<Rightarrow> real"
  and emap_get_imp :: "'fi \<Rightarrow> 'e \<Rightarrow> 'n Heap" and emap_upd_imp
  and ex_get_imp :: "'xi \<Rightarrow> 'v \<Rightarrow> 'n Heap" and ex_upd_imp
  and label_get_imp :: "'li \<Rightarrow> 'v \<Rightarrow> nat Heap" and label_upd_imp
  and count_get_imp :: "'ci \<Rightarrow> nat \<Rightarrow> nat Heap" and count_upd_imp
  and out_current_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'e Heap" and out_has_imp out_move_imp out_reset_imp
  and out_reset_to_imp and in_current_imp in_has_imp in_move_imp in_reset_imp in_reset_to_imp
  and gap_fold_imp edge_fold_imp
  and emap_assn ex_assn label_assn count_assn out_assn in_assn +
  fixes ends_assn :: "'ei \<Rightarrow> assn"
  assumes fst_imp_rule:
    "\<And> e Ei. e \<in> \<E> \<Longrightarrow> <ends_assn Ei> fst_imp Ei e <\<lambda>u. ends_assn Ei * \<up>(u = fst e)>"
  and snd_imp_rule:
    "\<And> e Ei. e \<in> \<E> \<Longrightarrow> <ends_assn Ei> snd_imp Ei e <\<lambda>v. ends_assn Ei * \<up>(v = snd e)>"
  and gap_fold_imp_rule:
    "\<And> l k g g_imp R r Li.
       \<lbrakk>label_invar l;
        \<And> acc v. \<lbrakk>label_invar (prod.fst acc); v \<in> \<V>; k < label_get (prod.fst acc) v;
                   label_get (prod.fst acc) v < card \<V>\<rbrakk> \<Longrightarrow>
          (\<exists> k'. card \<V> \<le> k' \<and> prod.fst (g acc v) = label_upd (prod.fst acc) v k') \<and>
          <label_assn (prod.fst acc) Li * R (prod.snd acc)> g_imp v
          <\<lambda>_. label_assn (prod.fst (g acc v)) Li * R (prod.snd (g acc v))>\<rbrakk> \<Longrightarrow>
       <label_assn l Li * R r> gap_fold_imp Li k g_imp
       <\<lambda>_. label_assn (prod.fst (gap_fold l k g (l, r))) Li * R (prod.snd (gap_fold l k g (l, r)))>"
  and edge_fold_imp_rule:
    "\<And> g g_imp P R acc og Oi.
       \<lbrakk>out_invar og; P acc;
        \<And> acc e. \<lbrakk>P acc; e \<in> \<E>\<rbrakk> \<Longrightarrow>
          P (g acc e) \<and> <R acc> g_imp e <\<lambda>_. R (g acc e)>\<rbrakk> \<Longrightarrow>
       <out_assn og Oi * R acc> edge_fold_imp Oi g_imp <\<lambda>_. out_assn og Oi * R (edge_fold g acc)>"
begin

text \<open>The minimum of a relabelling scan is kept in three references: a flag telling whether a
      residual edge was found, the least label and the edge reaching it. Between the scans they
      hold arbitrary values.\<close>

definition min_assn :: "(nat \<times> 'e) option \<Rightarrow> ('fi, 'xi, 'li, 'ci, 'gi, 'ei, 'e) pr_imp \<Rightarrow> assn" where
  "min_assn mb Si =
     (\<exists>\<^sub>A f k d. pi_mf Si \<mapsto>\<^sub>r f * pi_mk Si \<mapsto>\<^sub>r k * pi_md Si \<mapsto>\<^sub>r d *
                 \<up>(mb = (if f then Some (k, d) else None)))"

definition "min_scratch_assn Si = (\<exists>\<^sub>A mb. min_assn mb Si)"

lemma min_clear_rule: "<min_assn mb Si> pi_mf Si := False <\<lambda>_. min_assn None Si>"
  unfolding min_assn_def by sep_auto

lemma min_set_rule: "<min_assn mb Si> min_set_imp Si k d <\<lambda>_. min_assn (Some (k, d)) Si>"
  unfolding min_set_imp_def min_assn_def by sep_auto

lemma min_get_flag_rule: "<min_assn mb Si> !(pi_mf Si) <\<lambda>f. min_assn mb Si * \<up>(f = (mb \<noteq> None))>"
  unfolding min_assn_def by sep_auto

lemma min_get_label_rule:
  "<min_assn mb Si> !(pi_mk Si) <\<lambda>k. min_assn mb Si * \<up>(\<forall> k0 d0. mb = Some (k0, d0) \<longrightarrow> k = k0)>"
  unfolding min_assn_def by sep_auto

lemma min_get_edge_rule:
  "<min_assn mb Si> !(pi_md Si) <\<lambda>d. min_assn mb Si * \<up>(\<forall> k0 d0. mb = Some (k0, d0) \<longrightarrow> d = d0)>"
  unfolding min_assn_def by sep_auto

definition state_assn where
  "state_assn st Si =
     emap_assn (pr_fwd st) (pi_fwd Si) * emap_assn (pr_bwd st) (pi_bwd Si) *
     emap_assn caps (pi_caps Si) * ex_assn (pr_excess st) (pi_ex Si) *
     label_assn (pr_labels st) (pi_lab Si) * count_assn (pr_counts st) (pi_cnt Si) *
     out_assn (pr_out st) (pi_out Si) * in_assn (pr_in st) (pi_in Si) * ends_assn (pi_ends Si) *
     min_scratch_assn Si"

lemma state_assn_ctx[simp]: "state_assn (st\<lparr>pr_ctx := c\<rparr>) = state_assn st"
  by (simp add: state_assn_def fun_eq_iff)

lemma edge_verts: "d \<in> \<E> \<Longrightarrow> fst d \<in> \<V> \<and> snd d \<in> \<V>"
  by (auto intro: fst_E_V snd_E_V)

lemma fst_state_rule:
  "d \<in> \<E> \<Longrightarrow> <state_assn st Si> fst_imp (pi_ends Si) d <\<lambda>u. state_assn st Si * \<up>(u = fst d)>"
  unfolding state_assn_def by (sep_auto heap: fst_imp_rule)

lemma snd_state_rule:
  "d \<in> \<E> \<Longrightarrow> <state_assn st Si> snd_imp (pi_ends Si) d <\<lambda>v. state_assn st Si * \<up>(v = snd d)>"
  unfolding state_assn_def by (sep_auto heap: snd_imp_rule)

subsubsection \<open>Pushing\<close>

lemma admissible_fwd_imp_rule:
  assumes "emap_invar fw" "label_invar l" "d \<in> \<E>"
  shows "<ends_assn Ei * emap_assn fw Fi * label_assn l Li> admissible_fwd_imp Ei Fi Li d
         <\<lambda>r. ends_assn Ei * emap_assn fw Fi * label_assn l Li *
              \<up>(r = admissible_fwd_impl fw l d)>"
  using assms edge_verts[OF assms(3)]
  unfolding admissible_fwd_imp_def admissible_fwd_impl_def
  by (sep_auto heap: fst_imp_rule snd_imp_rule simp: eq_commute[of "h _"])

lemma admissible_bwd_imp_rule:
  assumes "emap_invar bw" "label_invar l" "d \<in> \<E>"
  shows "<ends_assn Ei * emap_assn bw Bi * label_assn l Li> admissible_bwd_imp Ei Bi Li d
         <\<lambda>r. ends_assn Ei * emap_assn bw Bi * label_assn l Li *
              \<up>(r = admissible_bwd_impl bw l d)>"
  using assms edge_verts[OF assms(3)]
  unfolding admissible_bwd_imp_def admissible_bwd_impl_def
  by (sep_auto heap: fst_imp_rule snd_imp_rule simp: eq_commute[of "h _"])

lemma augment_imp_rule:
  assumes "emap_invar (pr_fwd st)" "emap_invar (pr_bwd st)" "ex_invar (pr_excess st)" "d \<in> \<E>"
  shows "<state_assn st Si> augment_imp d (fst d) (snd d) \<delta> Si
         <\<lambda>_. state_assn (case augment_impl d (h \<delta>) (pr_fwd st) (pr_bwd st) (pr_excess st) of
                           (fw', bw', x') \<Rightarrow> st\<lparr>pr_fwd := fw', pr_bwd := bw', pr_excess := x'\<rparr>) Si>"
  using assms edge_verts[OF assms(4)]
  unfolding state_assn_def augment_imp_def augment_impl_def Let_def
  by (sep_auto simp: ex_map.fixed_univ_map_upd_invar ex_map.fixed_univ_map_upd h_add)

lemma ex_get_state_rule:
  assumes "ex_invar (pr_excess st)" "v \<in> \<V>"
  shows "<state_assn st Si> ex_get_imp (pi_ex Si) v
         <\<lambda>x. state_assn st Si * \<up>(ex_get (pr_excess st) v = h x)>"
  using assms unfolding state_assn_def by sep_auto

lemma fwd_get_state_rule:
  assumes "emap_invar (pr_fwd st)" "d \<in> \<E>"
  shows "<state_assn st Si> emap_get_imp (pi_fwd Si) d
         <\<lambda>x. state_assn st Si * \<up>(emap_get (pr_fwd st) d = h x)>"
  using assms unfolding state_assn_def by sep_auto

lemma bwd_get_state_rule:
  assumes "emap_invar (pr_bwd st)" "d \<in> \<E>"
  shows "<state_assn st Si> emap_get_imp (pi_bwd Si) d
         <\<lambda>x. state_assn st Si * \<up>(emap_get (pr_bwd st) d = h x)>"
  using assms unfolding state_assn_def by sep_auto

lemma push_fwd_imp_rule:
  assumes "invar_basic st" "d \<in> \<E>"
  shows "<state_assn st Si> push_fwd_imp d Si <\<lambda>_. state_assn (push_fwd_impl d st) Si>"
proof-
  have I: "emap_invar (pr_fwd st)" "emap_invar (pr_bwd st)" "ex_invar (pr_excess st)"
    using assms(1) by (simp_all add: invar_basic_def)
  show ?thesis
    unfolding push_fwd_imp_def
    using edge_verts[OF assms(2)]
    by (sep_auto heap: fst_state_rule[OF assms(2)] snd_state_rule[OF assms(2)]
                       ex_get_state_rule[OF I(3)] fwd_get_state_rule[OF I(1) assms(2)]
                       augment_imp_rule[OF I assms(2)]
                 simp: push_fwd_impl_def Let_def)
qed

lemma push_bwd_imp_rule:
  assumes "invar_basic st" "d \<in> \<E>"
  shows "<state_assn st Si> push_bwd_imp d Si <\<lambda>_. state_assn (push_bwd_impl d st) Si>"
proof-
  have I: "emap_invar (pr_fwd st)" "emap_invar (pr_bwd st)" "ex_invar (pr_excess st)"
    using assms(1) by (simp_all add: invar_basic_def)
  show ?thesis
    unfolding push_bwd_imp_def
    using edge_verts[OF assms(2)]
    by (sep_auto heap: fst_state_rule[OF assms(2)] snd_state_rule[OF assms(2)]
                       ex_get_state_rule[OF I(3)] bwd_get_state_rule[OF I(2) assms(2)]
                       augment_imp_rule[OF I assms(2)]
                 simp: push_bwd_impl_def Let_def)
qed

subsubsection \<open>Advancing\<close>

lemma skip_scan_imp_rule:
  assumes it: "indexed_iterable_set_imp it_invar it_abstract cur has it_iterated it_remaining move
                 it_reset \<V> A cur_i has_i move_i reset_i"
      and "it_invar C" "u \<in> \<V>" "finite (it_remaining C u)"
      and "\<And> e. e \<in> it_abstract C u \<Longrightarrow> <R> adm_imp e <\<lambda>r. R * \<up>(r = adm e)>"
  shows "<A C Ci * R> skip_scan_imp has_i cur_i move_i adm_imp u Ci
         <\<lambda>_. A (skip_scan has cur move adm u C) Ci * R>"
proof-
  interpret it: indexed_iterable_set_imp it_invar it_abstract cur has it_iterated it_remaining move
                 it_reset \<V> A cur_i has_i move_i reset_i
    by (rule it)
  show ?thesis
    using assms(2-5)
  proof(induction "card (it_remaining C u)" arbitrary: C rule: less_induct)
    case less
    show ?case
    proof(cases "has C u")
      case False
      show ?thesis
        by (subst skip_scan_imp.simps, subst skip_scan.simps)
           (sep_auto heap: it.idx_has_rule[OF less.prems(1,2)] simp: False)
    next
      case True
      have ne: "it_remaining C u \<noteq> {}"
        using it.idx_has[OF less.prems(1,2)] True by simp
      have cr: "cur C u \<in> it_remaining C u"
        using it.idx_current[OF less.prems(1,2) ne] .
      have ca: "cur C u \<in> it_abstract C u"
        using cr it.idx_partition_union[OF less.prems(1,2)] by auto
      note ad = less.prems(4)[OF ca]
      show ?thesis
      proof(cases "adm (cur C u)")
        case True
        thus ?thesis
          by (subst skip_scan_imp.simps, subst skip_scan.simps)
             (sep_auto heap: it.idx_has_rule[OF less.prems(1,2)]
                             it.idx_current_rule[OF less.prems(1,2) ne] ad simp: \<open>has C u\<close>)
      next
        case False
        define C' where "C' = move C u"
        have inv': "it_invar C'"
          using it.idx_move_invar[OF less.prems(1,2)] by (simp add: C'_def)
        have rem': "it_remaining C' u = it_remaining C u - {cur C u}"
          using it.idx_move_remaining[OF less.prems(1,2) ne] by (simp add: C'_def)
        have lt: "card (it_remaining C' u) < card (it_remaining C u)"
          unfolding rem' using less.prems(3) cr by (rule card_Diff1_less)
        have fin': "finite (it_remaining C' u)"
          using rem' less.prems(3) by simp
        have abs': "it_abstract C' u = it_abstract C u"
          using it.idx_move_abstract[OF less.prems(1,2) ne] by (simp add: C'_def)
        have adm': "\<And> e. e \<in> it_abstract C' u \<Longrightarrow> <R> adm_imp e <\<lambda>r. R * \<up>(r = adm e)>"
          using less.prems(4) abs' by simp
        note IH = less.hyps[OF lt inv' less.prems(2) fin' adm', unfolded C'_def]
        show ?thesis
          by (subst skip_scan_imp.simps, subst skip_scan.simps)
             (sep_auto heap: it.idx_has_rule[OF less.prems(1,2)]
                             it.idx_current_rule[OF less.prems(1,2) ne] ad
                             it.idx_move_rule[OF less.prems(1,2) ne] IH
                       simp: \<open>has C u\<close> False)
      qed
    qed
  qed
qed

lemma invar_basic_iters:
  assumes "invar_basic st" "u \<in> \<V>"
  shows "emap_invar (pr_fwd st)" "emap_invar (pr_bwd st)" "ex_invar (pr_excess st)"
        "label_invar (pr_labels st)" "count_invar (pr_counts st)"
        "out_invar (pr_out st)" "in_invar (pr_in st)"
        "out_abstract (pr_out st) u = \<delta>\<^sup>+ u" "in_abstract (pr_in st) u = \<delta>\<^sup>- u"
        "finite (out_remaining (pr_out st) u)" "finite (in_remaining (pr_in st) u)"
proof-
  have I: "out_invar (pr_out st)" "in_invar (pr_in st)"
          "out_abstract (pr_out st) u = \<delta>\<^sup>+ u" "in_abstract (pr_in st) u = \<delta>\<^sup>- u"
    using assms by (auto simp add: invar_basic_def out_graph_inv_def in_graph_inv_def)
  show "emap_invar (pr_fwd st)" "emap_invar (pr_bwd st)" "ex_invar (pr_excess st)"
       "label_invar (pr_labels st)" "count_invar (pr_counts st)"
    using assms(1) by (simp_all add: invar_basic_def)
  show "out_invar (pr_out st)" "in_invar (pr_in st)"
       "out_abstract (pr_out st) u = \<delta>\<^sup>+ u" "in_abstract (pr_in st) u = \<delta>\<^sup>- u"
    using I by simp_all
  have "out_remaining (pr_out st) u \<subseteq> \<delta>\<^sup>+ u" "in_remaining (pr_in st) u \<subseteq> \<delta>\<^sup>- u"
    using outg.idx_partition_union[OF I(1) assms(2)] ing.idx_partition_union[OF I(2) assms(2)] I(3,4)
    by auto
  thus "finite (out_remaining (pr_out st) u)" "finite (in_remaining (pr_in st) u)"
    using finite_delta finite_subset by blast+
qed

lemma skip_imp_rule:
  assumes "invar_basic st" "u \<in> \<V>"
  shows "<state_assn st Si> skip_imp u Si <\<lambda>_. state_assn (skip_impl u st) Si>"
proof-
  note I = invar_basic_iters[OF assms]
  define og' where "og' = skip_scan out_has out_current out_move
                            (admissible_fwd_impl (pr_fwd st) (pr_labels st)) u (pr_out st)"
  define ig' where "ig' = skip_scan in_has in_current in_move
                            (admissible_bwd_impl (pr_bwd st) (pr_labels st)) u (pr_in st)"
  have og': "out_invar og'"
    using skip_scan_props(1)[OF outg.indexed_iterable_set_axioms I(6) assms(2) I(10) og'_def[symmetric]] .
  have a1: "\<And> e. e \<in> out_abstract (pr_out st) u \<Longrightarrow>
      <ends_assn (pi_ends Si) * emap_assn (pr_fwd st) (pi_fwd Si) * label_assn (pr_labels st) (pi_lab Si)>
        admissible_fwd_imp (pi_ends Si) (pi_fwd Si) (pi_lab Si) e
      <\<lambda>r. ends_assn (pi_ends Si) * emap_assn (pr_fwd st) (pi_fwd Si) *
           label_assn (pr_labels st) (pi_lab Si) *
           \<up>(r = admissible_fwd_impl (pr_fwd st) (pr_labels st) e)>"
    using I(8) by (intro admissible_fwd_imp_rule[OF I(1,4)]) (simp add: delta_plus_def)
  have a2: "\<And> e. e \<in> in_abstract (pr_in st) u \<Longrightarrow>
      <ends_assn (pi_ends Si) * emap_assn (pr_bwd st) (pi_bwd Si) * label_assn (pr_labels st) (pi_lab Si)>
        admissible_bwd_imp (pi_ends Si) (pi_bwd Si) (pi_lab Si) e
      <\<lambda>r. ends_assn (pi_ends Si) * emap_assn (pr_bwd st) (pi_bwd Si) *
           label_assn (pr_labels st) (pi_lab Si) *
           \<up>(r = admissible_bwd_impl (pr_bwd st) (pr_labels st) e)>"
    using I(9) by (intro admissible_bwd_imp_rule[OF I(2,4)]) (simp add: delta_minus_def)
  note s1 = skip_scan_imp_rule[OF out_imp.indexed_iterable_set_imp_axioms I(6) assms(2) I(10) a1]
  note s2 = skip_scan_imp_rule[OF in_imp.indexed_iterable_set_imp_axioms I(7) assms(2) I(11) a2]
  show ?thesis
  proof(cases "out_has og' u")
    case True
    have "skip_impl u st = st\<lparr>pr_out := og'\<rparr>"
      by (simp add: skip_impl_def Let_def og'_def[symmetric] True)
    thus ?thesis
      using og' True assms(2)
      unfolding skip_imp_def state_assn_def og'_def
      by (sep_auto heap: s1)
  next
    case False
    have "skip_impl u st = st\<lparr>pr_out := og', pr_in := ig'\<rparr>"
      by (simp add: skip_impl_def Let_def og'_def[symmetric] ig'_def[symmetric] False)
    thus ?thesis
      using og' False assms(2)
      unfolding skip_imp_def state_assn_def og'_def ig'_def
      by (sep_auto heap: s1 s2)
  qed
qed

lemma move_imp_rule:
  assumes "invar_basic st" "u \<in> \<V>" "current_res st u \<noteq> None"
  shows "<state_assn st Si> move_imp u Si <\<lambda>_. state_assn (move_impl u st) Si>"
proof(cases "out_has (pr_out st) u")
  case True
  note I = invar_basic_iters[OF assms(1,2)]
  have ne: "out_remaining (pr_out st) u \<noteq> {}"
    using outg.idx_has[OF I(6) assms(2)] True by simp
  show ?thesis
    unfolding move_imp_def state_assn_def
    by (sep_auto heap: out_imp.idx_has_rule[OF I(6) assms(2)] out_imp.idx_move_rule[OF I(6) assms(2) ne]
                 simp: True move_impl_def)
next
  case False
  note I = invar_basic_iters[OF assms(1,2)]
  have "in_has (pr_in st) u"
    using assms(3) False by (simp add: current_res_def split: if_splits)
  hence ne: "in_remaining (pr_in st) u \<noteq> {}"
    using ing.idx_has[OF I(7) assms(2)] by simp
  show ?thesis
    unfolding move_imp_def state_assn_def
    by (sep_auto heap: out_imp.idx_has_rule[OF I(6) assms(2)] in_imp.idx_move_rule[OF I(7) assms(2) ne]
                 simp: False move_impl_def)
qed

lemma advance_imp_rule:
  assumes "invar_state st" "u \<in> \<V>" "current_res st u = Some e"
          "\<not> admissible (flow_abs st) (labels_abs st) e"
  shows "<state_assn st Si> advance_imp u Si <\<lambda>_. state_assn (advance_impl u st) Si>"
proof-
  have b: "invar_basic st" "invar_basic (move_impl u st)"
    using assms(1) move_impl_props(1)[OF assms] by (simp_all add: invar_state_def)
  show ?thesis
    unfolding advance_imp_def advance_impl_def
    by (sep_auto heap: move_imp_rule[OF b(1) assms(2)] skip_imp_rule[OF b(2) assms(2)]
                 simp: assms(3))
qed

subsubsection \<open>Relabelling\<close>

lemma min_scan_imp_rule:
  assumes it: "indexed_iterable_set_imp it_invar it_abstract cur has it_iterated it_remaining move
                 it_reset \<V> A cur_i has_i move_i reset_i"
      and "it_invar C" "u \<in> \<V>" "finite (it_remaining C u)" "emap_invar r" "label_invar l"
      and "\<And> e. e \<in> it_abstract C u \<Longrightarrow> e \<in> \<E> \<and> endp e \<in> \<V>"
      and endp_imp: "\<And> e. e \<in> \<E> \<Longrightarrow>
             <ends_assn (pi_ends Si)> endp_imp e <\<lambda>v. ends_assn (pi_ends Si) * \<up>(v = endp e)>"
  shows "<A C Ci * emap_assn r Ri * label_assn l (pi_lab Si) * ends_assn (pi_ends Si) * min_assn mb Si>
         min_scan_imp has_i cur_i move_i Ri endp_imp u Ci Si
         <\<lambda>_. case min_scan has cur move r endp l u C mb of (C', mb') \<Rightarrow>
              A C' Ci * emap_assn r Ri * label_assn l (pi_lab Si) * ends_assn (pi_ends Si) *
              min_assn mb' Si>"
proof-
  interpret it: indexed_iterable_set_imp it_invar it_abstract cur has it_iterated it_remaining move
                 it_reset \<V> A cur_i has_i move_i reset_i
    by (rule it)
  show ?thesis
    using assms(2-7)
  proof(induction "card (it_remaining C u)" arbitrary: C mb rule: less_induct)
    case less
    show ?case
    proof(cases "has C u")
      case False
      have "min_scan has cur move r endp l u C mb = (C, mb)"
        using False by (simp add: min_scan.simps)
      thus ?thesis
        by (subst min_scan_imp.simps)
           (sep_auto heap: it.idx_has_rule[OF less.prems(1,2)] simp: False)
    next
      case True
      have ne: "it_remaining C u \<noteq> {}"
        using it.idx_has[OF less.prems(1,2)] True by simp
      define d where "d = cur C u"
      have cr: "d \<in> it_remaining C u"
        using it.idx_current[OF less.prems(1,2) ne] by (simp add: d_def)
      have dE: "d \<in> \<E>" "endp d \<in> \<V>"
        using cr it.idx_partition_union[OF less.prems(1,2)] less.prems(6) by auto
      define C' where "C' = move C u"
      have inv': "it_invar C'"
        using it.idx_move_invar[OF less.prems(1,2)] by (simp add: C'_def)
      have rem': "it_remaining C' u = it_remaining C u - {d}"
        using it.idx_move_remaining[OF less.prems(1,2) ne] by (simp add: C'_def d_def)
      have lt: "card (it_remaining C' u) < card (it_remaining C u)"
        unfolding rem' using less.prems(3) cr by (rule card_Diff1_less)
      have fin': "finite (it_remaining C' u)"
        using rem' less.prems(3) by simp
      have abs': "it_abstract C' u = it_abstract C u"
        using it.idx_move_abstract[OF less.prems(1,2) ne] by (simp add: C'_def)
      have prem': "\<And> e. e \<in> it_abstract C' u \<Longrightarrow> e \<in> \<E> \<and> endp e \<in> \<V>"
        using less.prems(6) abs' by simp
      note IH = less.hyps[OF lt inv' less.prems(2) fin' less.prems(4,5) prem']
      define imp where
        "imp = (0 < emap_get r d \<and> (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> label_get l (endp d) < k'))"
      have step: "min_scan has cur move r endp l u C mb =
                  min_scan has cur move r endp l u C' (if imp then Some (label_get l (endp d), d) else mb)"
        using True unfolding imp_def d_def C'_def by (subst min_scan.simps) (simp add: Let_def)
      have cnd: "\<And> f k'. f = (mb \<noteq> None) \<Longrightarrow> (\<forall> k0 d0. mb = Some (k0, d0) \<longrightarrow> k' = k0) \<Longrightarrow>
                   (\<not> f \<or> label_get l (endp d) < k') =
                   (case mb of None \<Rightarrow> True | Some (k', _) \<Rightarrow> label_get l (endp d) < k')"
        by (cases mb) auto
      show ?thesis
        unfolding step
        using True dE less.prems(4,5) cnd IH
        unfolding imp_def d_def C'_def
        by (subst min_scan_imp.simps)
           (sep_auto heap: it.idx_has_rule[OF less.prems(1,2)] it.idx_current_rule[OF less.prems(1,2) ne]
                           it.idx_move_rule[OF less.prems(1,2) ne] min_get_flag_rule min_get_label_rule
                           min_set_rule IH[unfolded C'_def] endp_imp
                     simp: eq_commute[of "h _"])
    qed
  qed
qed

lemma new_label_imp_rule:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "<state_assn st Si> new_label_imp u Si
         <\<lambda>k. case new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u of
               (og', ig', k') \<Rightarrow> state_assn (st\<lparr>pr_out := og', pr_in := ig'\<rparr>) Si * \<up>(k = k')>"
proof-
  note inv = invar_stateD[OF assms(1)]
  have u: "u \<in> \<V>"
    using assms(2) by (auto elim!: relabel_precondE active_vertexE)
  obtain og' ig' k' where
    nl: "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = (og', ig', k')"
    by (cases "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u") auto
  obtain og1 mb1 ig1 M d where
    scan1: "min_scan out_has out_current out_move (pr_fwd st) snd (pr_labels st) u
              (out_reset (pr_out st) u) None = (og1, mb1)" and
    scan2: "min_scan in_has in_current in_move (pr_bwd st) fst (pr_labels st) u
              (in_reset (pr_in st) u) mb1 = (ig1, Some (M, d))" and
    dA: "if (case mb1 of None \<Rightarrow> True | Some (m1, _) \<Rightarrow> M < m1)
         then d \<in> in_abstract ig1 u else d \<in> out_abstract og1 u"
    using new_label_props(10)[OF assms nl] by blast
  define og0 where "og0 = out_reset (pr_out st) u"
  define ig0 where "ig0 = in_reset (pr_in st) u"
  have og0: "out_invar og0" "out_remaining og0 u = \<delta>\<^sup>+ u" "out_abstract og0 u = \<delta>\<^sup>+ u"
    using outg.idx_reset_invar[OF inv(5) u] outg.idx_reset_remaining[OF inv(5) u] inv(11)[OF u]
          outg.idx_reset_abstract[OF inv(5) u]
    by (simp_all add: og0_def)
  have ig0: "in_invar ig0" "in_remaining ig0 u = \<delta>\<^sup>- u" "in_abstract ig0 u = \<delta>\<^sup>- u"
    using ing.idx_reset_invar[OF inv(15) u] ing.idx_reset_remaining[OF inv(15) u] inv(16)[OF u]
          ing.idx_reset_abstract[OF inv(15) u]
    by (simp_all add: ig0_def)
  have E0: "\<And> e. e \<in> out_abstract og0 u \<Longrightarrow> e \<in> \<E> \<and> snd e \<in> \<V>"
           "\<And> e. e \<in> in_abstract ig0 u \<Longrightarrow> e \<in> \<E> \<and> fst e \<in> \<V>"
    using og0(3) ig0(3) edge_verts by (auto simp add: delta_plus_def delta_minus_def)
  have fin0: "finite (out_remaining og0 u)" "finite (in_remaining ig0 u)"
    using og0(2) ig0(2) finite_delta by simp_all
  have e0: "map_option prod.fst None = min_opt {}"
    by (simp add: min_opt_def)
  note p1 = min_scan_props[OF outg.indexed_iterable_set_axioms og0(1) u fin0(1) finite.emptyI e0
                              scan1[folded og0_def]]
  note p2 = min_scan_props[OF ing.indexed_iterable_set_axioms ig0(1) u fin0(2)
                              finite_UnI[OF finite.emptyI scan_labels_finite[OF fin0(1)]] p1(4)
                              scan2[folded ig0_def]]
  note s1 = min_scan_imp_rule[where mb = None, OF out_imp.indexed_iterable_set_imp_axioms og0(1) u
                              fin0(1) inv(1,3) E0(1) snd_imp_rule, unfolded og0_def scan1 prod.case]
  note s2 = min_scan_imp_rule[where mb = mb1, OF in_imp.indexed_iterable_set_imp_axioms ig0(1) u
                              fin0(2) inv(13,3) E0(2) fst_imp_rule, unfolded ig0_def scan2 prod.case]
  show ?thesis
  proof(cases "case mb1 of None \<Rightarrow> True | Some (m1, _) \<Rightarrow> M < m1")
    case True
    have dI: "d \<in> in_abstract ig1 u"
      using dA True by simp
    have "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u =
          (og1, in_reset_to ig1 u d, M + 1)"
      using scan1 scan2 True by (simp add: new_label_def)
    thus ?thesis
      using True
      unfolding new_label_imp_def state_assn_def min_scratch_assn_def
      by (sep_auto heap: out_imp.idx_reset_rule[OF inv(5) u] min_clear_rule s1 min_get_flag_rule
                         min_get_label_rule in_imp.idx_reset_rule[OF inv(15) u] s2 min_get_edge_rule
                         in_imp.idx_reset_to_rule[OF p2(1) u dI]
                   split: option.splits)
  next
    case False
    have dO: "d \<in> out_abstract og1 u"
      using dA False by simp
    have "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u =
          (out_reset_to og1 u d, in_reset ig1 u, M + 1)"
      using scan1 scan2 False by (simp add: new_label_def)
    thus ?thesis
      using False
      unfolding new_label_imp_def state_assn_def min_scratch_assn_def
      by (sep_auto heap: out_imp.idx_reset_rule[OF inv(5) u] min_clear_rule s1 min_get_flag_rule
                         min_get_label_rule in_imp.idx_reset_rule[OF inv(15) u] s2 min_get_edge_rule
                         out_imp.idx_reset_to_rule[OF p1(1) u dO] in_imp.idx_reset_rule[OF p2(1) u]
                   split: option.splits)
  qed
qed

lemma change_label_imp_rule:
  assumes "label_invar (pr_labels st)" "count_invar (pr_counts st)" "v \<in> \<V>"
          "label_get (pr_labels st) v < 2 * card \<V>" "k' < 2 * card \<V>"
  shows "<state_assn st Si> change_label_imp v k' Si
         <\<lambda>_. case change_label (pr_labels st) (pr_counts st) v k' of
               (l', cnt') \<Rightarrow> state_assn (st\<lparr>pr_labels := l', pr_counts := cnt'\<rparr>) Si>"
  using assms
  unfolding change_label_imp_def change_label_def Let_def state_assn_def
  by (sep_auto simp: count_map.fixed_univ_map_upd_invar count_map.fixed_univ_map_upd)

lemma relabel_imp_rule:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "<state_assn st Si> relabel_imp u Si <\<lambda>_. state_assn (relabel_impl u st) Si>"
proof-
  note inv = invar_stateD[OF assms(1)]
  have u: "u \<in> \<V>"
    using assms(2) by (auto elim!: relabel_precondE active_vertexE)
  obtain og' ig' k' where
    nl: "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u = (og', ig', k')"
    by (cases "new_label (pr_fwd st) (pr_bwd st) (pr_labels st) (pr_out st) (pr_in st) u") auto
  obtain l' cnt' where cl: "change_label (pr_labels st) (pr_counts st) u k' = (l', cnt')"
    by (cases "change_label (pr_labels st) (pr_counts st) u k'") auto
  have st': "relabel_impl u st = st\<lparr>pr_out := og', pr_in := ig', pr_labels := l', pr_counts := cnt'\<rparr>"
    using nl cl by (simp add: relabel_impl_def)
  have kb: "k' < 2 * card \<V>"
    using relabel_bounds(2)[OF assms] new_label_props(9)[OF assms nl] by simp
  note c = change_label_imp_rule[of "st\<lparr>pr_out := og', pr_in := ig'\<rparr>" u k', simplified,
                                 OF inv(3,4) u relabel_bounds(1)[OF assms] kb, unfolded cl prod.case]
  show ?thesis
    unfolding relabel_imp_def st'
    by (sep_auto heap: new_label_imp_rule[OF assms, unfolded nl prod.case] c)
qed

subsubsection \<open>Gap Relabelling\<close>

text \<open>During the gap fold, the counts and the iterators form the frame of the label map.\<close>

definition "gap_frame_assn Si = (\<lambda> (cnt, og, ig).
   count_assn cnt (pi_cnt Si) * out_assn og (pi_out Si) * in_assn ig (pi_in Si) *
   \<up>(count_invar cnt \<and> out_invar og \<and> in_invar ig))"

lemma gap_step_imp_rule:
  assumes "label_invar (prod.fst acc)" "v \<in> \<V>" "k < label_get (prod.fst acc) v"
          "label_get (prod.fst acc) v < card \<V>"
  shows "(\<exists> k'. card \<V> \<le> k' \<and> prod.fst (gap_step k acc v) = label_upd (prod.fst acc) v k') \<and>
         <label_assn (prod.fst acc) (pi_lab Si) * gap_frame_assn Si (prod.snd acc)> gap_step_imp k Si v
         <\<lambda>_. label_assn (prod.fst (gap_step k acc v)) (pi_lab Si) *
              gap_frame_assn Si (prod.snd (gap_step k acc v))>"
proof-
  obtain l cnt og ig where acc: "acc = (l, cnt, og, ig)"
    by (cases acc) auto
  have lv: "label_invar l" "label_get l v < 2 * card \<V>" "num_verts + 1 < 2 * card \<V>"
           "k < label_get l v" "label_get l v < num_verts" "card \<V> \<le> num_verts + 1"
    using assms card_V_ge_2[OF net_assms] by (simp_all add: acc num_verts)
  have g: "gap_step k (l, cnt, og, ig) v =
           (case change_label l cnt v (num_verts + 1) of
              (l', cnt') \<Rightarrow> (l', cnt', out_reset og v, in_reset ig v))"
    using lv(4,5) by (simp add: gap_step_def Let_def)
  show ?thesis
    unfolding acc fst_conv snd_conv
  proof(intro conjI)
    show "\<exists> k'. card \<V> \<le> k' \<and> prod.fst (gap_step k (l, cnt, og, ig) v) = label_upd l v k'"
      using lv(6) by (intro exI[of _ "num_verts + 1"]) (simp add: g change_label_def Let_def)
    show "<label_assn l (pi_lab Si) * gap_frame_assn Si (cnt, og, ig)> gap_step_imp k Si v
          <\<lambda>_. label_assn (prod.fst (gap_step k (l, cnt, og, ig) v)) (pi_lab Si) *
               gap_frame_assn Si (prod.snd (gap_step k (l, cnt, og, ig) v))>"
      using assms(2) lv(1-5)
      unfolding g gap_step_imp_def change_label_imp_def change_label_def Let_def gap_frame_assn_def
      by (sep_auto simp: count_map.fixed_univ_map_upd_invar outg.idx_reset_invar ing.idx_reset_invar)
  qed
qed

lemma gap_imp_rule:
  assumes "label_invar (pr_labels st)" "count_invar (pr_counts st)" "out_invar (pr_out st)"
          "in_invar (pr_in st)"
  shows "<state_assn st Si> gap_imp k Si <\<lambda>_. state_assn (gap_impl k st) Si>"
proof-
  obtain l' cnt' og' ig' where
    res: "gap_fold (pr_labels st) k (gap_step k) (pr_labels st, pr_counts st, pr_out st, pr_in st) =
          (l', cnt', og', ig')"
    by (cases "gap_fold (pr_labels st) k (gap_step k) (pr_labels st, pr_counts st, pr_out st, pr_in st)")
       auto
  note gf = gap_fold_imp_rule[where k = k and g = "gap_step k" and g_imp = "gap_step_imp k Si"
                                and R = "gap_frame_assn Si" and Li = "pi_lab Si"
                                and r = "(pr_counts st, pr_out st, pr_in st)",
                              OF assms(1) gap_step_imp_rule,
                              unfolded res fst_conv snd_conv gap_frame_assn_def prod.case]
  show ?thesis
    using assms
    unfolding gap_imp_def gap_impl_def res prod.case state_assn_def
    by (sep_auto heap: gf)
qed

lemma label_get_state_rule:
  assumes "label_invar (pr_labels st)" "v \<in> \<V>"
  shows "<state_assn st Si> label_get_imp (pi_lab Si) v
         <\<lambda>x. state_assn st Si * \<up>(x = label_get (pr_labels st) v)>"
  using assms unfolding state_assn_def by sep_auto

lemma count_get_state_rule:
  assumes "count_invar (pr_counts st)" "k < 2 * card \<V>"
  shows "<state_assn st Si> count_get_imp (pi_cnt Si) k
         <\<lambda>x. state_assn st Si * \<up>(x = count_get (pr_counts st) k)>"
  using assms unfolding state_assn_def by sep_auto

lemma relabel_gap_imp_rule:
  assumes "invar_state st" "relabel_precond s t (flow_abs st) (labels_abs st) u"
  shows "<state_assn st Si> relabel_gap_imp u Si <\<lambda>_. state_assn (relabel_gap_impl u st) Si>"
proof-
  note inv = invar_stateD[OF assms(1)]
  have u: "u \<in> \<V>"
    using assms(2) by (auto elim!: relabel_precondE active_vertexE)
  note inv' = invar_stateD[OF relabel_impl_props(1)[OF assms]]
  have bnd: "\<And> k. k < num_verts \<Longrightarrow> k < 2 * card \<V>"
    by (simp add: num_verts)
  show ?thesis
    unfolding relabel_gap_imp_def relabel_gap_impl_def Let_def
    by (sep_auto heap: label_get_state_rule[OF inv(3) u] relabel_imp_rule[OF assms]
                       count_get_state_rule[OF inv'(4) bnd] gap_imp_rule[OF inv'(3,4,5,15)])
qed

subsubsection \<open>Applying an Operation\<close>

text \<open>The edge of a valid push is an edge of the network.\<close>

lemma good_op_push_edge:
  assumes "good_op st (Push_Fwd d) \<or> good_op st (Push_Bwd d)"
  shows "d \<in> \<E>"
proof-
  have "F d \<in> \<EE> \<or> B d \<in> \<EE>"
    using assms by (auto simp add: good_op_def elim!: push_precondE admissibleE)
  thus ?thesis
    using o_edge_res[of "F d"] o_edge_res[of "B d"] by auto
qed

lemma apply_op_imp_rule:
  assumes "invar_state st" "good_op st op"
  shows "<state_assn st Si> apply_op_imp op Si <\<lambda>_. state_assn (apply_op op st) Si>"
proof(cases op)
  case (Push_Fwd d)
  have "d \<in> \<E>"
    using good_op_push_edge[of st d] assms(2) by (simp add: Push_Fwd)
  moreover have "invar_basic st"
    using assms(1) by (simp add: invar_state_def)
  ultimately show ?thesis
    using push_fwd_imp_rule by (simp add: Push_Fwd)
next
  case (Push_Bwd d)
  have "d \<in> \<E>"
    using good_op_push_edge[of st d] assms(2) by (simp add: Push_Bwd)
  moreover have "invar_basic st"
    using assms(1) by (simp add: invar_state_def)
  ultimately show ?thesis
    using push_bwd_imp_rule by (simp add: Push_Bwd)
next
  case (Advance u)
  then obtain e where e: "u \<in> \<V>" "current_res st u = Some e"
                         "\<not> admissible (flow_abs st) (labels_abs st) e"
    using assms(2) by (auto simp add: good_op_def)
  show ?thesis
    using advance_imp_rule[OF assms(1) e] by (simp add: Advance)
next
  case (Relabel u)
  thus ?thesis
    using relabel_imp_rule[OF assms(1)] assms(2) by (simp add: good_op_def)
next
  case (Relabel_Gap u)
  thus ?thesis
    using relabel_gap_imp_rule[OF assms(1)] assms(2) by (simp add: good_op_def)
next
  case Done
  thus ?thesis
    by sep_auto
qed
end

subsection \<open>Correctness of the Algorithm\<close>

lemma (in push_relabel_spec) init_state_ctx:
  "pr_ctx init_state = init_ctx (pr_fwd init_state) (pr_bwd init_state) (pr_excess init_state)
                         (pr_labels init_state) (pr_out init_state) (pr_in init_state)"
  unfolding init_state_def by (simp add: Let_def split: prod.split)

text \<open>The strategy is given by its Hoare triples: @{term select_imp} computes the operation and the
      new context selected by @{term select_of}, which is kept in place, and @{term init_ctx_imp}
      initialises the preallocated context.\<close>

locale push_relabel_imp =
  push_relabel_ops_imp +
  push_relabel where fst = fst and snd = snd +
  push_relabel_imp_code fst_imp snd_imp s t num_verts emap_get_imp emap_upd_imp ex_get_imp ex_upd_imp
    label_get_imp label_upd_imp count_get_imp count_upd_imp out_current_imp out_has_imp
    out_move_imp out_reset_imp out_reset_to_imp in_current_imp in_has_imp in_move_imp in_reset_imp
    in_reset_to_imp gap_fold_imp edge_fold_imp select_imp init_ctx_imp
  for select_imp init_ctx_imp +
  fixes ctx_assn
    and ctx_init_assn
  assumes select_imp_rule:
    "\<And> st op c Si Ci. \<lbrakk>invar_state st; ctx_invar st; select_of st = (op, c)\<rbrakk> \<Longrightarrow>
       <state_assn st Si * ctx_assn (pr_ctx st) Ci> select_imp Ci Si
       <\<lambda>r. state_assn st Si * ctx_assn c Ci * \<up>(r = op)>"
  and init_ctx_imp_rule:
    "\<And> Si Ci. <state_assn init_state Si * ctx_init_assn Ci> init_ctx_imp Ci Si
               <\<lambda>_. state_assn init_state Si * ctx_assn (pr_ctx init_state) Ci>"
begin

subsubsection \<open>Initialisation\<close>

definition "init_assn Si =
   emap_assn emap_init (pi_fwd Si) * emap_assn emap_init (pi_bwd Si) * emap_assn caps (pi_caps Si) *
   ex_assn ex_init (pi_ex Si) * label_assn label_init (pi_lab Si) * count_assn count_init (pi_cnt Si) *
   out_assn out_init (pi_out Si) * in_assn in_init (pi_in Si) * ends_assn (pi_ends Si) *
   min_scratch_assn Si"

definition "init_frame_assn Si = (\<lambda> (fw, bw, x).
   emap_assn fw (pi_fwd Si) * emap_assn bw (pi_bwd Si) * ex_assn x (pi_ex Si) *
   emap_assn caps (pi_caps Si) * ends_assn (pi_ends Si))"

definition "init_invar = (\<lambda> (fw, bw, x). emap_invar fw \<and> emap_invar bw \<and> ex_invar x)"

lemma init_step_imp_rule:
  assumes "init_invar acc" "d \<in> \<E>"
  shows "init_invar (init_step acc d) \<and>
         <init_frame_assn Si acc> init_step_imp Si d <\<lambda>_. init_frame_assn Si (init_step acc d)>"
proof-
  obtain fw bw x where acc: "acc = (fw, bw, x)"
    by (cases acc) auto
  have I: "emap_invar fw" "emap_invar bw" "ex_invar x"
    using assms(1) by (simp_all add: acc init_invar_def)
  note V = edge_verts[OF assms(2)] s_in_V
  show ?thesis
    unfolding acc
  proof(intro conjI)
    show "init_invar (init_step (fw, bw, x) d)"
      using I V assms(2)
      by (simp add: init_invar_def init_step_def Let_def edge_map.fixed_univ_map_upd_invar
                    ex_map.fixed_univ_map_upd_invar)
    show "<init_frame_assn Si (fw, bw, x)> init_step_imp Si d
          <\<lambda>_. init_frame_assn Si (init_step (fw, bw, x) d)>"
      using I V assms(2) caps(1)
      unfolding init_frame_assn_def init_step_imp_def init_step_def Let_def
      by (sep_auto heap: fst_imp_rule snd_imp_rule
                   simp: ex_map.fixed_univ_map_upd_invar ex_map.fixed_univ_map_upd h_add)
  qed
qed


lemma init_imp_rule: "<init_assn Si> init_imp Si <\<lambda>_. state_assn init_state Si>"
proof-
  obtain fw bw x where
    res: "edge_fold init_step (emap_init, emap_init, ex_init) = (fw, bw, x)"
    by (cases "edge_fold init_step (emap_init, emap_init, ex_init)") auto
  have og: "out_invar out_init"
    using init_adts(8) by (simp add: out_graph_inv_def)
  have i0: "init_invar (emap_init, emap_init, ex_init)"
    using init_adts(1,2) by (simp add: init_invar_def)
  note ef = edge_fold_imp_rule[where g = init_step and g_imp = "init_step_imp Si" and P = init_invar
                                 and R = "init_frame_assn Si" and Oi = "pi_out Si",
                               OF og i0 init_step_imp_rule, unfolded res init_frame_assn_def prod.case]
  have n: "0 < 2 * card \<V>" "num_verts < 2 * card \<V>"
    using card_V_ge_2[OF net_assms] by (simp_all add: num_verts)
  show ?thesis
    using init_adts(4,6) s_in_V n
    unfolding init_imp_def init_assn_def state_assn_def init_state_def res prod.case Let_def
    by (sep_auto heap: ef simp: count_map.fixed_univ_map_upd_invar)
qed

subsubsection \<open>The Loop\<close>

lemma push_relabel_loop_imp_rule:
  assumes "invar_state st" "ctx_invar st"
  shows "<state_assn st Si * ctx_assn (pr_ctx st) Ci> push_relabel_loop_imp Ci Si
         <\<lambda>_. state_assn (push_relabel_loop st) Si * ctx_assn (pr_ctx (push_relabel_loop st)) Ci>"
proof-
  define T where
    "T st \<longleftrightarrow> <state_assn st Si * ctx_assn (pr_ctx st) Ci> push_relabel_loop_imp Ci Si
               <\<lambda>_. state_assn (push_relabel_loop st) Si * ctx_assn (pr_ctx (push_relabel_loop st)) Ci>"
    for st :: "(_, _, _, _, _, _) pr_state"
  have "invar_state st \<longrightarrow> ctx_invar st \<longrightarrow> T st"
  proof(rule push_relabel_induct[OF push_relabel_loop_props(1)[OF assms]])
    fix st
    assume dom: "push_relabel_loop_dom st"
       and IH: "push_relabel_upd_cond st \<Longrightarrow>
                invar_state (push_relabel_upd st) \<longrightarrow> ctx_invar (push_relabel_upd st) \<longrightarrow>
                T (push_relabel_upd st)"
    show "invar_state st \<longrightarrow> ctx_invar st \<longrightarrow> T st"
    proof(intro impI)
      assume inv: "invar_state st" and ci: "ctx_invar st"
      obtain op c where sel: "select_of st = (op, c)"
        by (cases "select_of st") auto
      note sr = select_imp_rule[OF inv ci sel]
      show "T st"
      proof(cases "op = Done")
        case True
        have ret: "push_relabel_ret_cond st"
          using sel True by (simp add: push_relabel_ret_cond_def)
        have lp: "push_relabel_loop st = st\<lparr>pr_ctx := c\<rparr>"
          using push_relabel_simps(1)[OF ret] sel by (simp add: push_relabel_ret_def)
        show ?thesis
          unfolding T_def lp
          by (subst push_relabel_loop_imp.simps) (sep_auto heap: sr simp: True)
      next
        case False
        have upd: "push_relabel_upd_cond st"
          using sel False by (simp add: push_relabel_upd_cond_def)
        have u: "push_relabel_upd st = apply_op op (st\<lparr>pr_ctx := c\<rparr>)"
          using sel by (simp add: push_relabel_upd_def)
        have good: "good_op (st\<lparr>pr_ctx := c\<rparr>) op"
          using select(1)[OF inv ci sel] by (simp add: good_op_ctx)
        have A: "<state_assn st Si> apply_op_imp op Si <\<lambda>_. state_assn (push_relabel_upd st) Si>"
          using apply_op_imp_rule[OF _ good] inv by (simp add: u invar_state_ctx)
        note pu = push_relabel_upd_props[OF inv ci upd]
        have B: "<state_assn (push_relabel_upd st) Si * ctx_assn c Ci> push_relabel_loop_imp Ci Si
                 <\<lambda>_. state_assn (push_relabel_loop st) Si * ctx_assn (pr_ctx (push_relabel_loop st)) Ci>"
          using IH[OF upd] pu(1,2) push_relabel_simps(2)[OF dom upd]
          by (simp add: T_def u apply_op_ctx)
        show ?thesis
          unfolding T_def
          by (subst push_relabel_loop_imp.simps) (sep_auto heap: sr A B simp: False)
      qed
    qed
  qed
  thus ?thesis
    using assms by (simp add: T_def)
qed

text \<open>Started on the initial data structures, the program leaves the result of the functional
      algorithm, a maximum flow by @{thm push_relabel_correct}, in the backward residual
      capacities.\<close>

theorem push_relabel_imp_rule:
  "<init_assn Si * ctx_init_assn Ci> push_relabel_imp Ci Si
   <\<lambda>_. ends_assn (pi_ends Si) * emap_assn caps (pi_caps Si) * emap_assn push_relabel (pi_bwd Si) *
        true>"
proof-
  note ip = init_state_props
  note lp = push_relabel_loop_props[OF ip]
  have res: "pr_bwd (push_relabel_loop init_state) = push_relabel"
    using push_relabel_loop_impl_same[OF lp(1)] by (simp add: push_relabel_def)
  have "<init_assn Si * ctx_init_assn Ci> push_relabel_imp Ci Si
        <\<lambda>_. state_assn (push_relabel_loop init_state) Si *
             ctx_assn (pr_ctx (push_relabel_loop init_state)) Ci>"
    unfolding push_relabel_imp_def
    by (sep_auto heap: init_imp_rule init_ctx_imp_rule push_relabel_loop_imp_rule[OF ip])
  thus ?thesis
    by (rule ht_cons_post) (sep_auto simp: state_assn_def res[symmetric])
qed

end

end
