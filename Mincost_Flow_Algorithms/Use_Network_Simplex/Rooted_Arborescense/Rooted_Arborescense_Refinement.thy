theory Rooted_Arborescense_Refinement
  imports Rooted_Arborescense Data_Structures.More_Arith
Separation_Logic_Imperative_HOL_Partial.Array_Blit
    Separation_Logic_Imperative_HOL_Partial.Imperative_HOL_Addons
begin

provenance ai


record  ndtree_impl =
  prnt_impl :: "nat array"   \<comment> \<open>tree parent map\<close>
  thrd_impl :: "nat array"   \<comment> \<open>thread successor (preorder next)\<close>
  rvth_impl :: "nat array"    \<comment> \<open>thread predecessor (reverse thread)\<close>
  lsuc_impl :: "nat array"     \<comment> \<open>last successor: rightmost descendant of the subtree in the
    thread\<close>
  snum_impl :: "nat array"    \<comment> \<open>subtree size (number of successors, incl. the node itself)\<close>
  aux_impl :: "nat array"
subsection \<open>Imperative implementations over @{typ ndtree_impl}\<close>

text \<open>Arrays encode @{term None} as zero; vertices are nonzero.
  The auxiliary array and its fill pointer hold the deferred reverse-thread updates.\<close>

partial_function (heap) stem_loop_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat) Heap" where
  "stem_loop_imp Ti stm pstm lsx aft sp p =
     (if stm = p then return (pstm, lsx, aft, sp)
      else do {
        nxt_stm \<leftarrow> Array.nth (prnt_impl Ti) stm;
        _ \<leftarrow> Array.upd lsx nxt_stm (thrd_impl Ti);
        _ \<leftarrow> Array.upd sp lsx (aux_impl Ti);
        bef \<leftarrow> Array.nth (rvth_impl Ti) stm;
        _ \<leftarrow> (if aft = 0
               then do { _ \<leftarrow> Array.upd bef 0 (thrd_impl Ti); return () }
               else do { _ \<leftarrow> Array.upd bef aft (thrd_impl Ti);
                         _ \<leftarrow> Array.upd aft bef (rvth_impl Ti); return () });
        _ \<leftarrow> Array.upd stm pstm (prnt_impl Ti);
        ls_stm \<leftarrow> Array.nth (lsuc_impl Ti) nxt_stm;
        ls_pstm \<leftarrow> Array.nth (lsuc_impl Ti) stm;
        lsx' \<leftarrow> (if ls_stm = ls_pstm then Array.nth (rvth_impl Ti) stm else return ls_stm);
        aft' \<leftarrow> Array.nth (thrd_impl Ti) lsx';
        stem_loop_imp Ti nxt_stm stm lsx' aft' (sp + 1) p
      })"

text \<open>Apply deferred reverse-thread updates in insertion order.\<close>

partial_function (heap) dirty_pass_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "dirty_pass_imp Ti k sp =
     (if sp \<le> k then return ()
      else do {
        u \<leftarrow> Array.nth (aux_impl Ti) k;
        w \<leftarrow> Array.nth (thrd_impl Ti) u;
        _ \<leftarrow> (if w = 0 then return () else do { _ \<leftarrow> Array.upd w u (rvth_impl Ti); return () });
        dirty_pass_imp Ti (k + 1) sp
      })"

text \<open>The number pass reads each original size before overwriting it.\<close>

partial_function (heap) stem_num_loop_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "stem_num_loop_imp Ti u iv acc tls =
     (if u = iv then return ()
      else do {
        par \<leftarrow> Array.nth (prnt_impl Ti) u;
        (if par = 0 then return ()
         else do {
           snu \<leftarrow> Array.nth (snum_impl Ti) u;
           snpar \<leftarrow> Array.nth (snum_impl Ti) par;
           _ \<leftarrow> Array.upd u (acc + (snu - snpar)) (snum_impl Ti);
           _ \<leftarrow> Array.upd par tls (lsuc_impl Ti);
           stem_num_loop_imp Ti par iv (acc + (snu - snpar)) tls
         })
      })"

text \<open>The fused passes update last descendants and subtree sizes in one parent walk.\<close>

partial_function (heap) fused_vin_loop_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    bool \<Rightarrow> bool \<Rightarrow> unit Heap" where
  "fused_vin_loop_imp Ti u jv jn lso d la sa =
     do {
        lsu \<leftarrow> Array.nth (lsuc_impl Ti) u;
        (if \<not> (la \<and> lsu = jv) \<and> \<not> (sa \<and> u \<noteq> jn) then return ()
         else do {
           _ \<leftarrow> (if la \<and> lsu = jv then do { _ \<leftarrow> Array.upd u lso (lsuc_impl Ti); return () }
             else return ());
           _ \<leftarrow> (if sa \<and> u \<noteq> jn
                  then do { snu \<leftarrow> Array.nth (snum_impl Ti) u; _ \<leftarrow> Array.upd u (snu + d)
                    (snum_impl Ti); return () }
                  else return ());
           par \<leftarrow> Array.nth (prnt_impl Ti) u;
           (if par = 0 then return ()
            else fused_vin_loop_imp Ti par jv jn lso d (la \<and> lsu = jv) (sa \<and> u \<noteq> jn))
         })
      }"

partial_function (heap) fused_vout_loop_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit Heap" where
  "fused_vout_loop_imp Ti u stp gv sv jn d la sa =
     do {
        lsu \<leftarrow> Array.nth (lsuc_impl Ti) u;
        (if \<not> (la \<and> u \<noteq> stp \<and> lsu = gv) \<and> \<not> (sa \<and> u \<noteq> jn) then return ()
         else do {
           _ \<leftarrow> (if la \<and> u \<noteq> stp \<and> lsu = gv then do { _ \<leftarrow> Array.upd u sv
             (lsuc_impl Ti); return () } else return ());
           _ \<leftarrow> (if sa \<and> u \<noteq> jn
                  then do { snu \<leftarrow> Array.nth (snum_impl Ti) u; _ \<leftarrow> Array.upd u (snu - d)
                    (snum_impl Ti); return () }
                  else return ());
           par \<leftarrow> Array.nth (prnt_impl Ti) u;
           (if par = 0 then return ()
            else fused_vout_loop_imp Ti par stp gv sv jn d (la \<and> u \<noteq> stp \<and> lsu = gv) (sa \<and> u
              \<noteq> jn))
         })
      }"

definition update_tree_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> unit Heap" where
  "update_tree_imp Ti i j p jn =
     do {
        v_out \<leftarrow> Array.nth (prnt_impl Ti) p;
        old_rev \<leftarrow> Array.nth (rvth_impl Ti) p;
        old_num \<leftarrow> Array.nth (snum_impl Ti) p;
        old_last \<leftarrow> Array.nth (lsuc_impl Ti) p;
        \<comment> \<open>--- restructure the thread / parent pointers (build S1 in place) ---\<close>
        _ \<leftarrow> (if i = p
         then do {
           _ \<leftarrow> Array.upd i j (prnt_impl Ti);
           tj \<leftarrow> Array.nth (thrd_impl Ti) j;
           (if tj = p then return ()
            else do {
              aft1 \<leftarrow> Array.nth (thrd_impl Ti) old_last;
              _ \<leftarrow> (if aft1 = 0 then do { _ \<leftarrow> Array.upd old_rev 0 (thrd_impl Ti); return () }
                     else do { _ \<leftarrow> Array.upd old_rev aft1 (thrd_impl Ti);
                               _ \<leftarrow> Array.upd aft1 old_rev (rvth_impl Ti); return () });
              aft2 \<leftarrow> Array.nth (thrd_impl Ti) j;
              _ \<leftarrow> Array.upd j p (thrd_impl Ti);
              _ \<leftarrow> Array.upd p j (rvth_impl Ti);
              (if aft2 = 0 then do { _ \<leftarrow> Array.upd old_last 0 (thrd_impl Ti); return () }
               else do { _ \<leftarrow> Array.upd old_last aft2 (thrd_impl Ti);
                         _ \<leftarrow> Array.upd aft2 old_last (rvth_impl Ti); return () })
            })
         }
         else do {
           thread_cont \<leftarrow> (if old_rev = j then Array.nth (thrd_impl Ti) old_last else Array.nth (thrd_impl
             Ti) j);
           lsx0 \<leftarrow> Array.nth (lsuc_impl Ti) i;
           aft0 \<leftarrow> Array.nth (thrd_impl Ti) lsx0;
           _ \<leftarrow> Array.upd j i (thrd_impl Ti);
           _ \<leftarrow> Array.upd 0 j (aux_impl Ti);
           r \<leftarrow> stem_loop_imp Ti i j lsx0 aft0 1 p;
           (case r of (pstm, lsx, aft, sp) \<Rightarrow> do {
              _ \<leftarrow> Array.upd p pstm (prnt_impl Ti);
              _ \<leftarrow> (if thread_cont = 0 then do { _ \<leftarrow> Array.upd lsx 0 (thrd_impl Ti); return () }
                     else do { _ \<leftarrow> Array.upd lsx thread_cont (thrd_impl Ti);
                               _ \<leftarrow> Array.upd thread_cont lsx (rvth_impl Ti); return () });
              _ \<leftarrow> Array.upd p lsx (lsuc_impl Ti);
              _ \<leftarrow> (if old_rev \<noteq> j
                     then (if aft = 0 then do { _ \<leftarrow> Array.upd old_rev 0 (thrd_impl Ti); return () }
                           else do { _ \<leftarrow> Array.upd old_rev aft (thrd_impl Ti);
                                     _ \<leftarrow> Array.upd aft old_rev (rvth_impl Ti); return () })
                     else return ());
              _ \<leftarrow> dirty_pass_imp Ti 0 sp;
              tls \<leftarrow> Array.nth (lsuc_impl Ti) p;
              _ \<leftarrow> stem_num_loop_imp Ti p i 0 tls;
              _ \<leftarrow> Array.upd i old_num (snum_impl Ti);
              return ()
           })
         });
        \<comment> \<open>--- fix lsuc and snum along the branches up to the join (fused passes) ---\<close>
        ls_jn \<leftarrow> Array.nth (lsuc_impl Ti) jn;
        last_out \<leftarrow> Array.nth (lsuc_impl Ti) p;
        up_limit \<leftarrow> return (if ls_jn = j then jn else 0);
        _ \<leftarrow> fused_vin_loop_imp Ti j j jn last_out old_num True True;
        (if jn \<noteq> old_rev \<and> j \<noteq> old_rev
         then fused_vout_loop_imp Ti v_out up_limit old_last old_rev jn old_num True True
         else if last_out \<noteq> old_last
              then fused_vout_loop_imp Ti v_out up_limit old_last last_out jn old_num True True
              else fused_vout_loop_imp Ti v_out up_limit old_last old_last jn old_num False True)
      }"

definition ndtree_assn :: "nat set \<Rightarrow> nat ndtree \<Rightarrow> ndtree_impl \<Rightarrow> assn" where
 "ndtree_assn V T Ti =
  (\<exists>\<^sub>A prnt_list thrd_list rvth_list lsuc_list snum_list aux_list.
      prnt_impl Ti \<mapsto>\<^sub>a prnt_list *
      thrd_impl Ti \<mapsto>\<^sub>a thrd_list *
      rvth_impl Ti \<mapsto>\<^sub>a rvth_list *
      lsuc_impl Ti \<mapsto>\<^sub>a lsuc_list *
      snum_impl Ti \<mapsto>\<^sub>a snum_list *
      aux_impl Ti \<mapsto>\<^sub>a aux_list *
     \<up> (  0 \<notin> V \<and>
         dom (prnt T) \<subseteq> V \<and> dom (thrd T) \<subseteq> V \<and> dom (rvth T) \<subseteq> V \<and>
         ran (prnt T) \<subseteq> V \<and> ran (thrd T) \<subseteq> V \<and> ran (rvth T) \<subseteq> V \<and>
        V \<subseteq> {0..<length prnt_list} \<and>
        V \<subseteq> {0..<length thrd_list} \<and>
        V \<subseteq> {0..<length rvth_list} \<and>
        V \<subseteq> {0..<length lsuc_list} \<and>
        V \<subseteq> {0..<length snum_list}\<and>
        V \<subseteq> {0..<length aux_list} \<and>
        (\<forall> v \<in> V. (\<forall> u. prnt T v = Some u \<longrightarrow> prnt_list ! v = u) \<and>
              (prnt T v = None \<longrightarrow> prnt_list ! v = 0)) \<and>
        (\<forall> v \<in> V. (\<forall> u. thrd T v = Some u \<longrightarrow> thrd_list ! v = u) \<and>
              (thrd T v = None \<longrightarrow> thrd_list ! v = 0)) \<and>
        (\<forall> v \<in> V. (\<forall> u. rvth T v = Some u \<longrightarrow> rvth_list ! v = u) \<and>
              (rvth T v = None \<longrightarrow> rvth_list ! v = 0)) \<and>
        (\<forall> v \<in> V. lsuc T v \<in> V) \<and>
        (\<forall> v \<in> V. lsuc T v = lsuc_list ! v \<and>
                   snum T v = snum_list ! v)
        )
        )
        "

subsection \<open>The pure refinement relation and its consistency lemmas\<close>

definition opt_of_nat :: "nat \<Rightarrow> nat option" where
  "opt_of_nat n = (if n = 0 then None else Some n)"

definition nat_of_opt :: "nat option \<Rightarrow> nat" where
  "nat_of_opt x = (case x of None \<Rightarrow> 0 | Some u \<Rightarrow> u)"

lemma nat_of_opt_simps[simp]:
  "nat_of_opt None = 0" "nat_of_opt (Some u) = u"
  by (simp_all add: nat_of_opt_def)

lemma opt_of_nat_simps[simp]:
  "opt_of_nat 0 = None" "n \<noteq> 0 \<Longrightarrow> opt_of_nat n = Some n"
  by (simp_all add: opt_of_nat_def)

text \<open>The pure relation records the array bounds and their agreement with the abstract tree.\<close>

definition ndtree_rel ::
  "nat set \<Rightarrow> nat ndtree \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
  "ndtree_rel V T pl thl rl ll sl al \<longleftrightarrow>
     0 \<notin> V \<and>
     dom (prnt T) \<subseteq> V \<and> dom (thrd T) \<subseteq> V \<and> dom (rvth T) \<subseteq> V \<and>
     ran (prnt T) \<subseteq> V \<and> ran (thrd T) \<subseteq> V \<and> ran (rvth T) \<subseteq> V \<and>
     V \<subseteq> {0..<length pl} \<and> V \<subseteq> {0..<length thl} \<and> V \<subseteq> {0..<length rl} \<and>
     V \<subseteq> {0..<length ll} \<and> V \<subseteq> {0..<length sl} \<and> V \<subseteq> {0..<length al} \<and>
     (\<forall>v\<in>V. (\<forall>u. prnt T v = Some u \<longrightarrow> pl ! v = u) \<and> (prnt T v = None
       \<longrightarrow> pl ! v = 0)) \<and>
     (\<forall>v\<in>V. (\<forall>u. thrd T v = Some u \<longrightarrow> thl ! v = u) \<and> (thrd T v = None
       \<longrightarrow> thl ! v = 0)) \<and>
     (\<forall>v\<in>V. (\<forall>u. rvth T v = Some u \<longrightarrow> rl ! v = u) \<and> (rvth T v = None
       \<longrightarrow> rl ! v = 0)) \<and>
     (\<forall>v\<in>V. lsuc T v \<in> V) \<and>
     (\<forall>v\<in>V. lsuc T v = ll ! v \<and> snum T v = sl ! v)"

lemma ndtree_assn_unfold:
  "ndtree_assn V T Ti =
   (\<exists>\<^sub>A pl thl rl ll sl al.
      prnt_impl Ti \<mapsto>\<^sub>a pl * thrd_impl Ti \<mapsto>\<^sub>a thl * rvth_impl Ti \<mapsto>\<^sub>a rl *
      lsuc_impl Ti \<mapsto>\<^sub>a ll * snum_impl Ti \<mapsto>\<^sub>a sl * aux_impl Ti \<mapsto>\<^sub>a al *
      \<up> (ndtree_rel V T pl thl rl ll sl al))"
  by (simp add: ndtree_assn_def ndtree_rel_def)

subsubsection \<open>Domains, ranges, bounds and read correspondences\<close>

lemma ndtree_rel_0_notin[dest]: "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> 0 \<notin> V"
  and ndtree_rel_aux_bound[dest]: "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> V \<subseteq> {0..<length al}"
  and ndtree_rel_lsuc_V: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> lsuc T v
    \<in> V"
  and ndtree_rel_thrd_ranI: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; thrd T v = Some u\<rbrakk> \<Longrightarrow> u
    \<in> V"
  and ndtree_rel_rvth_ranI: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; rvth T v = Some u\<rbrakk> \<Longrightarrow> u
    \<in> V"
  by (auto simp: ndtree_rel_def ran_def)

lemma ndtree_rel_len_prnt: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> v < length
  pl"
  and ndtree_rel_len_thrd: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> v < length
    thl"
  and ndtree_rel_len_rvth: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> v < length
    rl"
  and ndtree_rel_len_lsuc: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> v < length
    ll"
  and ndtree_rel_len_snum: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> v < length
    sl"
  by (auto simp: ndtree_rel_def)

lemma ndtree_rel_prnt_nat_of_opt: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> pl
  ! v = nat_of_opt (prnt T v)"
  and ndtree_rel_thrd_nat_of_opt: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> thl
    ! v = nat_of_opt (thrd T v)"
  and ndtree_rel_rvth_nat_of_opt: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> rl
    ! v = nat_of_opt (rvth T v)"
  and ndtree_rel_lsuc: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> ll ! v = lsuc
    T v"
  and ndtree_rel_snum: "\<lbrakk>ndtree_rel V T pl thl rl ll sl al; v \<in> V\<rbrakk> \<Longrightarrow> sl ! v = snum
    T v"
  by (auto simp: ndtree_rel_def nat_of_opt_def split: option.splits)
text \<open>The dirty assertion additionally records the occupied prefix of the auxiliary array.\<close>

definition ndtree_drt_assn ::
  "nat set \<Rightarrow> nat ndtree \<Rightarrow> ndtree_impl \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
    assn" where
  "ndtree_drt_assn V T Ti sp xs =
     (\<exists>\<^sub>A pl thl rl ll sl al.
        prnt_impl Ti \<mapsto>\<^sub>a pl * thrd_impl Ti \<mapsto>\<^sub>a thl * rvth_impl Ti \<mapsto>\<^sub>a rl *
        lsuc_impl Ti \<mapsto>\<^sub>a ll * snum_impl Ti \<mapsto>\<^sub>a sl * aux_impl Ti \<mapsto>\<^sub>a al *
        \<up> (ndtree_rel V T pl thl rl ll sl al \<and>
           sp = length xs \<and> length xs \<le> length al \<and> take (length xs) al = xs))"

lemma ndtree_drt_assn_weaken:
  "ndtree_drt_assn V T Ti sp xs \<Longrightarrow>\<^sub>A ndtree_assn V T Ti"
  unfolding ndtree_drt_assn_def ndtree_assn_unfold
  by sep_auto

subsection \<open>Primitive array operations preserve the refinement\<close>

lemma ndtree_rel_upd_lsuc:
    "\<lbrakk>ndtree_rel V S pl thl rl ll sl al; u \<in> V; x \<in> V\<rbrakk>
       \<Longrightarrow> ndtree_rel V (S\<lparr>lsuc := (lsuc S)(u := x)\<rparr>) pl thl rl (ll[u := x]) sl al"
  and ndtree_rel_upd_snum:
    "\<lbrakk>ndtree_rel V S pl thl rl ll sl al; u \<in> V\<rbrakk>
       \<Longrightarrow> ndtree_rel V (S\<lparr>snum := (snum S)(u := x)\<rparr>) pl thl rl ll (sl[u := x]) al"
  and ndtree_rel_upd_rvth:
    "\<lbrakk>ndtree_rel V S pl thl rl ll sl al; w \<in> V; u \<in> V\<rbrakk>
       \<Longrightarrow> ndtree_rel V (S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) pl thl (rl[w := u]) ll sl al"
  and ndtree_rel_upd_thrd_Some:
    "\<lbrakk>ndtree_rel V S pl thl rl ll sl al; w \<in> V; u \<in> V\<rbrakk>
       \<Longrightarrow> ndtree_rel V (S\<lparr>thrd := (thrd S)(w \<mapsto> u)\<rparr>) pl (thl[w := u]) rl ll sl al"
  and ndtree_rel_upd_thrd_None:
    "\<lbrakk>ndtree_rel V S pl thl rl ll sl al; w \<in> V\<rbrakk>
       \<Longrightarrow> ndtree_rel V (S\<lparr>thrd := (thrd S)(w := None)\<rparr>) pl (thl[w := 0]) rl ll sl al"
  and ndtree_rel_upd_prnt_Some:
    "\<lbrakk>ndtree_rel V S pl thl rl ll sl al; w \<in> V; u \<in> V\<rbrakk>
       \<Longrightarrow> ndtree_rel V (S\<lparr>prnt := (prnt S)(w \<mapsto> u)\<rparr>) (pl[w := u]) thl rl ll sl al"
  by (auto simp: ndtree_rel_def nth_list_update ran_def subset_iff split: if_splits)
lemma ndtree_nth_prnt[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (prnt_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = nat_of_opt (prnt S u))>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_prnt ndtree_rel_prnt_nat_of_opt)

lemma ndtree_nth_lsuc[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (lsuc_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = lsuc S u)>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_lsuc ndtree_rel_lsuc)

lemma ndtree_nth_snum[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (snum_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = snum S u)>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_snum ndtree_rel_snum)

lemma ndtree_upd_lsuc[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> x \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd u x (lsuc_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>lsuc := (lsuc S)(u := x)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_lsuc ndtree_rel_upd_lsuc)

lemma ndtree_upd_snum[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd u x (snum_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>snum := (snum S)(u := x)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_snum ndtree_rel_upd_snum)

text \<open>Conditional updates keep the refinement assertion folded across the fused-loop branches.\<close>

lemma ndtree_cond_upd_lsuc[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> x \<in> V \<Longrightarrow>
   <ndtree_assn V S Ti> (if c then Array.upd u x (lsuc_impl Ti) \<bind> (\<lambda>_. return ()) else return ())
   <\<lambda>_. ndtree_assn V (S\<lparr>lsuc := (if c then (lsuc S)(u := x) else lsuc S)\<rparr>) Ti>"
  by (cases c) (sep_auto simp: fun_upd_idem)+

lemma ndtree_cond_upd_snum[sep_heap_rules]:
  "u \<in> V \<Longrightarrow>
   <ndtree_assn V S Ti> (if c then Array.nth (snum_impl Ti) u \<bind> (\<lambda>snu. Array.upd u (snu + d) (snum_impl
     Ti) \<bind> (\<lambda>_. return ())) else return ())
   <\<lambda>_. ndtree_assn V (S\<lparr>snum := (if c then (snum S)(u := snum S u + d) else snum S)\<rparr>) Ti>"
  by (cases c) (sep_auto simp: fun_upd_idem)+

subsection \<open>Primitive operations on the dirty-list assertion @{const ndtree_drt_assn}\<close>

lemma ndtree_drt_nth_aux[sep_heap_rules]:
  "k < length drt \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (aux_impl Ti) k
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = drt ! k)>"
  unfolding ndtree_drt_assn_def
  by (sep_auto dest: take_nth_eq)

lemma ndtree_drt_nth_thrd[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (thrd_impl Ti) u
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = nat_of_opt (thrd S u))>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_thrd_nat_of_opt)

lemma ndtree_drt_upd_rvth[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w u (rvth_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_rvth ndtree_rel_upd_rvth)

lemma ndtree_drt_nth_prnt[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (prnt_impl Ti) u
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = nat_of_opt (prnt S u))>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_prnt ndtree_rel_prnt_nat_of_opt)

lemma ndtree_drt_nth_rvth[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (rvth_impl Ti) u
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = nat_of_opt (rvth S u))>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_rvth ndtree_rel_rvth_nat_of_opt)

lemma ndtree_drt_nth_lsuc[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (lsuc_impl Ti) u
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = lsuc S u)>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_lsuc ndtree_rel_lsuc)

lemma ndtree_drt_upd_thrd_Some[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w u (thrd_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>thrd := (thrd S)(w \<mapsto> u)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_upd_thrd_Some)

lemma ndtree_drt_upd_thrd_None[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w 0 (thrd_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>thrd := (thrd S)(w := None)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_upd_thrd_None)

lemma ndtree_drt_upd_prnt_Some[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w u (prnt_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>prnt := (prnt S)(w \<mapsto> u)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_prnt ndtree_rel_upd_prnt_Some)

lemma ndtree_rel_upd_aux[simp]:
  "ndtree_rel V S pl thl rl ll sl (al[i := x]) = ndtree_rel V S pl thl rl ll sl al"
  by (simp add: ndtree_rel_def)

lemma dp_base:
  "<ndtree_drt_assn V S Ti (length pre) pre> dirty_pass_imp Ti (length pre) (length pre) <\<lambda>_. ndtree_assn V S
    Ti>"
  apply(subst dirty_pass_imp.simps)
  apply simp
  apply(rule ht_cons_pre[OF ndtree_drt_assn_weaken])
  apply sep_auto
  done

lemma dirty_pass_imp_aux:
  assumes "0 \<notin> V" and "set drt \<subseteq> V"
  shows "ran (thrd S) \<subseteq> V \<Longrightarrow> k \<le> length drt \<Longrightarrow>
    <ndtree_drt_assn V S Ti (length drt) drt> dirty_pass_imp Ti k (length drt)
    <\<lambda>_. ndtree_assn V (foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow>
      S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) S (drop k drt)) Ti>"
proof(induction "length drt - k" arbitrary: k S)
  case 0
  thus ?case
    using dp_base[where pre = drt and S = S and Ti = Ti and V = V]
    by simp
next
  case (Suc n)
  have kl: "k < length drt" and decrease: "n = length drt - Suc k"
    using Suc.hyps(2) Suc.prems(2)
    by auto
  have bound: "Suc k \<le> length drt"
  using kl
  by simp
  note IH = Suc.hyps(1)[OF decrease _ bound]
  have notle: "\<not> length drt \<le> k"
  using kl
  by simp
  have dkV: "drt ! k \<in> V"
    using assms(2) kl
    by auto
  show ?case
  proof(cases "thrd S (drt ! k)")
    case None
    show ?thesis
      unfolding Cons_nth_drop_Suc[OF kl, symmetric]
      by (subst dirty_pass_imp.simps, subst if_not_P[OF notle])
         (sep_auto simp: kl dkV None nat_of_opt_def heap: IH[OF Suc.prems(1)])
  next
    case (Some w)
    have "w \<in> V" "w \<noteq> 0"
      using Some Suc.prems(1) assms(1)
      by (auto simp: ran_def)
    show ?thesis
      unfolding Cons_nth_drop_Suc[OF kl, symmetric]
      by (subst dirty_pass_imp.simps, subst if_not_P[OF notle])
         (sep_auto simp: kl dkV Some \<open>w \<in> V\<close> \<open>w \<noteq> 0\<close>
           Suc.prems(1) nat_of_opt_def heap: IH)
  qed
qed

subsection \<open>Refinement correspondences (Hoare triples)\<close>

text \<open>Agreement with a well-founded reference map suffices for the number pass.\<close>

lemma stem_num_loop_imp_wf:
  assumes "parent_spec P" and "ran P \<subseteq> V" and "0 \<notin> V"
  shows "(\<forall>w \<in> set (follow P u). w \<noteq> iv \<longrightarrow> prnt S w = P w) \<and> u \<in> V \<and>
    tls \<in> V
           \<and> (\<forall>w \<in> set (follow P u). snum S w = sn0 w) \<longrightarrow>
         <ndtree_assn V S Ti> stem_num_loop_imp Ti u iv acc tls <\<lambda>_. ndtree_assn V (stem_num_loop S sn0 u iv
           acc tls) Ti>"
proof(induction arbitrary: S acc rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF assms(1), of u]])
  case (1 u)
  show ?case
    apply(intro impI, elim conjE)
    subgoal premises prems
      using prems assms(2) assms(3) follow_mem_ps[OF assms(1), of u] follow_distinct_ps[OF assms(1), of u]
        follow_ps_simps[OF assms(1), of u] follow_mem_ps[OF assms(1)]
      by (cases "u = iv"; cases "P u"; subst stem_num_loop_imp.simps; subst stem_num_loop.simps)
         (sep_auto simp: Let_def nat_of_opt_def ran_def heap: 1(2)[rule_format])+
    done
qed

subsection \<open>Stem-loop, dirty-pass and stem-number-loop refinement\<close>

lemma dirty_pass_imp_rule:
  "\<lbrakk>0 \<notin> V; set drt \<subseteq> V; ran (thrd S) \<subseteq> V\<rbrakk> \<Longrightarrow>
    <ndtree_drt_assn V S Ti (length drt) drt> dirty_pass_imp Ti 0 (length drt)
         <\<lambda>_. ndtree_assn V (dirty_pass S drt) Ti>"
  by (auto intro!: dirty_pass_imp_aux[where k = 0, simplified drop_0, folded dirty_pass_def])

subsection \<open>Primitives for the top-level composition\<close>

lemma ndtree_nth_rvth[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (rvth_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = nat_of_opt (rvth S u))>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_rvth ndtree_rel_rvth_nat_of_opt)

lemma ndtree_nth_thrd[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (thrd_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = nat_of_opt (thrd S u))>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_thrd_nat_of_opt)

lemma ndtree_upd_prnt_Some[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd w u (prnt_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>prnt := (prnt S)(w \<mapsto> u)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_prnt ndtree_rel_upd_prnt_Some)

lemma ndtree_upd_thrd_Some[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd w u (thrd_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>thrd := (thrd S)(w \<mapsto> u)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_upd_thrd_Some)

lemma ndtree_upd_thrd_None[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd w 0 (thrd_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>thrd := (thrd S)(w := None)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_upd_thrd_None)

lemma ndtree_upd_rvth[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd w u (rvth_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_rvth ndtree_rel_upd_rvth)

text \<open>The first auxiliary-array write starts the dirty list; the unused zero index supplies its capacity.\<close>

lemma ndtree_assn_to_drt:
  "j \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd 0 j (aux_impl Ti) <\<lambda>_. ndtree_drt_assn V S Ti 1
    [j]>"
  by (sep_auto simp: take_Suc_conv_app_nth ndtree_assn_unfold ndtree_drt_assn_def dest: ndtree_rel_aux_bound)

lemma zero_not_in_V_ndtree_assn_extract:
  "<ndtree_assn V S0 Ti> program <Q> = (0 \<notin> V \<longrightarrow> <ndtree_assn V S0 Ti> program <Q>)"
  by (sep_auto simp: ndtree_assn_def)

text \<open>Fixpoint induction gives partial correctness of both fused passes without join geometry.\<close>

lemma fused_vin_loop_imp_uncond:
  assumes "0 \<notin> V"
  shows "u \<in> V \<and> lso \<in> V \<and> ran (prnt S) \<subseteq> V \<longrightarrow>
    <ndtree_assn V S Ti> fused_vin_loop_imp Ti u jv jn lso d la sa
    <\<lambda>_. ndtree_assn V (fused_vin_loop S u jv jn lso d la sa) Ti>"
  apply(induction arbitrary: S u la sa jv jn lso d rule: fused_vin_loop_imp.fixp_induct)
    apply simp
   apply simp
  subgoal premises IH for f S u la sa jv jn lso d
    apply(intro impI, elim conjE)
    subgoal premises prems
      using prems assms(1)
      by (cases "prnt S u"; subst fused_vin_loop.simps)
         (sep_auto simp: Let_def nat_of_opt_def ran_def heap: IH[rule_format] split: if_split_asm)+
    done
  done

lemma fused_vout_loop_imp_uncond:
  assumes "0 \<notin> V"
  shows "u \<in> V \<and> sv \<in> V \<and> ran (prnt S) \<subseteq> V \<longrightarrow>
    <ndtree_assn V S Ti> fused_vout_loop_imp Ti u stp gv sv jn d la sa
    <\<lambda>_. ndtree_assn V (fused_vout_loop S u (opt_of_nat stp) gv sv jn d la sa) Ti>"
  apply(induction arbitrary: S u la sa stp gv sv jn d rule: fused_vout_loop_imp.fixp_induct)
    apply simp
   apply simp
  subgoal premises IH for f S u la sa stp gv sv jn d
    apply(intro impI, elim conjE)
    subgoal premises prems
      using prems assms(1)
      by (cases "prnt S u"; subst fused_vout_loop.simps)
         (sep_auto simp: Let_def nat_of_opt_def opt_of_nat_def ran_def
            heap: IH[rule_format] split: if_split_asm)+
    done
  done

lemma ran_prnt_ndtree_assn_extract:
  "<ndtree_assn V S Ti> program <Q> = (ran (prnt S) \<subseteq> V \<longrightarrow> <ndtree_assn V S Ti> program <Q>)"
  by (cases "ran (prnt S) \<subseteq> V") (auto simp: ndtree_assn_def)

lemma lsuc_ndtree_assn_extract:
  "\<lbrakk>p \<in> V\<rbrakk> \<Longrightarrow>
    <ndtree_assn V S Ti> program <Q> = (lsuc S p \<in> V \<longrightarrow> <ndtree_assn V S Ti> program <Q>)"
  by (sep_auto simp: ndtree_assn_def)

lemma UT_tail:
  fixes S1 :: "nat ndtree"
  assumes "j \<in> V" and "jn \<in> V" and "p \<in> V"
      and "v_out \<in> V" and "old_rev \<in> V" and "old_last \<in> V"
  shows "<ndtree_assn V S1 Ti>
     Array.nth (lsuc_impl Ti) jn \<bind> (\<lambda>ls_jn.
     Array.nth (lsuc_impl Ti) p \<bind> (\<lambda>last_out.
     return (if ls_jn = j then jn else 0) \<bind> (\<lambda>up_limit.
     fused_vin_loop_imp Ti j j jn last_out old_num True True \<bind> (\<lambda>_.
     if jn \<noteq> old_rev \<and> j \<noteq> old_rev then fused_vout_loop_imp Ti v_out up_limit old_last old_rev jn
       old_num True True
     else if last_out \<noteq> old_last then fused_vout_loop_imp Ti v_out up_limit old_last last_out jn old_num True
       True
     else fused_vout_loop_imp Ti v_out up_limit old_last old_last jn old_num False True))))
   <\<lambda>_. ndtree_assn V (
     if jn \<noteq> old_rev \<and> j \<noteq> old_rev
     then fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) old_num True True) v_out (if lsuc S1 jn = j then Some
       jn else None) old_last old_rev jn old_num True True
     else if lsuc S1 p \<noteq> old_last
          then fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) old_num True True) v_out (if lsuc S1 jn = j then
            Some jn else None) old_last (lsuc S1 p) jn old_num True True
          else fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) old_num True True) v_out (if lsuc S1 jn = j then
            Some jn else None) old_last old_last jn old_num False True) Ti>"
proof(subst zero_not_in_V_ndtree_assn_extract, subst ran_prnt_ndtree_assn_extract,
      subst lsuc_ndtree_assn_extract[OF assms(3)], (rule impI)+, goal_cases)
  case 1
  have stop: "opt_of_nat (if lsuc S1 jn = j then jn else 0) =
      (if lsuc S1 jn = j then Some jn else None)"
    using assms(2) 1(1)
    by (auto simp: opt_of_nat_def)
  have vout: "sv \<in> V \<Longrightarrow>
    <ndtree_assn V S Ti> fused_vout_loop_imp Ti v_out (if lsuc S1 jn = j then jn else 0) gv sv jn old_num la True
    <\<lambda>_. ndtree_assn V (fused_vout_loop S v_out (if lsuc S1 jn = j then Some jn else None)
      gv sv jn old_num la True) Ti>" for S gv sv la
    apply(subst ran_prnt_ndtree_assn_extract, rule impI)
    apply(subst stop[symmetric])
    apply(rule fused_vout_loop_imp_uncond[OF 1(1), THEN mp])
    using assms(4)
    by blast
  show ?thesis
    apply(rule ht_bind[OF ndtree_nth_lsuc[OF assms(2)]], rule ht_extract_pre_pure, hypsubst)
    apply(rule ht_bind[OF ndtree_nth_lsuc[OF assms(3)]], rule ht_extract_pre_pure, hypsubst)
    apply(simp only: return_bind)
    apply(rule ht_bind[OF fused_vin_loop_imp_uncond[OF 1(1), THEN mp]])
     apply(use assms(1) 1 in blast)
    apply(cases "jn \<noteq> old_rev \<and> j \<noteq> old_rev"; cases "lsuc S1 p \<noteq> old_last")
    by (simp_all only: if_True if_False simp_thms vout assms(5) 1(3) assms(6))
qed

text \<open>The same thread and reverse-thread splice rule serves both pivot branches.\<close>

lemma aftT:
  "\<lbrakk>0 \<notin> V; bef \<in> V; \<And>a. aft_opt = Some a \<Longrightarrow> a \<in> V\<rbrakk> \<Longrightarrow>
    <ndtree_assn V St Ti>
     (if nat_of_opt aft_opt = 0 then Array.upd bef 0 (thrd_impl Ti) \<bind> (\<lambda>_. return ())
      else Array.upd bef (nat_of_opt aft_opt) (thrd_impl Ti) \<bind> (\<lambda>_. Array.upd (nat_of_opt aft_opt) bef
        (rvth_impl Ti) \<bind> (\<lambda>_. return ())))
   <\<lambda>_. ndtree_assn V (case aft_opt of None \<Rightarrow> St\<lparr>thrd := (thrd St)(bef := None)\<rparr>
                        | Some a \<Rightarrow> St\<lparr>thrd := (thrd St)(bef \<mapsto> a), rvth := (rvth St)(a
                          \<mapsto> bef)\<rparr>) Ti>"
  by (cases aft_opt; simp only: option.case nat_of_opt_simps if_True)
     (sep_auto simp: nat_of_opt_def heap: ndtree_upd_thrd_None)+

lemma ndtree_drt_upd_lsuc[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> x \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w x (lsuc_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>lsuc := (lsuc S)(w := x)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: ndtree_rel_len_lsuc ndtree_rel_upd_lsuc)

lemma aftT_drt:
  "\<lbrakk>0 \<notin> V; bef \<in> V; \<And>a. aft_opt = Some a \<Longrightarrow> a \<in> V\<rbrakk> \<Longrightarrow>
    <ndtree_drt_assn V St Ti sp drt>
     (if nat_of_opt aft_opt = 0 then Array.upd bef 0 (thrd_impl Ti) \<bind> (\<lambda>_. return ())
      else Array.upd bef (nat_of_opt aft_opt) (thrd_impl Ti) \<bind> (\<lambda>_. Array.upd (nat_of_opt aft_opt) bef
        (rvth_impl Ti) \<bind> (\<lambda>_. return ())))
   <\<lambda>_. ndtree_drt_assn V (case aft_opt of None \<Rightarrow> St\<lparr>thrd := (thrd St)(bef := None)\<rparr>
                        | Some a \<Rightarrow> St\<lparr>thrd := (thrd St)(bef \<mapsto> a), rvth := (rvth St)(a
                          \<mapsto> bef)\<rparr>) Ti sp drt>"
  by (cases aft_opt; simp only: option.case nat_of_opt_simps if_True)
     (sep_auto simp: nat_of_opt_def heap: ndtree_drt_upd_thrd_None)+

text \<open>A simple subtree move changes its parent and splices its thread block after @{term j}.\<close>

lemma UT_simple:
  fixes S0 :: "nat ndtree"
  assumes "i \<in> V" and "j \<in> V" and "p \<in> V"
      and "old_rev \<in> V" and "old_last \<in> V"
      and "ran (thrd S0) \<subseteq> V"
  shows "<ndtree_assn V S0 Ti>
     do {
        _ \<leftarrow> Array.upd i j (prnt_impl Ti);
        tj \<leftarrow> Array.nth (thrd_impl Ti) j;
        (if tj = p then return ()
         else do {
           aft1 \<leftarrow> Array.nth (thrd_impl Ti) old_last;
           _ \<leftarrow> (if aft1 = 0 then do { _ \<leftarrow> Array.upd old_rev 0 (thrd_impl Ti); return () }
                  else do { _ \<leftarrow> Array.upd old_rev aft1 (thrd_impl Ti);
                            _ \<leftarrow> Array.upd aft1 old_rev (rvth_impl Ti); return () });
           aft2 \<leftarrow> Array.nth (thrd_impl Ti) j;
           _ \<leftarrow> Array.upd j p (thrd_impl Ti);
           _ \<leftarrow> Array.upd p j (rvth_impl Ti);
           (if aft2 = 0 then do { _ \<leftarrow> Array.upd old_last 0 (thrd_impl Ti); return () }
            else do { _ \<leftarrow> Array.upd old_last aft2 (thrd_impl Ti);
                      _ \<leftarrow> Array.upd aft2 old_last (rvth_impl Ti); return () })
         })
     }
   <\<lambda>_. ndtree_assn V (
     let Sa = S0\<lparr>prnt := (prnt S0)(i \<mapsto> j)\<rparr>
     in if thrd Sa j = Some p then Sa
        else (let Sb = (case thrd Sa old_last of None \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev :=
          None)\<rparr>
                        | Some a \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev \<mapsto> a), rvth := (rvth Sa)(a
                          \<mapsto> old_rev)\<rparr>);
                  Sc = Sb\<lparr>thrd := (thrd Sb)(j \<mapsto> p), rvth := (rvth Sb)(p \<mapsto> j)\<rparr>
              in (case thrd Sb j of None \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(old_last := None)\<rparr>
                  | Some a \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(old_last \<mapsto> a), rvth := (rvth Sc)(a
                    \<mapsto> old_last)\<rparr>))) Ti>"
proof(subst zero_not_in_V_ndtree_assn_extract, rule impI, goal_cases)
  case 1
  note V0 = this
  define Sa where "Sa = S0\<lparr>prnt := (prnt S0)(i \<mapsto> j)\<rparr>"
  define Sb where "Sb = (case thrd Sa old_last of None \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev :=
    None)\<rparr>
                        | Some a \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev \<mapsto> a), rvth := (rvth Sa)(a
                          \<mapsto> old_rev)\<rparr>)"
  define Sc where "Sc = Sb\<lparr>thrd := (thrd Sb)(j \<mapsto> p), rvth := (rvth Sb)(p \<mapsto> j)\<rparr>"
  have thrdSa: "thrd Sa = thrd S0"
  by (simp add: Sa_def)
  have pne0: "p \<noteq> 0"
  using assms(3) V0
  by (cases "p = 0") simp_all
  have rvth_thrd: "\<And>St x. rvth (St\<lparr>thrd := x\<rparr>) = rvth St"
  by simp
  have aft1V: "\<And>a. thrd Sa old_last = Some a \<Longrightarrow> a \<in> V"
  using assms(6) thrdSa
  by (auto simp: ran_def)
  have ranSb: "ran (thrd Sb) \<subseteq> V"
  using assms(6) thrdSa aft1V
  by (cases "thrd Sa old_last") (auto simp: Sb_def ran_def)
  have aft2V: "\<And>a. thrd Sb j = Some a \<Longrightarrow> a \<in> V"
  using ranSb
  by (auto simp: ran_def)
  have condeq: "(nat_of_opt (thrd Sa j) = p) = (thrd Sa j = Some p)"
    using pne0
    by (cases "thrd Sa j") auto
  note aft1 = aftT[where aft_opt = "thrd Sa old_last" and St = Sa and Ti = Ti,
    OF V0 assms(4) aft1V, simplified, folded Sb_def]
  note aft2 = aftT[where aft_opt = "thrd Sb j" and St = Sc and Ti = Ti,
    OF V0 assms(5) aft2V, simplified]
  show ?thesis
    unfolding Let_def Sa_def[symmetric] Sb_def[symmetric] Sc_def[symmetric]
    apply(rule ht_bind[OF ndtree_upd_prnt_Some[OF assms(1) assms(2)]])
    apply(fold Sa_def)
    apply(rule ht_bind[OF ndtree_nth_thrd[OF assms(2)]], rule ht_extract_pre_pure, hypsubst)
    apply(simp only: condeq)
    apply(cases "thrd Sa j = Some p")
    subgoal premises P
      apply(simp only: if_P[OF P(1)])
      apply sep_auto
      done
    subgoal premises P
      apply(simp only: if_not_P[OF P(1)])
      apply(rule ht_bind[OF ndtree_nth_thrd[OF assms(5)]], rule ht_extract_pre_pure, hypsubst)
      apply(rule ht_bind[OF aft1])
      apply(rule ht_bind[OF ndtree_nth_thrd[OF assms(2)]], rule ht_extract_pre_pure, hypsubst)
      apply(rule ht_bind[OF ndtree_upd_thrd_Some[OF assms(2) assms(3)]])
      apply(rule ht_bind[OF ndtree_upd_rvth[OF assms(3) assms(2)]])
      apply(simp only: rvth_thrd)
      apply(fold Sc_def)
      apply(rule aft2)
      done
    done
qed

text \<open>The reversal branch and its functional counterpart are exposed for compositional refinement.\<close>

definition ut_reversal_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "ut_reversal_imp Ti i j p old_rev old_num old_last =
     do {
        thread_cont \<leftarrow> (if old_rev = j then Array.nth (thrd_impl Ti) old_last else Array.nth (thrd_impl Ti)
          j);
        lsx0 \<leftarrow> Array.nth (lsuc_impl Ti) i;
        aft0 \<leftarrow> Array.nth (thrd_impl Ti) lsx0;
        _ \<leftarrow> Array.upd j i (thrd_impl Ti);
        _ \<leftarrow> Array.upd 0 j (aux_impl Ti);
        r \<leftarrow> stem_loop_imp Ti i j lsx0 aft0 1 p;
        (case r of (pstm, lsx, aft, sp) \<Rightarrow> do {
           _ \<leftarrow> Array.upd p pstm (prnt_impl Ti);
           _ \<leftarrow> (if thread_cont = 0 then do { _ \<leftarrow> Array.upd lsx 0 (thrd_impl Ti); return () }
                  else do { _ \<leftarrow> Array.upd lsx thread_cont (thrd_impl Ti);
                            _ \<leftarrow> Array.upd thread_cont lsx (rvth_impl Ti); return () });
           _ \<leftarrow> Array.upd p lsx (lsuc_impl Ti);
           _ \<leftarrow> (if old_rev \<noteq> j
                  then (if aft = 0 then do { _ \<leftarrow> Array.upd old_rev 0 (thrd_impl Ti); return () }
                        else do { _ \<leftarrow> Array.upd old_rev aft (thrd_impl Ti);
                                  _ \<leftarrow> Array.upd aft old_rev (rvth_impl Ti); return () })
                  else return ());
           _ \<leftarrow> dirty_pass_imp Ti 0 sp;
           tls \<leftarrow> Array.nth (lsuc_impl Ti) p;
           _ \<leftarrow> stem_num_loop_imp Ti p i 0 tls;
           _ \<leftarrow> Array.upd i old_num (snum_impl Ti);
           return ()
        })
     }"

definition ut_reversal_fun :: "nat ndtree \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat ndtree" where
  "ut_reversal_fun S0 i j p old_rev old_num old_last =
     (let thread_cont = (if old_rev = j then thrd S0 old_last else thrd S0 j)
     in let Sinit = S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>
     in (case stem_loop Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p of (Sl, pstm, lsx, aft, drt) \<Rightarrow>
        let Sp = Sl\<lparr>prnt := (prnt Sl)(p \<mapsto> pstm)\<rparr>
        in let Sq = (case thread_cont of None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx := None)\<rparr>
                     | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx \<mapsto> a), rvth := (rvth Sp)(a \<mapsto>
                       lsx)\<rparr>)
        in let Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx)\<rparr>
        in let Ss = (if old_rev \<noteq> j
                     then (case aft of None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(old_rev := None)\<rparr>
                           | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(old_rev \<mapsto> a), rvth := (rvth Sr)(a
                             \<mapsto> old_rev)\<rparr>)
                     else Sr)
        in let St = dirty_pass Ss drt
        in let Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)
        in Su\<lparr>snum := (snum Su)(i := old_num)\<rparr>))"

text \<open>The parent-path length bounds the pushes by @{term "card V"}; index zero supplies one extra cell.\<close>

lemma ndtree_rel_drt_cap_cnt:
  "\<lbrakk>ndtree_rel V S pl thl rl ll sl al; finite V; V \<noteq> {}; length xs \<le> card V\<rbrakk>
    \<Longrightarrow>
    length xs < length al"
  by (auto intro: drt_push_cap_cnt)

lemma ndtree_drt_push_aux_cnt:
  "\<lbrakk>finite V; V \<noteq> {}; length drt \<le> card V\<rbrakk> \<Longrightarrow>
    <ndtree_drt_assn V S Ti (length drt) drt> Array.upd (length drt) lsx (aux_impl Ti)
         <\<lambda>_. ndtree_drt_assn V S Ti (Suc (length drt)) (drt @ [lsx])>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: take_Suc_conv_app_nth nth_list_update_eq take_update_cancel ndtree_rel_drt_cap_cnt)

lemma ndtree_drt_assn_facts:
  "ndtree_drt_assn V S Ti sp drt \<Longrightarrow>\<^sub>A ndtree_drt_assn V S Ti sp drt *
     \<up>(ran (thrd S) \<subseteq> V \<and> ran (rvth S) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc S v \<in> V)
       \<and> sp = length drt \<and> 0 \<notin> V \<and> finite V)"
  unfolding ndtree_drt_assn_def
  apply(subst ent_pure_post_iff, rule conjI, rule ent_refl)
  apply(clarsimp simp: mod_ex_dist mod_pure_star_dist)
  by (auto simp: ran_def ndtree_rel_lsuc_V ndtree_rel_0_notin
           dest: ndtree_rel_thrd_ranI ndtree_rel_rvth_ranI
           intro: finite_subset[OF ndtree_rel_aux_bound finite_atLeastLessThan])

text \<open>The stem refinement tracks agreement with the unvisited reference path and free auxiliary capacity.\<close>

definition stem_loop_pre where
  "stem_loop_pre P V S stm pstm lsx aft p \<longleftrightarrow>
    (\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm) \<and>
    stm \<in> V \<and> pstm \<in> V \<and> lsx \<in> V \<and> (\<forall>a. aft = Some a \<longrightarrow> a \<in> V)
      \<and>
    (\<forall>v \<in> set (follow P stm). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S v
      \<noteq> None)"

lemma stem_loop_imp_wf:
  assumes "parent_spec P" and "ran P \<subseteq> V"
  shows "stem_loop_pre P V S stm pstm lsx aft p \<and>
         length drt + length (follow P stm) \<le> Suc (card V)
     \<longrightarrow> <ndtree_drt_assn V S Ti sp drt> stem_loop_imp Ti stm pstm lsx (nat_of_opt aft) sp p
         <\<lambda>(pstm', lsx', aft', sp'). case stem_loop S stm pstm lsx aft drt p of (Sl, pst, ls, af, dr)
           \<Rightarrow>
             ndtree_drt_assn V Sl Ti sp' dr * \<up>(pstm' = pst \<and> lsx' = ls \<and> aft' = nat_of_opt af \<and> sp'
               = length dr)>"
  unfolding stem_loop_pre_def
proof(induction arbitrary: S pstm lsx aft drt sp rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF assms(1), of
  stm]])
  case (1 stm)
  show ?case
  proof(intro impI, elim conjE, rule ht_cons_pre[OF ndtree_drt_assn_facts], rule ht_extract_pre_pure, elim conjE)
    assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)"
       and stmV: "stm \<in> V" and pstmV: "pstm \<in> V" and lsxV: "lsx \<in> V"
       and aftV: "\<forall>a. aft = Some a \<longrightarrow> a \<in> V"
       and rvthdef: "\<forall>v \<in> set (follow P stm). p \<in> set (follow P v) \<and> v \<noteq> p
         \<longrightarrow> rvth S v \<noteq> None"
       and cap: "length drt + length (follow P stm) \<le> Suc (card V)"
       and ranthrd: "ran (thrd S) \<subseteq> V" and ranrvth: "ran (rvth S) \<subseteq> V"
       and lsucVV: "\<forall>v \<in> V. lsuc S v \<in> V" and spd: "sp = length drt" and V0: "0 \<notin> V" and finV:
         "finite V"
    show "<ndtree_drt_assn V S Ti sp drt> stem_loop_imp Ti stm pstm lsx (nat_of_opt aft) sp p
          <\<lambda>(pstm', lsx', aft', sp'). case stem_loop S stm pstm lsx aft drt p of (Sl, pst, ls, af, dr)
            \<Rightarrow>
             ndtree_drt_assn V Sl Ti sp' dr * \<up>(pstm' = pst \<and> lsx' = ls \<and> aft' = nat_of_opt af \<and> sp'
               = length dr)>"
    proof(cases "stm = p")
      case True
      thus ?thesis
        using spd
        by (subst stem_loop_imp.simps, subst stem_loop.simps) sep_auto
    next
      case False
      then obtain nxt where Pnxt: "P stm = Some nxt" and fstm: "follow P stm = stm # follow P nxt"
        using pin follow_ps_simps[OF assms(1), of stm]
        by (cases "P stm") auto
      have nxtV: "nxt \<in> V"
        using assms(2) Pnxt
        by (auto simp: ran_def)
      have prntstm: "prnt S stm = Some nxt"
        using agr fstm Pnxt
        by auto
      obtain bef where bef: "rvth S stm = Some bef"
        using rvthdef fstm pin False
        by auto
      hence befV: "bef \<in> V"
        using ranrvth
        by (auto simp: ran_def)
      define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
      define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(bef := None)\<rparr>
                            | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(bef \<mapsto> a), rvth := (rvth S1)(a
                              \<mapsto> bef)\<rparr>)"
      define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
      define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
      define aft' where "aft' = thrd S3 lsx'"
      have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
        using False prntstm bef
        by (subst stem_loop.simps)
           (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
      have rvth3: "rvth S3 stm = Some bef" "ran (thrd S3) \<subseteq> V" "lsuc S3 = lsuc S"
        using ranthrd nxtV aftV bef
        by (cases aft; auto simp: S3_def S2_def S1_def ran_def)+
      hence lsx'V: "lsx' \<in> V"
        using befV lsucVV nxtV
        by (auto simp: lsx'_def)
      have IH: "<ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx])> stem_loop_imp Ti nxt stm lsx' (nat_of_opt aft') (Suc
        sp) p
          <\<lambda>(pstm', lsx'', aft'', sp'). case stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p of (Sl, pst, ls,
            af, dr) \<Rightarrow>
             ndtree_drt_assn V Sl Ti sp' dr * \<up>(pstm' = pst \<and> lsx'' = ls \<and> aft'' = nat_of_opt af \<and>
               sp' = length dr)>"
        by (rule 1(2)[OF Pnxt, THEN mp])
           (use agr rvthdef fstm cap pin False nxtV stmV lsx'V rvth3(2) follow_distinct_ps[OF assms(1), of stm] in
             \<open>auto simp: aft'_def ran_def, auto simp: S3_def S2_def S1_def split: option.splits\<close>)
      have LSX: "<ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx])>
                   (if lsuc S3 nxt = lsuc S3 stm then Array.nth (rvth_impl Ti) stm else return (lsuc S3 nxt))
                 <\<lambda>r. ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx]) * \<up>(r = lsx')>"
        using stmV rvth3
        by (cases "lsuc S3 nxt = lsuc S3 stm") (sep_auto simp: lsx'_def)+
      have rvthS1: "nat_of_opt (rvth S1 stm) = bef" and cntV: "V \<noteq> {}" "length drt \<le> card V"
        using bef cap fstm stmV
        by (auto simp: S1_def)
      show ?thesis
        apply(subst stem_loop_imp.simps)
        apply(simp only: if_not_P[OF False])
        apply(rule ht_bind[OF ndtree_drt_nth_prnt[OF stmV]], rule ht_extract_pre_pure, hypsubst)
        apply(simp only: prntstm nat_of_opt_simps(2))
        apply(rule ht_bind[OF ndtree_drt_upd_thrd_Some[OF lsxV nxtV]], fold S1_def)
        apply(simp only: spd)
        apply(rule ht_bind[OF ndtree_drt_push_aux_cnt[OF finV cntV]])
        apply(simp only: spd[symmetric])
        apply(rule ht_bind[OF ndtree_drt_nth_rvth[OF stmV]], rule ht_extract_pre_pure, hypsubst)
        apply(simp only: rvthS1)
        apply(rule ht_bind[OF aftT_drt[OF V0 befV]], use aftV in blast, fold S2_def)
        apply(rule ht_bind[OF ndtree_drt_upd_prnt_Some[OF stmV pstmV]], fold S3_def)
        apply(rule ht_bind[OF ndtree_drt_nth_lsuc[OF nxtV]], rule ht_extract_pre_pure, hypsubst)
        apply(rule ht_bind[OF ndtree_drt_nth_lsuc[OF stmV]], rule ht_extract_pre_pure, hypsubst)
        apply(rule ht_bind[OF LSX], rule ht_extract_pre_pure, hypsubst)
        apply(rule ht_bind[OF ndtree_drt_nth_thrd[OF lsx'V]], rule ht_extract_pre_pure, hypsubst)
        apply(simp only: aft'_def[symmetric] Suc_eq_plus1[symmetric])
        apply(rule IH[unfolded fstep[symmetric]])
        done
    qed
  qed
qed

text \<open>The number pass follows the reversed stem towards its head, where the reference map is undefined.\<close>

lemma parent_spec_rev_seq:
  assumes "inj_on s {..k}"
  shows "parent_spec (\<lambda>w. if w \<in> s ` {Suc 0..k} then Some (s (inv_into {..k} s w - 1)) else None)"
  unfolding parent_spec_def
proof(rule wf_subset[OF wf_measure], safe)
  fix x y
  assume h: "Some x = (if y \<in> s ` {Suc 0..k} then Some (s (inv_into {..k} s y - 1)) else None)"
  then obtain j where jj: "j \<in> {Suc 0..k}" and yj: "y = s j"
    by (auto split: if_splits)
  hence "inv_into {..k} s y = j" "x = s (j - 1)"
    using assms(1) h
    by (auto simp: inv_into_f_f)
  moreover have "inv_into {..k} s (s (j - 1)) = j - 1"
    using jj
    by (intro inv_into_f_f[OF assms(1)]) auto
  ultimately show "(x, y) \<in> measure (inv_into {..k} s)"
    using jj
    by simp
qed

text \<open>One induction establishes the stem loop's parent updates, unchanged sizes and valid output
  vertices.\<close>

definition stem_parent_result where
  "stem_parent_result P S stm pstm p Sl pst \<longleftrightarrow>
    (\<forall>v. v \<notin> set (follow P stm) \<longrightarrow> prnt Sl v = prnt S v) \<and>
    (\<forall>u w. u \<in> set (follow P stm) \<and> P u = Some w \<and> p \<in> set (follow P w) \<and> w \<noteq> p
      \<longrightarrow> prnt Sl w = Some u) \<and> snum Sl = snum S \<and>
    (stm \<noteq> p \<longrightarrow> prnt Sl stm = Some pstm \<and>
      (\<exists>u. u \<in> set (follow P stm) \<and> P u = Some p \<and> pst = u))"

lemma stem_loop_props:
  assumes "parent_spec P" and "ran P \<subseteq> V"
    and "stem_loop_pre P V S stm pstm lsx aft p \<and> ran (thrd S) \<subseteq> V \<and>
      ran (rvth S) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc S v \<in> V) \<and> set drt \<subseteq> V"
  shows "case stem_loop S stm pstm lsx aft drt p of (Sl, pst, ls, af, dr) \<Rightarrow> stem_parent_result P S stm pstm
    p Sl pst \<and> pst \<in> V \<and> ls \<in> V
           \<and> (\<forall>a. af = Some a \<longrightarrow> a \<in> V) \<and> set dr \<subseteq> V \<and> ran (thrd
             Sl) \<subseteq> V \<and> ran (rvth Sl) \<subseteq> V"
  using assms(3)[unfolded stem_loop_pre_def]
proof(induction arbitrary: S pstm lsx aft drt rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF assms(1), of
  stm]])
  case (1 stm)
  show ?case
  proof(cases "stm = p")
    case True
    have "False" if "u \<in> set (follow P p)" "P u = Some w" "p \<in> set (follow P w)" for u w
      using follow_parent_in_tail[OF assms(1) that(1,2)] ancestor_antisym[OF assms(1) _ that(3)]
      by blast
    thus ?thesis
      using 1(3) True
      by (auto simp: stem_loop.simps[of S p] stem_parent_result_def stem_loop_pre_def)
  next
    case False
    then obtain nxt where Pnxt: "P stm = Some nxt"
      using 1(3) follow_None_ps[OF assms(1), of stm]
      by (cases "P stm") auto
    note fstm = follow_Some_ps[OF assms(1) Pnxt]
    obtain bef where bef: "rvth S stm = Some bef"
      using 1(3) fstm False
      by auto
    define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
    define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(bef := None)\<rparr>
                          | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(bef \<mapsto> a), rvth := (rvth S1)(a
                            \<mapsto> bef)\<rparr>)"
    define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
    define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
    define aft' where "aft' = thrd S3 lsx'"
    have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
      using False 1(3) fstm Pnxt bef
      by (subst stem_loop.simps)
         (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
    have nxtV: "nxt \<in> V" and befV: "bef \<in> V"
      using assms(2) Pnxt 1(3) bef
      by (auto simp: ran_def)
    have S3: "rvth S3 stm = Some bef" "ran (thrd S3) \<subseteq> V" "ran (rvth S3) \<subseteq> V" "lsuc S3 = lsuc S"
      "prnt S3 = (prnt S)(stm \<mapsto> pstm)" "\<forall>v. rvth S v \<noteq> None \<longrightarrow> rvth S3 v \<noteq>
        None"
      "snum S3 = snum S"
      using 1(3) nxtV befV bef
      by (cases aft; auto simp: S3_def S2_def S1_def ran_def)+
    have pre: "stem_loop_pre P V S3 nxt stm lsx' aft' p \<and> ran (thrd S3) \<subseteq> V \<and>
      ran (rvth S3) \<subseteq> V \<and> (\<forall>v\<in>V. lsuc S3 v \<in> V) \<and> set (drt @ [lsx]) \<subseteq> V"
      using 1(3) S3 fstm Pnxt False nxtV befV follow_distinct_ps[OF assms(1), of stm]
      by (auto simp: stem_loop_pre_def lsx'_def aft'_def ran_def)
    note IH = 1(2)[OF Pnxt pre[unfolded stem_loop_pre_def]]
    have "nxt = p \<Longrightarrow> fst (snd (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p)) = stm"
      by (simp add: stem_loop.simps[of S3 p])
    thus ?thesis
      unfolding fstep
      using IH S3 fstm Pnxt False follow_distinct_ps[OF assms(1), of stm]
      by (cases "stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p")
         (auto simp: stem_parent_result_def)
  qed
qed

lemma follow_pred_unique:
  "\<lbrakk>parent_spec P\<rbrakk> \<Longrightarrow>
    x \<in> set (follow P u) \<and> y \<in> set (follow P u) \<and> P x = Some z \<and> P y = Some z
    \<longrightarrow> x = y"
  using follow_linear[of P x u y] follow_Some_ps[of P x z] follow_Some_ps[of P y z]
    follow_parent_in_tail[of P x z z] follow_parent_in_tail[of P y z z]
  by auto

lemma seq_p_in_follow:
  assumes "parent_spec P" and "\<forall>t<k. P (s t) = Some (s (Suc t))"
  shows "t \<le> k \<longrightarrow> s k \<in> set (follow P (s t))"
proof(induction "k - t" arbitrary: t)
  case 0
  thus ?case
    using follow_mem_ps[OF assms(1)]
    by auto
next
  case (Suc d)
  thus ?case
    using Suc.hyps(1)[of "Suc t"] assms(2) follow_Some_ps[OF assms(1), of "s t" "s (Suc t)"]
    by auto
qed

lemma follow_ran_subset:
  assumes "parent_spec P"
  shows "set (follow P u) \<subseteq> insert u (ran P)"
proof(induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF assms(1), of u]])
  case (1 u)
  thus ?case
    using follow_ps_simps[OF assms(1), of u]
    by (cases "P u") (auto simp: ran_def)
qed

lemma dirty_pass_keeps:
  "prnt (dirty_pass S drt) = prnt S \<and> snum (dirty_pass S drt) = snum S \<and> lsuc (dirty_pass S drt) = lsuc S
   \<and> thrd (dirty_pass S drt) = thrd S"
  unfolding dirty_pass_def
  by (induction drt arbitrary: S) (auto split: option.split)

lemma arb_ranges:
  assumes "arb_invar r V S"
  shows "ran (thrd S) \<subseteq> V" "ran (rvth S) \<subseteq> V" "ran (prnt S) \<subseteq> V"
    "finite V" "\<And>v. v \<in> V \<Longrightarrow> lsuc S v \<in> V"
proof-
  show "ran (thrd S) \<subseteq> V" "ran (rvth S) \<subseteq> V"
    using domI[of "rvth S"] domI[of "thrd S"] arb_invarD(8,9,10)[OF assms]
    by (auto simp: ran_def)
  show "ran (prnt S) \<subseteq> V"
    using dVsI(2)[of _ _ "{(y, x) |x y. Some x = prnt S y}"]
      rooted_arborescense_invar_dVs[OF arb_invarD(1)[OF assms]]
    by (auto simp: ran_def eq_commute[of "Some _" "prnt S _"])
  show "finite V" "\<And>v. v \<in> V \<Longrightarrow> lsuc S v \<in> V"
    using assms arb_invarD(11)[OF assms]
    by (auto simp: arb_invar_def)
qed

lemma UT_reversal:
  fixes S0 :: "nat ndtree"
  assumes "arb_invar r V S0" and "i \<in> V" and "j \<in> V"
      and "p \<in> set (follow (prnt S0) i)"
      and "p \<noteq> r"
      and "i \<noteq> p"
      and "old_rev = the (rvth S0 p)"
      and "old_num = snum S0 p"
      and "old_last = lsuc S0 p"
  shows "<ndtree_assn V S0 Ti> ut_reversal_imp Ti i j p old_rev old_num old_last
   <\<lambda>_. ndtree_assn V (ut_reversal_fun S0 i j p old_rev old_num old_last) Ti>"
proof(subst zero_not_in_V_ndtree_assn_extract, rule impI, goal_cases)
  case 1
  note V0 = this
  note rinv = arb_invarD(1)[OF assms(1)] and ps0 = arb_invarD(2)[OF assms(1)]
  have fV: "set (follow (prnt S0) i) \<subseteq> V"
    by (rule follow_subset_V[OF rinv assms(2)])
  have pV: "p \<in> V" and lsx0V: "lsuc S0 i \<in> V" and old_lastV: "old_last \<in> V"
    using assms(4) fV assms(2) arb_invarD(11)[OF assms(1)] assms(9)
    by auto
  note finV = arb_ranges(4)[OF assms(1)]
  have prntrN: "prnt S0 r = None" and rvthN: "\<And>v. v \<in> V - {r} \<Longrightarrow> rvth S0 v \<noteq> None"
    using arb_invarD(5,9)[OF assms(1)]
    by (auto simp: dom_def)
  note ranT0 = arb_ranges(1)[OF assms(1)] and ranR0 = arb_ranges(2)[OF assms(1)]
  note ranP0 = arb_ranges(3)[OF assms(1)]
  have old_revV: "old_rev \<in> V"
    using rvthN[of p] pV assms(5) ranR0 assms(7)
    by (cases "rvth S0 p") (auto simp: ran_def)
  have tcV: "\<And>a. (if old_rev = j then thrd S0 old_last else thrd S0 j) = Some a \<Longrightarrow> a \<in> V"
    using ranT0
    by (cases "old_rev = j") (auto simp: ran_def)
  define Sinit where "Sinit = S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>"
  obtain Sl pst ls af dr where steq: "stem_loop Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p = (Sl, pst, ls, af,
    dr)"
    by (cases "stem_loop Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p") auto
  obtain s k where s0: "s 0 = i" and sk: "s k = p" and step: "\<forall>t<k. prnt S0 (s t) = Some (s (Suc t))"
    and inj: "inj_on s {..k}" and smem: "\<forall>t\<le>k. s t \<in> set (follow (prnt S0) i)"
    by (rule follow_path[OF ps0 assms(4)], rule that) auto
  have kpos: "0 < k"
    using assms(6) s0 sk
    by (cases k) auto
  define P_snl where "P_snl = (\<lambda>w. if w \<in> s ` {Suc 0..k} then Some (s (inv_into {..k} s w - 1)) else None)"
  have psN: "parent_spec P_snl"
    unfolding P_snl_def
    by (rule parent_spec_rev_seq[OF inj])
  have Psnl_val: "P_snl (s t) = Some (s (t - 1))" if "t \<in> {Suc 0..k}" for t
    using that inj
    by (auto simp: P_snl_def inv_into_f_f)
  have ranPsnlS: "ran P_snl \<subseteq> s ` {..k}"
    using inj
    by (auto simp: P_snl_def ran_def inv_into_f_f split: if_splits)
  have ranPsnl: "ran P_snl \<subseteq> V"
    using ranPsnlS smem fV
    by auto
  have skm1: "prnt S0 (s (k - 1)) = Some p"
    using step kpos sk
    by (cases k) auto
  have rvthdef0: "\<forall>v \<in> set (follow (prnt S0) i). p \<in> set (follow (prnt S0) v) \<and> v \<noteq> p
    \<longrightarrow> rvth Sinit v \<noteq> None"
    using fV follow_None_ps[OF ps0 prntrN] assms(5)
    by (auto simp: Sinit_def intro!: rvthN[unfolded not_None_eq])
  have pre: "stem_loop_pre (prnt S0) V Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) p"
    using assms(2-4) lsx0V ranT0 rvthdef0
    by (auto simp: stem_loop_pre_def Sinit_def ran_def)
  have outpre: "stem_loop_pre (prnt S0) V Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) p \<and>
      ran (thrd Sinit) \<subseteq> V \<and> ran (rvth Sinit) \<subseteq> V \<and>
      (\<forall>v \<in> V. lsuc Sinit v \<in> V) \<and> set [j] \<subseteq> V"
    using pre assms(2,3) ranT0 ranR0 arb_invarD(11)[OF assms(1)]
    by (auto simp: Sinit_def ran_def)
  have pstV: "pst \<in> V" and lsV: "ls \<in> V" and afV: "\<forall>a. af = Some a \<longrightarrow> a \<in> V" and
    drV: "set dr \<subseteq> V"
    and ranthrdSl: "ran (thrd Sl) \<subseteq> V"
    and parents: "stem_parent_result (prnt S0) Sinit i j p Sl pst"
    using stem_loop_props[OF ps0 ranP0 outpre] steq
    by auto
  note SLP = parents[unfolded stem_parent_result_def]
  have pstsk: "pst = s (k - 1)"
    using SLP assms(6) smem skm1 follow_pred_unique[OF ps0, where x = pst and u = i and y = "s (k - 1)" and z = p]
    by auto
  have SLpre: "stem_loop_pre (prnt S0) V Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) p \<and>
      length [j] + length (follow (prnt S0) i) \<le> Suc (card V)"
    using pre card_mono[OF finV fV] distinct_card[OF follow_distinct_ps[OF ps0, of i]]
    by simp
  note SL = stem_loop_imp_wf[where Ti = Ti and sp = 1, OF ps0 ranP0, THEN mp, OF SLpre,
    simplified steq prod.case]
  have agrstem: "((prnt Sl)(p \<mapsto> pst)) (s t) = P_snl (s t)" if t: "t \<in> {Suc 0..k}" for t
  proof(cases "t = k")
    case True
    thus ?thesis
      using pstsk sk Psnl_val[OF t]
      by simp
  next
    case False
    hence stp: "s t \<noteq> p"
      using inj_onD[OF inj, of t k] t sk
      by auto
    have "prnt Sl (s t) = Some (s (t - 1))"
      using SLP[THEN conjunct2, THEN conjunct1, rule_format, of "s (t - 1)" "s t"] t False stp sk
        smem[rule_format, of "t - 1"] step[rule_format, of "t - 1"] seq_p_in_follow[OF ps0 step, of t]
      by auto
    thus ?thesis
      using Psnl_val[OF t] stp
      by simp
  qed
  have agr: "\<forall>w \<in> set (follow P_snl p). w \<noteq> i \<longrightarrow> ((prnt Sl)(p \<mapsto> pst)) w =
    P_snl w"
  proof(intro ballI impI)
    fix w
    assume "w \<in> set (follow P_snl p)" "w \<noteq> i"
    moreover have "set (follow P_snl p) \<subseteq> s ` {..k}"
      using follow_ran_subset[OF psN, of p] ranPsnlS sk
      by (auto intro: rev_image_eqI)
    ultimately obtain t where "t \<le> k" "w = s t" "w \<noteq> i"
      by auto
    thus "((prnt Sl)(p \<mapsto> pst)) w = P_snl w"
      using agrstem s0
      by (cases t) auto
  qed
  have TC: "<ndtree_assn V S0 Ti> (if old_rev = j then Array.nth (thrd_impl Ti) old_last else Array.nth (thrd_impl Ti)
    j)
      <\<lambda>r. ndtree_assn V S0 Ti * \<up>(r = nat_of_opt (if old_rev = j then thrd S0 old_last else thrd S0 j))>"
    by (cases "old_rev = j") (sep_auto simp: old_lastV assms(3))+
  note RE = heap_cond_return[where A = "\<lambda>S. ndtree_drt_assn V S Ti (length dr) dr"
    and b = "old_rev \<noteq> j", OF aftT_drt[where aft_opt = af, OF V0 old_revV afV[rule_format], simplified]]
  show ?thesis
    unfolding ut_reversal_imp_def ut_reversal_fun_def Let_def Sinit_def[symmetric] steq prod.case
    apply(rule ht_bind[OF TC], rule ht_extract_pre_pure, hypsubst)
    apply(rule ht_bind[OF ndtree_nth_lsuc[OF assms(2)]], rule ht_extract_pre_pure, hypsubst)
    apply(rule ht_bind[OF ndtree_nth_thrd[OF lsx0V]], rule ht_extract_pre_pure, hypsubst)
    apply(rule ht_bind[OF ndtree_upd_thrd_Some[OF assms(3) assms(2)]])
    apply(rule ht_bind[OF ndtree_assn_to_drt[OF assms(3)]], fold Sinit_def)
    apply(rule ht_bind[OF SL])
    apply(case_tac xe)
    apply(simp only: prod.case)
    apply(rule ht_extract_pre_pure, elim conjE, hypsubst)
    apply(rule ht_bind[OF ndtree_drt_upd_prnt_Some[OF pV pstV]])
    apply(rule ht_bind[OF aftT_drt[OF V0 lsV tcV]], assumption)
    apply(rule ht_bind[OF ndtree_drt_upd_lsuc[OF pV lsV]])
    apply(rule ht_bind[OF RE])
    apply(rule ht_bind[OF dirty_pass_imp_rule[OF V0 drV]])
     apply((use ranthrdSl tcV afV in
       \<open>auto simp: ran_def split: option.splits if_splits\<close>)[1])
    apply(rule ht_bind[OF ndtree_nth_lsuc[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply(rule ht_bind[OF stem_num_loop_imp_wf[OF psN ranPsnl V0, THEN mp]])
     apply((use agr pV lsV SLP in
       \<open>auto simp: Sinit_def split: option.splits if_splits\<close>)[1])
    apply(rule ht_bind[OF ndtree_upd_snum[OF assms(2)]])
    apply sep_auto
    done
qed

text \<open>The refinement needs no join geometry: the stem and fused-pass rules establish partial
  correctness directly. Join geometry is required only for preservation of @{const arb_invar}.\<close>

theorem update_tree_imp_rule:
  assumes "arb_invar r V S" and "i \<in> V" and "j \<in> V"
      and "p \<in> set (follow (prnt S) i)"
      and "jn \<in> V"
      and "p \<noteq> r"
  shows "<ndtree_assn V S Ti>
     update_tree_imp Ti i j p jn
   <\<lambda>_. ndtree_assn V (update_tree S i j p jn) Ti>"
proof-
  note rinv = arb_invarD(1)[OF assms(1)]
  have pV: "p \<in> V"
    using assms(4) follow_subset_V[OF rinv assms(2)]
    by auto
  have pdomP: "p \<in> dom (prnt S)" and pdomR: "p \<in> dom (rvth S)"
    using pV assms(6) arb_invarD(5,9)[OF assms(1)]
    by auto
  have vouteq: "nat_of_opt (prnt S p) = the (prnt S p)" and oldreveq: "nat_of_opt (rvth S p) = the (rvth S p)"
    using pdomP pdomR
    by auto
  note ranT = arb_ranges(1)[OF assms(1)] and ranR = arb_ranges(2)[OF assms(1)]
  note ranP = arb_ranges(3)[OF assms(1)]
  have voutV: "the (prnt S p) \<in> V" and oldrevV: "the (rvth S p) \<in> V" and oldlastV: "lsuc S p \<in> V"
    using pdomP pdomR ranP ranR pV arb_invarD(11)[OF assms(1)]
    by (auto simp: ran_def)
  show ?thesis
    unfolding update_tree_imp_def
    apply(rule ht_bind[OF ndtree_nth_prnt[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply(rule ht_bind[OF ndtree_nth_rvth[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply(rule ht_bind[OF ndtree_nth_snum[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply(rule ht_bind[OF ndtree_nth_lsuc[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply(simp only: vouteq oldreveq)
    apply(fold ut_reversal_imp_def)
    apply(cases "i = p")
    subgoal premises ip
      unfolding update_tree_def Let_def if_P[OF ip]
      apply(rule ht_bind[OF UT_simple[OF assms(2,3) pV oldrevV oldlastV ranT]])
      apply(simp only: Let_def)
      apply(rule UT_tail[OF assms(3,5) pV voutV oldrevV oldlastV, unfolded Let_def])
      done
    subgoal premises ip
      unfolding update_tree_def Let_def if_not_P[OF ip]
      apply(rule ht_bind[OF UT_reversal[OF assms(1-4,6) ip refl refl refl]])
      apply(simp only: ut_reversal_fun_def Let_def)
      apply(rule UT_tail[OF assms(3,5) pV voutV oldrevV oldlastV, unfolded Let_def])
      done
    done
qed

subsection \<open>Refinement of the join / path-pair search @{const get_path_pair_impl}\<close>

text \<open>The join search writes its two paths into the caller's arrays and returns their lengths.\<close>

partial_function (heap) join_paths_loop_imp ::
  "ndtree_impl \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
    \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) Heap" where
  "join_paths_loop_imp Ti a1 a2 u v q1 q2 =
     (if u = v then return (q1, q2)
      else do {
        snu \<leftarrow> Array.nth (snum_impl Ti) u;
        snv \<leftarrow> Array.nth (snum_impl Ti) v;
        (if snu \<le> snv
         then do {
           pu \<leftarrow> Array.nth (prnt_impl Ti) u;
           _ \<leftarrow> Array.upd q1 u a1;
           join_paths_loop_imp Ti a1 a2 pu v (q1 + 1) q2
         }
         else do {
           pv \<leftarrow> Array.nth (prnt_impl Ti) v;
           _ \<leftarrow> Array.upd q2 v a2;
           join_paths_loop_imp Ti a1 a2 u pv q1 (q2 + 1)
         })
      })"

definition get_path_pair_imp :: "ndtree_impl \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat
  \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) Heap" where
  "get_path_pair_imp Ti a1 a2 u v = join_paths_loop_imp Ti a1 a2 u v 0 0"

lemma finite_V_arb: "arb_invar r V S \<Longrightarrow> finite V"
  by (auto simp: arb_invar_def)

lemma join_paths_loop_imp_rule:
  assumes "arb_invar r V S" and "W = (\<lambda>x. takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) x))"
  shows "u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> j \<in> set (follow (prnt S) u) \<Longrightarrow> j
    \<in> set (follow (prnt S) v) \<Longrightarrow>
    set (W u) \<inter> set (W v) = {} \<Longrightarrow> q1 + length (W u) \<le> length xs1 \<Longrightarrow> q2 +
      length (W v) \<le> length xs2 \<Longrightarrow>
    <ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a xs1 * a2 \<mapsto>\<^sub>a xs2>
      join_paths_loop_imp Ti a1 a2 u v q1 q2
    <\<lambda>(r1, r2). \<exists>\<^sub>A ys1 ys2. ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a ys1 * a2 \<mapsto>\<^sub>a
      ys2 *
        \<up>(r1 = q1 + length (W u) \<and> r2 = q2 + length (W v) \<and> length ys1 = length xs1 \<and> length ys2 =
          length xs2 \<and>
          take r1 ys1 = take q1 xs1 @ W u \<and> take r2 ys2 = take q2 xs2 @ W v)>"
proof(induct "length (follow (prnt S) u) + length (follow (prnt S) v)" arbitrary: u v q1 q2 xs1 xs2
    rule: less_induct)
  case (less u v q1 q2 xs1 xs2)
  note rinv = arb_invarD(1)[OF assms(1)] and ps = arb_invarD(2)[OF assms(1)]
  have jV: "j \<in> V"
    using follow_subset_V[OF rinv less.prems(1)] less.prems(3)
    by auto
  have Wj: "W j = []"
    using follow_ne_ps[OF ps, of j] follow_hd_ps[OF ps, of j]
    by (simp add: assms(2) takeWhile_eq_Nil_iff)
  have Wstep: "\<exists>w. prnt S x = Some w \<and> W x = x # W w \<and> w \<in> V \<and> j \<in> set (follow (prnt S)
    w)
      \<and> follow (prnt S) x = x # follow (prnt S) w" if xV: "x \<in> V" and jx: "j \<in> set (follow (prnt S) x)"
      and xj: "x \<noteq> j" for x
  proof-
    obtain w where "prnt S x = Some w" "follow (prnt S) x = x # follow (prnt S) w" "j \<in> set (follow (prnt S) w)"
      using follow_cons_of_anc[OF ps jx xj]
      by blast
    thus ?thesis
      using follow_subset_V[OF rinv xV] follow_mem_ps[OF ps, of w] xj
      by (auto simp: assms(2))
  qed
  have upd: "(take (Suc b) ys)[b := c] = take b ys @ [c]" if "b < length ys" for b ys and c :: nat
    using that
    by (simp add: take_Suc_conv_app_nth list_update_append)
  show ?case
  proof(cases "u = v")
    case True
    hence "W u = []"
      using Wstep[OF less.prems(1,3)] less.prems(5) Wj
      by (cases "u = j") auto
    thus ?thesis
      using True
      by (subst join_paths_loop_imp.simps) sep_auto
  next
    case uv: False
    show ?thesis
    proof(cases "snum S u \<le> snum S v")
      case True
      hence "u \<noteq> j"
        using snum_proper_anc_lt[OF assms(1) jV less.prems(4)] uv
        by auto
      then obtain w where w: "prnt S u = Some w" "W u = u # W w" "w \<in> V" "j \<in> set (follow (prnt S) w)"
        "follow (prnt S) u = u # follow (prnt S) w"
        using Wstep[OF less.prems(1,3)]
        by blast
      note IH = less.hyps[of w v]
      show ?thesis
        using less.prems w uv True
        by (subst join_paths_loop_imp.simps) (sep_auto simp: upd heap: IH)
    next
      case False
      hence "v \<noteq> j"
        using snum_proper_anc_lt[OF assms(1) jV less.prems(3)] uv
        by auto
      then obtain w where w: "prnt S v = Some w" "W v = v # W w" "w \<in> V" "j \<in> set (follow (prnt S) w)"
        "follow (prnt S) v = v # follow (prnt S) w"
        using Wstep[OF less.prems(2,4)]
        by blast
      note IH = less.hyps[of u w]
      show ?thesis
        using less.prems w uv False
        by (subst join_paths_loop_imp.simps) (sep_auto simp: upd heap: IH)
    qed
  qed
qed

text \<open>Arrays of length at least @{term "card V - 1"} suffice for the two branch paths.\<close>

lemma get_path_pair_imp_rule:
  assumes "arb_invar r V S" and "u \<in> V" and "v \<in> V"
      and "card V \<le> Suc (length xs1)" and "card V \<le> Suc (length xs2)"
      and "get_path_pair_impl S u v = (p1, p2)"
  shows "<ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a xs1 * a2 \<mapsto>\<^sub>a xs2>
           get_path_pair_imp Ti a1 a2 u v
         <\<lambda>(r1, r2). \<exists>\<^sub>A ys1 ys2. ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a ys1 * a2
           \<mapsto>\<^sub>a ys2 *
             \<up>(r1 = length p1 \<and> r2 = length p2 \<and> length ys1 = length xs1 \<and> length ys2 = length xs2
               \<and>
               take r1 ys1 = p1 \<and> take r2 ys2 = p2)>"
proof-
  note rinv = arb_invarD(1)[OF assms(1)] and ps = arb_invarD(2)[OF assms(1)]
  define j where "j = join_of (prnt S) u v"
  define W where "W = (\<lambda>x. takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) x))"
  have lst: "last (follow (prnt S) u) = last (follow (prnt S) v)"
    using follow_last_root[OF assms(1) assms(2)] follow_last_root[OF assms(1) assms(3)]
    by simp
  have ju: "j \<in> set (follow (prnt S) u)" and jv: "j \<in> set (follow (prnt S) v)"
    using join_of_mem[OF ps lst]
    by (simp_all add: j_def)
  have disjj: "set (W u) \<inter> set (W v) = {}"
    using join_takeWhile_disjoint[OF assms(1) assms(2) assms(3)]
    by (simp add: j_def W_def)
  have p1eq: "p1 = W u" and p2eq: "p2 = W v"
    using assms(6)
    by (simp_all add: get_path_pair_impl_def
        join_paths_loop_eval[OF assms(1) assms(2) assms(3) ju jv disjj[unfolded W_def], of "[]" "[]"] W_def j_def)
  have Wlen: "length (W x) \<le> card V - 1" if xV: "x \<in> V" for x
  proof-
    have Wsub: "set (W x) \<subseteq> V - {j}"
      using follow_subset_V[OF rinv xV]
      by (auto simp: W_def dest: set_takeWhileD)
    thus ?thesis
      using card_mono[OF _ Wsub] distinct_card[of "W x"] follow_distinct_ps[OF ps, of x] finite_V_arb[OF assms(1)]
        follow_subset_V[OF rinv assms(2)] ju
      by (auto simp: W_def)
  qed
  have b1: "0 + length (W u) \<le> length xs1" and b2: "0 + length (W v) \<le> length xs2"
    using Wlen[OF assms(2)] Wlen[OF assms(3)] assms(4) assms(5)
    by auto
  show ?thesis
    unfolding get_path_pair_imp_def
    by (rule ht_cons_post_prec[OF join_paths_loop_imp_rule[OF assms(1) W_def assms(2) assms(3) ju jv disjj b1 b2]])
      (sep_auto simp: p1eq p2eq)
qed

subsection \<open>Refinement of the subtree iteration @{const iterate_root_opposed_impl}\<close>

partial_function (heap) subtree_fold_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat
  \<Rightarrow> 'ai \<Rightarrow> unit Heap) \<Rightarrow> 'ai \<Rightarrow> unit Heap" where
  "subtree_fold_imp Ti stop u fi ai =
     do {
       _ \<leftarrow> fi u ai;
       (if u = stop then return ()
        else do {
          w \<leftarrow> Array.nth (thrd_impl Ti) u;
          subtree_fold_imp Ti stop w fi ai
        })
     }"

text \<open>The subtree iteration includes both @{term v} and its last descendant @{term "lsuc S v"}.\<close>

definition iterate_root_opposed_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'ai
  \<Rightarrow> unit Heap) \<Rightarrow> 'ai \<Rightarrow> unit Heap" where
  "iterate_root_opposed_imp Ti v fi ai =
     do { ls \<leftarrow> Array.nth (lsuc_impl Ti) v; subtree_fold_imp Ti ls v fi ai }"

lemma follow_thrd_subset_V:
  "\<lbrakk>arb_invar r V S; x \<in> V\<rbrakk> \<Longrightarrow>
    set (follow (thrd S) x) \<subseteq> V"
  using follow_sub_of_mem[of "thrd S" x r]
  by (auto simp: arb_invar_def)

text \<open>@{term "R ai a"} relates the imperative accumulator to its functional value.\<close>

lemma subtree_fold_imp_rule:
  assumes "parent_spec (thrd S)"
      and "\<And>x a. x \<in> V \<Longrightarrow> <R ai a> fi x ai <\<lambda>_. R ai (f x a)>"
  shows "follow (thrd S) u = bl @ stp # rest \<Longrightarrow> stp \<notin> set bl \<Longrightarrow> set (follow (thrd
    S) u) \<subseteq> V \<Longrightarrow>
    <ndtree_assn V S Ti * R ai acc>
      subtree_fold_imp Ti stp u fi ai
    <\<lambda>_. ndtree_assn V S Ti * R ai (subtree_fold S stp u f acc)>"
proof(induct bl arbitrary: u acc)
  case Nil
  thus ?case
    using follow_hd_ps[OF assms(1), of u] follow_mem_ps[OF assms(1), of u]
    by (subst subtree_fold_imp.simps, subst subtree_fold.simps)
       (sep_auto simp: Let_def heap: assms(2))
next
  case (Cons b bs)
  thus ?case
    using follow_ps_simps[OF assms(1), of u] follow_hd_ps[OF assms(1), of u]
    by (cases "thrd S u"; subst subtree_fold_imp.simps; subst subtree_fold.simps)
       (sep_auto simp: Let_def heap: assms(2) Cons.hyps)+
qed

lemma iterate_root_opposed_imp_rule:
  assumes "arb_invar r V S" and "v \<in> V"
      and "\<And>x a. x \<in> V \<Longrightarrow> <R ai a> fi x ai <\<lambda>_. R ai (f x a)>"
  shows "<ndtree_assn V S Ti * R ai acc>
           iterate_root_opposed_imp Ti v fi ai
         <\<lambda>_. ndtree_assn V S Ti * R ai (iterate_root_opposed_impl S v f acc)>"
proof-
  have pst: "parent_spec (thrd S)"
    using assms(1)
    by (simp add: arb_invar_def)
  define rest where "rest = (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
  have L: "follow (thrd S) v = butlast (block S v) @ lsuc S v # rest"
    using block_props[OF assms(1) assms(2)] append_butlast_last_id[of "block S v"]
    by (simp add: rest_def)
  hence notin: "lsuc S v \<notin> set (butlast (block S v))"
    using follow_distinct_ps[OF pst, of v]
    by simp
  show ?thesis
    unfolding iterate_root_opposed_imp_def iterate_root_opposed_impl_def
    by (sep_auto simp: assms(2) heap: subtree_fold_imp_rule[where R = R and f = f and fi = fi and Ti = Ti and ai = ai,
        OF pst assms(3) L notin follow_thrd_subset_V[OF assms(1) assms(2)]])
qed

end
