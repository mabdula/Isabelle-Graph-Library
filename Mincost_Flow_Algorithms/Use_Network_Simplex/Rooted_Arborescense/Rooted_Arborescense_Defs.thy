theory Rooted_Arborescense_Defs
  imports Graph_Algorithms_Dev.Parent_Map
begin

section \<open>Rooted-arborescence invariant\<close>

definition "children T v = {u | u. v \<in> set (follow T u)}"

definition "rooted_arborescense_invar r V T =
    (parent_spec T \<and> r \<in> V \<and> dom T = V - {r} \<and> dVs {(y, x) |x y. (Some x = T y)} = V)"

lemma rooted_arborescense_invarI[intro]:
  assumes "parent_spec T"
    and "r \<in> V"
    and "dom T = V - {r}"
    and "dVs {(y, x) |x y. (Some x = T y)} = V"
  shows "rooted_arborescense_invar r V T"
  unfolding rooted_arborescense_invar_def
  using assms
  by auto

lemma rooted_arborescense_invarE[elim]:
  assumes "rooted_arborescense_invar r V T"
  obtains "parent_spec T" "r \<in> V" "dom T = V - {r}" "dVs {(y, x) |x y. (Some x = T y)} = V"
  using assms unfolding rooted_arborescense_invar_def
  by auto

named_theorems rooted_arborescense_invarD

lemma rooted_arborescense_invar_parent_spec[dest,rooted_arborescense_invarD]:
  "rooted_arborescense_invar r V T \<Longrightarrow> parent_spec T"
  unfolding rooted_arborescense_invar_def
  by auto

lemma rooted_arborescense_invar_r_in_V[dest,rooted_arborescense_invarD]:
  "rooted_arborescense_invar r V T \<Longrightarrow> r \<in> V"
  unfolding rooted_arborescense_invar_def
  by auto

lemma rooted_arborescense_invar_dom[dest,rooted_arborescense_invarD]:
  "rooted_arborescense_invar r V T \<Longrightarrow> dom T = V - {r}"
  unfolding rooted_arborescense_invar_def
  by auto

lemma rooted_arborescense_invar_dVs[dest,rooted_arborescense_invarD]:
  "rooted_arborescense_invar r V T \<Longrightarrow> dVs {(y, x) |x y. (Some x = T y)} = V"
  unfolding rooted_arborescense_invar_def
  by auto

section \<open>The threaded-tree state (last/size representation)\<close>

text \<open>The structure is a record of the five maps (mirroring the array-of-structs layout of real
      implementations such as LEMON's network simplex, where these are
      \<open>_parent\<close> / \<open>_thread\<close> / \<open>_rev_thread\<close> / \<open>_last_succ\<close> /
        \<open>_succ_num\<close>).\<close>
record 'a ndtree =
  prnt :: "'a \<rightharpoonup> 'a"   \<comment> \<open>tree parent map\<close>
  thrd :: "'a \<rightharpoonup> 'a"   \<comment> \<open>thread successor (preorder next)\<close>
  rvth :: "'a \<rightharpoonup> 'a"   \<comment> \<open>thread predecessor (reverse thread)\<close>
  lsuc :: "'a \<Rightarrow> 'a"    \<comment> \<open>last successor: rightmost descendant of the subtree in the
    thread\<close>
  snum :: "'a \<Rightarrow> nat"   \<comment> \<open>subtree size (number of successors, incl. the node itself)\<close>

definition "arb_invar r V S =
  (rooted_arborescense_invar r V (prnt S) \<and>
   parent_spec (thrd S) \<and> parent_spec (rvth S) \<and>
   set (follow (thrd S) r) = V \<and>
   dom (thrd S) = V - {lsuc S r} \<and> dom (rvth S) = V - {r} \<and>
   (\<forall> v v'. thrd S v = Some v' \<longleftrightarrow> rvth S v' = Some v) \<and>
   (\<forall> v \<in> V. lsuc S v \<in> V) \<and>
   (\<forall> v \<in> V. snum S v = card (children (prnt S) v)) \<and>
   (\<forall> v \<in> V. \<exists> pre.
       follow (thrd S) v
         = pre @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w) \<and>
       pre \<noteq> [] \<and> last pre = lsuc S v \<and> set pre = children (prnt S) v))"

lemma arb_invarI[intro]:
  assumes "rooted_arborescense_invar r V (prnt S)"
    and "parent_spec (thrd S)" "parent_spec (rvth S)"
    and "set (follow (thrd S) r) = V"
    and "dom (thrd S) = V - {lsuc S r}" "dom (rvth S) = V - {r}"
    and "\<forall> v v'. thrd S v = Some v' \<longleftrightarrow> rvth S v' = Some v"
    and "\<forall> v \<in> V. lsuc S v \<in> V"
    and "\<forall> v \<in> V. snum S v = card (children (prnt S) v)"
    and "\<forall> v \<in> V. \<exists> pre.
       follow (thrd S) v
         = pre @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w) \<and>
       pre \<noteq> [] \<and> last pre = lsuc S v \<and> set pre = children (prnt S) v"
  shows "arb_invar r V S"
  unfolding arb_invar_def
  using assms
  by auto

section \<open>The tree-update program (port of LEMON's updateTreeStructure)\<close>

text \<open>The stem loop: walk the path nodes from @{term i} (@{text stm}) up to @{term p}, reversing
      parents and re-threading.  @{text pstm} is the new parent of the current stem node,
      @{text lsx} its last successor, @{text aft} the thread node after that block, @{text drt}
      the list of nodes whose reverse-thread must be refreshed afterwards.\<close>
partial_function (tailrec) stem_loop ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> 'a list
    \<Rightarrow> 'a
     \<Rightarrow> ('a ndtree \<times> 'a \<times> 'a \<times> 'a option \<times> 'a list)" where
  "stem_loop S stm pstm lsx aft drt p =
     (if stm = p then (S, pstm, lsx, aft, drt)
      else
        (let nxt_stm = the (prnt S stm);
             S1   = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt_stm)\<rparr>;
             drt1 = drt @ [lsx];
             bef  = the (rvth S1 stm);
             S2   = (case aft of
                       None   \<Rightarrow> S1\<lparr>thrd := (thrd S1)(bef := None)\<rparr>
                     | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(bef \<mapsto> a), rvth := (rvth S1)(a \<mapsto>
                       bef)\<rparr>);
             S3   = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>;
             pstm' = stm;
             stm'  = nxt_stm;
             lsx'  = (if lsuc S3 stm' = lsuc S3 pstm' then the (rvth S3 pstm') else lsuc S3 stm');
             aft'  = thrd S3 lsx'
         in stem_loop S3 stm' pstm' lsx' aft' drt1 p))"

text \<open>Refresh the deferred reverse-thread links recorded in @{text drt}.\<close>
definition dirty_pass :: "'a ndtree \<Rightarrow> 'a list \<Rightarrow> 'a ndtree" where
  "dirty_pass S drt =
     foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w
       \<mapsto> u)\<rparr>) S drt"

text \<open>Recompute @{const snum} and @{const lsuc} for the stem nodes, walking the (now reversed)
      parents from @{term p} down to @{term i}.  @{text sn0} is the pre-surgery @{const snum}.\<close>
partial_function (tailrec) stem_num_loop ::
  "'a ndtree \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a
    \<Rightarrow> 'a ndtree" where
  "stem_num_loop S sn0 u iv acc tls =
     (if u = iv then S
      else (case prnt S u of None \<Rightarrow> S
            | Some par \<Rightarrow>
                (let acc' = acc + (sn0 u - sn0 par);
                     S'   = S\<lparr>snum := (snum S)(u := acc'), lsuc := (lsuc S)(par := tls)\<rparr>
                 in stem_num_loop S' sn0 par iv acc' tls)))"

text \<open>Extend @{const lsuc} from @{term j} towards the root while it still equals @{term j}.\<close>
partial_function (tailrec) last_vin_loop ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a ndtree" where
  "last_vin_loop S u jv lso =
     (if lsuc S u \<noteq> jv then S
      else (let S' = S\<lparr>lsuc := (lsuc S)(u := lso)\<rparr>
            in (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> last_vin_loop S' par jv lso)))"

text \<open>Reset @{const lsuc} from @{term v_out} towards the root (stopping at @{text stp}) while it
      still equals the old last successor.\<close>
partial_function (tailrec) last_vout_loop ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a ndtree" where
  "last_vout_loop S u stp gv sv =
     (if Some u = stp \<or> lsuc S u \<noteq> gv then S
      else (let S' = S\<lparr>lsuc := (lsuc S)(u := sv)\<rparr>
            in (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> last_vout_loop S' par stp gv sv)))"

text \<open>Add the detached size to @{const snum} from @{term j} up to the join.\<close>
partial_function (tailrec) succ_vin_loop ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a ndtree" where
  "succ_vin_loop S u jn d =
     (if u = jn then S
      else (let S' = S\<lparr>snum := (snum S)(u := snum S u + d)\<rparr>
            in (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> succ_vin_loop S' par jn d)))"

text \<open>Subtract the detached size from @{const snum} from @{term v_out} up to the join.\<close>
partial_function (tailrec) succ_vout_loop ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a ndtree" where
  "succ_vout_loop S u jn d =
     (if u = jn then S
      else (let S' = S\<lparr>snum := (snum S)(u := snum S u - d)\<rparr>
            in (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> succ_vout_loop S' par jn d)))"

text \<open>Fused @{term j}-side pass: a single walk of the parent chain from @{term j} that does the
      @{const last_vin_loop} work on @{const lsuc} (guard @{term "la"}: while @{term "lsuc S u = jv"})
      and the @{const succ_vin_loop} work on @{const snum} (guard @{term "sa"}: while @{term "u \<noteq> jn"}).
      Each side latches off independently once its guard first fails, so the walk covers the longer of
      the two prefixes.  See for the equivalence to the two loops.\<close>
partial_function (tailrec) fused_vin_loop ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool
    \<Rightarrow> bool \<Rightarrow> 'a ndtree" where
  "fused_vin_loop S u jv jn lso d la sa =
     (let la' = la \<and> lsuc S u = jv;
          sa' = sa \<and> u \<noteq> jn
      in (if \<not> la' \<and> \<not> sa' then S
          else (let S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := lso) else lsuc S),
                            snum := (if sa' then (snum S)(u := snum S u + d) else snum S)\<rparr>
                in (case prnt S' u of None \<Rightarrow> S'
                    | Some par \<Rightarrow> fused_vin_loop S' par jv jn lso d la' sa'))))"

text \<open>Fused @{term v_out}-side pass: one walk from @{term v_out} doing the @{const last_vout_loop} work
      on @{const lsuc} (guard @{term la}: while @{term "Some u \<noteq> stp \<and> lsuc S u = gv"}) and the
      @{const succ_vout_loop} work on @{const snum} (guard @{term sa}: while @{term "u \<noteq> jn"}).  Passing
      @{term "la = False"} runs only the @{const snum} side (the degenerate @{term "S3 = S2"} case).\<close>
partial_function (tailrec) fused_vout_loop ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>
    nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'a ndtree" where
  "fused_vout_loop S u stp gv sv jn d la sa =
     (let la' = la \<and> Some u \<noteq> stp \<and> lsuc S u = gv;
          sa' = sa \<and> u \<noteq> jn
      in (if \<not> la' \<and> \<not> sa' then S
          else (let S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := sv) else lsuc S),
                            snum := (if sa' then (snum S)(u := snum S u - d) else snum S)\<rparr>
                in (case prnt S' u of None \<Rightarrow> S'
                    | Some par \<Rightarrow> fused_vout_loop S' par stp gv sv jn d la' sa'))))"

paragraph \<open>The orchestrator (port of @{text updateTreeStructure}).\<close>

definition update_tree :: "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>
  'a ndtree" where
  "update_tree S0 i j p jn =
   (let v_out    = the (prnt S0 p);
        old_rev  = the (rvth S0 p);
        old_num  = snum S0 p;
        old_last = lsuc S0 p;
        sn0      = snum S0;
        \<comment> \<open>--- restructure the thread / parent pointers ---\<close>
        S1 =
          (if i = p
           then \<comment> \<open>simple move: the whole subtree of @{term p} goes below @{term j}\<close>
             (let Sa = S0\<lparr>prnt := (prnt S0)(i \<mapsto> j)\<rparr>
              in (if thrd Sa j = Some p then Sa
                  else
                    (let aft1 = thrd Sa old_last;
                         Sb = (case aft1 of
                                 None   \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev := None)\<rparr>
                               | Some a \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev \<mapsto> a),
                                               rvth := (rvth Sa)(a \<mapsto> old_rev)\<rparr>);
                         aft2 = thrd Sb j;
                         Sc = Sb\<lparr>thrd := (thrd Sb)(j \<mapsto> p), rvth := (rvth Sb)(p \<mapsto> j)\<rparr>;
                         Sd = (case aft2 of
                                 None   \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(old_last := None)\<rparr>
                               | Some a \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(old_last \<mapsto> a),
                                               rvth := (rvth Sc)(a \<mapsto> old_last)\<rparr>)
                     in Sd)))
           else \<comment> \<open>genuine path reversal from @{term i} up to @{term p}\<close>
             (let thread_cont = (if old_rev = j then thrd S0 old_last else thrd S0 j);
                  lsx0  = lsuc S0 i;
                  aft0  = thrd S0 lsx0;
                  Sinit = S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>;
                  (Sl, pstm, lsx, aft, drt) = stem_loop Sinit i j lsx0 aft0 [j] p;
                  Sp = Sl\<lparr>prnt := (prnt Sl)(p \<mapsto> pstm)\<rparr>;
                  Sq = (case thread_cont of
                          None   \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx := None)\<rparr>
                        | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx \<mapsto> a), rvth := (rvth Sp)(a
                          \<mapsto> lsx)\<rparr>);
                  Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx)\<rparr>;
                  Ss = (if old_rev \<noteq> j
                        then (case aft of
                                None   \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(old_rev := None)\<rparr>
                              | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(old_rev \<mapsto> a),
                                              rvth := (rvth Sr)(a \<mapsto> old_rev)\<rparr>)
                        else Sr);
                  St = dirty_pass Ss drt;
                  Su = stem_num_loop St sn0 p i 0 (lsuc St p);
                  Sv = Su\<lparr>snum := (snum Su)(i := old_num)\<rparr>
              in Sv));
        \<comment> \<open>--- fix @{const lsuc} and @{const snum} along the branches up to the join, each branch in
              a single fused pass over its parent chain (one traversal touching both arrays) ---\<close>
        up_limit = (if lsuc S1 jn = j then Some jn else None);
        last_out = lsuc S1 p;
        Sa = fused_vin_loop S1 j j jn last_out old_num True True;
        Sb = (if jn \<noteq> old_rev \<and> j \<noteq> old_rev
              then fused_vout_loop Sa v_out up_limit old_last old_rev jn old_num True True
              else if last_out \<noteq> old_last
                   then fused_vout_loop Sa v_out up_limit old_last last_out jn old_num True True
                   else fused_vout_loop Sa v_out up_limit old_last old_last jn old_num False True)
    in Sb)"

section \<open>Subtree iteration along the thread\<close>

text \<open>Fold @{term f} over the subtree of a node by walking the thread from that node up to its
      last successor: in a threaded tree the subtree of a node is exactly the contiguous thread
      block that starts at the node and ends at its last successor @{const lsuc}.  This is a plain
      recursion on @{const thrd}, stopping once @{const lsuc} of the start node has been processed.\<close>
partial_function (tailrec) subtree_fold ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'acc \<Rightarrow> 'acc) \<Rightarrow>
    'acc \<Rightarrow> 'acc" where
  "subtree_fold S stop u f acc =
     (let acc' = f u acc
      in (if u = stop then acc'
          else subtree_fold S stop (the (thrd S u)) f acc'))"

text \<open>The @{term iterate_root_opposed} operation of the arborescence ADT: fold @{term f} over every
      node whose (unique) path to the root passes through @{term v} --- i.e. over the subtree of
      @{term v}, in thread (preorder) order.\<close>
definition iterate_root_opposed_impl ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'acc \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow>
    'acc" where
  "iterate_root_opposed_impl S v f acc = subtree_fold S (lsuc S v) v f acc"

section \<open>The pair-of-paths (join) search\<close>

text \<open>Find the join (lowest common ancestor) of @{term u} and @{term v} by repeatedly lifting
      whichever endpoint currently sits in the smaller subtree --- equivalently the deeper one, since
      @{const snum} strictly increases towards the root --- to its parent, until the two pointers meet.
      The nodes lifted on the @{term u}-side and the @{term v}-side, recorded bottom-up and then
      reversed, are the two branch paths from @{term u} and @{term v} up to (but excluding) the join.\<close>
partial_function (tailrec) join_paths_loop ::
  "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a list
    \<times> 'a list)" where
  "join_paths_loop S u v acc1 acc2 =
     (if u = v then (rev acc1, rev acc2)
      else if snum S u \<le> snum S v
           then join_paths_loop S (the (prnt S u)) v (u # acc1) acc2
           else join_paths_loop S u (the (prnt S v)) acc1 (v # acc2))"

text \<open>The @{term get_path_pair} operation of the arborescence ADT.\<close>
definition get_path_pair_impl :: "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a list \<times> 'a list)"
  where
  "get_path_pair_impl S u v = join_paths_loop S u v [] []"


end
