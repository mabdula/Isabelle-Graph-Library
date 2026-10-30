theory Find_Aug_Path_Subprocedures_Imperative
  imports
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Blossom_Executable.Find_Aug_Path_Subprocedures
begin

provenance ai

section \<open>Imperative refinement of the computation of a path or a blossom\<close>

text \<open>The imperative program mirrors @{const Find_Aug_Path_subprocedures.compute_match_blossom}.
  Paths are stored in arrays. The alternating forest search is a parameter; it returns the two
  alternating paths in two arrays. If the paths end at different roots, they are joined to an
  augmenting path in a new array. Otherwise, the length of their common tail determines the stem
  and the cycle of the blossom, which are copied into two new arrays.\<close>

subsection \<open>Copying parts of arrays\<close>

text \<open>Writing a list into a list from a position on.\<close>

fun put_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "put_list dst off [] = dst"
| "put_list dst off (x # xs) = put_list (list_update dst off x) (Suc off) xs"

lemma length_put_list[simp]: "length (put_list dst off xs) = length dst"
  by (induction xs arbitrary: dst off) auto

lemma put_list_eq:
  "off + length xs \<le> length dst \<Longrightarrow>
   put_list dst off xs = take off dst @ xs @ drop (off + length xs) dst"
proof(induction xs arbitrary: dst off)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  have "put_list (list_update dst off x) (Suc off) xs =
      take (Suc off) (list_update dst off x) @ xs @
      drop (Suc off + length xs) (list_update dst off x)"
    using Cons by (intro Cons.IH) simp
  moreover have "take (Suc off) (list_update dst off x) = take off dst @ [x]"
    using Cons.prems by (simp add: take_Suc_conv_app_nth list_update_append)
  ultimately show ?case
    by simp
qed
lemma put_list_full: "length xs = length dst \<Longrightarrow> put_list dst 0 xs = xs"
  by (simp add: put_list_eq)

text \<open>Copying @{term cnt} entries from position @{term lo} on, and copying @{term cnt} entries
  below position @{term hi} in reverse order.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) copy_fwd_imp ::
  "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "copy_fwd_imp Src lo cnt Dst off =
     (if cnt = 0 then return ()
      else do { x \<leftarrow> Array.nth Src lo;
                _ \<leftarrow> Array.upd off x Dst;
                copy_fwd_imp Src (Suc lo) (cnt - 1) Dst (Suc off) })"

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) copy_rev_imp ::
  "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "copy_rev_imp Src hi cnt Dst off =
     (if cnt = 0 then return ()
      else do { x \<leftarrow> Array.nth Src (hi - 1);
                _ \<leftarrow> Array.upd off x Dst;
                copy_rev_imp Src (hi - 1) (cnt - 1) Dst (Suc off) })"

lemma copy_fwd_imp_rule:
  "\<lbrakk>lo + cnt \<le> length src; off + cnt \<le> length dst\<rbrakk> \<Longrightarrow>
   <Src \<mapsto>\<^sub>a src * Dst \<mapsto>\<^sub>a dst> copy_fwd_imp Src lo cnt Dst off
   <\<lambda>_. Src \<mapsto>\<^sub>a src * Dst \<mapsto>\<^sub>a put_list dst off (take cnt (drop lo src))>"
proof(induction cnt arbitrary: lo off dst)
  case 0
  then show ?case
    by (subst copy_fwd_imp.simps) sep_auto
next
  case (Suc cnt)
  have tk: "take (Suc cnt) (drop lo src) = src ! lo # take cnt (drop (Suc lo) src)"
    using Suc.prems by (simp add: Cons_nth_drop_Suc[symmetric])
  show ?case
    using Suc.prems
    by (subst copy_fwd_imp.simps) (sep_auto heap: Suc.IH simp: tk)
qed

lemma copy_rev_imp_rule:
  "\<lbrakk>cnt \<le> hi; hi \<le> length src; off + cnt \<le> length dst\<rbrakk> \<Longrightarrow>
   <Src \<mapsto>\<^sub>a src * Dst \<mapsto>\<^sub>a dst> copy_rev_imp Src hi cnt Dst off
   <\<lambda>_. Src \<mapsto>\<^sub>a src * Dst \<mapsto>\<^sub>a put_list dst off (rev (take cnt (drop (hi - cnt) src)))>"
proof(induction cnt arbitrary: hi off dst)
  case 0
  then show ?case
    by (subst copy_rev_imp.simps) sep_auto
next
  case (Suc cnt)
  have d: "hi - Suc cnt + cnt = hi - 1"
    using Suc.prems by simp
  have "take (Suc cnt) (drop (hi - Suc cnt) src) =
      take cnt (drop (hi - Suc cnt) src) @ [src ! (hi - 1)]"
    using Suc.prems d by (simp add: take_Suc_conv_app_nth)
  hence tk: "rev (take (Suc cnt) (drop (hi - Suc cnt) src)) =
      src ! (hi - 1) # rev (take cnt (drop (hi - Suc cnt) src))"
    by simp  show ?case
    using Suc.prems
    by (subst copy_rev_imp.simps) (sep_auto heap: Suc.IH simp: tk)
qed

subsection \<open>The common tail of two paths\<close>

text \<open>The number of vertices that @{const longest_disj_sfx} strips from its arguments.\<close>

fun disj_sfx_len :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "disj_sfx_len (x1 # y1 # r1) (x2 # y2 # r2) =
     (if y1 = y2 then Suc (disj_sfx_len (y1 # r1) (y2 # r2)) else 0)"
| "disj_sfx_len r1 r2 = 0"

lemma longest_disj_sfx_drop:
  "longest_disj_sfx r1 r2 = (drop (disj_sfx_len r1 r2) r1, drop (disj_sfx_len r1 r2) r2)"
  by (induction r1 r2 rule: longest_disj_sfx.induct) auto

lemma disj_sfx_len_less:
  "\<lbrakk>r1 \<noteq> []; r2 \<noteq> []\<rbrakk> \<Longrightarrow> disj_sfx_len r1 r2 < length r1 \<and> disj_sfx_len r1 r2 < length r2"
  by (induction r1 r2 rule: disj_sfx_len.induct) auto

lemma disj_sfx_len_short:
  "length r1 \<le> 1 \<or> length r2 \<le> 1 \<Longrightarrow> disj_sfx_len r1 r2 = 0"
  by (cases "(r1, r2)" rule: disj_sfx_len.cases) auto

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) common_tail_imp ::
  "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "common_tail_imp P1 P2 n1 n2 i =
     (if Suc i < n1 \<and> Suc i < n2 then
        do { a \<leftarrow> Array.nth P1 (n1 - Suc (Suc i));
             b \<leftarrow> Array.nth P2 (n2 - Suc (Suc i));
             if a = b then common_tail_imp P1 P2 n1 n2 (Suc i) else return i }
      else return i)"

lemma disj_sfx_len_step:
  assumes "Suc i < length p1" "Suc i < length p2"
  shows "disj_sfx_len (drop i (rev p1)) (drop i (rev p2)) =
    (if p1 ! (length p1 - Suc (Suc i)) = p2 ! (length p2 - Suc (Suc i))
     then Suc (disj_sfx_len (drop (Suc i) (rev p1)) (drop (Suc i) (rev p2))) else 0)"
proof-
  have d: "drop i (rev p) = rev p ! i # p ! (length p - Suc (Suc i)) # drop (Suc (Suc i)) (rev p)"
    "drop (Suc i) (rev p) = p ! (length p - Suc (Suc i)) # drop (Suc (Suc i)) (rev p)"
    if "Suc i < length p" for p :: "'a list"
    using that
    by (simp_all add: Cons_nth_drop_Suc[symmetric] rev_nth Suc_diff_Suc)
  show ?thesis
    by (simp add: d[OF assms(1)] d[OF assms(2)])
qed

lemma common_tail_imp_rule:
  "\<lbrakk>i < length p1; i < length p2\<rbrakk> \<Longrightarrow>
   <P1 \<mapsto>\<^sub>a p1 * P2 \<mapsto>\<^sub>a p2> common_tail_imp P1 P2 (length p1) (length p2) i
   <\<lambda>r. P1 \<mapsto>\<^sub>a p1 * P2 \<mapsto>\<^sub>a p2 *
        \<up>(r = i + disj_sfx_len (drop i (rev p1)) (drop i (rev p2)))>"
proof(induction "length p1 - i" arbitrary: i rule: less_induct)
  case less
  show ?case
  proof(cases "Suc i < length p1 \<and> Suc i < length p2")
    case True
    have IH: "<P1 \<mapsto>\<^sub>a p1 * P2 \<mapsto>\<^sub>a p2> common_tail_imp P1 P2 (length p1) (length p2) (Suc i)
              <\<lambda>r. P1 \<mapsto>\<^sub>a p1 * P2 \<mapsto>\<^sub>a p2 *
                   \<up>(r = Suc i + disj_sfx_len (drop (Suc i) (rev p1)) (drop (Suc i) (rev p2)))>"
      using True less.prems by (intro less.hyps) auto
    show ?thesis
      using True
      by (subst common_tail_imp.simps) (sep_auto heap: IH simp: disj_sfx_len_step)
  next
    case False
    have "disj_sfx_len (drop i (rev p1)) (drop i (rev p2)) = 0"
      using False less.prems by (intro disj_sfx_len_short) auto
    thus ?thesis
      using False
      by (subst common_tail_imp.simps) sep_auto
  qed
qed

subsection \<open>An augmenting path or a blossom from two alternating paths\<close>

datatype \<^marker>\<open>provenance ai_human\<close> 'p match_blossom_res_imp = Path_imp 'p | Blossom_imp 'p 'p

text \<open>The functional computation of @{const Find_Aug_Path_subprocedures.compute_match_blossom}
  once the two alternating paths are found.\<close>

definition "match_blossom_of_paths p1 p2 =
  (if last p1 \<noteq> last p2 then Path (rev p1 @ p2)
   else (case longest_disj_sfx (rev p1) (rev p2) of
           (c1, c2) \<Rightarrow> Blossom (rev (drop (length c1) p1)) (c1 @ rev c2)))"

definition \<^marker>\<open>provenance ai_human\<close> "match_blossom_res_assn R Ri =
  (case (R, Ri) of
     (Path p, Path_imp Pt) \<Rightarrow> Pt \<mapsto>\<^sub>a p
   | (Blossom stem C, Blossom_imp St Ct) \<Rightarrow> St \<mapsto>\<^sub>a stem * Ct \<mapsto>\<^sub>a C
   | _ \<Rightarrow> false)"

definition \<^marker>\<open>provenance ai_human\<close> "blossom_of_paths_imp P1 P2 =
  do { n1 \<leftarrow> Array.len P1;
       n2 \<leftarrow> Array.len P2;
       l1 \<leftarrow> Array.nth P1 (n1 - 1);
       l2 \<leftarrow> Array.nth P2 (n2 - 1);
       x \<leftarrow> Array.nth P1 0;
       if l1 \<noteq> l2 then
         do { R \<leftarrow> Array.new (n1 + n2) x;
              copy_rev_imp P1 n1 n1 R 0;
              copy_fwd_imp P2 0 n2 R n1;
              return (Path_imp R) }
       else
         do { k \<leftarrow> common_tail_imp P1 P2 n1 n2 0;
              S \<leftarrow> Array.new k x;
              copy_rev_imp P1 n1 k S 0;
              C \<leftarrow> Array.new ((n1 - k) + (n2 - k)) x;
              copy_rev_imp P1 (n1 - k) (n1 - k) C 0;
              copy_fwd_imp P2 0 (n2 - k) C (n1 - k);
              return (Blossom_imp S C) } }"

lemma blossom_of_paths_imp_rule:
  assumes "p1 \<noteq> []" "p2 \<noteq> []"
  shows "<P1 \<mapsto>\<^sub>a p1 * P2 \<mapsto>\<^sub>a p2> blossom_of_paths_imp P1 P2
         <\<lambda>R. P1 \<mapsto>\<^sub>a p1 * P2 \<mapsto>\<^sub>a p2 * match_blossom_res_assn (match_blossom_of_paths p1 p2) R>"
proof(cases "last p1 = last p2")
  case False
  define n where "n = length p1 + length p2"
  have arr: "put_list (put_list (replicate n x) 0 (rev (take (length p1) (drop 0 p1))))
               (length p1) (take (length p2) (drop 0 p2)) = rev p1 @ p2" for x
    by (simp add: put_list_eq n_def)
  have res: "match_blossom_of_paths p1 p2 = Path (rev p1 @ p2)"
    using False by (simp add: match_blossom_of_paths_def)
  show ?thesis
    using assms False arr
    by (sep_auto heap: copy_rev_imp_rule copy_fwd_imp_rule
        simp: blossom_of_paths_imp_def res match_blossom_res_assn_def last_conv_nth n_def)
next
  case True
  define k where "k = disj_sfx_len (rev p1) (rev p2)"
  have k: "k < length p1" "k < length p2"
    using disj_sfx_len_less[of "rev p1" "rev p2"] assms by (simp_all add: k_def)
  have stem: "put_list (replicate k x) 0 (rev (take k (drop (length p1 - k) p1))) =
      rev (drop (length p1 - k) p1)" for x
    using k by (simp add: put_list_eq)
  have cyc: "put_list (put_list (replicate (length p1 - k + (length p2 - k)) x) 0
               (rev (take (length p1 - k) (drop (length p1 - k - (length p1 - k)) p1))))
               (length p1 - k) (take (length p2 - k) (drop 0 p2)) =
      drop k (rev p1) @ rev (drop k (rev p2))" for x
    using k by (simp add: put_list_eq drop_rev)
  have res: "match_blossom_of_paths p1 p2 =
      Blossom (rev (drop (length p1 - k) p1)) (drop k (rev p1) @ rev (drop k (rev p2)))"
    using True by (simp add: match_blossom_of_paths_def longest_disj_sfx_drop k_def)
  have CT: "<P1 \<mapsto>\<^sub>a p1 * P2 \<mapsto>\<^sub>a p2> common_tail_imp P1 P2 (length p1) (length p2) 0
            <\<lambda>r. P1 \<mapsto>\<^sub>a p1 * P2 \<mapsto>\<^sub>a p2 * \<up>(r = k)>"
    using common_tail_imp_rule[of 0 p1 p2 P1 P2] assms by (simp add: k_def)
  show ?thesis
    using assms True k stem cyc
    by (sep_auto heap: CT copy_rev_imp_rule copy_fwd_imp_rule
        simp: blossom_of_paths_imp_def res match_blossom_res_assn_def last_conv_nth)
qed

subsection \<open>The program\<close>

definition \<^marker>\<open>provenance ai_human\<close> "alt_paths_assn P r =
  (case P of
     None \<Rightarrow> \<up>(r = None)
   | Some (p1, p2) \<Rightarrow>
       (case r of None \<Rightarrow> false | Some (Pt1, Pt2) \<Rightarrow> Pt1 \<mapsto>\<^sub>a p1 * Pt2 \<mapsto>\<^sub>a p2))"

definition \<^marker>\<open>provenance ai_human\<close> "match_blossom_opt_assn R r =
  (case R of
     None \<Rightarrow> \<up>(r = None)
   | Some B \<Rightarrow> (case r of None \<Rightarrow> false | Some Bi \<Rightarrow> match_blossom_res_assn B Bi))"

locale \<^marker>\<open>provenance ai_human\<close> Find_Aug_Path_Subprocedures_Imperative_spec =
  fixes compute_alt_path_imp :: "'gi \<Rightarrow> 'mi \<Rightarrow> 'v::heap array \<Rightarrow> ('v array \<times> 'v array) option Heap"
begin

definition \<^marker>\<open>provenance ai_human\<close> "compute_match_blossom_imp Gi Mi Vi =
  do { r \<leftarrow> compute_alt_path_imp Gi Mi Vi;
       case r of
         None \<Rightarrow> return None
       | Some (P1, P2) \<Rightarrow> do { R \<leftarrow> blossom_of_paths_imp P1 P2; return (Some R) } }"

end

text \<open>The alternating forest search is a parameter. Its Hoare triple holds for every input whose
  vertex list is not longer than @{term max_vertices}; this bound is needed by the imperative
  search of the theory \<open>Compute_Alt_Path_Imperative\<close>, whose queue has a fixed capacity.\<close>

locale \<^marker>\<open>provenance ai_human\<close> Find_Aug_Path_Subprocedures_Imperative =
  Find_Aug_Path_subprocedures where lookup = lookup and mate_empty = mate_empty +
  Find_Aug_Path_Subprocedures_Imperative_spec where compute_alt_path_imp = compute_alt_path_imp
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
    and mate_empty :: 'mate
    and compute_alt_path_imp :: "'gi \<Rightarrow> 'mi \<Rightarrow> 'v array \<Rightarrow> ('v array \<times> 'v array) option Heap" +
  fixes graph_assn :: "'adjmap \<Rightarrow> 'gi \<Rightarrow> assn"
    and matching_assn :: "'mate \<Rightarrow> 'mi \<Rightarrow> assn"
    and max_vertices :: nat
  assumes compute_alt_path_imp_rule:
    "\<And>H ws N Gi Mi Wi. \<lbrakk>graph_input H ws; matching_invar H N; length ws \<le> max_vertices\<rbrakk> \<Longrightarrow>
       <graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws> compute_alt_path_imp Gi Mi Wi
       <\<lambda>r. graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws *
            alt_paths_assn (compute_alt_path H ws N) r * true>"
begin

lemma compute_match_blossom_of_paths:
  "compute_match_blossom H ws N =
     map_option (\<lambda>(p1, p2). match_blossom_of_paths p1 p2) (compute_alt_path H ws N)"
  by (auto simp: compute_match_blossom_def match_blossom_of_paths_def
      split: option.splits prod.splits)

theorem \<^marker>\<open>provenance ai_human\<close> compute_match_blossom_imp_rule:
  assumes "graph_input H ws" "matching_invar H N" "length ws \<le> max_vertices"
  shows "<graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws> compute_match_blossom_imp Gi Mi Wi
         <\<lambda>r. graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws *
              match_blossom_opt_assn (compute_match_blossom H ws N) r * true>"
proof \<^marker>\<open>provenance ai\<close> (cases "compute_alt_path H ws N")
  case None
  show ?thesis
    using None
    by (sep_auto heap: compute_alt_path_imp_rule[OF assms]
        simp: compute_match_blossom_imp_def compute_match_blossom_of_paths alt_paths_assn_def
          match_blossom_opt_assn_def)
next
  case (Some ps)
  obtain p1 p2 where ps: "ps = (p1, p2)"
    by (cases ps)
  have "compute_alt_path_spec (ugraph_abs H) (matching_abs N) (Some (p1, p2))"
    using compute_alt_path(1)[OF assms(1,2)] Some ps by simp
  hence "odd (length p1)" "odd (length p2)"
    by (auto simp: compute_alt_path_spec_def)
  hence ne: "p1 \<noteq> []" "p2 \<noteq> []"
    by auto
  show ?thesis
    using Some ps
    by (sep_auto heap: compute_alt_path_imp_rule[OF assms] blossom_of_paths_imp_rule[OF ne]
        simp: compute_match_blossom_imp_def compute_match_blossom_of_paths alt_paths_assn_def
          match_blossom_opt_assn_def)
qed

text \<open>The result of the imperative procedure is that of the functional one, and hence satisfies
  @{thm [source] compute_match_blossom}.\<close>

theorem \<^marker>\<open>provenance ai_human\<close> compute_match_blossom_imp_correct:
  assumes "graph_input H ws" "matching_invar H N" "length ws \<le> max_vertices"
  shows "<graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws> compute_match_blossom_imp Gi Mi Wi
         <\<lambda>r. \<exists>\<^sub>A R. graph_assn H Gi * matching_assn N Mi * Wi \<mapsto>\<^sub>a ws *
              match_blossom_opt_assn R r *
              \<up>((\<forall>p. R = Some (Path p) \<longrightarrow>
                   graph_augmenting_path (ugraph_abs H) (matching_abs N) p) \<and>
                (\<forall>stem C. R = Some (Blossom stem C) \<longrightarrow>
                   blossom (ugraph_abs H) (matching_abs N) stem C) \<and>
                ((\<exists>p. graph_augmenting_path (ugraph_abs H) (matching_abs N) p) \<longrightarrow> R \<noteq> None))>"
  using \<^marker>\<open>provenance ai\<close> compute_match_blossom[OF assms(1,2)]
  by \<^marker>\<open>provenance ai\<close> (sep_auto heap: compute_match_blossom_imp_rule[OF assms])

end

end
