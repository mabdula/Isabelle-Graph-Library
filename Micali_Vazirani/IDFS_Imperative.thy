theory IDFS_Imperative
  imports IDFS Imperative.Bounded_Stack_Specs_Imp Imperative.Fixed_Univ_Set_Specs_Imp
begin

section \<open>Imperative Refinement of the Incremental DFS\<close>

text \<open>The imperative program mirrors the incremental DFS of @{theory Micali_Vazirani.IDFS}, i.e.\
      @{const DFS_skel.DFS_skel_impl} as instantiated by @{locale DFS_avoid}, started from a
      single root. The stack is an imperative bounded stack (@{locale bounded_stack_imp}), and the
      avoided, visited and seen vertices are imperative sets over a fixed universe
      (@{locale fixed_univ_set_basic_imp}); the imperative sets are related to the functional ones
      by their abstraction @{term t_set}. The graph is only accessed by an operation that selects
      the next unseen neighbour of a vertex, as the functional search does with @{term sel} and
      @{term diff}, and the target predicate by a test. These operations, the initialisation of the
      seen set and their Hoare triples are parameters. A found path is left on the stack.\<close>

subsection \<open>The program\<close>

locale IDFS_Imperative_spec =
  fixes sel_unseen_imp :: "'gi \<Rightarrow> 'v::heap \<Rightarrow> 'si \<Rightarrow> 'v option Heap"
    and target_imp :: "'v \<Rightarrow> bool Heap"
    and seen_init_imp :: "'si \<Rightarrow> 'si \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and set_isin_imp :: "'si \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and set_insert_imp :: "'v \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and stack_is_empty_imp :: "'stki \<Rightarrow> bool Heap"
    and stack_top_imp :: "'stki \<Rightarrow> 'v Heap"
    and stack_push_imp :: "'stki \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and stack_pop_imp :: "'stki \<Rightarrow> unit Heap"
begin

partial_function (heap) IDFS_loop :: "'gi \<Rightarrow> 'si \<Rightarrow> 'si \<Rightarrow> 'si \<Rightarrow> 'stki \<Rightarrow> bool Heap" where
  "IDFS_loop Gi Ai Vi SNi Si =
     do { e \<leftarrow> stack_is_empty_imp Si;
          if e then return False
          else do { v \<leftarrow> stack_top_imp Si;
                    t \<leftarrow> target_imp v;
                    a \<leftarrow> set_isin_imp Ai v;
                    if t \<and> \<not> a then return True
                    else do { r \<leftarrow> sel_unseen_imp Gi v SNi;
                              (case r of
                                 Some u \<Rightarrow> do { stack_push_imp Si u;
                                               set_insert_imp u SNi;
                                               IDFS_loop Gi Ai Vi SNi Si }
                               | None \<Rightarrow> do { stack_pop_imp Si;
                                             (if a then return () else set_insert_imp v Vi);
                                             IDFS_loop Gi Ai Vi SNi Si }) } } }"

text \<open>The incremental DFS from a root: the root is pushed unless it is avoided or visited, the
      seen set is initialised to the avoided, visited and pushed vertices, and the search runs. It
      returns whether a path was found, together with the visited set; a found path is left on the
      stack.\<close>

definition "IDFS_imp Gi Ai r Vi SNi Si =
  do { a \<leftarrow> set_isin_imp Ai r;
       b \<leftarrow> set_isin_imp Vi r;
       seen_init_imp SNi Ai Vi;
       (if a \<or> b then return () else do { stack_push_imp Si r; set_insert_imp r SNi });
       found \<leftarrow> IDFS_loop Gi Ai Vi SNi Si;
       return (found, Vi) }"

end

subsection \<open>Correctness\<close>

locale IDFS_Imperative =
  IDFS_witness where lookup = lookup +
  IDFS_Imperative_spec where sel_unseen_imp = sel_unseen_imp and stack_push_imp = stack_push_imp +
  stk: bounded_stack_imp where stack_abstract = stack_abstract and stack_push_imp = stack_push_imp +
  vs: fixed_univ_set_basic_imp where U = U and fixed_univ_set_invar = "\<lambda>S. S \<subseteq> U"
    and fixed_univ_set_abstract = id and fixed_univ_set_empty = "{}"
    and fixed_univ_set_insert = Set.insert and fixed_univ_set_delete = "\<lambda>x S. S - {x}"
    and fixed_univ_set_isin = "\<lambda>S x. x \<in> S" and fixed_univ_set_assn = set_assn
    and fixed_univ_set_insert_imp = set_insert_imp and fixed_univ_set_isin_imp = set_isin_imp
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
  and sel_unseen_imp :: "'gi \<Rightarrow> 'v \<Rightarrow> 'si \<Rightarrow> 'v option Heap"
  and stack_push_imp :: "'stki \<Rightarrow> 'v \<Rightarrow> unit Heap"
  and stack_abstract :: "'s \<Rightarrow> 'v list"
  and U :: "'v set"
  and set_assn :: "'v set \<Rightarrow> 'si \<Rightarrow> assn" +
  fixes P :: "'v \<Rightarrow> bool"
    and graph_assn :: "'adjmap \<Rightarrow> 'gi \<Rightarrow> assn"
    and target_assn :: assn
  assumes sel_unseen_rule:
      "\<And>Gi v S Si Sf. \<lbrakk>vset_inv Sf; t_set Sf = S; S \<subseteq> U; v \<in> U\<rbrakk> \<Longrightarrow>
       <graph_assn G Gi * set_assn S Si> sel_unseen_imp Gi v Si
       <\<lambda>r. graph_assn G Gi * set_assn S Si *
            \<up>(r = (if diff (Graph.neighbourhood G v) Sf \<noteq> vset_empty
                   then Some (sel (diff (Graph.neighbourhood G v) Sf)) else None))>"
    and target_rule:
      "\<And>v. v \<in> U \<Longrightarrow> <target_assn> target_imp v <\<lambda>r. target_assn * \<up>(r \<longleftrightarrow> P v)>"
    and seen_init_rule:
      "\<And>A Ai V Vi S SNi. \<lbrakk>A \<subseteq> U; V \<subseteq> U; S \<subseteq> U\<rbrakk> \<Longrightarrow>
       <set_assn A Ai * set_assn V Vi * set_assn S SNi> seen_init_imp SNi Ai Vi
       <\<lambda>_. set_assn A Ai * set_assn V Vi * set_assn (A \<union> V) SNi>"
    and universe: "dVs (Graph.digraph_abs G) \<subseteq> U" "finite U" "card U \<le> cap"
begin

text \<open>The functional search, for an arbitrary initial stack, visited set and avoided set.\<close>

sublocale idfs_av: DFS_avoid
  where lookup = lookup and G = G and stack0 = p0 and vis0 = V0 and avoid = A0 and Pv = P
    and level = lev
  for p0 V0 A0
  by unfold_locales

subsection \<open>Auxiliary lemmas\<close>

lemma isin_iff: "vset_inv S \<Longrightarrow> isin S x \<longleftrightarrow> x \<in> t_set S"
  by (simp add: Graph.vset.set.set_isin)

lemma neighbourhood_in_U: "u \<in> t_set (Graph.neighbourhood G v) \<Longrightarrow> u \<in> U"
  using universe(1) wf_graph(1) by auto

lemma length_less_cap:
  assumes "distinct xs" "set xs \<subseteq> U" "u \<in> U" "u \<notin> set xs"
  shows "length xs < cap"
proof-
  have "set xs \<subseteq> U - {u}"
    using assms(2,4) by auto
  hence "card (set xs) \<le> card (U - {u})"
    using universe(2) by (intro card_mono) auto
  hence "length xs < card U"
    using assms(1,3) universe(2) card_Diff1_less[of U u] by (simp add: distinct_card)
  thus ?thesis
    using universe(3) by simp
qed

subsection \<open>The stack\<close>

definition "stk_assn xs Si = (\<exists>\<^sub>A S. stack_assn S Si * \<up>(stack_invar S \<and> stack_abstract S = xs))"

lemma stk_is_empty_rule:
  "<stk_assn xs Si> stack_is_empty_imp Si <\<lambda>r. stk_assn xs Si * \<up>(r \<longleftrightarrow> xs = [])>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_is_empty_rule simp: stk.stack_is_empty)

lemma stk_top_rule:
  "xs \<noteq> [] \<Longrightarrow> <stk_assn xs Si> stack_top_imp Si <\<lambda>r. stk_assn xs Si * \<up>(r = hd xs)>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_top_rule simp: stk.stack_top)

lemma stk_push_rule:
  "length xs < cap \<Longrightarrow> <stk_assn xs Si> stack_push_imp Si x <\<lambda>_. stk_assn (x # xs) Si>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_push_rule simp: stk.stack_push)

lemma stk_pop_rule:
  "xs \<noteq> [] \<Longrightarrow> <stk_assn xs Si> stack_pop_imp Si <\<lambda>_. stk_assn (tl xs) Si>"
  unfolding stk_assn_def
  by (sep_auto heap: stk.stack_pop_rule simp: stk.stack_pop)


subsection \<open>The search loop\<close>

text \<open>The functional search, unfolded.\<close>

lemma idfs_av_simps:
  "stack st = [] \<Longrightarrow> idfs_av.DFS_avoid_impl A st = st\<lparr>ret := None\<rparr>"
  "\<lbrakk>stack st = v # stl; P v; \<not> isin A v\<rbrakk> \<Longrightarrow>
     idfs_av.DFS_avoid_impl A st = st\<lparr>ret := Some (stack st)\<rparr>"
  "\<lbrakk>stack st = v # stl; \<not> (P v \<and> \<not> isin A v);
    diff (Graph.neighbourhood G v) (seen st) \<noteq> vset_empty\<rbrakk>
   \<Longrightarrow> idfs_av.DFS_avoid_impl A st =
         idfs_av.DFS_avoid_impl A
           (st\<lparr>stack := sel (diff (Graph.neighbourhood G v) (seen st)) # stack st,
               seen := insert (sel (diff (Graph.neighbourhood G v) (seen st))) (seen st)\<rparr>)"
  "\<lbrakk>stack st = v # stl; \<not> (P v \<and> \<not> isin A v);
    diff (Graph.neighbourhood G v) (seen st) = vset_empty\<rbrakk>
   \<Longrightarrow> idfs_av.DFS_avoid_impl A st =
         idfs_av.DFS_avoid_impl A
           (st\<lparr>stack := stl, visited := (if isin A v then visited st else insert v (visited st))\<rparr>)"
  by (auto simp add: idfs_av.av.DFS_skel_impl.simps[of _ st] idfs_av.av_found_def
                     idfs_av.av_on_empty_def idfs_av.av_on_found_def idfs_av.av_on_backtrack_def
                     Let_def)

text \<open>The invariant of the search loop: the stack is distinct and seen, and the seen and visited
      sets are well-formed and lie in the universe.\<close>

definition "loop_inv st =
  (distinct (stack st) \<and> set (stack st) \<subseteq> t_set (seen st) \<and>
   vset_inv (seen st) \<and> t_set (seen st) \<subseteq> U \<and>
   vset_inv (visited st) \<and> t_set (visited st) \<subseteq> U)"

lemma loop_inv_push:
  assumes "loop_inv st" "diff (Graph.neighbourhood G v) (seen st) \<noteq> vset_empty"
  defines "u \<equiv> sel (diff (Graph.neighbourhood G v) (seen st))"
  shows "u \<in> U" "u \<notin> set (stack st)"
        "loop_inv (st\<lparr>stack := u # stack st, seen := insert u (seen st)\<rparr>)"
proof-
  have I: "distinct (stack st)" "set (stack st) \<subseteq> t_set (seen st)" "vset_inv (seen st)"
          "t_set (seen st) \<subseteq> U" "vset_inv (visited st)" "t_set (visited st) \<subseteq> U"
    using assms(1) by (simp_all add: loop_inv_def)
  have N: "vset_inv (Graph.neighbourhood G v)"
    using wf_graph(1) by simp
  have "isin (diff (Graph.neighbourhood G v) (seen st)) u"
    using Graph.vset.choose[OF assms(2)] by (simp add: u_def)
  hence "u \<in> t_set (Graph.neighbourhood G v)" "u \<notin> t_set (seen st)"
    using Graph.vset.set.set_isin[OF set_ops.invar_diff[OF N I(3)]] set_ops.set_diff[OF N I(3)]
    by auto
  thus "u \<in> U" "u \<notin> set (stack st)"
    using neighbourhood_in_U I(2) by auto
  thus "loop_inv (st\<lparr>stack := u # stack st, seen := insert u (seen st)\<rparr>)"
    using I by (auto simp: loop_inv_def Graph.vset.set.set_insert Graph.vset.set.invar_insert)
qed

lemma loop_inv_pop:
  assumes "loop_inv st" "stack st = v # stl"
  shows "loop_inv (st\<lparr>stack := stl, visited := (if b then visited st else insert v (visited st))\<rparr>)"
  using assms
  by (auto simp: loop_inv_def Graph.vset.set.set_insert Graph.vset.set.invar_insert)

lemma IDFS_loop_rule:
  assumes "vset_inv A" "t_set A \<subseteq> U"
  shows
  "<graph_assn G Gi * target_assn * set_assn (t_set A) Ai * set_assn (t_set (visited st)) Vi *
    set_assn (t_set (seen st)) SNi * stk_assn (stack st) Si * \<up>(loop_inv st)>
     IDFS_loop Gi Ai Vi SNi Si
   <\<lambda>r. graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
        set_assn (t_set (visited (idfs_av.DFS_avoid_impl A st))) Vi *
        (\<exists>\<^sub>A S. set_assn S SNi * \<up>(S \<subseteq> U)) *
        stk_assn (case ret (idfs_av.DFS_avoid_impl A st) of None \<Rightarrow> [] | Some q \<Rightarrow> q) Si *
        \<up>(r \<longleftrightarrow> ret (idfs_av.DFS_avoid_impl A st) \<noteq> None)>"
proof(induction arbitrary: st rule: IDFS_loop.fixp_induct)
  case 1
  then show ?case
    by auto
next
  case 2
  then show ?case
    by simp
next
  case (3 f st)
  show ?case
  proof(rule ht_extract_pre_pure(1), goal_cases)
    case 1
    hence inv: "loop_inv st" .
    have I: "distinct (stack st)" "set (stack st) \<subseteq> t_set (seen st)" "vset_inv (seen st)"
            "t_set (seen st) \<subseteq> U" "vset_inv (visited st)" "t_set (visited st) \<subseteq> U"
      using inv by (simp_all add: loop_inv_def)
    show ?case
    proof(cases "stack st")
      case Nil
      thus ?thesis
        using I by (sep_auto heap: stk_is_empty_rule simp: idfs_av_simps(1)[OF Nil])
    next
      case stk: (Cons v stl)
      have vU: "v \<in> U"
        using I(2,4) stk by auto
      have hd: "hd (stack st) = v" and ne: "stack st \<noteq> []"
        using stk by simp_all
      have av_iff: "isin A v \<longleftrightarrow> v \<in> t_set A"
        by (rule isin_iff[OF assms(1)])
      show ?thesis
      proof(cases "P v \<and> v \<notin> t_set A")
        case True
        have F: "idfs_av.DFS_avoid_impl A st = st\<lparr>ret := Some (stack st)\<rparr>"
          using idfs_av_simps(2)[OF stk] True av_iff by simp
        show ?thesis
          using vU hd ne True assms(2) I
          by (sep_auto heap: stk_is_empty_rule stk_top_rule target_rule
                             vs.fixed_univ_set_isin_rule simp: F)
      next
        case notfound: False
        hence nf: "\<not> (P v \<and> \<not> isin A v)"
          using av_iff by simp
        note scan = sel_unseen_rule[OF I(3) refl I(4) vU, of Gi SNi]
        show ?thesis
        proof(cases "diff (Graph.neighbourhood G v) (seen st) \<noteq> vset_empty")
          case True
          define u where "u = sel (diff (Graph.neighbourhood G v) (seen st))"
          note push = loop_inv_push[OF inv True, folded u_def]
          have room: "length (stack st) < cap"
            by (rule length_less_cap[OF I(1) _ push(1,2)]) (use I(2,4) in auto)
          define st' where "st' = st\<lparr>stack := u # stack st, seen := insert u (seen st)\<rparr>"
          have F: "idfs_av.DFS_avoid_impl A st' = idfs_av.DFS_avoid_impl A st"
            using idfs_av_simps(3)[OF stk nf True] by (simp add: st'_def u_def)
          have IH: "<graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
                     set_assn (t_set (visited st)) Vi * set_assn (Set.insert u (t_set (seen st))) SNi *
                     stk_assn (u # stack st) Si>
                      f Gi Ai Vi SNi Si
                    <\<lambda>r. graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
                         set_assn (t_set (visited (idfs_av.DFS_avoid_impl A st))) Vi *
                         (\<exists>\<^sub>A S. set_assn S SNi * \<up>(S \<subseteq> U)) *
                         stk_assn (case ret (idfs_av.DFS_avoid_impl A st) of None \<Rightarrow> [] | Some q \<Rightarrow> q) Si *
                         \<up>(r \<longleftrightarrow> ret (idfs_av.DFS_avoid_impl A st) \<noteq> None)>"
            using 3[of st'] push(3) I(3) unfolding F
            by (simp add: st'_def Graph.vset.set.set_insert)
          show ?thesis
            using vU hd ne notfound True assms(2) I push(1) room
            by (sep_auto heap: stk_is_empty_rule stk_top_rule target_rule vs.fixed_univ_set_isin_rule
                               scan stk_push_rule vs.fixed_univ_set_insert_rule IH
                         simp: u_def[symmetric])
        next
          case False
          hence empty: "diff (Graph.neighbourhood G v) (seen st) = vset_empty"
            by simp
          show ?thesis
          proof(cases "v \<in> t_set A")
            case av: True
            define st' where "st' = st\<lparr>stack := stl, visited := visited st\<rparr>"
            have F: "idfs_av.DFS_avoid_impl A st' = idfs_av.DFS_avoid_impl A st"
              using idfs_av_simps(4)[OF stk nf empty] av_iff av by (simp add: st'_def)
            have inv': "loop_inv st'"
              using loop_inv_pop[OF inv stk, of "v \<in> t_set A"] av by (simp add: st'_def)
            have IH: "<graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
                       set_assn (t_set (visited st)) Vi * set_assn (t_set (seen st)) SNi *
                       stk_assn (tl (stack st)) Si>
                        f Gi Ai Vi SNi Si
                      <\<lambda>r. graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
                         set_assn (t_set (visited (idfs_av.DFS_avoid_impl A st))) Vi *
                         (\<exists>\<^sub>A S. set_assn S SNi * \<up>(S \<subseteq> U)) *
                         stk_assn (case ret (idfs_av.DFS_avoid_impl A st) of None \<Rightarrow> [] | Some q \<Rightarrow> q) Si *
                         \<up>(r \<longleftrightarrow> ret (idfs_av.DFS_avoid_impl A st) \<noteq> None)>"
              using 3[of st'] inv' stk I(5) unfolding F
              by (simp add: st'_def Graph.vset.set.set_insert)
            show ?thesis
              using vU hd ne notfound empty assms(2) I av
              by (sep_auto heap: stk_is_empty_rule stk_top_rule target_rule vs.fixed_univ_set_isin_rule
                                 scan stk_pop_rule vs.fixed_univ_set_insert_rule IH)
          next
            case av: False
            define st' where "st' = st\<lparr>stack := stl, visited := insert v (visited st)\<rparr>"
            have F: "idfs_av.DFS_avoid_impl A st' = idfs_av.DFS_avoid_impl A st"
              using idfs_av_simps(4)[OF stk nf empty] av_iff av by (simp add: st'_def)
            have inv': "loop_inv st'"
              using loop_inv_pop[OF inv stk, of "v \<in> t_set A"] av by (simp add: st'_def)
            have IH: "<graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
                       set_assn (Set.insert v (t_set (visited st))) Vi * set_assn (t_set (seen st)) SNi *
                       stk_assn (tl (stack st)) Si>
                        f Gi Ai Vi SNi Si
                      <\<lambda>r. graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
                         set_assn (t_set (visited (idfs_av.DFS_avoid_impl A st))) Vi *
                         (\<exists>\<^sub>A S. set_assn S SNi * \<up>(S \<subseteq> U)) *
                         stk_assn (case ret (idfs_av.DFS_avoid_impl A st) of None \<Rightarrow> [] | Some q \<Rightarrow> q) Si *
                         \<up>(r \<longleftrightarrow> ret (idfs_av.DFS_avoid_impl A st) \<noteq> None)>"
              using 3[of st'] inv' stk I(5) unfolding F
              by (simp add: st'_def Graph.vset.set.set_insert)
            show ?thesis
              using vU hd ne notfound empty assms(2) I av
              by (sep_auto heap: stk_is_empty_rule stk_top_rule target_rule vs.fixed_univ_set_isin_rule
                                 scan stk_pop_rule vs.fixed_univ_set_insert_rule IH)
          qed
        qed
      qed
    qed
  qed
qed

subsection \<open>The incremental DFS\<close>

lemma initial_state_props:
  assumes "vset_inv A" "vset_inv V" "t_set A \<subseteq> U" "t_set V \<subseteq> U" "set s \<subseteq> U"
          "s = [] \<or> s = [r]"
  shows "loop_inv (idfs_av.avoid_initial_state s V A)"
        "stack (idfs_av.avoid_initial_state s V A) = s"
        "visited (idfs_av.avoid_initial_state s V A) = V"
        "t_set (seen (idfs_av.avoid_initial_state s V A)) = t_set A \<union> t_set V \<union> set s"
  using assms
  by (auto simp: loop_inv_def idfs_av.avoid_initial_state_def idfs_av.vset_of_list_def
                 set_ops.set_union set_ops.invar_union Graph.vset.set.set_insert
                 Graph.vset.set.invar_insert Graph.vset.set.set_empty Graph.vset.set.invar_empty)

definition "seen_assn SNi = (\<exists>\<^sub>A S. set_assn S SNi * \<up>(S \<subseteq> U))"

definition "path_assn res Si = stk_assn (case res of None \<Rightarrow> [] | Some q \<Rightarrow> q) Si"

lemma seen_init_rule':
  "\<lbrakk>A \<subseteq> U; V \<subseteq> U\<rbrakk> \<Longrightarrow>
   <set_assn A Ai * set_assn V Vi * seen_assn SNi> seen_init_imp SNi Ai Vi
   <\<lambda>_. set_assn A Ai * set_assn V Vi * set_assn (A \<union> V) SNi>"
  unfolding seen_assn_def
  by (sep_auto heap: seen_init_rule)

text \<open>The imperative incremental DFS from a root @{term r} computes the result and the visited
      set of the functional one, @{term "IDFS_impl P A [r] V"}. The stack is empty before the
      search; afterwards, it holds the found path, if any. The seen set is internal to the search.\<close>

theorem IDFS_imp_rule:
  assumes "vset_inv A" "vset_inv V" "t_set A \<subseteq> U" "t_set V \<subseteq> U" "r \<in> U"
  shows "<graph_assn G Gi * target_assn * set_assn (t_set A) Ai * set_assn (t_set V) Vi *
          seen_assn SNi * path_assn None Si>
           IDFS_imp Gi Ai r Vi SNi Si
         <\<lambda>(found, Vi'). graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
              set_assn (t_set (snd (IDFS_impl P A [r] V))) Vi' * seen_assn SNi *
              path_assn (fst (IDFS_impl P A [r] V)) Si *
              \<up>(found \<longleftrightarrow> fst (IDFS_impl P A [r] V) \<noteq> None)>"
proof-
  define s where "s = IDFS_stack0 A V [r]"
  have s: "s = (if r \<in> t_set A \<or> r \<in> t_set V then [] else [r])"
    using assms(1,2) by (simp add: s_def IDFS_stack0_def isin_iff)
  have s_props: "set s \<subseteq> U" "s = [] \<or> s = [r]"
    using assms(5) by (simp_all add: s)
  note init = initial_state_props[OF assms(1-4) s_props]
  have loop: "<graph_assn G Gi * target_assn * set_assn (t_set A) Ai * set_assn (t_set V) Vi *
               set_assn SN SNi * stk_assn s Si>
                IDFS_loop Gi Ai Vi SNi Si
              <\<lambda>r'. graph_assn G Gi * target_assn * set_assn (t_set A) Ai *
                    set_assn (t_set (snd (IDFS_impl P A [r] V))) Vi * seen_assn SNi *
                    path_assn (fst (IDFS_impl P A [r] V)) Si *
                    \<up>(r' \<longleftrightarrow> fst (IDFS_impl P A [r] V) \<noteq> None)>"
    if "SN = t_set A \<union> t_set V \<union> set s" for SN
    using IDFS_loop_rule[OF assms(1,3), where st = "idfs_av.avoid_initial_state s V A"]
    unfolding init(2-4) that[symmetric]
    by (simp add: init(1) IDFS_impl_def idfs_av.avoid_final_state_impl_def s_def[symmetric] Let_def
                  seen_assn_def path_assn_def)
  show ?thesis
  proof(cases "r \<in> t_set A \<or> r \<in> t_set V")
    case True
    hence "s = []"
      by (simp add: s)
    note L = loop[unfolded this]
    show ?thesis
      unfolding IDFS_imp_def
      using assms(3-5) True
      by (sep_auto heap: vs.fixed_univ_set_isin_rule seen_init_rule' L simp: path_assn_def)
  next
    case False
    hence "s = [r]"
      by (simp add: s)
    note L = loop[unfolded this]
    have room: "length ([]::'v list) < cap"
      by (rule length_less_cap) (use assms(5) in auto)
    show ?thesis
      unfolding IDFS_imp_def
      using assms(3-5) False room
      by (sep_auto heap: vs.fixed_univ_set_isin_rule seen_init_rule stk_push_rule
                         vs.fixed_univ_set_insert_rule L simp: seen_assn_def path_assn_def)
  qed
qed

end

end
