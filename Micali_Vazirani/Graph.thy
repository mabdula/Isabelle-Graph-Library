theory Graph
imports Main
begin

section\<open>Undirected Graphs\<close>

abbreviation "dblgraph G \<equiv> \<forall>e\<in>G. \<exists>u v. e = {u,v} \<and> u \<noteq> v"

definition Vs where "Vs E \<equiv> \<Union> E"

lemma finite_dbl_finite_verts: "finite G \<Longrightarrow> dblgraph G \<Longrightarrow> finite (Vs G)"
  by (auto simp: Vs_def)

definition connected_at where
  "connected_at v e e' \<equiv> (v \<in> (e \<inter> e'))"

definition degree where
  "degree E v \<equiv> card ({e. v \<in> e} \<inter> E)"

lemma edges_are_Vs:
  assumes "{v, v'} \<in> E"
  shows "v \<in> Vs E"
  unfolding Vs_def
  using assms
  by auto

lemma nempty_tl_hd_tl:
  "(tl l) \<noteq>[] \<Longrightarrow> l = (hd l) # (tl l)"
  by (induct "l"; simp)

lemma lt_sum:
  assumes "(\<Sum>x\<in>s. g x) < (\<Sum>x\<in>s. f x)"
        shows "\<exists>(x::'a ) \<in> s. ((g::'a \<Rightarrow> nat) x < f x)"
  using assms sum_mono
  by (metis not_le)

lemma Union_lt:
  assumes finite: "finite S" "finite t" "finite u" and
    card_lt: "card ((\<Union> S) \<inter> t) < card ((\<Union> S) \<inter> u)" and 
    disj: "\<forall>s\<in>S.\<forall>s'\<in>S. s \<noteq> s' \<longrightarrow> s \<inter> s' = {}"
  shows "\<exists>s\<in>S. card (s \<inter> t) < card (s \<inter> u)"
proof-
  {
    fix t::"'a set"
    assume ass: "finite t"
    have "card (\<Union>s\<in>S. s \<inter> t) = (\<Sum>s\<in>S. card (s \<inter> t))"
      apply(intro card_UN_disjoint finite)
      subgoal using ass by simp
      subgoal using disj by auto
      done
  }note * = this
  show ?thesis
    apply (intro lt_sum)
    using card_lt *[OF finite(2)] *[OF finite(3)]
    by auto
qed

lemma less_edges_less_degree:
  assumes "finite E"
          "v \<in> Vs (E - E')"
        shows "degree (E - E') v \<le> degree E v"
  using assms
  unfolding degree_def Vs_def
  by (simp add: card_mono subset_iff)

lemma subset_edges_less_degree:
  assumes "finite E"
          "v \<in> Vs E'"
          "E' \<subseteq> E"
        shows "degree E' v \<le> degree E v"
  using assms 
  by (simp add: degree_def card_mono subset_iff)

lemma Vs_subset:
  assumes "E \<subseteq> E'"
  shows "Vs E \<subseteq> Vs E'"
  using assms
  unfolding Vs_def
  by auto

lemma card3_subset:
  assumes "card s \<ge> 3"
  shows "\<exists>x y z. {x, y, z} \<subseteq> s \<and> x \<noteq> y  \<and> x \<noteq> z  \<and> y \<noteq> z"  
  using assms by(auto simp: numeral_3_eq_3 card_le_Suc_iff)


subsection \<open>Paths: lists of vertices that are not necessarily simple\<close>

locale path_abs =

fixes P::"'a \<Rightarrow> 'a \<Rightarrow> bool" and P0::"'a \<Rightarrow> bool"

begin

(*fun path_abs where
  path0: "path_abs [] = True" |
  path1: "path_abs [v] = P0 v" |
  path2: "path_abs (v#v'#vs) = (P v v' \<and> path_abs (v'#vs))"*)

inductive path_abs where
  path0: "path_abs []" |
  path1: "P0 v \<Longrightarrow> path_abs [v]" |
  path2: "P v v' \<Longrightarrow> path_abs (v'#vs) \<Longrightarrow> path_abs (v#v'#vs)"

(*
inductive path_abs where
  path0: "path_abs P P0 []" |
  path1: "P0 v \<Longrightarrow> path_abs P P0 [v]" |
  path2: "P v v' \<Longrightarrow> path_abs P P0 (v'#vs) \<Longrightarrow> path_abs P P0 (v#v'#vs)"

thm path_abs.induct

abbreviation "path G p \<equiv> path_abs (\<lambda>v1 v2. {v1, v2} \<in> G) (\<lambda>v. v \<in> Vs G) p"

inductive path where
  path0: "path G []" |
  path1: "v \<in> Vs G \<Longrightarrow> path G [v]" |
  path2: "{v, v'} \<in> G \<Longrightarrow> path G (v'#vs) \<Longrightarrow> path G (v#v'#vs)"

thm path.induct*)

(*lemma "path G p \<Longrightarrow>
(\<And>G. P G []) \<Longrightarrow>
(\<And>v G. v \<in> Vs G \<Longrightarrow> P G [v]) \<Longrightarrow>
(\<And>v v' G vs. {v, v'} \<in> G \<Longrightarrow> path G (v' # vs) \<Longrightarrow> P G (v' # vs) \<Longrightarrow> P G (v # v' # vs)) \<Longrightarrow> P G p"
  apply(rule path_abs.induct[of p "\<lambda>v1 v2. {v1,v2} \<in> G" "\<lambda>v. v \<in> Vs G"])
     apply blast
  apply blast
  sledgehammer
  by auto*)

declare path0[simp]

inductive_simps path_1[simp]: "path_abs [v]"

inductive_simps path_2[simp]: "path_abs (v # v' # vs)"

lemma tl_path_abs_is_path_abs:
  "path_abs p \<Longrightarrow> path_abs (tl p)"
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  show ?case
  proof(cases p)
    case Nil
    then show ?thesis by (simp) 
  next
    case p: (Cons h l)
    show ?thesis 
    proof(cases l)
      case Nil
      then show ?thesis using Cons by (auto simp add: Vs_def p)
    next
      case l: (Cons h' l')
      then show ?thesis
        using Cons
        by (simp add: p)
    qed
  qed
qed

lemma path_abs_append:
  assumes "path_abs p1" "path_abs p2" "P (last p1) (hd p2)"
  shows "path_abs (p1 @ p2)"
  using assms
proof(induction )
  case path0
  then show ?case
    by simp
next
  case (path1 v)
  show ?case
  proof(cases p2)
    case T1: Nil
    then show ?thesis
      by (simp add: path1)
  next
    case F1: (Cons a' p2')
    then show ?thesis
      using path_abs.path2 path1.prems(1,2)
      by simp
  qed
next
  case (path2 v v' vs)
  then have "path_abs ((v' # vs) @ p2)"
    by auto
  then show ?case
    using path2
    by auto
qed

lemma mem_path_abs_Vs: 
  assumes "path_abs p" "\<And>v v'. P v v' \<Longrightarrow> P0 v \<and> P0 v'" "a\<in>set p" 
  shows "P0 a"
  using assms
proof(induction)
  case path0
  then show ?case by simp
next
  case (path1 v)
  then show ?case by simp
next
  case (path2 v v' vs)
  then show ?case
    by auto
qed

lemma path_abs_suff:
  assumes "path_abs (p1 @ p2)"
  shows "path_abs p2"
  using assms
proof(induction p1)
  case Nil
  then show ?case
    by (simp)
next
  case (Cons a p1)
  then show ?case
      using Cons tl_path_abs_is_path_abs
      by force
qed

lemma path_abs_pref:
  assumes "path_abs (p1 @ p2)" "\<And>v v'. P v v' \<Longrightarrow> P0 v \<and> P0 v'"
  shows "path_abs p1"
  using assms
proof(induction p1)
  case Nil
  then show ?case
    by (simp)
next
  case (Cons a p1)
  then show ?case
    apply (cases p1)
    using tl_path_abs_is_path_abs mem_path_abs_Vs[OF _ Cons(3)]
    by fastforce+
qed

lemma rev_path_is_path:
  assumes "path E p"
  shows "path E (rev p)"
  using assms
proof(induction)
  case path0
  then show ?case by (simp)
next
  case path1
  then show ?case by (simp)
next
  case path2
  then show ?case
    apply (simp)
    using path_append path_suff
    by (smt append_assoc append_butlast_last_id butlast.simps(2) edges_are_Vs insert_commute last_ConsR last_snoc list.sel(1) list.simps(3) path1)
qed

lemma v_in_apath_in_Vs:
  assumes "path E p" "v \<in> set p"
  shows "v \<in> Vs E"
  using assms
proof(induction)
  case path0
  then show ?case
    by simp
next
  case path1
  then show ?case
    by simp
next
  case path2
  then show ?case
    unfolding Vs_def
    by auto
qed

lemma path_subset:
  assumes "path E p"
          "E \<subseteq> E'"
        shows "path E' p"
  using assms
proof(induction)
  case path0
  then show ?case by (simp)
next
  case path1
  then show ?case
    using Vs_subset
    by auto 
next
  case path2
  then show ?case
    by (auto)
qed

lemma mid_path_deg_ge_2:
  assumes "path E p"
    "v \<in> set p"
    "v \<noteq> hd p"
    "v \<noteq> last p"
    "distinct p"
    "finite E"
  shows "degree E v \<ge> 2"
  using assms
proof(induction)
  case path0
  then show ?case
    by simp
next
  case path1
  then show ?case
    by simp
next
  case (path2 u u' E us)
  then show ?case 
  proof(cases "v = u'")
    case True
      have "{{u, u'}} \<subseteq> (Collect ((\<in>) u') \<inter> E)"
        using path2
        by (auto simp add: split: if_splits)
      then show ?thesis
        using path2
        apply (cases us; auto simp add: Ball_def Vs_def degree_def numeral_2_eq_2 card_le_Suc0_iff_eq not_le less_Suc_eq_le split: if_splits)
        by (smt Int_insert_left Set.set_insert card_le_Suc0_iff_eq doubleton_eq_iff finite_Int insertI1 insert_commute mem_Collect_eq not_less_eq_eq)+
  next
    case False
    then show ?thesis
      apply(intro path2)
      using path2 by simp+
  qed
qed

lemma path_repl_edge:
  assumes "path E' p" "p \<noteq> []" "E' = (insert {w,x} E)" "path E puv" "hd puv = w" "last puv = x" "puv \<noteq> []"
  shows "\<exists>p'. p' \<noteq> [] \<and> path E p' \<and> hd p' = hd p \<and> last p' = last p"
  using assms
proof(induction)
  case path0
  then show ?case
    using path0
    by fastforce
next
  case path1
  then show ?case
    unfolding Vs_def
    apply simp
    using path_1
    by (metis UnionI Vs_def hd_in_set last_ConsL last_in_set list.sel(1) path1.prems(1) v_in_apath_in_Vs)
next
  case (path2 v v' _ vs)
  then obtain p' where p': "p' \<noteq> []" "path E p'" "hd p' = hd (v' # vs)" "last p' = last (v' # vs)"
    by auto
  show ?case
  proof(cases "w =v")
    case T1: True
    show ?thesis
    proof(cases "x = v'")
      case T2: True
      then have "path E (puv @ tl p')"
      proof(cases "tl p' = []")
        case True
        then show ?thesis using path2.prems by simp
      next
        case False
        then show ?thesis
          apply (intro path_append tl_path_is_path path2 p'(2))
          using T2 p'(1-3) path2.prems
          using path.simps by fastforce
      qed
      then show ?thesis
        by (metis (mono_tags, hide_lams) Nil_is_append_conv T1 T2 hd_append2 last.simps last_ConsR last_appendR last_tl list.collapse list.discI list.sel(1) p'(1) p'(3) p'(4) path2.prems(3) path2.prems(4) path2.prems(5) path2.prems(6))
    next
      case False
      then have "{v,v'} \<in> E"
        using path2.prems
        by (metis T1 doubleton_eq_iff insertE path2.hyps(1))
      then show ?thesis
        using path2
        by (metis (no_types, hide_lams) append_Cons append_Nil edges_are_Vs last.simps list.sel(1) path_append path1)
    qed
  next
    case F1: False
    then show ?thesis
      using path2
    proof(cases "x = v'")
      case T2: True
      then have "{v,v'} \<in> E"
        using path2.prems
        by (metis F1 doubleton_eq_iff insertE path2.hyps(1))
      then show ?thesis
        using path2
        by (metis (no_types, hide_lams) append_Cons append_Nil edges_are_Vs last.simps list.sel(1) path_append path1)
    next
      case F2: False
      show ?thesis
      proof(cases "x = v")
        case T3: True
        show ?thesis
        proof(cases "w = v'")
          case T4: True
          then have "path E ((rev puv) @ tl p')"
          proof(cases "tl p' = []")
            case True
            then show ?thesis using path2.prems
              by (simp add: rev_path_is_path)
          next
            case F3: False
            then show ?thesis
              apply (intro path_append rev_path_is_path tl_path_is_path path2 p'(2))
              using F2 F3 T3 T4  p'(1-3) path2.prems
              apply simp
              by (metis last_rev list.exhaust_sel path_2)
          qed
          then show ?thesis
            by (smt T3 T4 append_is_Nil_conv hd_append2 hd_conv_nth hd_rev last_ConsR last_append last_conv_nth last_rev last_tl length_tl list.distinct(1) list.sel(1) list.size(3) p'(1) p'(3) p'(4) rev_is_Nil_conv path2.prems(4) path2.prems(5) path2.prems(6))
        next
          case False
          then have "{v,v'} \<in> E"
            using path2.prems
            using F1 path2.hyps(1) by blast
          then show ?thesis
            using path2
            by (metis (no_types, hide_lams) append_Cons append_Nil edges_are_Vs last.simps list.sel(1) path_append path1)
        qed
      next
        case False
        moreover with F1 F2 have "{v,v'} \<in> E"
          using path2.prems
          using F1 path2.hyps(1) by blast
        then show ?thesis
          using path2
          by (metis (no_types, hide_lams) append_Cons append_Nil edges_are_Vs last.simps list.sel(1) path_append path1)
      qed
    qed
  qed
qed

lemma path_can_be_split:
  assumes "path E' p" "E' = insert {w,x} E" "{w,x} \<subseteq> Vs E" "p \<noteq> []"
  shows "(\<exists>p'. p' \<noteq> [] \<and> path E p' \<and> hd p' = hd p \<and> last p' = last p) \<or>
         (\<exists>p1 p2. p1 \<noteq> [] \<and> p2 \<noteq> [] \<and> path E p1 \<and> path E p2 \<and>
                             ((last p1 = w \<and> hd p2 = x) \<or> (last p1 = x \<and> hd p2 = w)) \<and>
                             hd p1 = hd p \<and> last p2 = last p)"
  using assms
proof(induction)
  case path0
  then show ?case 
    by (simp)
next
  case path1
  then show ?case
    apply (simp add: Vs_def)
    by (metis last.simps list.sel(1) Vs_def mem_simps(9) path.path1 path1.prems(3))
next
  case (path2 v v' _ vs)
  show ?case
  proof(cases "(\<exists>p'. p' \<noteq> [] \<and> path E p' \<and> hd p' = hd (v' # vs) \<and> last p' = last (v'# vs))")
    case T1: True
    then obtain p' where p': "p' \<noteq> [] \<and> path E p' \<and> hd p' = hd (v' # vs) \<and> last p' = last (v' # vs)"
      by fastforce
    show ?thesis
    proof(cases "{v, v'} \<in> E")
      case T2: True
      then have "path E (v # p') \<and> hd (v # p') = hd (v # v' # vs) \<and> last (v # p') = last (v # v' # vs)"
        using p'
        apply simp
        by (metis (no_types, hide_lams) append_Cons append_Nil edges_are_Vs last.simps  path_append path1)
      then show ?thesis
        using T1
        by auto
    next
      case F2: False
      then have "{v, v'} = {w, x}"
        using path2 
        by simp
      then have "path E [v] \<and> path E p' \<and>
                 (last [v] = w \<and> hd p' = x \<or> last [v] = x \<and> hd p' = w)
                 \<and> hd (v # p') = hd [v] \<and> last (v # p') = last p'"
        using F2 path2 T1 p'
        by (auto simp add: doubleton_eq_iff)
      then show ?thesis
        by (metis last_ConsR list.distinct(1) list.sel(1) p')
    qed
  next
    case F1: False
    then obtain p1 p2 where p1p2: "p1 \<noteq> [] \<and> p2 \<noteq> [] \<and> path E p1 \<and> path E p2 \<and>
                                   (last p1 = w \<and> hd p2 = x \<or> last p1 = x \<and> hd p2 = w) \<and>
                                   hd (v' # vs) = hd p1 \<and> last (v' # vs) = last p2"
      using path2
      by (metis list.distinct(1))
    show ?thesis
    proof(cases "{v, v'} \<in> E")
      case T2: True
      then have "(v # p1) \<noteq> [] \<and> p2 \<noteq> [] \<and> path E (v # p1) \<and> path E p2 \<and>
                 (last (v # p1) = w \<and> hd p2 = x \<or> last (v # p1) = x \<and> hd p2 = w) \<and>
                 hd (v # v' # vs) = hd (v # p1) \<and> last (v # v' # vs) = last p2"
        using p1p2
        apply simp
        by (metis (no_types, hide_lams) append_Cons append_Nil edges_are_Vs last.simps path_append path1)
      then show ?thesis
        by metis
    next
      case F2: False
      then have "{v, v'} = {w, x}"
        using path2 
        by simp
      obtain p1' a p2' b where p1'p2': "p1 = p1' @ [a]" "p2 = b # p2'"
        using p1p2
        using rev_exhaust list.exhaust
        by metis
      then have abwx: "(a = w \<and> b = x) \<or> (a = x \<and> b = w)"
        using p1p2
        by auto
      then show ?thesis
        by (metis F1 \<open>{v, v'} = {w, x}\<close> doubleton_eq_iff last_ConsR list.distinct(1) list.sel(1) p1p2)
    qed
  qed
qed

lemma path_can_be_split_2:
  assumes "path E' p" "E' = insert {w,x} E" "w \<in> Vs E" "x \<notin> Vs E" "p \<noteq> []"
  shows "(\<exists>p'. p' \<noteq> [] \<and> path E p' \<and> hd p' = hd p \<and> last p' = last p) \<or>
         (\<exists>p'. path E p' \<and> (p' \<noteq> [] \<longrightarrow> hd p' = w) \<and> ((hd p = last (x # p') \<and> last p = x) \<or> (hd p = x \<and> last p = last (x # p'))))"
  using assms
proof(induction)
  case path0
  then show ?case 
    by (simp)
next
  case path1
  then show ?case
    apply (simp add: Vs_def)
    by (metis Sup_insert Un_iff distinct.simps(2) distinct_singleton empty_set insert_iff last.simps list.sel(1) Vs_def path.path1 path1.hyps path1.prems(2,4))
next
  case (path2 v v' _ vs)
  show ?case
  proof(cases "(\<exists>p'. path E p' \<and>
          (p' \<noteq> [] \<longrightarrow> hd p' = w) \<and>
          (hd (v' # vs) = last (x # p') \<and> last (v' # vs) = x \<or> hd (v' # vs) = x \<and> last (v' # vs) = last (x # p')))")
    case T1: True
    then obtain p' where p':  "path E p' \<and>
       (p' \<noteq> [] \<longrightarrow> hd p' = w) \<and>
       (hd (v' # vs) = last (x # p') \<and> last (v' # vs) = x \<or> hd (v' # vs) = x \<and> last (v' # vs) = last (x # p'))"
      by fastforce
    show ?thesis
    proof(cases "{v, v'} \<in> E")
      case T2: True
      then have "(p' \<noteq> [] \<longrightarrow> hd p' = w) \<and> path E (p' @ [v]) \<and> (hd (v # v' # vs) = last (p' @ [v]) \<and> last (v # v' # vs) = x)"
        using p'
        apply (simp split: if_splits add: edges_are_Vs)
        by (smt edges_are_Vs insert_commute list.sel(1) path_append path1 path2.prems(3))+
      then show ?thesis
        using path2 T1
        by (metis T2 edges_are_Vs hd_append insert_commute last_ConsL last_ConsR list.sel(1) p' snoc_eq_iff_butlast)
    next
      case F2: False
      then have "{v, v'} = {w, x}"
        using path2 
        by simp
      show ?thesis
      proof(cases "v = w")
        case T3: True
        then have v'x: "v' = x"
          using F2
          using \<open>{v, v'} = {w, x}\<close> doubleton_eq_iff by fastforce
        show ?thesis
        proof(cases "path E p' \<and> (hd (v' # vs) = last (x # p') \<and> last (v' # vs) = x)")
          case True
          then show ?thesis
            using T3 
            apply (simp split: if_splits)
            subgoal using path1 path2.prems(2) by (fastforce simp del: path_1)
            subgoal using path0 p' by blast
            subgoal using path1 path2.prems(2) by(force simp del: path_1)
            subgoal using p' v'x by blast
            done
        next
          case False
          then have "path E p' \<and> (hd (v' # vs) = x \<and> last (v' # vs) = last (x # p'))"
            using p'
            by blast
          then show ?thesis 
            apply (simp split: if_splits)
            subgoal using T3 path1 path2.prems(2) by (fastforce simp del: path_1)
            subgoal using False by auto
            subgoal proof-
              have "{w, x} \<notin> E"
                using assms(4)
                unfolding Vs_def
                by auto
              moreover have "w \<noteq> x"
                using assms(3,4)
                by blast
              moreover assume " p' \<noteq> []" "vs = []"
              ultimately show ?thesis
                apply(simp add: T3)
                using p' by auto
            qed
            subgoal proof-
              assume "p' \<noteq> []"
                "vs \<noteq> []"
                "path E p' \<and> v' = x \<and> last vs = last p'"
              then have "path E p' \<and> hd p' = hd (v # v' # vs) \<and> last p' = last (v # v' # vs)"
                apply simp
                using T3 p' by blast
              then show ?thesis
                using T3 \<open>p' \<noteq> []\<close> p' by blast
            qed
            done
        qed
      next
        case F3: False
        then have "v = x" "v' = w"
          using doubleton_eq_iff
          using \<open>{v, v'} = {w, x}\<close> by fastforce+
        then show ?thesis
          using p'
          by (metis last.simps list.sel(1) path0)
      qed
    qed
  next
    case F1: False
    then obtain p' where p': "p' \<noteq> [] \<and> path E p' \<and> hd p' = hd (v' # vs) \<and> last p' = last (v' # vs)"
      using path2
      by auto
    show ?thesis
    proof(cases "{v, v'} \<in> E")
      case T2: True
      then have "path E (v # p') \<and> hd (v # p') = hd (v # v' # vs) \<and> last (v # p') = last (v # v' # vs)"
        using p'
        by (auto split: if_splits simp add: neq_Nil_conv)
      then show ?thesis
        by blast
    next
      case F2: False
      then have "{v, v'} = {w, x}"
        using path2 
        by simp
      then have "v = x"
        using p'
        apply (simp add: doubleton_eq_iff)
        by (metis list.set_sel(1) mem_path_Vs path2.prems(3))
      then show ?thesis
        using p'
        using \<open>{v, v'} = {w, x}\<close> by fastforce
    qed
  qed
qed

lemma path_can_be_split_3:
  assumes "path E' p" "E' = insert {w,x} E" "w \<notin> Vs E" "x \<notin> Vs E" "p \<noteq> []"
  shows "path E p \<or> path {{w, x}} p"
  using assms
proof(induction)
  case path0
  then show ?case 
    by (simp)
next
  case path1
  then show ?case
    by (auto simp add: Vs_def)
next
  case (path2 v v' _ vs)
  show ?case
  proof(cases "path E (v' #  vs)")
    case True
    then have "path E (v # v' # vs)"
      by (smt doubleton_eq_iff insert_iff list.set_intros(1) mem_path_Vs path.path2 path2.hyps path2.prems(1,2,3))
    then show ?thesis
      by auto
  next
    case False
    then have path: "path {{w,x}} (v' # vs)"
      using path2
      by auto
    then have "v' = w \<or> v' = x"
      by (cases "vs"; auto simp add: doubleton_eq_iff Vs_def)
    then have "path {{w,x}} (v # v' # vs)"
      using path
      by (metis (no_types, lifting) edges_are_Vs insert_commute insert_iff path.path2 path2.hyps(1) path2.prems(1-3))
    then show ?thesis
      by auto
  qed
qed

lemma v_in_apath_in_Vs_append:
  assumes "path E (p1 @ v # p2)"
  shows "v \<in> Vs E"
  using assms
  by (meson list.set_intros(1) path_suff v_in_apath_in_Vs)

lemma path_Vs_subset:
assumes "path E p"
shows "set p \<subseteq> Vs E"
  using assms
proof(induction p)
  case (path0 E)
  then show ?case by simp
next
  case (path1 v E)
  then show ?case by simp
next
  case (path2 v v' E vs)
  then show ?case by (auto simp add: Vs_def)
qed

lemma construct_path:
  assumes
    paths: "path G p1" "path G p2"
    "{hd p1, hd p2} \<in> G"
  shows "path G ((rev p1) @ p2)"
  by (metis Nil_is_rev_conv last_rev path_append paths(1) paths(2) paths(3) rev_path_is_path self_append_conv2)

lemma edge_between_pref_suff:
  "p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> path G (p1 @ p2) \<Longrightarrow> {last p1, hd p2} \<in> G"
  apply(induction p1; cases p2; auto)
  using tl_path_is_path
  by fastforce

text \<open>A function to remove a cycle from a path\<close>

fun remove_cycle_pfx where
"remove_cycle_pfx a [] = []" |
"remove_cycle_pfx a (b#l) = (if (a = b) then (remove_cycle_pfx a l) else (b#l))"

lemma remove_cycle_pfx_works:
 "\<exists>pfx. (l = pfx @ (remove_cycle_pfx h l) \<and> (\<forall>x\<in>set pfx. x = h))"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then obtain pfx where "l = pfx @ remove_cycle_pfx h l \<and> (\<forall>x\<in>set pfx. x = h)"
    by blast
  then have *: "a # l = (a # pfx) @ remove_cycle_pfx a l \<and> (\<forall>x\<in>set pfx. x = a)" if "h = a"
    using append_Cons that by auto
  show ?case
  proof(cases "h = a")
    case True
    then show ?thesis
      unfolding remove_cycle_pfx.simps
      apply simp
      using *
      by (meson set_ConsD)
  next
    case False
    then show ?thesis
      unfolding remove_cycle_pfx.simps
      by simp
  qed
qed

lemma remove_cycle_pfx_works_card_ge_2:
 "card (set l) \<ge> 2 \<Longrightarrow> (hd (remove_cycle_pfx (last l) l) \<noteq> last (remove_cycle_pfx (last l) l) \<and> (set (remove_cycle_pfx (last l) l) = set l))"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  show ?case
  proof(cases "card (set l) < 2")
    case True
    then show ?thesis
      using Cons(2)
      apply simp
      by (metis List.finite_set One_nat_def Suc_1 Suc_le_eq card.insert card_empty insert_absorb last_in_set list.set(1) not_le order_refl)
  next
    case False
    then have *: "card (set l) \<ge> 2"
      by simp
    show ?thesis
      using Cons(1)[OF *]
      using "*" by force
  qed
qed

subsection \<open>Theory about edges in a path\<close>

fun edges_of_path where
"edges_of_path [] = []" |
"edges_of_path [v] = []" |
"edges_of_path (v#v'#l) = {v,v'} # (edges_of_path (v'#l))"

lemma edges_of_path_append:
  "\<exists>ep. (edges_of_path (p @ p')) = ep @ (edges_of_path p')"
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  show ?case
  proof(cases p)
    case Nil
    show ?thesis
      proof(cases p')
        case Nil
        then show ?thesis by simp
      next
        case p': Cons
        thus ?thesis
          using Nil Cons[unfolded p']
          by (auto simp add: neq_Nil_conv)
      qed
  next
    case p: Cons
    then show ?thesis
      using Cons
      by (auto simp add: neq_Nil_conv)
  qed
qed

lemma edges_of_path_append_2:
  assumes "p' \<noteq> []"
  shows "(edges_of_path (p @ p')) = (edges_of_path (p @ [hd p'])) @ (edges_of_path p')"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons _ p)
  show ?case
  proof(cases p)
    case Nil
    show ?thesis
      proof(cases p')
        case Nil
        then show ?thesis using Cons by simp
      next
        case p': (Cons)
        then show ?thesis
          using Nil Cons
          by simp
      qed
  next
    case p: Cons
    then show ?thesis
      using Cons
      by (auto)
  qed
qed

lemma edges_of_path_rev:
  shows "rev (edges_of_path p) = edges_of_path (rev p)"
proof(induction "length p" arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc x)
  then obtain a' p' where p': "p = a' # p'"
    by (metis length_Suc_conv)
  then have "rev (edges_of_path p') = edges_of_path (rev p')"
    using Suc
    by auto
  then show ?case
    using p' edges_of_path_append_2
    apply (cases p' ;simp)
    by (smt edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append_2 insert_commute list.distinct(1) list.sel(1))
qed

lemma length_edges_of_path:
  "length (edges_of_path l) = (length l - 1)"
proof(induction l)
  case Nil
  then show ?case
    by simp
next
  case cons1: (Cons a l)
  then show ?case
  proof(cases l)
    case Nil
    then show ?thesis by auto
  next
    case cons2: (Cons a' l')
    then show ?thesis
    proof(cases l')
      case Nil
      then show ?thesis using cons2 by auto
    next
      case (Cons a list)
      then show ?thesis using cons1 cons2 by auto
    qed 
  qed
qed

lemma length_edges_of_path_2:
  assumes "l \<noteq> []"
  shows "length (edges_of_path l) + 1 = length l"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by simp
next
  case cons1: (Cons a l)
  then show ?case
  proof(cases l)
    case Nil
    then show ?thesis by auto
  next
    case cons2: (Cons a' l')
    then show ?thesis
    proof(cases l')
      case Nil
      then show ?thesis using cons2 by auto
    next
      case (Cons a list)
      then show ?thesis using cons1 cons2 by auto
    qed 
  qed
qed

lemma edges_of_path_nempty:
  "edges_of_path xs \<noteq> [] \<longleftrightarrow> length xs \<ge> 2"
  apply(induction xs)
  subgoal by simp
  subgoal for x xs
    by(cases xs; auto)
  done

lemma v_in_edge_in_path:
  assumes "{u, v} \<in> set (edges_of_path p)"
  shows "u \<in> set p"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case by (cases p; auto)
qed

lemma v_in_edge_in_path_gen:
  assumes "e \<in> set (edges_of_path p)" "u \<in> e"
  shows "u \<in> set p"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case by (cases p; auto)
qed

lemma distinct_edges_of_vpath:
  assumes "distinct p"
  shows "distinct (edges_of_path p)"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case
    apply (cases p; simp)
    using v_in_edge_in_path
    by fastforce
qed

lemma distinct_edges_of_paths_cons:
  assumes "distinct (edges_of_path (v # p))"
  shows "distinct (edges_of_path p)"
  using assms
  by(cases "p"; simp)

lemma last_v_in_last_e: 
  assumes "length p \<ge> 2"
  shows "last p \<in> last (edges_of_path p)"
  using assms
proof(induction "p")
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  show ?case
  proof(cases p)
    case Nil
    then show ?thesis using Cons by simp
  next
    case p: Cons
    then show ?thesis using Cons apply (auto split: if_splits)
      subgoal using edges_of_path.elims by blast
      subgoal by (simp add: Suc_leI)
      done      
  qed
qed

lemma hd_v_in_hd_e: 
  assumes "length p \<ge> 2"
  shows "hd p \<in> hd (edges_of_path p)"
  using assms
proof(induction "p")
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  show ?case
  proof(cases p)
    case Nil
    then show ?thesis using Cons by simp
  next
    case Cons
    then show ?thesis
      by (auto split: if_splits)
  qed
qed

lemma hd_edges_neq_last:
  assumes "{hd p, last p} \<notin> set (edges_of_path p)" "hd p \<noteq> last p" "p \<noteq> []"
  shows "hd (edges_of_path (last p # p)) \<noteq> last (edges_of_path (last p # p))"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons)
  then show ?case
    apply (auto split: if_splits)
    using edges_of_path.elims apply blast
    by (simp add: insert_commute)
qed

lemma edges_of_path_append_subset:
  shows "set (edges_of_path p') \<subseteq> set (edges_of_path (p @ p'))"
  using edges_of_path_append
  by (metis eq_iff le_supE set_append)

lemma in_edges_of_path:
  assumes "v \<in> set p" "v \<noteq> hd p" "v \<noteq> last p"
  shows "v \<in> Vs (set (edges_of_path p))"
  using assms
proof(induction p)
  case Nil
  then show ?case
    by simp
next
  case (Cons _ p)
  then show ?case
    apply (cases p; simp add: Vs_def split: if_splits)
    by blast
qed

lemma degree_edges_of_path_ge_2:
  assumes "distinct p"
  shows "\<forall>v\<in>set p. v \<noteq> hd p \<and> v \<noteq> last p \<longrightarrow> degree (set (edges_of_path p)) v \<ge> 2"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then have hyp: "2 \<le> degree (set (edges_of_path p)) v" if  "v\<in>set p" "v \<noteq> hd p" "v \<noteq> last p" for v
    using that
    by simp
  show ?case
  proof(cases p)
    case Nil
    then show ?thesis 
      using Cons
      by simp
  next
    case p: (Cons a' p')
    show ?thesis
    proof(cases p')
      case Nil
      then show ?thesis
        using Cons p by simp
    next
      case p': (Cons a'' p'')
      then have "{a, a'} \<noteq> {a', a''}"
        using Cons.prems p
        by auto
      then have "2 \<le> degree (set (edges_of_path (a # p))) a'"
        using p p'
        unfolding degree_def
        by (auto simp add: card_insert not_le)
       moreover have "2 \<le> degree (set (edges_of_path (a # p))) v" if  "v\<in>set p" "v \<noteq> hd p" "v \<noteq> last p" for v
         apply(rule le_trans[where j = "degree (set (edges_of_path p)) v"])
         subgoal using hyp[OF that] .
         subgoal apply(rule subset_edges_less_degree)
           subgoal by simp
           subgoal using in_edges_of_path[OF that] .
           subgoal using p by auto
           done
         done
       ultimately show ?thesis
         unfolding p
         apply auto
         by blast
    qed
  qed
qed

lemma degree_edges_of_path_ge_2':
  assumes "distinct p" "v\<in>set p" "v \<noteq> hd p" "v \<noteq> last p"
  shows "degree (set (edges_of_path p)) v \<ge> 2"
  using assms degree_edges_of_path_ge_2
  by auto

lemma last_in_edge:
  assumes "p \<noteq> []"
  shows "\<exists>u. {u, last p} \<in> set (edges_of_path (v # p)) \<and> u \<in> set (v # p)"
  using assms
proof(induction "length p" arbitrary: v p)
  case 0
  then show ?case by simp
next
  case (Suc x)
  show ?case
  proof(cases p)
    case Nil
    then show ?thesis
      using Suc
      by auto
  next
    case p: (Cons _ p')
    show ?thesis
    proof(cases "p' = []")
      case True
      then show ?thesis
        using p
        by auto
    next
      case False
      then show ?thesis
        using Suc
        by(auto simp add: p)
    qed
  qed
qed

lemma degree_edges_of_path_ge_2_all:
  assumes "distinct p" "length p \<ge> 3" "v\<in>set p"
  shows "degree (set (edges_of_path (last p # p))) v \<ge> 2"
proof(cases "v = hd p \<or> v = last p")
  case True
  moreover obtain a a' a'' p' where p: "p = a # a' # a'' # p'"
    using assms(2)
    apply(cases p; simp)
    by (metis One_nat_def Suc_1 Suc_le_length_iff)
  ultimately have "v = a \<or> v = last (a'' # p')"
    by auto
  moreover have "degree (set (edges_of_path (last p # p))) a \<ge> 2"
    using assms(1)
    unfolding p degree_def
    by (auto simp add: card_insert insert_Diff_if doubleton_eq_iff split: if_splits)
  moreover have "degree (set (edges_of_path (last p # p))) (last (a'' # p')) \<ge> 2"
    unfolding p 
    apply (auto simp add: doubleton_eq_iff split: if_splits)
    subgoal using assms(1)
      by(auto simp add: p degree_def card_insert card_Diff_singleton_if)
    subgoal proof-
      assume ass: "p' \<noteq> []"
      define E where "E = {e. last p' \<in> e} \<inter> ((insert {last p', a} (insert {a, a'} (insert {a', a''} (set (edges_of_path (a'' # p')))))))"
      obtain u where u: "{u, last p'} \<in> set (edges_of_path (a'' # p')) \<and> u \<in> set (a'' # p')" "u \<in> set (a'' # p')"
        using last_in_edge[OF ass]
        by auto
      moreover have "{u, last p'} \<noteq> {a, last p'}"
        using assms(1) u
        by (auto simp add: p doubleton_eq_iff)
      moreover have "{u, last p'} \<in> E"
        "{a, last p'} \<in> E"
        using u E_def
        by auto
      moreover have "card s \<ge> 2" if "finite s" "x \<in> s" "y \<in> s" "x \<noteq> y" for x y s
        using that
        by (metis One_nat_def Suc_1 Suc_leI Suc_mono card_gt_0_iff card_insert_disjoint finite_insert insertE mk_disjoint_insert)
      moreover have "finite E"
        using E_def
        by auto
      ultimately show ?thesis
        unfolding degree_def E_def
        by metis
    qed
    done
  ultimately show ?thesis
    by auto
next
  case False
  then show ?thesis
    using degree_edges_of_path_ge_2 assms(1)
    by (smt List.finite_set assms(3) degree_edges_of_path_ge_2 dual_order.trans edges_of_path.simps(3) ex_in_conv in_edges_of_path list.exhaust_sel set_empty set_subset_Cons subset_edges_less_degree)
qed

lemma last_edge_in_last_vert_in:
  assumes "length p \<ge> 2" "last (edges_of_path p) \<in> E"
  shows "last p \<in> Vs E"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case cons1: (Cons a p)
  show ?case 
  proof(cases "p")
    case Nil
    then show ?thesis 
      using cons1
      by simp
  next
    case cons2: (Cons a' p')
    then show ?thesis
      using cons1
      apply(auto split: if_splits)
      subgoal unfolding Vs_def
        by auto
      subgoal 
        using edges_of_path.elims by blast
      subgoal 
        by (simp add: Suc_le_eq)
      done
  qed
qed

lemma hd_edge_in_hd_vert_in:
  assumes "length p \<ge> 2" "hd (edges_of_path p) \<in> E"
  shows "hd p \<in> Vs E"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case cons1: (Cons a p)
  show ?case 
  proof(cases "p")
    case Nil
    then show ?thesis 
      using cons1
      by simp
  next
    case cons2: (Cons a' p')
    then show ?thesis
      using cons1
      by(auto simp add: Vs_def split: if_splits)
  qed
qed

lemma path_edges_subset:
  assumes "path E p"
  shows "set (edges_of_path p) \<subseteq> E"
  using assms
proof(induction)
  case path0
  then show ?case
    by simp
next
  case path1
  then show ?case 
    by simp
next
  case path2
  then show ?case
    by simp
qed

lemma last_vert_in_last_edge:
  assumes "last p \<in> e" "e \<in> set (edges_of_path p)" "distinct p" "length p \<ge> 2"
  shows "e = last (edges_of_path p)"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case cons1: (Cons a p)
  then show ?case
  proof(cases p)
    case Nil
    then show ?thesis using cons1 by simp
  next
    case cons2: (Cons a' p')
    then show ?thesis 
      using cons1 cons2 not_less_eq_eq
      by (auto split: if_splits)
  qed
qed

lemma degree_inc:
  assumes "finite E1" "e \<notin> E1" "v \<in> e"
  shows "degree (insert e E1) v = degree E1 v + 1"
  using assms
  unfolding degree_def
  by auto

lemma edges_of_path_snoc:
  assumes "p \<noteq> []"
  shows "(edges_of_path p) @ [{last p, a}] = edges_of_path (p @ [a])"
proof-
  have "edges_of_path (p @ [a]) = rev (edges_of_path (a # rev p))"
    using edges_of_path_rev[of "p @ [a]"]
    by (metis rev.simps(2) rev_rev_ident)
  then have "... = rev ({a, last p} # edges_of_path (rev p))"
    using assms
    by (metis edges_of_path.simps(3) hd_rev list.exhaust_sel rev_is_Nil_conv)
  then show ?thesis
    using edges_of_path_rev[of "p"]
    by (metis \<open>edges_of_path (p @ [a]) = rev (edges_of_path (a # rev p))\<close> doubleton_eq_iff rev.simps(2) rev_rev_ident)
qed

lemma degree_hd:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (hd p) = 1"
  using assms
proof(induction "length p" arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc x)
  show ?case
    apply(rule rev_cases[of p])
    subgoal using Suc by simp
    subgoal for p' a' proof-
      assume p': "p = p' @ [a']"
      show ?thesis
      proof(cases "length p' < 2")
        case True
        then show ?thesis
          apply(cases p'; simp)
          using Suc(4) p' by (auto simp add: degree_def)
      next
        case False
        then have lenp': "length p' \<ge> 2"
          by simp
        then have "degree (set (edges_of_path p')) (hd p') = 1"
          apply(intro Suc)
          using Suc p' by auto
        then have "degree (set (edges_of_path p')) (hd p) = 1"
          using Suc p'
          by (metis \<open>2 \<le> length p'\<close> hd_append le_zero_eq list.size(3) zero_neq_numeral)
        moreover have "hd p \<notin> {last p', a'}"
          (* Long metis call *)
          apply auto
           apply (metis False One_nat_def Suc.prems(1) Suc_1 distinct.simps(2) distinct_rev hd_append2 last_ConsR last_in_set length_Suc_conv less_Suc_eq list.exhaust_sel list.size(3) p' rev.simps(1) rev.simps(2) rev_append self_append_conv2)
            by (metis False One_nat_def Suc.hyps(2) Suc.prems(1) Suc_1 distinct.simps(2) last_ConsR last_in_set last_snoc length_Suc_conv lessI less_SucI list.sel(1) list.size(3) p' self_append_conv2)
        moreover have "edges_of_path (p' @ [a']) = edges_of_path p' @ [{last p', a'}]"
          apply(intro edges_of_path_snoc[symmetric])
          using lenp' by auto
        ultimately show ?thesis
          using p' edges_of_path_snoc[symmetric]
          unfolding degree_def
          by simp
      qed
    qed
    done
qed

lemma in_edges_of_path_split: "e \<in> set (edges_of_path p) \<Longrightarrow> \<exists>v1 v2 p1 p2. e = {v1, v2} \<and> p = p1 @ [v1, v2] @ p2"
proof(induction p)
  case Nil
  then show ?case
    by auto
next
  case (Cons v p')
  then have "p' \<noteq> []"
    by auto
  show ?case
  proof(cases "e \<in> set (edges_of_path p')")
    case True
    then show ?thesis
      using Cons
      by (metis append_Cons)
  next
    case False
    then have "e = {v, hd p'}"
      using Cons
      by (cases p'; auto)
    moreover have "v # p' = [] @ [v, hd p'] @ tl p'"
      using \<open>p' \<noteq> []\<close>
      by auto
    ultimately show ?thesis
      by metis
  qed
qed

lemma in_edges_of_path_hd_or_tl:
      assumes "e \<in> set (edges_of_path p)"
      shows "e = hd (edges_of_path p) \<or> e \<in> set (edges_of_path (tl p))"
proof-
  obtain v1 v2 p1 p2 where "e = {v1, v2}" "p = p1 @ [v1, v2] @ p2"
    using in_edges_of_path_split[OF assms]
    by auto
  then show ?thesis
    apply(cases "p1 = []"; simp)
    using edges_of_path_append_2
    by (metis edges_of_path.simps(3) in_set_conv_decomp list.distinct(1))
qed

lemma where_is_v:
  assumes "e \<in> set (edges_of_path (p @ (v # p')))" "v \<in> e" "v \<notin> set p" "v \<notin> set p'" "p \<noteq> []"
  shows "e = {last p, v} \<or> e = {v, hd p'}"
proof-
  obtain v1 v2 p1 p2 us
    where v1v2p1p2us:
      "e = {v1, v2}" 
      "p = p1 @ us \<and> us @ v # p' = v1 # v2 # p2 \<or> p @ us = p1 \<and> v # p' = us @ v1 # v2 # p2"
    using in_edges_of_path_split[OF assms(1)]
    apply(simp add: append_eq_append_conv2)
    by metis
  moreover have "v1 = v \<or> v2 = v"
    using assms(2) v1v2p1p2us
    by auto
  ultimately consider
    "p = p1 @ us \<and> us @ v # p' = v # v2 # p2" |
    "p @ us = p1 \<and> v # p' = us @ v # v2 # p2" |
    "p = p1 @ us \<and> us @ v # p' = v1 # v # p2" |
    "p @ us = p1 \<and> v # p' = us @ v1 # v # p2"
    by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using assms(3-) v1v2p1p2us(1)
      by (metis \<open>v1 = v \<or> v2 = v\<close> append_eq_Cons_conv in_set_conv_decomp list.sel(1) list.sel(3))
  next
    case 2
    then show ?thesis
      using assms(3-) v1v2p1p2us(1)
      by (metis \<open>v1 = v \<or> v2 = v\<close> append.assoc append_Cons_eq_iff list.sel(1) list.set_intros(1))
  next
    case 3
    then have "v \<notin> set us"
      using assms(3) v1v2p1p2us(1)
      by auto
    then have "e = {last us, v}"
      using assms(4) v1v2p1p2us(1)
      by (metis "3" \<open>v1 = v \<or> v2 = v\<close> hd_append2 last_ConsL list.exhaust_sel list.sel(1) list.sel(3) list.set_intros(1) list.set_sel(2) self_append_conv2 tl_append2)
    then have "e = {last p, v}"
      by (metis "3" assms(4) last_appendR list.inject list.set_intros(1) self_append_conv2)
    then show ?thesis
      by simp
  next
    case 4
    then show ?thesis
      using assms(3-) v1v2p1p2us(1)
      by (metis Cons_in_lists_iff append.left_neutral append_in_lists_conv in_listsI list.sel(3) same_append_eq tl_append2)
  qed
qed

lemma length_edges_of_path_rev[simp]: "length (edges_of_path (rev p)) = length (edges_of_path p)"
  by (simp add: length_edges_of_path)

lemma mem_eq_last_edge:
  assumes "distinct p" "e \<in> set (edges_of_path p)" "last p \<in> e"
  shows "e = last (edges_of_path p)"
  using assms
proof(induction p arbitrary: e)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a' p')
  then show ?case
    by (smt One_nat_def Suc_1 Suc_le_mono dual_order.trans edges_of_path.simps(2) equals0D last_vert_in_last_edge le_less le_zero_eq length_0_conv length_Cons list.set(1) not_less_eq_eq)
qed

lemma edges_of_path_disj:
  assumes "set p1 \<inter> set p2 = {}"
  shows "set (edges_of_path p1) \<inter> set (edges_of_path p2) = {}"
  using assms
proof(induction p1 arbitrary: p2)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a1' p1')
  then show ?case
    by (cases p1'; auto simp add: v_in_edge_in_path)
qed

lemma edges_of_path_nempty_edges:
  assumes "e \<in> set (edges_of_path p)"
  shows "e \<noteq> {}"
  using assms
proof(induction p)
  case Nil
  then show ?case by auto
next
  case (Cons a' p')
  then show ?case by (cases p'; auto)
qed

lemma edges_of_path_snoc_2: "edges_of_path (p @ [v1, v2]) = edges_of_path (p @ [v1]) @ [{v1 ,v2}]"
  by (smt Nil_is_append_conv append_butlast_last_id butlast.simps(2) butlast_append edges_of_path_snoc last.simps last_appendR list.distinct(1))

lemma edges_of_path_snoc_3: "p \<noteq> [] \<Longrightarrow> edges_of_path (p @ [v1, v2]) = edges_of_path p @ [{last p, v1}, {v1 ,v2}]"
  by (smt Nil_is_append_conv append_butlast_last_id butlast.simps(2) butlast_append edges_of_path_snoc last.simps last_appendR list.distinct(1))

subsection \<open>Connected components: connected components of vertices and of edges\<close>

text\<open>One interesting point is the use of the concepts of connected components, which partition the
     set of vertices, and the analogous partition of edges. Juggling around between the two
     partitions, we get a much shorter proof for the first direction of Berge's lemma, which is the
     harder one.\<close>

definition connected_component where
  "connected_component E v = {v'. v' = v \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v \<and> last p = v')}"

definition connected_components where
  "connected_components E \<equiv> {vs. \<exists>v. vs = connected_component E v \<and> v \<in> (Vs E)}"

text\<open>
  If a set of edges cannot be partitioned in paths, then it has a junction of 3 or more edges.
  In particular, an edge from one of the two matchings belongs to the path
  equivalent to one connected component. Otherwise, there will be a vertex whose degree is
  more than 2.
\<close>

text\<open>
  Every edge lies completely in a connected component.
\<close>

lemma in_own_connected_component:
  assumes "{v,v'} \<in> E"
  shows "v \<in> connected_component E v"
  unfolding connected_component_def
  by simp

lemma in_own_connected_component':
  assumes "v \<in> Vs E"
  shows "v \<in> connected_component E v"
  unfolding connected_component_def
  by simp

lemma connected_components_closed:
  assumes v1_in_C: "v1 \<in> connected_component E v4" and
    v3_in_C: "v3 \<in> connected_component E v4" and
    v4: "v4 \<in> Vs E"
  shows "v3 \<in> connected_component E v1"
proof(cases "v4 \<noteq> v1")
  case v4_neq_v1: True
  show ?thesis
  proof(cases "v4 \<noteq> v3")
    case v4_neq_v3: True      
    obtain p1 p2 where p1: "path E p1" " hd p1 = v4"" last p1 = v1" "p1 \<noteq> []" and p2: "path E p2" "hd p2 = v4" "last p2 = v3" "p2 \<noteq> []"
      using v1_in_C v3_in_C v4 v4_neq_v1 v4_neq_v3
      unfolding connected_component_def
      by auto
    have "path E ((rev (tl p1)) @ p2)"
    proof (cases "tl p1 = []")
      case True
      then show ?thesis using p2 by simp
    next
      case False
      then obtain h l where tl_nempty: "(tl p1) = h#l" using neq_Nil_conv by metis
      show ?thesis
        apply (intro path_append p2)
        subgoal using p1 rev_path_is_path tl_path_is_path
          by blast
        subgoal proof(cases "l")
          case Nil
          then show ?thesis
            using p1 p2 tl_nempty
            by (smt False insert_commute last_rev list.sel(1) nempty_tl_hd_tl path_2)
        next
          have rw: "{h, v4} = {v4, h}" by auto
          case (Cons a list)
          then show ?thesis
            using p1 p2 tl_nempty nempty_tl_hd_tl[OF False]
            by (simp add: rw)
        qed
        done
    qed
    moreover have "hd ((rev (tl p1)) @ p2) = v1"
    proof(cases "(tl p1) = []")
      case True
      show ?thesis
        using p1 v4_neq_v1
        apply (simp add: True)
        by (metis True last.simps list.exhaust_sel)
    next
      case False
      then show ?thesis
        using p1 by (simp add: hd_rev last_tl)
    qed
    moreover have "last ((rev (tl p1)) @ p2) = v3"
    proof(cases "p2 = []")
      case True
      then show ?thesis
        using p2 v3_in_C
        by (simp)
    next
      case False
      then show ?thesis
        using p2 last_appendR by simp
    qed
    ultimately show ?thesis
      unfolding connected_component_def
      using p2(2) v4_neq_v1 by force
  next
    case False
    then have v4_eq_v3: "v4 = v3" by simp
    obtain p1 where p1: "path E p1" "hd p1 = v4" "last p1 = v1" "p1 \<noteq> []"
      using v1_in_C v3_in_C v4 v4_neq_v1
      unfolding connected_component_def
      by auto
    then have "path E (rev p1)"
      using rev_path_is_path by blast
    moreover have "hd (rev p1) = v1" "last (rev p1) = v4"
      using p1
      by (simp add: hd_rev last_rev)+
    ultimately show ?thesis
      unfolding connected_component_def
      using p1 v4_eq_v3
      by auto
  qed
next
  case False
  then have v4_eq_v1: "v4 = v1" by simp
  show ?thesis
  proof(cases "v4 \<noteq> v3")
    case True
    then obtain p1 where p1: "path E p1" "hd p1 = v4" "last p1 = v3" "p1 \<noteq> []"
      using v3_in_C v4 v4_eq_v1
      unfolding connected_component_def
      by auto
    then have "path E (rev p1)"
      using rev_path_is_path by blast
    moreover have "hd (rev p1) = v3" "last (rev p1) = v4"
      using p1
      by (simp add: hd_rev last_rev)+
    ultimately show ?thesis
      unfolding connected_component_def
      using p1 v4_eq_v1
      by auto
  next
    case False
    then have "v4 = v3" by simp
    then show ?thesis
      unfolding connected_component_def
      using v4_eq_v1
      by auto
  qed
qed

lemma connected_components_closed':
  assumes is_an_edge: "{v1, v2} \<in> E" and 
    C_is_comp: "C \<in> connected_components E" and 
    v_in_C: "v1 \<in> C"
  shows "C = connected_component E v1"
proof(safe)
  from C_is_comp obtain v4 where v4: "C = connected_component E v4" "v4 \<in> Vs E"
    unfolding connected_components_def 
    by blast
  fix v3
  assume "v3 \<in> C"
  then show "v3 \<in> connected_component E v1"
    using v4 connected_components_closed C_is_comp v_in_C
    by fastforce
next
  fix v3
  assume ass: "v3 \<in> connected_component E v1"
  moreover from C_is_comp obtain v4 where v4: "C = connected_component E v4" "v4 \<in> Vs E"
    unfolding connected_components_def 
    by blast
  ultimately show "v3 \<in> C"
    using v4 connected_components_closed[OF] C_is_comp v_in_C
    by (metis (mono_tags, lifting) connected_component_def edges_are_Vs is_an_edge mem_Collect_eq)
qed

lemma connected_components_closed'':
  assumes is_an_edge: "v \<in> Vs E" and 
    graph: "\<forall>e\<in>E. \<exists>u v. e = {u,v}" and
    C_is_comp: "C \<in> connected_components E" and 
    v_in_C: "v \<in> C"
  shows "C = connected_component E v"
proof-
  obtain v2 where "{v,v2} \<in> E" using is_an_edge graph
    unfolding Vs_def                                             
    apply simp
    by (metis empty_iff insert_commute insert_iff)
  then show ?thesis
    apply(intro connected_components_closed' assms)
    by auto
qed

lemma edge_in_component:
  assumes "{x,y} \<in> E"
  shows "\<exists>C. C \<in> connected_components E \<and> {x,y} \<subseteq> C"
proof-
  have "y \<in> connected_component E x"
    unfolding connected_component_def
    using assms
      (*sledgehammer*)
  proof -
    have "path E [x, y]"
      apply (simp add: assms)
      using assms Vs_def by fastforce
    then show "y \<in> {a. a = x \<or> (\<exists>as. as \<noteq> [] \<and> path E as \<and> hd as = x \<and> last as = a)}"
      by (force simp del: path_2)
  qed
  moreover have "x \<in> Vs E"
    using assms
    unfolding Vs_def 
    by auto
  ultimately show ?thesis
    unfolding connected_components_def
    using in_own_connected_component[OF assms]
    by blast
qed

lemma edge_in_unique_component:
  assumes "{x,y} \<in> E"
  shows "\<exists>!C. C \<in> connected_components E \<and> {x,y} \<subseteq> C"
  using edge_in_component connected_components_closed'
  by (metis assms insert_subset)

text\<open>Now we should be able to partition the set of edges into equivalence classes
     corresponding to the connected components.\<close>

definition component_edges where
"component_edges E C = {{x,y} | x y.  {x,y} \<subseteq> C \<and> {x,y} \<in> E}"

lemma component_edges_disj:
  assumes "C \<in> connected_components E" "C' \<in> connected_components E" "C \<noteq> C'"
        shows "component_edges E C \<inter> component_edges E C' = {}"
proof(rule ccontr)
  assume ass: "component_edges E C \<inter> component_edges E C' \<noteq> {}"
  then obtain e where "e \<in> component_edges E C \<inter> component_edges E C'"
    by auto
  then obtain x y where xy: "e = {x,y}"  "{x,y} \<in> E" "{x,y} \<subseteq> C" "{x,y} \<subseteq> C'"
    unfolding component_edges_def
    apply simp
    by (metis doubleton_eq_iff)
  then show False
    using assms edge_in_unique_component[OF xy(2)]
    by auto
qed

definition components_edges where
"components_edges E = {component_edges E C| C. C \<in> connected_components E}"

lemma component_edges_partition:
  shows "\<Union> (components_edges E) = E \<inter> {{x,y}| x y. True}"
  unfolding components_edges_def
proof(safe)
  fix x y
  assume "{x, y} \<in> E"
  then show "{x, y} \<in> \<Union> {component_edges E C |C. C \<in> connected_components E}"
    unfolding component_edges_def
    apply simp
    by (smt edge_in_unique_component insertI1 insert_commute mem_Collect_eq subset_iff)
qed(auto simp add: component_edges_def)

subsection\<open>Every connected component can be linearised in a path.\<close>

lemma conn_comp_verts_in_verts:
  assumes "v \<in> C" "C \<in> connected_components E"
  shows "v \<in> Vs E"
proof-
  obtain v2 where v2: "v \<in> connected_component E v2" "v2 \<in> Vs E"
    using assms
    unfolding connected_components_def
    by auto
  show ?thesis
  proof(cases "v = v2")
    case True
    then show ?thesis
      using v2 by auto
  next
    case False
    then obtain p where p: "path E (v2 # p)" "last p = v" "p \<noteq> []"
      using v2
      unfolding connected_component_def
      apply simp
      by (metis last_ConsL last_tl list.exhaust_sel)
    then have "v \<in> set (v2 # p)" 
      by auto
    then show ?thesis
      using v_in_apath_in_Vs p
      by force
  qed
qed

lemma conn_comp_subset_verts:
  assumes "C \<in> connected_components E"
  shows "C \<subseteq> Vs E"
  using conn_comp_verts_in_verts[OF _ assms]
  by blast

lemma path_subset_conn_comp:
  assumes "path E p" "hd p = u"
  shows "set p \<subseteq> connected_component E u"
  using assms
proof(induction arbitrary: u)
  case path0
  then show ?case by simp
next
  case path1
  then show ?case using in_own_connected_component' by simp
next
  case path2
  then show ?case
    apply (simp split: if_splits add: )
    by (metis connected_components_closed' edge_in_component insert_commute insert_subset)+
qed

lemma component_has_path:
  assumes "finite C'" "C' \<subseteq> C" "C \<in> connected_components E"
  shows "\<exists>p. path E p \<and> C' \<subseteq> (set p) \<and> (set p) \<subseteq> C"
  using assms
proof(induction C' arbitrary: E)
  case empty
  then show ?case
    using path0
    by fastforce
next
  case ass: (insert x F)
  then obtain p where p: "path E p" "F \<subseteq> set p" "set p \<subseteq> C"
    by (meson insert_subset)
  show ?case
  proof(cases "p = []")
    case True
    have "path E [x]"
      using ass
      by (auto simp add: conn_comp_verts_in_verts)
    then show ?thesis
      using True p ass.prems(1) by fastforce
  next
    case F1: False
    show ?thesis
    proof(cases "last p = x")
      case True
      then show ?thesis
        using F1 p(1) p(2) p(3) by auto
    next
      case F2: False
      obtain v where v: "C = connected_component E v" "v \<in> Vs E"
        using ass
        unfolding connected_components_def
        by auto
      moreover have "last p \<in> C"
        using F1 p(3) by auto
      moreover have "x \<in> C"
        using ass by simp
      ultimately obtain p' where p': "last p = hd p'" "path E p'" "last p' = x" "p' \<noteq> []"
        using connected_components_closed[OF _ _ v(2)] F2
        unfolding connected_component_def
      (*sledgehammer*)
      proof -
        assume a1: "\<And>p'. \<lbrakk>last p = hd p'; path E p'; last p' = x; p' \<noteq> []\<rbrakk> \<Longrightarrow> thesis"
        assume a2: "C = {v'. v' = v \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v \<and> last p = v')}"
        assume "\<And>v1 v3. \<lbrakk>v1 \<in> {v'. v' = v \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v \<and> last p = v')}; v3 \<in> {v'. v' = v \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v \<and> last p = v')}\<rbrakk> \<Longrightarrow> v3 \<in> {v'. v' = v1 \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v1 \<and> last p = v')}"
        then have "\<forall>a aa. aa \<in> {aa. aa = a \<or> (\<exists>as. as \<noteq> [] \<and> path E as \<and> hd as = a \<and> last as = aa)} \<or> aa \<notin> C \<or> a \<notin> C"
          using a2 by meson
        then show ?thesis
          using a1 F2 \<open>last p \<in> C\<close> \<open>x \<in> C\<close> by moura
      qed
      define p'' where "p'' = (p @ tl p')"
      have "path E p''"
      proof(cases "p' = []")
        case True
        then show ?thesis
          by (simp add: p(1) p''_def)
      next
        case F3: False
        show ?thesis
          unfolding p''_def
          apply(intro path_append p tl_path_is_path p')
          using F2 F3 p'(1) p'(2) p'(3) path.simps by fastforce
      qed
      moreover have "insert x F \<subseteq> set p''" (is ?P1) "set p'' \<subseteq> C" (is ?P2)
      proof-
        have union: "set p'' = set p \<union> set p'"
          unfolding p''_def set_append
          using p'
          by(auto simp: neq_Nil_conv F1)
        moreover have "x \<in> set (tl p')"
          using p' F2
          by (metis last.simps last_in_set list.exhaust_sel)
        ultimately show ?P1
          using p''_def p(2) by auto
        have "set p' \<subseteq> connected_component E (last p)"
          using path_subset_conn_comp p'
          by force
        moreover have "C = connected_component E (last p)"
        proof-
          have "last p \<in> C"
            using ass
            using \<open>last p \<in> C\<close> by blast
          moreover obtain v' where "{last p, v'} \<in> E"
            by (metis F2 hd_conv_nth last_conv_nth length_tl list.sel(1) list.sel(3) list.size(3) p'(1) p'(2) p'(3) p'(4) path.simps)
          ultimately show ?thesis
          apply(intro connected_components_closed' ass)
            by auto
        qed
        ultimately show ?P2
          using union p(3) by blast
      qed
      ultimately show ?thesis
        by auto
  qed
qed
qed

lemma component_has_path':
  assumes "finite C" "C \<in> connected_components E"
  shows "\<exists>p. path E p \<and> C = (set p)"
  using assms component_has_path
  by (metis subset_antisym subset_refl)

subsection\<open>Every connected component can be linearised in a simple path\<close>

text\<open>An important part of this proof is setting up and induction on the graph, i.e. on a set of
     edges, and the different cases that could arise.\<close>

lemma con_comp_nempty:
  assumes "Vs E \<noteq> {}"
          "C \<in> connected_components E"
        shows "C \<noteq> {}"
  using assms
  unfolding Vs_def connected_components_def connected_component_def
  apply simp
  by blast

lemma same_con_comp_path:
  assumes "C \<in> connected_components E"
    "w \<in> C" "x \<in> C"
  shows "\<exists>pwx. pwx \<noteq> [] \<and> path E pwx \<and> hd pwx = w \<and> last pwx = x"
proof-
  obtain v' where v': "C = connected_component E v'" "v' \<in> Vs E"
    using assms
    unfolding connected_components_def
    by blast
  obtain p_v_w where pvw: "p_v_w \<noteq> [] \<and> path E p_v_w \<and> hd p_v_w = v' \<and> last p_v_w = w"
    using assms v'
    by (smt connected_component_def last_ConsL list.distinct(1) list.sel(1) mem_Collect_eq path1)
  obtain p_v_x where pvx: "p_v_x \<noteq> [] \<and> path E p_v_x \<and> hd p_v_x = v' \<and> last p_v_x = x"
    using assms v'
    by (smt connected_component_def last_ConsL list.distinct(1) list.sel(1) mem_Collect_eq path1)
  define p_w_x where "p_w_x = (rev p_v_w) @ (tl p_v_x)"
  have "p_w_x \<noteq> [] \<and> path E p_w_x \<and> hd p_w_x = w \<and> last p_w_x = x"
  proof(cases "(tl p_v_x)")
    case Nil
    then show ?thesis
      unfolding p_w_x_def
      using pvw pvx
      apply simp
      by (metis hd_rev last.simps last_rev list.exhaust_sel rev_path_is_path)
  next
    case (Cons a list)
    then show ?thesis
      unfolding p_w_x_def
      using pvw pvx
      apply (intro conjI path_append rev_path_is_path tl_path_is_path; simp add: hd_rev)
      subgoal using last_rev path.simps by fastforce
      subgoal by (metis last.simps last_tl list.distinct(1))
      done
  qed
  then show ?thesis
    by metis
qed

lemma in_con_compI:
  assumes connected: "puv \<noteq> []" "path E puv" "hd puv = u" "last puv = v" and
    u_mv: "u\<in>Vs E" and
    uC: "u \<in> C" and
    C_in_comp: "C \<in> connected_components E"
  shows "v \<in> C"
proof(cases "u = v")
  case True
  then show ?thesis using assms by simp
next
  obtain w where w: "w \<in> Vs E" "C = connected_component E w"
    using C_in_comp
    by (smt connected_components_def mem_Collect_eq)
  then obtain pwu where pwu: "pwu \<noteq> []" "path E pwu" "hd pwu = w" "last pwu = u"
    using uC C_in_comp
    unfolding connected_components_def connected_component_def
    apply simp
    by (metis last_ConsL list.sel(1) list.simps(3) path1)
  moreover case False
  ultimately have "path E (pwu @ (tl puv))" "hd (pwu @ (tl puv)) = w" "last (pwu @ (tl puv)) = v"
      apply(intro path_append connected pwu tl_path_is_path; simp)
    using connected pwu path.simps by fastforce+
  then show ?thesis
    using w
    by (metis Nil_is_append_conv contra_subsetD last_in_set path_subset_conn_comp pwu(1))
qed

lemma conn_comp_disj:
  assumes "C \<noteq> C'" "C \<in> connected_components E" "C' \<in> connected_components E" "\<forall>e\<in>E. \<exists>u v. e = {u,v}"
  shows "C \<inter> C' = {}"
proof(rule ccontr)
  assume "C \<inter> C' \<noteq> {}"
  then obtain v where v: "v \<in> C" "v \<in> C'" "v \<in> Vs E"
    by (meson Int_emptyI assms(2) conn_comp_verts_in_verts)
  have "u \<in> C" if uC: "u \<in> C'" for u
  proof-
    obtain puv where puv: "puv \<noteq> []" "path E puv" "hd puv = v" "last puv = u"
      using same_con_comp_path[OF assms(3) v(2) uC]
      by auto
    show ?thesis
      apply(rule in_con_compI puv(1,2,3))+
      by(intro puv(4) v assms)+
  qed
  moreover have "u \<in> C'" if uC: "u \<in> C" for u
  proof-
    obtain puv where puv: "puv \<noteq> []" "path E puv" "hd puv = v" "last puv = u"
      using same_con_comp_path[OF assms(2) v(1) uC]
      by auto
    show ?thesis
      apply(rule in_con_compI puv(1,2,3))+
      by(intro puv(4) v assms)+
  qed
  ultimately show False
    using assms(1)
    by auto
qed

lemma unchanged_con_comp:
  assumes "u \<notin> C" "v \<notin> C" "{u,v} \<subseteq> Vs E"
  shows "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u,v} E)"
proof-
  have "C \<in> connected_components (insert {u, v} E)" if "C \<in> connected_components E"
  proof-
    obtain w where w: "w \<in> Vs E" "C = connected_component E w"
      using that
      by (smt \<open>C \<in> connected_components E\<close> connected_components_def mem_Collect_eq)
    moreover have "C = connected_component (insert {u, v} E) w"
      unfolding connected_components_def connected_component_def
      apply(intro equalityI subsetI)
      subgoal for x proof-
        {
          fix C v1 v2
          assume ass: "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v1 \<and> last p = v2)" 
          have "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = v1 \<and> last p = v2)"
          proof(cases "v1 = v2")
            case True
            then show ?thesis by simp
          next
            case F1: False
            then show ?thesis
              using F1 path_subset same_con_comp_path
              by (smt ass subset_insertI)
          qed
        }
        moreover assume "x \<in> C"
        ultimately show ?thesis
          using w
          unfolding connected_components_def connected_component_def
          apply simp
          by metis
      qed        
      subgoal for x proof-
        {
          fix v'
          assume ass: "v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')"
          have "v' \<in> connected_component E w"
          proof(cases "v' = w")
            case True
            then show ?thesis
              unfolding connected_component_def
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = w" "last puv' = v'"
              using ass
              by blast
            show ?thesis
              using assms path_can_be_split[OF  puv'(1,2) _ puv'(3)] 
                w(2) that
              apply(simp add: puv'(4,5))
              by (smt conn_comp_verts_in_verts connected_components_closed'' last_in_set path_subset_conn_comp subsetCE)
          qed
        }
        moreover assume "x \<in> {v'. v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')}"
        ultimately show ?thesis
          by (simp add: w(2))
      qed
      done
    moreover have "w \<in> Vs (insert {u,v} E)"
      using w(1)
      unfolding Vs_def
      by blast
    ultimately show ?thesis
      unfolding connected_components_def
      by auto
  qed
  moreover have "C \<in> connected_components E" if "C \<in> connected_components (insert {u, v} E)"
  proof-
    obtain w where w: "w \<in> Vs (insert {u, v} E)" "C = connected_component (insert {u, v} E) w"
      using that
      by (smt \<open>C \<in> connected_components (insert {u, v} E)\<close> connected_components_def mem_Collect_eq)
    moreover have "C = connected_component E w"
      unfolding connected_components_def connected_component_def
      apply(intro equalityI subsetI)
      subgoal for x proof-
        {
          fix v'
          assume ass: "v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')"
          have "v' \<in> connected_component E w"
          proof(cases "v' = w")
            case True
            then show ?thesis
              unfolding connected_component_def
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = w" "last puv' = v'"
              using ass
              by blast
            then show ?thesis
              using path_can_be_split[OF  puv'(1,2) _ puv'(3), unfolded puv'(4,5)]
              using that
              using assms
              apply(simp add: puv'(4,5) w(2) Int_Un_distrib insert_Diff path_subset path_subset_conn_comp subsetCE subset_insertI)
              by (smt disjoint_insert(1) insert_Diff last_in_set path_subset path_subset_conn_comp subsetCE subset_insertI)
          qed
        }
        moreover assume "x \<in> C"
        ultimately show ?thesis
          using w(2)
          unfolding connected_component_def
          by simp
      qed
      subgoal for x proof-
        {
          fix C v1 v2
          assume ass: "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v1 \<and> last p = v2)" 
          have "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = v1 \<and> last p = v2)"
          proof(cases "v1 = v2")
            case True
            then show ?thesis by simp
          next
            case F1: False
            then show ?thesis
              using path_subset
              by (smt ass subset_insertI)
          qed
        }
        moreover assume "x \<in> {v'. v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = w \<and> last p = v')}"
        ultimately show ?thesis
          unfolding w connected_components_def connected_component_def
          apply simp
          by metis
      qed
      done
    moreover have "w \<in> Vs E" 
      by (metis Sup_insert assms(3) Vs_def subset_Un_eq w(1))
    ultimately have "C \<in> connected_components E"
      unfolding connected_components_def
      by auto
    then show ?thesis
      using that
      by auto
  qed
  ultimately show ?thesis
    by blast
qed

lemma connected_components_insert_1:
  assumes "C \<in> connected_components E"
    "w \<in> C" "x \<in> C"
  shows "connected_components E = connected_components (insert {w, x} E)"
proof-
  {
    fix v
    assume ass: "v \<in> Vs E" 
    then obtain C' where C': "C' \<in> connected_components E" "C' = connected_component E v"
      unfolding connected_components_def
      using \<open>v \<in> Vs E\<close> by blast
    {
      fix u
      assume "u \<in> connected_component E v" 
      then have "u \<in> connected_component (insert {w, x} E) v"
        unfolding connected_component_def
        using path_subset by blast
    }note d1 = this
    {
      fix u
      assume ass: "u \<in> connected_component (insert {w, x} E) v" 
      have "u \<in> connected_component E v"
      proof(cases "u = v")
        case True
        then show ?thesis
          unfolding connected_component_def
          by simp
      next
        case False
        with ass obtain p where p: "p \<noteq> [] \<and> path (insert {w, x} E) p \<and> hd p = v \<and> last p = u"
          unfolding connected_component_def
          by auto
        moreover obtain pwx where "pwx \<noteq> [] \<and> path E pwx \<and> hd pwx = w \<and> last pwx = x"
          using assms same_con_comp_path by force
        ultimately have "\<exists>p'. p' \<noteq> [] \<and> path E p' \<and> hd p' = hd p \<and> last p' = last p"
          by (intro path_repl_edge[where puv = pwx]; simp)          
        then show ?thesis
          unfolding connected_component_def
          using p
          by simp
      qed
    }note d2 = this
    have "connected_component E v = connected_component (insert {w, x} E) v"
      apply auto
      using d1 d2
      by metis+
  }
  then show ?thesis
    unfolding connected_components_def
    apply auto
    subgoal by (metis Sup_insert Un_iff Vs_def)
    subgoal by (metis Sup_insert Un_iff assms(1) assms(2) assms(3) conn_comp_subset_verts empty_iff insert_iff Vs_def subset_iff)
    done
qed

lemma connected_components_insert_2:
  assumes "Cu \<noteq> Cv"
    "Cu \<in> connected_components E"
    "Cv \<in> connected_components E"
    "u \<in> Cu" "v \<in> Cv"
    "\<forall>e\<in>E. \<exists>u v. e = {u, v}"
  shows "insert (Cu \<union> Cv) ((connected_components E) - {Cu, Cv}) = connected_components (insert {u,v} E)"
proof-
  have uv_subs: "{u, v} \<subseteq> Vs E"
    using assms(2-5) conn_comp_subset_verts by blast
  have un_con_comp: "(Cu \<union> Cv) \<in> connected_components (insert {u, v} E)"
  proof-
    have "v \<in> Vs (insert {u, v} E)"
      using assms
      by (simp add: Vs_def)
    moreover have "Cu \<union> Cv = connected_component (insert {u, v} E) v"
      unfolding connected_component_def
      apply(intro equalityI)
      subgoal proof-
        {
          fix v'
          assume ass: "v' \<in> Cu \<union> Cv"
          have "v' = v \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = v \<and> last p = v')"
          proof(cases "v' = v")
            case True
            then show ?thesis by simp
          next
            case F1: False
            show ?thesis
            proof(cases "v' \<in> Cv")
              case True
              show ?thesis
                using F1 path_subset same_con_comp_path[OF assms(3,5) True]
                by (metis subset_insertI)
            next
              case F2: False
              then have *: "v' \<in> Cu"
                using ass by simp
              then obtain puv' where puv': "puv' \<noteq> []" "path (insert {u, v} E) puv'" "hd puv' = u" "last puv' = v'"
                using path_subset same_con_comp_path[OF assms(2,4) *]
                by (metis subset_insertI)
              then obtain p' where p': "puv' = u # p'"
                using list.exhaust_sel by blast
              have "path (insert {u, v} E) (v # puv')" (*"hd (v # puv') = v" "last (v # puv') = v'"*)
                by(cases p') (insert puv', auto simp add: p')
              then show ?thesis
                using puv'
                by auto
            qed
          qed
        }
        then show ?thesis
          by auto
      qed
      subgoal proof-
        {
          fix v'
          assume ass: "v' = v \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = v \<and> last p = v')"
          have "v' \<in> Cu \<union> Cv"
          proof(cases "v' = v")
            case True
            then show ?thesis
              using assms
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = v" "last puv' = v'"
              using ass by blast
            have uv_match_vs: "{u, v} \<subseteq> Vs E"
              using assms(2-5) conn_comp_subset_verts by blast
            show ?thesis
              using assms(3,5,6) path_subset_conn_comp conn_comp_verts_in_verts connected_components_closed''
                path_can_be_split[OF  puv'(1,2) uv_match_vs puv'(3)]
              apply(simp add: puv'(4,5))
              by (smt assms(2) assms(4) connected_components_closed'' insert_subset last_in_set path_subset_conn_comp subsetCE uv_match_vs)
          qed
        }
        then show ?thesis
          by auto
      qed
      done
    ultimately show ?thesis
      unfolding connected_components_def
      by auto
  qed
  show ?thesis
    apply(intro equalityI subsetI)
    subgoal using unchanged_con_comp[OF _ _ uv_subs] un_con_comp
      apply simp
      by (metis Int_iff assms(2-6) conn_comp_disj empty_iff)
    subgoal for C proof-
      assume "C \<in> connected_components (insert {u, v} E)"
      moreover have "C' = Cu \<union> Cv" if "v \<in> C'" "C' \<in> connected_components (insert {u,v} E)" for C'
        using conn_comp_disj[OF _ _ _ assms(6)]
        by (smt assms(5) connected_components_closed' insertI1 insert_commute subsetCE sup.cobounded2 that(1) that(2) un_con_comp)
      moreover have "C' = Cu \<union> Cv" if "u \<in> C'" "C' \<in> connected_components (insert {u,v} E)" for C'
        using conn_comp_disj[OF _ _ _ assms(6)]
        by (smt assms(4) connected_components_closed' insertI1 insert_Diff insert_subset sup_ge1 that(1) that(2) un_con_comp)
      ultimately show ?thesis
        using unchanged_con_comp[OF _ _ uv_subs] un_con_comp
        apply simp
        using assms(4,5) by blast
    qed
    done
qed

lemma unchanged_con_comp_2:
  (* This proof is almost exactly the same as that of unchanged_con_comp. There must be a way to
     factor both. *)
  assumes "u \<notin> C" "v \<notin> C"  "u \<in> Vs E" "v \<notin> Vs E"
  shows "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u,v} E)"
proof-
  have "C \<in> connected_components (insert {u, v} E)" if "C \<in> connected_components E"
  proof-
    obtain w where w: "w \<in> Vs E" "C = connected_component E w"
      using that
      by (smt \<open>C \<in> connected_components E\<close> connected_components_def mem_Collect_eq)
    moreover have "C = connected_component (insert {u, v} E) w"
      unfolding connected_components_def connected_component_def
      apply(intro equalityI subsetI)
      subgoal for x proof-
        {
          fix C v1 v2
          assume ass: "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v1 \<and> last p = v2)" 
          have "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = v1 \<and> last p = v2)"
          proof(cases "v1 = v2")
            case True
            then show ?thesis by simp
          next
            case F1: False
            then show ?thesis
              using F1 path_subset same_con_comp_path
              by (smt ass subset_insertI)
          qed
        }
        moreover assume "x \<in> C"
        ultimately show ?thesis
          using w
          unfolding connected_components_def connected_component_def
          apply simp
          by metis
      qed        
      subgoal for x proof-
        {
          fix v'
          assume ass: "v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')"
          have "v' \<in> connected_component E w"
          proof(cases "v' = w")
            case True
            then show ?thesis
              unfolding connected_component_def
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = w" "last puv' = v'"
              using ass
              by blast
            show ?thesis
              using assms path_can_be_split path_can_be_split_2[OF puv'(1,2) _ _ puv'(3)] 
                w(2) that
              apply(simp add: puv'(4,5))
              by (metis connected_components_closed in_own_connected_component' last_in_set path_subset_conn_comp subsetCE w(1))
          qed
        }
        moreover assume "x \<in> {v'. v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')}"
        ultimately show ?thesis
          by (simp add: w(2))
      qed
      done
    moreover have "w \<in> Vs (insert {u,v} E)"
      using w(1)
      unfolding Vs_def
      by blast
    ultimately show ?thesis
      unfolding connected_components_def
      by auto
  qed
  moreover have "C \<in> connected_components E" if "C \<in> connected_components (insert {u, v} E)"
  proof-
    obtain w where w: "w \<in> Vs (insert {u, v} E)" "C = connected_component (insert {u, v} E) w"
      using that
      by (smt \<open>C \<in> connected_components (insert {u, v} E)\<close> connected_components_def mem_Collect_eq)
    moreover have "C = connected_component E w"
      unfolding connected_components_def connected_component_def
      apply(intro equalityI subsetI)
      subgoal for x proof-
        {
          fix v'
          assume ass: "v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')"
          have "v' \<in> connected_component E w"
          proof(cases "v' = w")
            case True
            then show ?thesis
              unfolding connected_component_def
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = w" "last puv' = v'"
              using ass
              by blast
            then show ?thesis
              using path_can_be_split path_can_be_split_2[OF puv'(1,2) _ _ puv'(3)]
              using that
              using assms
              apply(simp add: puv'(4,5) w(2) Int_Un_distrib insert_Diff path_subset path_subset_conn_comp subsetCE subset_insertI)
              by (metis in_own_connected_component' last_in_set path_subset_conn_comp puv'(4) puv'(5) subsetCE w(1))
          qed
        }
        moreover assume "x \<in> C"
        ultimately show ?thesis
          using w(2)
          unfolding connected_component_def
          by simp
      qed
      subgoal for x proof-
        {
          fix C v1 v2
          assume ass: "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v1 \<and> last p = v2)" 
          have "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = v1 \<and> last p = v2)"
          proof(cases "v1 = v2")
            case True
            then show ?thesis by simp
          next
            case F1: False
            then show ?thesis
              using path_subset
              by (smt ass subset_insertI)
          qed
        }
        moreover assume "x \<in> {v'. v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = w \<and> last p = v')}"
        ultimately show ?thesis
          unfolding w connected_components_def connected_component_def
          apply simp
          by metis
      qed
      done
    moreover have "w \<in> Vs E"
      by (smt CollectI Sup_insert UnE assms(1) assms(2) connected_component_def empty_iff insert_iff Vs_def w(1) w(2))
    ultimately have "C \<in> connected_components E"
      unfolding connected_components_def
      by auto
    then show ?thesis
      using that
      by auto
  qed
  ultimately show ?thesis
    by blast
qed

lemma connected_components_insert_3:
  assumes "C \<in> connected_components E"
    "u \<in> C"
    "v \<notin> Vs E"
    "\<forall>e\<in>E. \<exists>u v. e = {u, v}"
  shows "insert (insert v C) (connected_components E - {C}) = connected_components (insert {u,v} E)"
proof-
  have un_con_comp: "(insert v C) \<in> connected_components (insert {u, v} E)"
  proof-
    have "v \<in> Vs (insert {u, v} E)"
      using assms
      by (simp add: Vs_def)
    moreover have "insert v C = connected_component (insert {u, v} E) u"
      unfolding connected_component_def
      apply(intro equalityI)
      subgoal proof-
        {
          fix v'
          assume ass: "v' \<in> insert v C"
          have "v' = u \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = u \<and> last p = v')"
          proof(cases "v' = u")
            case True
            then show ?thesis by simp
          next
            case F1: False
            show ?thesis
            proof(cases "v' \<in> C")
              case True
              show ?thesis
                using F1 path_subset same_con_comp_path[OF assms(1,2) True]
                by (metis subset_insertI)
            next
              case F2: False
              then have *: "v' = v"
                using ass by simp
              then have "path (insert {u, v} E) [u,v] \<and> hd [u,v] = u \<and> last [u,v] = v'"
                by (auto simp add: Vs_def)
              then show ?thesis
                by blast
            qed
          qed
        }
        then show ?thesis
          by auto
      qed
      subgoal proof-
        {
          fix v'
          assume ass: "v' = u \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = u \<and> last p = v')"
          have "v' \<in> insert v C"
          proof(cases "v' = v")
            case True
            then show ?thesis
              using assms
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = u" "last puv' = v'"
              using ass
              by (metis edges_are_Vs insertI1 last_ConsL list.sel(1) list.simps(3) path1)
            show ?thesis
              using assms path_subset_conn_comp conn_comp_verts_in_verts connected_components_closed''
                path_can_be_split_2[OF  puv'(1,2)]
              apply(simp add: puv'(4,5))
              by (smt conn_comp_verts_in_verts in_con_compI puv'(3))
          qed
        }
        then show ?thesis
          by auto
      qed
      done
    ultimately show ?thesis
      unfolding connected_components_def
      by (metis (mono_tags, lifting) CollectI edges_are_Vs insertI1)
  qed
  show ?thesis
    apply(intro equalityI subsetI)
    subgoal using unchanged_con_comp_2 un_con_comp
      apply simp
      by (smt assms(1) assms(2) assms(3) conn_comp_verts_in_verts connected_components_closed' connected_components_insert_1 insertI1 unchanged_con_comp_2)
    subgoal for C proof-
      assume "C \<in> connected_components (insert {u, v} E)"
      then  show ?thesis
        using un_con_comp
        apply simp
        using assms
        by (smt conn_comp_verts_in_verts connected_components_closed' insertI1 insert_Diff insert_commute unchanged_con_comp_2)
    qed
    done
qed

lemma unchanged_con_comp_3:
  (* This proof is almost exactly the same as that of unchanged_con_comp. There must be a way to
     factor both. *)
  assumes "u \<notin> C" "v \<notin> C"  "u \<notin> Vs E" "v \<notin> Vs E"
  shows "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u,v} E)"
proof-                                     
  have "C \<in> connected_components (insert {u, v} E)" if "C \<in> connected_components E"
  proof-
    obtain w where w: "w \<in> Vs E" "C = connected_component E w"
      using that
      by (smt \<open>C \<in> connected_components E\<close> connected_components_def mem_Collect_eq)
    moreover have "C = connected_component (insert {u, v} E) w"
      unfolding connected_components_def connected_component_def
      apply(intro equalityI subsetI)
      subgoal for x proof-
        {
          fix C v1 v2
          assume ass: "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v1 \<and> last p = v2)" 
          have "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = v1 \<and> last p = v2)"
          proof(cases "v1 = v2")
            case True
            then show ?thesis by simp
          next
            case F1: False
            then show ?thesis
              using F1 path_subset same_con_comp_path
              by (smt ass subset_insertI)
          qed
        }
        moreover assume "x \<in> C"
        ultimately show ?thesis
          using w
          unfolding connected_components_def connected_component_def
          apply simp
          by metis
      qed        
      subgoal for x proof-
        {
          fix v'
          assume ass: "v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')"
          have "v' \<in> connected_component E w"
          proof(cases "v' = w")
            case True
            then show ?thesis
              unfolding connected_component_def
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = w" "last puv' = v'"
              using ass
              by blast
            show ?thesis
            proof(cases "path E puv'")
              case True
              then show ?thesis
                using path_subset_conn_comp puv'(3) puv'(4) puv'(5) by fastforce
            next
              case False
              then have "path {{u,v}} puv'"
                using path_can_be_split_3[OF puv'(1,2) assms(3) assms(4) puv'(3)] 
                by blast
              then have "w \<in> {u, v}"
                by (metis ccpo_Sup_singleton list.set_sel(1) Vs_def mem_path_Vs puv'(3) puv'(4))
              then show ?thesis
                using assms(3) assms(4) w(1) by blast
            qed
          qed
        }
        moreover assume "x \<in> {v'. v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')}"
        ultimately show ?thesis
          by (simp add: w(2))
      qed
      done
    moreover have "w \<in> Vs (insert {u,v} E)"
      using w(1)
      unfolding Vs_def
      by blast
    ultimately show ?thesis
      unfolding connected_components_def
      by auto
  qed
  moreover have "C \<in> connected_components E" if "C \<in> connected_components (insert {u, v} E)"
  proof-
    obtain w where w: "w \<in> Vs (insert {u, v} E)" "C = connected_component (insert {u, v} E) w"
      using that
      by (smt \<open>C \<in> connected_components (insert {u, v} E)\<close> connected_components_def mem_Collect_eq)
    moreover have "C = connected_component E w"
      unfolding connected_components_def connected_component_def
      apply(intro equalityI subsetI)
      subgoal for x proof-
        {
          fix v'
          assume ass: "v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = w \<and> last p = v')"
          have "v' \<in> connected_component E w"
          proof(cases "v' = w")
            case True
            then show ?thesis
              unfolding connected_component_def
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = w" "last puv' = v'"
              using ass
              by blast
            show ?thesis
            proof(cases "path E puv'")
              case True
              then show ?thesis
                using path_subset_conn_comp puv'(3) puv'(4) puv'(5) by fastforce
            next
              case False
              then have "path {{u,v}} puv'"
                using path_can_be_split_3[OF puv'(1,2) assms(3) assms(4) puv'(3)] 
                by blast
              then have "w \<in> {u, v}"
                by (metis ccpo_Sup_singleton list.set_sel(1) Vs_def mem_path_Vs puv'(3) puv'(4))
              then show ?thesis
                using assms(1) assms(2) in_own_connected_component' w(1) w(2) by fastforce
            qed
          qed
        }
        moreover assume "x \<in> C"
        ultimately show ?thesis
          using w(2)
          unfolding connected_component_def
          by simp
      qed
      subgoal for x proof-
        {
          fix C v1 v2
          assume ass: "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = v1 \<and> last p = v2)" 
          have "v1 = v2 \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = v1 \<and> last p = v2)"
          proof(cases "v1 = v2")
            case True
            then show ?thesis by simp
          next
            case F1: False
            then show ?thesis
              using path_subset
              by (smt ass subset_insertI)
          qed
        }
        moreover assume "x \<in> {v'. v' = w \<or> (\<exists>p. p \<noteq> [] \<and> path E p \<and> hd p = w \<and> last p = v')}"
        ultimately show ?thesis
          unfolding w connected_components_def connected_component_def
          apply simp
          by metis
      qed
      done
    moreover have "w \<in> Vs E"
      by (smt CollectI Sup_insert UnE assms(1) assms(2) connected_component_def empty_iff insert_iff Vs_def w(1) w(2))
    ultimately have "C \<in> connected_components E"
      unfolding connected_components_def
      by auto
    then show ?thesis
      using that
      by auto
  qed
  ultimately show ?thesis
    by blast
qed

lemma connected_components_insert_4:
  assumes "u \<notin> Vs E"
          "v \<notin> Vs E"
        shows "insert ({u,v}) (connected_components E) = connected_components (insert {u,v} E)"
proof-
  have un_con_comp: "{u,v} \<in> connected_components (insert {u, v} E)"
  proof-
    have "v \<in> Vs (insert {u, v} E)"
      using assms
      by (simp add: Vs_def)
    moreover have "{u, v} = connected_component (insert {u, v} E) u"
      unfolding connected_component_def
      apply(intro equalityI)
      subgoal proof-
        {
          fix v'
          assume ass: "v' \<in> {u, v}"
          have "v' = u \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = u \<and> last p = v')"
          proof(cases "v' = u")
            case True
            then show ?thesis by simp
          next
            case F1: False
            show ?thesis
            proof(cases "v' \<in> {u, v}")
              case True
              show ?thesis
                using F1
                by (metis ass calculation empty_iff insert_iff last.simps list.distinct(1) list.sel(1) path_1 path_2)
            next
              case F2: False
              then have *: "v' = v"
                using ass by simp
              then have "path (insert {u, v} E) [u,v] \<and> hd [u,v] = u \<and> last [u,v] = v'"
                by (auto simp add: Vs_def)
              then show ?thesis
                by blast
            qed
          qed
        }
        then show ?thesis
          by auto
      qed
      subgoal proof-
        {
          fix v'
          assume ass: "v' = u \<or> (\<exists>p. p \<noteq> [] \<and> path (insert {u, v} E) p \<and> hd p = u \<and> last p = v')"
          have "v' \<in> {u, v}"
          proof(cases "v' = v")
            case True
            then show ?thesis
              using assms
              by simp
          next
            case False
            then obtain puv' E' where puv': "path E' puv'" "E' = insert {u, v} E" "puv' \<noteq> []"  "hd puv' = u" "last puv' = v'"
              using ass
              by (metis edges_are_Vs insertI1 last_ConsL list.sel(1) list.simps(3) path1)
            show ?thesis
              using assms path_subset_conn_comp conn_comp_verts_in_verts connected_components_closed''
                path_can_be_split_3[OF  puv'(1,2)]
              apply(simp add: puv'(4,5))
              by (smt ccpo_Sup_singleton empty_iff insertE last_in_set list.set_sel(1) Vs_def puv'(3) puv'(4) puv'(5) v_in_apath_in_Vs)
          qed
        }
        then show ?thesis
          by auto
      qed
      done
    ultimately show ?thesis
      unfolding connected_components_def
      by (metis (mono_tags, lifting) CollectI edges_are_Vs insertI1)
  qed
  show ?thesis
    apply(intro equalityI subsetI)
    subgoal using unchanged_con_comp_3 un_con_comp
      apply simp
      by (smt assms conn_comp_verts_in_verts connected_components_closed' connected_components_insert_1 insertI1 unchanged_con_comp_3)
    subgoal for C proof-
      assume "C \<in> connected_components (insert {u, v} E)"
      then  show ?thesis
        using un_con_comp
        apply simp
        using assms
        by (smt conn_comp_verts_in_verts connected_components_closed' insertI1 insert_Diff insert_commute unchanged_con_comp_3)
    qed
    done
qed

theorem component_has_path_distinct:
  assumes finite: "finite E" and
          conn_comp: "C \<in> connected_components E" and
          deg_le_2: "\<forall>v\<in>Vs E. degree E v \<le> 2" and
          edges_2: "\<forall>e\<in>E. \<exists>u v. e = {u, v}"
  shows "\<exists>p. path E p \<and> C = (set p) \<and> distinct p"
  using assms
proof(induction "card E" arbitrary: C E rule: nat_less_induct)
  case ass: 1
  show ?case 
  proof(cases "E = {}")
    case True
    then show ?thesis
      unfolding Vs_def connected_components_def connected_component_def
      using ass.prems(2)
      by (metis conn_comp_verts_in_verts distinct.simps(1) empty_iff empty_set equals0I Vs_def mem_simps(9) path0)
  next
    case False
    then obtain e E' where x_s: "E = insert e E'" "e \<notin> E'"
      by (metis Set.set_insert ass.prems(1) finite.cases insert_absorb)
    then have "card E' < card E"
      using ass.prems(1) by simp
    moreover have "(\<forall>v\<in>Vs E'. degree E' v \<le> 2)"
      using x_s less_edges_less_degree[OF ass.prems(1)]
      by (metis Diff_insert_absorb ass.prems(3) less_le_trans Vs_def mem_simps(9) not_le subset_iff subset_insertI)
    ultimately have E'_fine: "(\<exists>p. path E' p \<and> C' = set p \<and> distinct p)" if "C' \<in> connected_components E'" for C'
      using ass.hyps ass.prems(1,4) that x_s(1) ass
      by simp
    obtain u v where uv: "e = {u, v}"
      using ass.prems(4) x_s
      by auto
    show ?thesis
    proof(cases "u \<in> Vs E'")
      case T1: True
      then obtain Cu where Cu: "Cu \<in> connected_components E'" "u \<in> Cu"
        using connected_components_def in_own_connected_component' by fastforce
      obtain pu where pu: "path E' pu" "Cu = set pu" "distinct pu"
        using E'_fine[OF Cu(1)]
        by auto
      then have u_in_pu: "u \<in> set pu"
        using Cu(2) by blast
      have u_head_last: "u = hd pu \<or> u = last pu"
      proof(rule ccontr; simp)
        assume "u \<noteq> hd pu \<and> u \<noteq> last pu"
        then have "degree E' u \<ge> 2"
          using x_s mid_path_deg_ge_2[OF pu(1) u_in_pu _ _ pu(3)]
          using ass.prems(1) by simp
        then have "degree E u > 2"
          using x_s ass.prems(1) uv
          unfolding degree_def
          by simp
        moreover have "u \<in> Vs E"
          using x_s uv
          unfolding Vs_def
          by blast
        ultimately show False
          using ass.prems(3)
          by auto
      qed
      show ?thesis
      proof(cases "v \<in> Vs E'")
        case T2: True
        then obtain Cv where Cv: "Cv \<in> connected_components E'" "v \<in> Cv"
          using connected_components_def in_own_connected_component' by fastforce
        show ?thesis
        proof(cases "Cu = Cv")
          case T3: True
          then show ?thesis
            using connected_components_insert_1 E'_fine Cu path_subset
            by (metis Cv(2) ass.prems(2) subset_insertI uv x_s(1))
        next
          have rw: "insert {u,v} E' = E" using uv x_s by auto
          case F1: False
          show ?thesis
          proof(cases "C = (Cu \<union> Cv)")
            case True
            obtain pv where pv: "path E' pv" "Cv = set pv" "distinct pv"
              using E'_fine[OF Cv(1)]
              by auto
            then have v_in_pv: "v \<in> set pv"
              using Cv(2) by blast
            have "set pv \<inter> set pu = {}"
              using conn_comp_disj[OF F1 Cu(1) Cv(1)] ass.prems(4) x_s(1)
              by (auto simp: pu(2) pv(2))
            have v_head_last: "v = hd pv \<or> v = last pv"
            proof(rule ccontr; simp)
              assume "v \<noteq> hd pv \<and> v \<noteq> last pv"
              then have "degree E' v \<ge> 2"
                using x_s mid_path_deg_ge_2[OF pv(1) v_in_pv _ _ pv(3)]
                using ass.prems(1) by simp
              then have "degree E v > 2"
                using x_s ass.prems(1) uv
                unfolding degree_def
                by simp
              moreover have "v \<in> Vs E"
                using x_s uv
                unfolding Vs_def
                by blast
              ultimately show False
                using ass.prems(3)
                by auto
            qed
            show ?thesis
            proof(cases "u = hd pu")
              case T1: True
              show ?thesis
              proof(cases "v = hd pv")
                case T2: True
                have "path E ((rev pu) @ pv)"
                  apply(intro path_append)
                  subgoal using path_subset pu(1) rev_path_is_path x_s(1) by blast
                  subgoal using path_subset pv(1) x_s(1) by blast
                  subgoal using T1 T2 x_s uv Cu(2) pu
                    by (metis empty_iff empty_set insertI1 last_rev)
                  done
                moreover have "C = set ((rev pu) @ pv)"
                  by (simp add: True pu(2) pv(2) sup_commute)
                moreover have "distinct ((rev pu) @ pv)"
                  unfolding distinct_append
                  using \<open>set pv \<inter> set pu = {}\<close>
                  by (auto simp add: pv(3) pu(3))
                ultimately show ?thesis
                  by auto
              next
                case False
                then have "v = last pv" using v_head_last
                  by simp
                have "path E (pv @ pu)"
                  apply(intro path_append)
                  subgoal using path_subset pv(1) x_s(1) by blast
                  subgoal using path_subset pu(1) x_s(1) by blast
                  subgoal using T1 x_s uv 
                    by (simp add: \<open>v = last pv\<close> doubleton_eq_iff)
                  done
                moreover have "C = set (pv @ pu)"
                  by (simp add: True pu(2) pv(2) sup_commute)
                moreover have "distinct (pv @ pu)"
                  unfolding distinct_append
                  using \<open>set pv \<inter> set pu = {}\<close>
                  by (auto simp add: pv(3) pu(3))
                ultimately show ?thesis
                  by auto
              qed
            next
              case False
              then have u_last: "u = last pu"
                using u_head_last
                by simp
              show ?thesis
              proof(cases "v = hd pv")
                case T2: True
                have "path E (pu @ pv)"
                  apply(intro path_append)
                  subgoal using path_subset pu(1) rev_path_is_path x_s(1) by blast
                  subgoal using path_subset pv(1) x_s(1) by blast
                  subgoal using T1 T2 x_s uv
                    by (simp add: u_last doubleton_eq_iff)
                  done
                moreover have "C = set (pu @ pv)"
                  by (simp add: True pu(2) pv(2) sup_commute)
                moreover have "distinct (pu @ pv)"
                  unfolding distinct_append
                  using \<open>set pv \<inter> set pu = {}\<close>
                  by (auto simp add: pv(3) pu(3))
                ultimately show ?thesis
                  by auto
              next
                case False
                then have "v = last pv" using v_head_last
                  by simp
                have "path E (pv @ (rev pu))"
                  apply(intro path_append)
                  subgoal using path_subset pv(1) x_s(1) by blast
                  subgoal using path_subset pu(1) rev_path_is_path x_s(1) by blast
                  subgoal using x_s uv Cu(2) pu
                    by (metis \<open>v = last pv\<close> equals0D hd_rev insert_commute insert_subset list.set(1) subsetI u_last)
                  done
                moreover have "C = set (pv @ (rev pu))"
                  by (simp add: True pu(2) pv(2) sup_commute)
                moreover have "distinct (pv @ (rev pu))"
                  unfolding distinct_append
                  using \<open>set pv \<inter> set pu = {}\<close>
                  by (auto simp add: pv(3) pu(3))
                ultimately show ?thesis
                  by auto
              qed
            qed
          next
            case False
            then have "C \<in> connected_components E'" 
              using ass.prems(2) connected_components_insert_2[OF F1 Cu(1) Cv(1) Cu(2) Cv(2), unfolded rw] ass.prems(4) x_s
              by blast
            then show ?thesis
              using  E'_fine Cv x_s path_subset
              apply simp
              using T1 T2
              by (smt path_subset subset_insertI)
          qed
        qed
      next
        case F1: False
        show ?thesis
        proof(cases "C = insert v Cu")
          case T3: True
          show ?thesis
          proof(cases "u = hd pu")
            case T4: True
            then obtain pu' where pu': "pu = u # pu'"
              by (metis empty_iff list.exhaust_sel set_empty u_in_pu)
            then have "path E (v# u# pu')"
              using x_s uv
              apply(cases "pu'"; simp add: Vs_def)
              subgoal by auto
              subgoal by (metis insert_commute path_2 path_subset pu(1) subset_insertI)
              done
            then show ?thesis
              by (metis F1 T3 distinct.simps(2) list.simps(15) mem_path_Vs pu' pu(1) pu(2) pu(3))
          next
            case False
            then have u_last: "u = last pu"
              using u_head_last
              by simp
            then obtain pu' where pu': "pu = pu' @ [u]"
              by (metis Cu(2) append_butlast_last_id empty_iff empty_set pu(2))
            then have "path E ((pu' @ [u]) @ [v])"
              using path_append path_subset pu(1) x_s(1) pu'
              by (smt T3 ass.prems(2) conn_comp_subset_verts insertI1 list.sel(1) rev_subsetD path1 subset_insertI u_last uv)
            then show ?thesis
              using Cu(1) F1 T3 conn_comp_subset_verts pu' pu(2) pu(3) by fastforce
          qed
        next
          case False
          then have "C \<in> connected_components E'" 
            using F1 Cu(1) Cu(2) connected_components_insert_3 ass.prems(4) x_s
            by (smt ass.prems(2) insert_Diff insert_iff uv x_s(1))
          then show ?thesis
            by (metis E'_fine path_subset subset_insertI x_s(1))
        qed
      qed
    next
      case F1: False
      show ?thesis
      proof(cases "v \<in> Vs E'")
        case T2: True
        then obtain Cv where Cv: "Cv \<in> connected_components E'" "v \<in> Cv"
          using connected_components_def in_own_connected_component' by fastforce
        then obtain pv where pv: "path E' pv" "Cv = set pv" "distinct pv"
          using E'_fine
          by auto
        then have v_in_pv: "v \<in> set pv"
          using Cv(2) by blast
        show ?thesis
        proof(cases "C = insert u Cv")
          case T3: True
          show ?thesis
          proof(cases "v = hd pv")
            case T4: True
            then obtain pv' where pv': "pv = v # pv'"
              by (metis empty_iff list.exhaust_sel set_empty v_in_pv)
            then have "path E (u# v# pv')"
              using x_s uv
              apply(cases "pv'"; simp)
              subgoal by (simp add: Vs_def)
              subgoal by (metis path_2 path_subset pv(1) subset_insertI)
              done
            then show ?thesis
              by (metis Cv(1) F1 T3 conn_comp_verts_in_verts distinct.simps(2) list.simps(15) pv' pv(2) pv(3))
          next
            have v_head_last: "v = hd pv \<or> v = last pv"
            proof(rule ccontr; simp)
              assume "v \<noteq> hd pv \<and> v \<noteq> last pv"
              then have "degree E' v \<ge> 2"
                using x_s mid_path_deg_ge_2[OF pv(1) v_in_pv _ _ pv(3)]
                using ass.prems(1) by simp
              then have "degree E v > 2"
                using x_s ass.prems(1) uv
                unfolding degree_def
                by simp
              moreover have "v \<in> Vs E"
                using x_s uv
                unfolding Vs_def
                by blast
              ultimately show False
                using ass.prems(3)
                by auto
            qed
            case False
            then have v_last: "v = last pv"
              using v_head_last
              by simp
            then obtain pv' where pv': "pv = pv' @ [v]"
              by (metis Cv(2) append_butlast_last_id empty_iff empty_set pv(2))
            then have "path E ((pv' @ [v]) @ [u])"
              using path_append path_subset pv(1) x_s(1) pv'
              by (smt T3 ass.prems(2) conn_comp_verts_in_verts insertI1 insert_commute list.sel(1) path1 subset_insertI uv v_last)
            then show ?thesis
              by (smt Int_insert_right_if0 T3 Un_insert_right append_Nil2 distinct_append distinct_singleton insert_absorb list.simps(15) path_subset pv' pv(1) pv(2) pv(3) set_append subset_insertI x_s(1))
          qed
        next
          case False
          then have "C \<in> connected_components E'" 
            using F1 Cv(1) Cv(2) connected_components_insert_3[OF Cv(1) Cv(2) F1] ass.prems(4) x_s
            apply simp
            by (metis ass.prems(2) insert_Diff insert_commute insert_iff uv)
          then show ?thesis
            by (metis E'_fine path_subset subset_insertI x_s(1))
        qed
      next
        case F2: False
        show ?thesis
        proof(cases "C = {u, v}")
          case True
          then show ?thesis
            using connected_components_insert_4
            using  uv x_s(1)
            (*sledgehammer for 5 minutes*)
            by (metis (no_types, hide_lams) conn_comp_subset_verts distinct_length_2_or_more distinct_singleton doubleton_eq_iff empty_set insertI1 insert_absorb2 insert_subset list.simps(15) path.simps)
        next
          case F3: False
          then have "C \<in> connected_components E'" 
            using x_s uv ass.prems(2) connected_components_insert_4[OF F1 F2]
            by auto
          then show ?thesis
            by (metis E'_fine path_subset subset_insertI x_s(1))
        qed
      qed
    qed
  qed
qed

lemma component_has_path_no_cycle:
  assumes "finite C" "C \<in> connected_components E" "card C \<ge> 2"
  shows "\<exists>p. path E p \<and> C = (set p) \<and> hd p \<noteq> last p"
proof-
  obtain p where p: "path E p" "C = (set p)"
    using assms component_has_path'
    by auto
  then show ?thesis
    using remove_cycle_pfx_works_card_ge_2
    by (metis assms(3) path_suff remove_cycle_pfx_works)
qed

definition component_path where
"component_path E C \<equiv> (SOME p. path E p \<and> C = set p \<and> hd p \<noteq> last p)"

definition component_path' where
"component_path' E C \<equiv> (SOME p. path E p \<and> C = set p \<and> distinct p)"

lemma component_path_works:
  assumes "finite C" "C \<in> connected_components E" "card C \<ge> 2"
  shows "path E (component_path E C) \<and> C = set (component_path E C) \<and> hd (component_path E C) \<noteq> last (component_path E C)"
  unfolding component_path_def
  apply(rule someI_ex)
  using component_has_path_no_cycle[OF assms] .

lemma component_path'_works:
  assumes "finite E" "C \<in> connected_components E" "\<forall>v\<in>Vs E. degree E v \<le> 2" "\<forall>e\<in>E. \<exists>u v. e = {u, v}"
  shows "path E (component_path' E C) \<and> C = set (component_path' E C) \<and> distinct (component_path' E C)"
  unfolding component_path'_def
  apply(rule someI_ex)
  using component_has_path_distinct[OF assms] .

lemma component_path'_works':
  assumes "finite E" "C \<in> connected_components E" "\<forall>v\<in>Vs E. degree E v \<le> 2" "\<forall>e\<in>E. \<exists>u v. e = {u, v}"
  shows "path E (component_path' E C)" "set (component_path' E C) = C" "distinct (component_path' E C)"
  using component_path'_works[OF assms]
  by auto

lemma rev_component_path'_works:
  assumes "finite E" "C \<in> connected_components E" "\<forall>v\<in>Vs E. degree E v \<le> 2" "\<forall>e\<in>E. \<exists>u v. e = {u, v}"
  shows "path E (rev (component_path' E C))" "set (rev (component_path' E C)) = C" "distinct (rev (component_path' E C))"
  unfolding set_rev distinct_rev
  using component_path'_works'[OF assms]
  by (auto intro: rev_path_is_path)

lemma component_edges_subset:
  shows "component_edges E C \<subseteq> E"
  unfolding component_edges_def
  by auto

lemma edges_path_subset_edges:
  assumes "path E p" "set p \<subseteq> C"
  shows "set (edges_of_path p) \<subseteq> component_edges E C"
  using assms
proof(induction)
  case path0
  then show ?case by simp
next
  case path1
  then show ?case by simp
next
  case path2
  then show ?case by (auto simp add:  component_edges_def)
qed

lemma finite_con_comps:
  assumes "finite (Vs E)"
  shows "finite (connected_components E)"
  unfolding connected_components_def
  using assms
  by auto

end