theory Alt_BFS_Imperative_Arrays
  imports Alt_BFS_Imperative "../Alt_BFS_Lists"
begin

section \<open>The Imperative Alternating BFS on Arrays\<close>

text \<open>Frontiers are kept in two arrays that swap their roles, the visited sets are sets over the
      fixed universe of vertices below @{term N}, and the even and odd distances are kept in two
      arrays. The operations on the visited sets and the iteration over neighbour lists are
      parameters, as in the imperative BFS of the library.\<close>

lemma ht_ex_pre_and_post_pair_I:
  "(\<And>x. <P x> c <\<lambda>(r1, r2). Q x r1 r2>) \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <\<lambda>(r1, r2). \<exists>\<^sub>A x. Q x r1 r2>"
  by sep_auto

subsection \<open>Sets over a fixed universe\<close>

locale imp_fixed_univ_set =
  fixes is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  assumes only_in_univ: "is_fixed_univ_set U S Si = (is_fixed_univ_set U S Si * \<up> (S \<subseteq> U))"

locale imp_fixed_univ_set_memb = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes memb :: "'a \<Rightarrow> 's \<Rightarrow> bool Heap"
  assumes memb_rule[sep_heap_rules]:
    "<is_fixed_univ_set U s p * \<up> (a \<in> U)> memb a p <\<lambda>r. is_fixed_univ_set U s p * \<up>(r \<longleftrightarrow> a \<in> s)>"

locale imp_fixed_univ_set_distinct_ins = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes distinct_ins :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes distinct_ins_rule[sep_heap_rules]:
    "<is_fixed_univ_set U s p * \<up> (a \<in> U \<and> a \<notin> s)> distinct_ins a p <is_fixed_univ_set U (Set.insert a s)>"

subsection \<open>The operations\<close>

locale Alt_BFS_arrays_code =
  fixes visited_memb :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
    and distinct_ins :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_vis Heap"
    and iterate_neighbourhood :: "'g \<Rightarrow> nat \<Rightarrow>
          (nat \<Rightarrow> nat \<Rightarrow> nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap) \<Rightarrow>
          nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap"
begin

definition "inner_step u v = (\<lambda>(front, frontpt, vis).
   do { b \<leftarrow> visited_memb v vis;
        if \<not> b then do { front' \<leftarrow> Array.upd frontpt v front;
                         vis' \<leftarrow> distinct_ins v vis;
                         return (front', Suc frontpt, vis') }
        else return (front, frontpt, vis) })"

definition "inner_loop Gi u acc = iterate_neighbourhood Gi u inner_step acc"

definition "outer_loop Gi old_front old_frontp acc =
  iterate_range_strict old_front 0 old_frontp (inner_loop Gi) acc"

definition "next_frontier_and_visited_imp Gi =
  (\<lambda>(fronti, frontp, buffer_fronti) vis.
     do { (front', frontpt', vis') \<leftarrow> outer_loop Gi fronti frontp (buffer_fronti, 0, vis);
          return ((front', frontpt', fronti), vis') })"

definition "imp_cf_is_empty = (\<lambda>(fronti, frontp, buffer_fronti). return (frontp = 0))"

definition "imp_src_to_cf = (\<lambda>x. return x)"

definition "set_srcs_visited vis =
  (\<lambda>(fronti, frontp, buffer_fronti).
     iterate_range_strict fronti 0 frontp
       (\<lambda>v vis. do { b \<leftarrow> visited_memb v vis; if \<not> b then distinct_ins v vis else return vis }) vis)"

definition "set_all_dists_imp =
  (\<lambda>(dE, dO) p (fronti, frontp, buffer_fronti) n.
     (case p of
        Even \<Rightarrow> do { dE' \<leftarrow> iterate_range_strict fronti 0 frontp (\<lambda>v d. Array.upd v n d) dE;
                     return (dE', dO) }
      | Odd \<Rightarrow> do { dO' \<leftarrow> iterate_range_strict fronti 0 frontp (\<lambda>v d. Array.upd v n d) dO;
                    return (dE, dO') }))"

end

subsection \<open>Correctness of the operations\<close>

locale Alt_BFS_arrays =
  Alt_BFS_lists matchingG unmatchingG srcsL +
  Alt_BFS_arrays_code where visited_memb = visited_memb and distinct_ins = distinct_ins
    and iterate_neighbourhood = iterate_neighbourhood +
  imp_fixed_univ_set_memb where is_fixed_univ_set = is_visited_set and memb = visited_memb +
  imp_fixed_univ_set_distinct_ins where is_fixed_univ_set = is_visited_set
    and distinct_ins = distinct_ins
  for matchingG unmatchingG :: "nat \<Rightarrow> nat list option" and srcsL :: "nat list"
    and is_visited_set and visited_memb :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
    and distinct_ins :: "nat \<Rightarrow> 'imp_vis \<Rightarrow> 'imp_vis Heap"
    and iterate_neighbourhood :: "'g \<Rightarrow> nat \<Rightarrow>
          (nat \<Rightarrow> nat \<Rightarrow> nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap) \<Rightarrow>
          nat array \<times> nat \<times> 'imp_vis \<Rightarrow> (nat array \<times> nat \<times> 'imp_vis) Heap" +
  fixes graph_assn :: "(nat \<Rightarrow> nat list option) \<Rightarrow> 'g \<Rightarrow> assn"
    and N :: nat
    and Mi Ui :: 'g
    and Lf :: nat
  assumes iterate_neighbourhood_rule:
    "\<And>H Hi v fi f acc acci F
       (acc_assn :: nat list \<times> nat list \<Rightarrow> nat array \<times> nat \<times> 'imp_vis \<Rightarrow> assn).
     (\<And>acc acci x. x \<in> set (nbs H v) \<Longrightarrow>
        <acc_assn acc acci * F> fi v x acci <\<lambda>r. acc_assn (f acc x) r * F>) \<Longrightarrow>
     <graph_assn H Hi * acc_assn acc acci * F>
       iterate_neighbourhood Hi v fi acci
     <\<lambda>r. graph_assn H Hi * F * acc_assn (foldl f acc (nbs H v)) r>"
    and vertices_bounded: "dVs alt.G \<subseteq> {..<N}"
begin

abbreviation "U \<equiv> {..<N::nat}"

text \<open>The frontier under construction, in the array @{term fronti} of length @{term L}: it is
      contained in the visited set, so the array has room for one more vertex as long as the
      visited set does not yet contain all vertices.\<close>

definition "front_assn L vis (front::nat list) fronti frontp =
  (\<exists>\<^sub>A fl. fronti \<mapsto>\<^sub>a fl * \<up>(N < length fl \<and> frontp < length fl - N + card vis \<and>
     rev (take frontp fl) = front \<and> vis \<subseteq> U \<and> set front \<subseteq> U \<and> length fl = L))"

definition "nfv_acc_assn L = (\<lambda>(front, vis) (fronti, frontp, visi).
   is_visited_set U (set vis) visi * front_assn L (set vis) front fronti frontp)"

definition "nfv_step = (\<lambda>(nf, vis) y. if y \<notin> set vis then (y # nf, y # vis) else (nf, vis))"

lemma card_less_N: "\<lbrakk>S \<subseteq> U; y \<in> U; y \<notin> S\<rbrakk> \<Longrightarrow> card S < N"
  using psubset_card_mono[of U S] by auto

lemma inner_step_rule:
  assumes "y \<in> U"
  shows "<nfv_acc_assn L (front, vis) (fronti, frontp, visi)> inner_step u y (fronti, frontp, visi)
         <\<lambda>r. nfv_acc_assn L (nfv_step (front, vis) y) r>"
proof(cases "y \<in> set vis")
  case True
  thus ?thesis
    unfolding inner_step_def nfv_acc_assn_def nfv_step_def prod.case
    using assms by sep_auto
next
  case False
  show ?thesis
    unfolding inner_step_def nfv_acc_assn_def nfv_step_def prod.case front_assn_def
    apply (subst only_in_univ)
    using assms card_less_N[of "set vis" y] False
    apply (sep_auto simp: False)
    subgoal for fl r a b rb
      apply (rule mod_exI[of _ "list_update fl frontp y"])
      apply (sep_auto simp: mod_pure_star_dist)
      by (simp add: take_update_last)
    by simp
qed

lemma inner_step_rule_frame:
  "y \<in> U \<Longrightarrow> <nfv_acc_assn L acc acci * F> inner_step u y acci <\<lambda>r. nfv_acc_assn L (nfv_step acc y) r * F>"
  by (cases acc, cases acci) (auto intro: ht_frame inner_step_rule)

lemma digraph_abs_alt: "alt.Graph.digraph_abs H = {(u, v). v \<in> set (nbs H u)}"
  by (rule digraph_abs_lists)

lemma nbs_in_U: "alt.Graph.digraph_abs H \<subseteq> alt.G \<Longrightarrow> set (nbs H u) \<subseteq> U"
proof
  fix v
  assume "alt.Graph.digraph_abs H \<subseteq> alt.G" "v \<in> set (nbs H u)"
  hence "(u, v) \<in> alt.G"
    by (auto simp: digraph_abs_alt)
  hence "v \<in> dVs alt.G"
    by (rule dVsI(2))
  thus "v \<in> U"
    using vertices_bounded by blast
qed

lemma inner_loop_rule:
  assumes "set (nbs H u) \<subseteq> U"
  shows "<graph_assn H Hi * nfv_acc_assn L acc acci> inner_loop Hi u acci
         <\<lambda>r. graph_assn H Hi * nfv_acc_assn L (foldl nfv_step acc (nbs H u)) r>"
  unfolding inner_loop_def
  apply (rule iterate_neighbourhood_rule[where acc_assn = "nfv_acc_assn L" and F = emp and f = nfv_step,
                                         simplified])
  using assms by (auto intro!: inner_step_rule_frame[where F = emp, simplified])

lemma nfv_l_alt:
  "next_frontier_and_visited_l H F V = foldl (\<lambda>acc u. foldl nfv_step acc (nbs H u)) ([], V) (rev F)"
  unfolding next_frontier_and_visited_l_def nfv_step_def
  by (simp add: case_prod_unfold)

lemma outer_loop_rule:
  assumes "\<And>u. set (nbs H u) \<subseteq> U" "old_frontp < length ofl"
  shows "<graph_assn H Hi * nfv_acc_assn L acc acci * old_fronti \<mapsto>\<^sub>a ofl>
           outer_loop Hi old_fronti old_frontp acci
         <\<lambda>r. graph_assn H Hi * old_fronti \<mapsto>\<^sub>a ofl *
               nfv_acc_assn L (foldl (\<lambda>acc u. foldl nfv_step acc (nbs H u)) acc
                                 (take old_frontp ofl)) r>"
proof-
  have R: "<old_fronti \<mapsto>\<^sub>a ofl * \<up>(old_frontp < length ofl) * graph_assn H Hi * nfv_acc_assn L acc acci>
          iterate_range_strict old_fronti 0 old_frontp (inner_loop Hi) acci
        <\<lambda>r. old_fronti \<mapsto>\<^sub>a ofl *
              nfv_acc_assn L (foldl (\<lambda>acc u. foldl nfv_step acc (nbs H u)) acc
                                (nths ofl {0..<old_frontp})) r * graph_assn H Hi>"
    by (rule iterate_range_strict_rule) (sep_auto heap: inner_loop_rule[OF assms(1)])
  show ?thesis
    unfolding outer_loop_def
    using assms(2)
    by (sep_auto heap: R simp: nths_intervall_strict_as_drop_and_take)
qed

text \<open>A frontier together with the buffer for the next one.\<close>

definition "imp_cf_assn L front = (\<lambda>(fronti, frontp, bufi).
   \<exists>\<^sub>A fl bl. fronti \<mapsto>\<^sub>a fl * bufi \<mapsto>\<^sub>a bl *
     \<up>(N < length fl \<and> frontp < length fl \<and> rev (take frontp fl) = front \<and> set front \<subseteq> U \<and>
       length fl = L \<and> length bl = L))"

lemma card_le_N: "S \<subseteq> U \<Longrightarrow> card S \<le> N"
  using card_mono[of U S] by auto

lemma next_frontier_and_visited_imp_rule:
  assumes "alt.Graph.digraph_abs H \<subseteq> alt.G"
  shows "<imp_cf_assn L F Fi * is_visited_set U (set V) Vi * graph_assn H Hi>
           next_frontier_and_visited_imp Hi Fi Vi
         <\<lambda>(Fi', Vi'). imp_cf_assn L (fst (next_frontier_and_visited_l H F V)) Fi' *
                       is_visited_set U (set (snd (next_frontier_and_visited_l H F V))) Vi' *
                       graph_assn H Hi>"
proof-
  obtain fronti frontp bufi where Fi: "Fi = (fronti, frontp, bufi)"
    by (cases Fi)
  obtain F' V' where nf: "next_frontier_and_visited_l H F V = (F', V')"
    by (cases "next_frontier_and_visited_l H F V")
  have main: "<fronti \<mapsto>\<^sub>a fl * bufi \<mapsto>\<^sub>a bl * is_visited_set U (set V) Vi * graph_assn H Hi>
                outer_loop Hi fronti frontp (bufi, 0, Vi) \<bind>
                (\<lambda>(front', frontpt', vis'). return ((front', frontpt', fronti), vis'))
              <\<lambda>(Fi', Vi'). imp_cf_assn L F' Fi' * is_visited_set U (set V') Vi' * graph_assn H Hi>"
    if fl: "N < length fl" "frontp < length fl" "rev (take frontp fl) = F" "length fl = L" "length bl = L"
           "set V \<subseteq> U" for fl bl
  proof-
    have pre: "fronti \<mapsto>\<^sub>a fl * bufi \<mapsto>\<^sub>a bl * is_visited_set U (set V) Vi * graph_assn H Hi \<Longrightarrow>\<^sub>A
               graph_assn H Hi * nfv_acc_assn L ([], V) (bufi, 0, Vi) * fronti \<mapsto>\<^sub>a fl"
      using fl unfolding nfv_acc_assn_def front_assn_def prod.case by sep_auto
    have fold: "foldl (\<lambda>acc u. foldl nfv_step acc (nbs H u)) ([], V) (take frontp fl) = (F', V')"
    proof-
      have "take frontp fl = rev F"
        using fl(3) by (simp add: rev_swap)
      thus ?thesis
        using nf by (simp only: nfv_l_alt)
    qed
    have post: "graph_assn H Hi * fronti \<mapsto>\<^sub>a fl * nfv_acc_assn L (F', V') r \<Longrightarrow>\<^sub>A
                (case ((fst r, fst (snd r), fronti), snd (snd r)) of (Fi', Vi') \<Rightarrow>
                   imp_cf_assn L F' Fi' * is_visited_set U (set V') Vi' * graph_assn H Hi)" for r
    proof(cases r)
      case (fields fronti' frontp' visi')
      show ?thesis
        unfolding fields nfv_acc_assn_def front_assn_def imp_cf_assn_def prod.case fst_conv snd_conv
        apply (subst only_in_univ)
        using fl card_le_N[of "set V'"]
        by sep_auto
    qed
    have R: "<fronti \<mapsto>\<^sub>a fl * bufi \<mapsto>\<^sub>a bl * is_visited_set U (set V) Vi * graph_assn H Hi>
               outer_loop Hi fronti frontp (bufi, 0, Vi)
             <\<lambda>r. graph_assn H Hi * fronti \<mapsto>\<^sub>a fl * nfv_acc_assn L (F', V') r>"
      using ht_cons_prec[OF pre ent_refl outer_loop_rule[OF nbs_in_U[OF assms] fl(2)]]
      unfolding fold .
    have P: "<graph_assn H Hi * fronti \<mapsto>\<^sub>a fl * nfv_acc_assn L (F', V') r>
               (case r of (front', frontpt', vis') \<Rightarrow> return ((front', frontpt', fronti), vis'))
             <\<lambda>(Fi', Vi'). imp_cf_assn L F' Fi' * is_visited_set U (set V') Vi' * graph_assn H Hi>"
      for r
    proof(cases r)
      case (fields a b c)
      show ?thesis
        unfolding fields prod.case
        apply (rule ht_cons_prec[OF _ ent_refl ht_return_wp])
        using post[of "(a, b, c)"] by simp
    qed
    show ?thesis
      by (rule ht_bind[OF R P])
  qed
  have E: "(\<exists>\<^sub>A fl bl. fronti \<mapsto>\<^sub>a fl * bufi \<mapsto>\<^sub>a bl *
              \<up>(N < length fl \<and> frontp < length fl \<and> rev (take frontp fl) = F \<and> set F \<subseteq> U \<and>
                length fl = L \<and> length bl = L)) * is_visited_set U (set V) Vi * graph_assn H Hi \<Longrightarrow>\<^sub>A
           \<exists>\<^sub>A fl bl. (fronti \<mapsto>\<^sub>a fl * bufi \<mapsto>\<^sub>a bl * is_visited_set U (set V) Vi * graph_assn H Hi) *
             \<up>(N < length fl \<and> frontp < length fl \<and> rev (take frontp fl) = F \<and>
               length fl = L \<and> length bl = L \<and> set V \<subseteq> U)"
    by (subst only_in_univ) sep_auto
  have T: "<\<exists>\<^sub>A fl bl. (fronti \<mapsto>\<^sub>a fl * bufi \<mapsto>\<^sub>a bl * is_visited_set U (set V) Vi * graph_assn H Hi) *
             \<up>(N < length fl \<and> frontp < length fl \<and> rev (take frontp fl) = F \<and>
               length fl = L \<and> length bl = L \<and> set V \<subseteq> U)>
             outer_loop Hi fronti frontp (bufi, 0, Vi) \<bind>
             (\<lambda>(front', frontpt', vis'). return ((front', frontpt', fronti), vis'))
           <\<lambda>(Fi', Vi'). imp_cf_assn L F' Fi' * is_visited_set U (set V') Vi' * graph_assn H Hi>"
    by (intro norm_pre_extractI(2) norm_pre_extractI(5)) (elim conjE, rule main)
  show ?thesis
    unfolding Fi nf next_frontier_and_visited_imp_def prod.case fst_conv snd_conv
    apply (rule ht_cons_prec[OF _ ent_refl T])
    unfolding imp_cf_assn_def prod.case by (rule E)
qed

text \<open>The distances of the even and of the odd copies are kept in two arrays.\<close>

definition "par_arr_assn p (d::nat labelled_vtx \<Rightarrow> nat) a =
  (\<exists>\<^sub>A l. a \<mapsto>\<^sub>a l * \<up>(length l = N \<and> (\<forall>i < N. d (Vtx p i) = l ! i)))"

definition "imp_dist_assn d = (\<lambda>(dE, dO). par_arr_assn Even d dE * par_arr_assn Odd d dO)"

lemma par_arr_upd_rule:
  "x < N \<Longrightarrow> <par_arr_assn p d a> Array.upd x n a <\<lambda>r. par_arr_assn p (fun_upd d (Vtx p x) n) r>"
  unfolding par_arr_assn_def by (sep_auto simp: nth_list_update)

lemma par_arr_assn_cong:
  "(\<And>i. i < N \<Longrightarrow> d (Vtx p i) = d' (Vtx p i)) \<Longrightarrow> par_arr_assn p d a = par_arr_assn p d' a"
  unfolding par_arr_assn_def by simp

lemma eq_Vtx_iff: "w = Vtx p x \<longleftrightarrow> label w = p \<and> vtx w = x"
  by (cases w) auto

lemma foldl_upd_set_all_dists:
  "foldl (\<lambda>d x. fun_upd d (Vtx p x) n) d xs = set_all_dists_l d p xs n"
  by (induction xs arbitrary: d) (auto simp: set_all_dists_l_def eq_Vtx_iff)

lemma set_all_dists_l_set: "set xs = set ys \<Longrightarrow> set_all_dists_l d p xs n = set_all_dists_l d p ys n"
  by (simp add: set_all_dists_l_def)

lemma par_arr_other: "q \<noteq> p \<Longrightarrow> par_arr_assn q (set_all_dists_l d p F n) a = par_arr_assn q d a"
  by (rule par_arr_assn_cong) (simp add: set_all_dists_l_def)

lemma par_arr_fill_rule:
  assumes "set (take frontp fl) \<subseteq> U" "frontp < length fl"
  shows "<fronti \<mapsto>\<^sub>a fl * par_arr_assn p d a * R>
           iterate_range_strict fronti 0 frontp (\<lambda>v d. Array.upd v n d) a
         <\<lambda>r. fronti \<mapsto>\<^sub>a fl * par_arr_assn p (set_all_dists_l d p (take frontp fl) n) r * R>"
proof-
  have I: "<fronti \<mapsto>\<^sub>a fl * \<up>(frontp < length fl) * R * par_arr_assn p d a>
          iterate_range_strict fronti 0 frontp (\<lambda>v d. Array.upd v n d) a
        <\<lambda>r. fronti \<mapsto>\<^sub>a fl *
              par_arr_assn p (foldl (\<lambda>d x. fun_upd d (Vtx p x) n) d (nths fl {0..<frontp})) r * R>"
  proof(rule iterate_range_strict_rule[where acc_assn = "par_arr_assn p" and F = R
                                         and f = "\<lambda>d x. fun_upd d (Vtx p x) n"])
    fix acc acci x
    assume "x \<in> set (nths fl {0..<frontp})"
    hence "x < N"
      using assms(1) by (auto simp: nths_intervall_strict_as_drop_and_take)
    thus "<par_arr_assn p acc acci * R> Array.upd x n acci
          <\<lambda>r. par_arr_assn p (fun_upd acc (Vtx p x) n) r * R>"
      by (rule ht_frame[OF par_arr_upd_rule])
  qed
  show ?thesis
    using assms(2)
    by (sep_auto heap: I simp: nths_intervall_strict_as_drop_and_take foldl_upd_set_all_dists)qed

lemma set_all_dists_imp_rule:
  assumes "set F \<subseteq> U"
  shows "<imp_dist_assn d di * imp_cf_assn L F Fi> set_all_dists_imp di p Fi n
         <\<lambda>r. imp_dist_assn (set_all_dists_l d p F n) r * imp_cf_assn L F Fi>"
proof-
  obtain dE dO where di: "di = (dE, dO)"
    by (cases di)
  obtain fronti frontp bufi where Fi: "Fi = (fronti, frontp, bufi)"
    by (cases Fi)
  have set_eq: "set (take frontp fl) = set F" if "rev (take frontp fl) = F" for fl
    using that by auto
  show ?thesis
    unfolding di Fi set_all_dists_imp_def imp_dist_assn_def imp_cf_assn_def prod.case
    using assms
    by (cases p)
       (sep_auto heap: par_arr_fill_rule simp: par_arr_other set_eq[THEN set_all_dists_l_set])+
qed

lemma imp_cf_is_empty_rule:
  "<imp_cf_assn L S Si> imp_cf_is_empty Si <\<lambda>b. imp_cf_assn L S Si * \<up>(b \<longleftrightarrow> S = [])>"
  by (cases Si) (sep_auto simp: imp_cf_is_empty_def imp_cf_assn_def)

lemma imp_src_to_cf_rule: "<imp_cf_assn L S Si> imp_src_to_cf Si <\<lambda>r. imp_cf_assn L S r>"
  by (sep_auto simp: imp_src_to_cf_def)

lemma set_srcs_visited_rule:
  "<imp_cf_assn L S Si * is_visited_set U (set []) Vi> set_srcs_visited Vi Si
   <\<lambda>r. is_visited_set U (set S) r * imp_cf_assn L S Si>"
proof-
  obtain fronti frontp bufi where Si: "Si = (fronti, frontp, bufi)"
    by (cases Si)
  have I: "<fronti \<mapsto>\<^sub>a fl * \<up>(frontp < length fl) * (bufi \<mapsto>\<^sub>a bl) * is_visited_set U {} Vi>
             iterate_range_strict fronti 0 frontp
               (\<lambda>v vis. do { b \<leftarrow> visited_memb v vis; if b then return vis else distinct_ins v vis }) Vi
           <\<lambda>r. fronti \<mapsto>\<^sub>a fl * is_visited_set U (foldl (\<lambda>A x. Set.insert x A) {} (nths fl {0..<frontp})) r *
                 bufi \<mapsto>\<^sub>a bl>"
    if "set (take frontp fl) \<subseteq> U" for fl bl
  proof(rule iterate_range_strict_rule[where acc_assn = "is_visited_set U" and F = "bufi \<mapsto>\<^sub>a bl"
                                         and f = "\<lambda>A x. Set.insert x A"])
    fix acc acci x
    assume "x \<in> set (nths fl {0..<frontp})"
    hence "x \<in> U"
      using that by (auto simp: nths_intervall_strict_as_drop_and_take)
    thus "<is_visited_set U acc acci * bufi \<mapsto>\<^sub>a bl>
            do { b \<leftarrow> visited_memb x acci; if b then return acci else distinct_ins x acci }          <\<lambda>r. is_visited_set U (Set.insert x acc) r * bufi \<mapsto>\<^sub>a bl>"
      by (sep_auto simp: insert_absorb)
  qed
  have fold_ins: "foldl (\<lambda>A x. Set.insert x A) A xs = A \<union> set xs" for A and xs :: "nat list"
    by (induction xs arbitrary: A) auto
  show ?thesis
    unfolding Si set_srcs_visited_def imp_cf_assn_def prod.case
    by (sep_auto heap: I simp: fold_ins nths_intervall_strict_as_drop_and_take)
qed

end

subsection \<open>The imperative alternating BFS on arrays\<close>

text \<open>The instance for the graphs with the heap handles @{term Mi} and @{term Ui}; the frontier
      arrays have length @{term Lf}.\<close>

context Alt_BFS_arrays
begin
sublocale imp: Alt_BFS_Imperative
  where empty = "\<lambda>_. None" and delete = "\<lambda>x M. fun_upd M x None" and lookup_neighb = "\<lambda>M x. M x"
    and insert = Cons and isin = "\<lambda>xs x. x \<in> set xs" and t_set = set and sel = hd
    and update = "\<lambda>x z M. M(x \<mapsto> z)" and adjmap_inv = "\<lambda>_. True"
    and vset_empty = Nil and vset_delete = "\<lambda>x xs. filter (\<lambda>y. y \<noteq> x) xs" and vset_inv = "\<lambda>_. True"
    and union = append and inter = "\<lambda>xs ys. filter (\<lambda>y. y \<in> set ys) xs"
    and diff = "\<lambda>xs ys. filter (\<lambda>y. y \<notin> set ys) xs"
    and lookup_dist = "\<lambda>m k. m k" and empty_dist = Map.empty and update_dist = "\<lambda>k v m. m(k \<mapsto> v)"
    and delete_dist = "\<lambda>k m. fun_upd m k None" and invar_dist = "\<lambda>_. True"
    and srcs = srcsL and matching = matchingG and unmatching = unmatchingG
    and expand_tree = expand_tree_l and next_frontier_impl = next_frontier_l
    and upd_dists = upd_dists_l and init_dists = "init_dists_l srcsL"
    and next_frontier_and_visited = next_frontier_and_visited_l and set_all_dists = set_all_dists_l
    and dist_lookup = "\<lambda>d w. d w" and dist_invar = "\<lambda>_ _. True" and some_dist = "\<lambda>_. 0"
    and imp_cf_is_empty = imp_cf_is_empty and next_frontier_and_visited_imp = next_frontier_and_visited_imp
    and set_all_dists_imp = set_all_dists_imp and imp_src_to_cf = imp_src_to_cf
    and set_srcs_visited = set_srcs_visited and matching_imp = Mi and unmatching_imp = Ui
    and graph_assn = graph_assn and imp_src_assn = "imp_cf_assn Lf" and imp_cf_assn = "imp_cf_assn Lf"
    and imp_vis_assn = "\<lambda>V. is_visited_set U (set V)" and imp_dist_assn = imp_dist_assn
proof(intro Alt_BFS_Imperative.intro alt.Alt_BFS_distance_axioms Alt_BFS_Imperative_axioms.intro,
      goal_cases)
  case (1 S Si)
  then show ?case
    by (rule imp_cf_is_empty_rule)
next
  case (2 H Hi F Fi V Vi)
  show ?case
    by (rule next_frontier_and_visited_imp_rule[OF 2(4)])next
  case (3 d di p F Fi n)
  then show ?case
    using vertices_bounded by (intro set_all_dists_imp_rule) auto
next
  case (4 S Si)
  then show ?case
    by (rule imp_src_to_cf_rule)
next
  case (5 S Si Vi)
  then show ?case
    by (rule set_srcs_visited_rule)
qed

text \<open>The array program computes the visited sets and the distances of the alternating BFS, and
      its distances determine the DAG of the alternating BFS.\<close>

lemmas Alt_BFS_arrays_correct = imp.Alt_BFS_run_imp_correct

end

end
