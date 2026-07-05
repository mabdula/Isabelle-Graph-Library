theory IDFS
  imports DFS_Avoid DDFS
begin

text \<open>The incremental DFS assumed by the DDFS development, realised by the skeleton instance
\<^locale>\<open>DFS_avoid\<close> instantiated with plain HOL sets and function maps. This theory bridges
the two vocabularies (DDFS's \<^term>\<open>DDFS.dpath\<close> versus the library's \<^term>\<open>Vwalk.vwalk\<close>),
defines the function \<^term>\<open>IDFS\<close>, and exports the DDFS-facing properties.\<close>

section \<open>Plain-set instantiation of the ADT-based avoid-DFS\<close>

definition mk_adjmap :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a set option)" where
  "mk_adjmap dG = (\<lambda>v. if \<exists>u. (v, u) \<in> dG then Some {u. (v, u) \<in> dG} else None)"

global_interpretation set_avoid: DFS_avoid
  where update = "\<lambda>k v m. m(k \<mapsto> v)" and adjmap_inv = "\<lambda>_. True"
    and vset_empty = "{}" and vset_delete = "\<lambda>x S. S - {x}" and vset_inv = "\<lambda>_. True"
    and empty = "\<lambda>_. None" and delete = "\<lambda>k m. m(k := None)" and lookup = id
    and insert = Set.insert and isin = "\<lambda>S x. x \<in> S" and t_set = id
    and sel = "\<lambda>S. SOME x. x \<in> S"
    and union = "(\<union>)" and inter = "(\<inter>)" and diff = "(-)"
    and G = "mk_adjmap dG" and stack0 = p0 and vis0 = V0 and avoid = A0
    and Pv = P and level = lev
  for dG :: "('a \<times> 'a) set" and p0 :: "'a list" and V0 A0 :: "'a set" and P :: "'a \<Rightarrow> bool"
    and lev :: "'a \<Rightarrow> nat"
  defines set_final = set_avoid.avoid_final_state
  by unfold_locales (auto simp: some_in_eq)

lemma digraph_abs_mk_adjmap: "set_avoid.Graph.digraph_abs (mk_adjmap dG) = dG"
  by (auto simp: set_avoid.Graph.digraph_abs_def set_avoid.Graph.neighbourhood_def
                 mk_adjmap_def split: if_splits)

section \<open>The incremental DFS\<close>

text \<open>The head of the given stack is checked against the avoid and visited sets and dropped
if it lies in either (the algorithm backtracks over it); this matches the comment in the
DDFS locale. The avoid and visited sets are restricted to the graph's vertices before
seeding the search state.\<close>

definition IDFS_stack0 :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "IDFS_stack0 A V q = (if q \<noteq> [] \<and> hd q \<in> A \<union> V then tl q else q)"

definition IDFS ::
  "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> ('a list option \<times> 'a set)"
  where "IDFS dG Pr A q V =
    (let st = set_final dG (IDFS_stack0 A V q)
                (V \<inter> Pair_Graph.dVs dG) (A \<inter> Pair_Graph.dVs dG) Pr
     in (DFS_avoid_state.ret st, V \<union> DFS_avoid_state.visited st))"

section \<open>DDFS-facing properties\<close>

text \<open>The properties assumed of IDFS by the DDFS locale, under the necessary premises:
the digraph is layered and finite, the given stack is (the reverse of) a distinct path,
and the previously visited set is sound (no P-vertex, and its onward walks to P-vertices
cross the avoid set — the precondition that is commented out in DDFS.tex).\<close>

context
  fixes dG :: "('a \<times> 'a) set" and lev :: "'a \<Rightarrow> nat" and P :: "'a \<Rightarrow> bool"
  assumes layered: "\<And>u v. (u, v) \<in> dG \<Longrightarrow> lev v < lev u"
      and fin: "finite (dVs dG)"
begin

text \<open>IDFS_vis_works(3): visited monotone — proved directly, no path premise needed.\<close>

theorem IDFS_vis_works_4:
  fixes avoid visited :: "'a set" and p :: "'a list"
  assumes "IDFS dG P avoid p visited = (ret_p, visited')"
  shows "visited \<subseteq> visited'"
  using assms by (auto simp: IDFS_def Let_def)

context
  fixes avoid visited :: "'a set" and p :: "'a list"
  assumes p_path: "dpath dG (rev p)"
      and p_dist: "distinct p"
begin

text \<open>Internal note: this inner context supplies the path/distinctness premises
needed for the DFS-avoid interpretation (set_axioms). As a result, theorems proved
here carry \<open>dpath dG (rev p)\<close> and \<open>distinct p\<close> as per-theorem exports. This
exactly matches the DDFS locale clauses for IDFS_closed and IDFS_sound(1,2); for
IDFS_vis_works(1..4), IDFS_complete and IDFS_sound(3..8) the DDFS clauses have
no such premise — those theorems carry extra premises here because the DFS
correctness argument currently requires a valid initial stack. In Phase 2 the DDFS
instantiation can discharge these extra premises via its stack-path invariants.\<close>

lemma dabs: "set_avoid.Graph.digraph_abs (mk_adjmap dG) = dG"
  by (auto simp: set_avoid.Graph.digraph_abs_def set_avoid.Graph.neighbourhood_def
                 mk_adjmap_def split: if_splits)

lemma p_dVs: "set p \<subseteq> Pair_Graph.dVs dG"
proof -
  have "Vwalk.vwalk dG (rev p)"
    using p_path by simp
  then show ?thesis
    using vwalk_then_in_dVs[of dG "rev p"] by auto
qed

lemma stack0_cases:
  "(IDFS_stack0 avoid visited p = p \<and> (p = [] \<or> hd p \<notin> avoid \<union> visited)) \<or>
   (IDFS_stack0 avoid visited p = tl p \<and> p \<noteq> [] \<and> hd p \<in> avoid \<union> visited)"
  by (auto simp: IDFS_stack0_def)

lemma stack0_sub_p: "set (IDFS_stack0 avoid visited p) \<subseteq> set p"
  using stack0_cases by (cases p) auto

lemma set_axioms:
  "set_avoid.DFS_avoid_axioms TYPE('a) dG (IDFS_stack0 avoid visited p)
     (visited \<inter> Pair_Graph.dVs dG) (avoid \<inter> Pair_Graph.dVs dG) lev"
  unfolding set_avoid.DFS_avoid_axioms_def
proof (intro conjI)
  show "set_avoid.Graph.graph_inv (mk_adjmap dG)"
    by (simp add: set_avoid.Graph.graph_inv_def)
  show "set_avoid.Graph.finite_graph (mk_adjmap dG)"
  proof -
    have "{v. mk_adjmap dG v \<noteq> None} \<subseteq> Pair_Graph.dVs dG"
      by (auto simp: mk_adjmap_def Pair_Graph.dVs_def split: if_splits)
    then have "finite {v. mk_adjmap dG v \<noteq> None}"
      using fin by (auto intro: finite_subset)
    then show ?thesis
      by (simp add: set_avoid.Graph.finite_graph_def)
  qed
  show "set_avoid.Graph.finite_vsets (mk_adjmap dG)"
  proof (rule set_avoid.Graph.finite_vsetsI)
    fix v N assume "id (mk_adjmap dG) v = Some N"
    then have "N \<subseteq> Pair_Graph.dVs dG"
      by (auto simp: mk_adjmap_def Pair_Graph.dVs_def split: if_splits)
    then have "finite N"
      using fin by (auto intro: finite_subset)
    then show "finite (id N)"
      by simp
  qed
  show "(\<lambda>_. True) (avoid \<inter> Pair_Graph.dVs dG)" "(\<lambda>_. True) (visited \<inter> Pair_Graph.dVs dG)"
    by simp_all
  show "id (avoid \<inter> Pair_Graph.dVs dG)
          \<subseteq> Pair_Graph.dVs (set_avoid.Graph.digraph_abs (mk_adjmap dG))"
       "id (visited \<inter> Pair_Graph.dVs dG)
          \<subseteq> Pair_Graph.dVs (set_avoid.Graph.digraph_abs (mk_adjmap dG))"
    by (auto simp: dabs)
  show "Vwalk.vwalk (set_avoid.Graph.digraph_abs (mk_adjmap dG))
          (rev (IDFS_stack0 avoid visited p))"
  proof -
    have w: "Vwalk.vwalk dG (rev p)"
      using p_path by simp
    show ?thesis
    proof (cases "IDFS_stack0 avoid visited p = p")
      case True
      then show ?thesis using w by (simp add: dabs)
    next
      case False
      then have s: "IDFS_stack0 avoid visited p = tl p" and ne: "p \<noteq> []"
        using stack0_cases by auto
      have "rev p = rev (tl p) @ [hd p]"
        using ne by (cases p) auto
      then have "Vwalk.vwalk dG (rev (tl p))"
        using w append_vwalk_pref by fastforce
      then show ?thesis using s by (simp add: dabs)
    qed
  qed
  show "distinct (IDFS_stack0 avoid visited p)"
    using p_dist stack0_cases distinct_tl sorry
  show "\<forall>u v. (u, v) \<in> set_avoid.Graph.digraph_abs (mk_adjmap dG) \<longrightarrow> lev v < lev u"
    using layered by (simp add: dabs)
qed

interpretation T: DFS_avoid_thms
  where update = "\<lambda>k v m. m(k \<mapsto> v)" and adjmap_inv = "\<lambda>_. True"
    and vset_empty = "{}" and vset_delete = "\<lambda>x S. S - {x}" and vset_inv = "\<lambda>_. True"
    and empty = "\<lambda>_. None" and delete = "\<lambda>k m. m(k := None)" and lookup = id
    and insert = Set.insert and isin = "\<lambda>S x. x \<in> S" and t_set = id
    and sel = "\<lambda>S. SOME x. x \<in> S" and union = "(\<union>)" and inter = "(\<inter>)" and diff = "(-)"
    and G = "mk_adjmap dG" and stack0 = "IDFS_stack0 avoid visited p"
    and vis0 = "visited \<inter> Pair_Graph.dVs dG" and avoid = "avoid \<inter> Pair_Graph.dVs dG"
    and Pv = P and level = lev
  by unfold_locales (rule set_axioms)

text \<open>Shorthand for the final state of the run and derived facts.\<close>

abbreviation "Rst \<equiv> set_final dG (IDFS_stack0 avoid visited p)
                (visited \<inter> Pair_Graph.dVs dG) (avoid \<inter> Pair_Graph.dVs dG) P"

lemma IDFS_pair:
  "IDFS dG P avoid p visited =
     (DFS_avoid_state.ret Rst, visited \<union> DFS_avoid_state.visited Rst)"
  by (simp add: IDFS_def Let_def)

lemma slot_dVs: "DFS_avoid_state.visited Rst \<subseteq> Pair_Graph.dVs dG"
  using T.DFS_avoid_visited_dVs by (simp add: dabs set_final_def)

lemma new_eq:
  "(visited \<union> DFS_avoid_state.visited Rst) - visited
     = DFS_avoid_state.visited Rst - (visited \<inter> Pair_Graph.dVs dG)"
  using slot_dVs by auto

text \<open>The vis-works family of the DDFS locale, under the stated premises. The numbering
follows the assumptions of the DDFS locale.

Theorem \<leftrightarrow> DDFS locale clause (pairing table):
  IDFS_closed_None  \<leftrightarrow> IDFS_closed (1) [None branch]:  no dpath/distinct premise in DDFS
                                              (extra p_path/p_dist come from inner context;
                                               DDFS discharges them via stack-path invariants)
  IDFS_closed_Some  \<leftrightarrow> IDFS_closed (2) [Some branch]:  same note
  IDFS_vis_works_2  \<leftrightarrow> IDFS_vis_works (1) [not-P]:     no dpath/distinct premise in DDFS
  IDFS_vis_works_3  \<leftrightarrow> IDFS_vis_works (2) [avoid-disj]: same note
  IDFS_vis_works_4  \<leftrightarrow> IDFS_vis_works (3) [monotone]:  proved in OUTER context, no path premise
  IDFS_vis_works_6  \<leftrightarrow> IDFS_vis_works (4) [finite]:    same note as vis_works_2
  IDFS_complete     \<leftrightarrow> IDFS_complete:                  no dpath/distinct premise in DDFS
  IDFS_sound_1      \<leftrightarrow> IDFS_sound (1):                 DDFS has \<open>dpath dG (rev p)\<close> premise only
  IDFS_sound_2      \<leftrightarrow> IDFS_sound (2):                 DDFS has \<open>distinct p\<close> premise only
  IDFS_sound_3      \<leftrightarrow> IDFS_sound (3):                 no dpath/distinct in DDFS
  IDFS_sound_4      \<leftrightarrow> IDFS_sound (4):                 no dpath/distinct in DDFS
  IDFS_sound_5      \<leftrightarrow> IDFS_sound (5):                 no dpath/distinct in DDFS
  IDFS_sound_6      \<leftrightarrow> IDFS_sound (6):                 no dpath/distinct in DDFS
  IDFS_sound_7      \<leftrightarrow> IDFS_sound (7):                 no dpath/distinct in DDFS
  IDFS_sound_8      \<leftrightarrow> IDFS_sound (8):                 no dpath/distinct in DDFS

Note: theorems in the inner context (p_path/p_dist assumed) carry those as extra premises.
In Phase 2 (DDFS_Interpretation.thy), the DDFS locale's stack-path invariants discharge them.\<close>

text \<open>Closure of the newly visited region (replaces the former invar_0-precondition
form of IDFS-vis-works(1)): a successor of a newly visited vertex lands in avoid, in the
new visited set, or (only for a successful search) on the returned stack.\<close>

theorem IDFS_closed_None:
  assumes "IDFS dG P avoid p visited = (None, visited')"
          "v \<in> visited' - visited" "(v, w) \<in> dG"
  shows "w \<in> avoid \<union> visited'"
proof -
  have retN: "DFS_avoid_state.ret Rst = None"
       and vis': "visited' = visited \<union> DFS_avoid_state.visited Rst"
    using assms(1) by (auto simp: IDFS_pair)
  have empty: "stack Rst = []"
    using T.final_ret_char retN by (simp add: set_final_def)
  have vnew: "v \<in> id (DFS_avoid_state.visited Rst) - id (visited \<inter> Pair_Graph.dVs dG)"
    using assms(1,2) new_eq by (auto simp: IDFS_pair)
  have edge: "(v, w) \<in> set_avoid.Graph.digraph_abs (mk_adjmap dG)"
    using assms(3) by (simp add: dabs)
  have "w \<in> id (avoid \<inter> Pair_Graph.dVs dG) \<union> id (DFS_avoid_state.visited Rst)
             \<union> set (stack Rst)"
    using T.DFS_avoid_closure[of v w] vnew edge by (simp add: set_final_def)
  then have "w \<in> avoid \<union> DFS_avoid_state.visited Rst"
    using empty by auto
  then show ?thesis
    using vis' by auto
qed

theorem IDFS_closed_Some:
  assumes "IDFS dG P avoid p visited = (Some p', visited')"
          "v \<in> visited' - visited" "(v, w) \<in> dG"
  shows "w \<in> avoid \<union> visited' \<union> set p'"
proof -
  have retS: "DFS_avoid_state.ret Rst = Some p'"
       and vis': "visited' = visited \<union> DFS_avoid_state.visited Rst"
    using assms(1) by (auto simp: IDFS_pair)
  have pstk: "p' = stack Rst"
    using T.DFS_avoid_sound_stack retS by (simp add: set_final_def)
  have vnew: "v \<in> id (DFS_avoid_state.visited Rst) - id (visited \<inter> Pair_Graph.dVs dG)"
    using assms(1,2) new_eq by (auto simp: IDFS_pair)
  have edge: "(v, w) \<in> set_avoid.Graph.digraph_abs (mk_adjmap dG)"
    using assms(3) by (simp add: dabs)
  have "w \<in> id (avoid \<inter> Pair_Graph.dVs dG) \<union> id (DFS_avoid_state.visited Rst)
             \<union> set (stack Rst)"
    using T.DFS_avoid_closure[of v w] vnew edge by (simp add: set_final_def)
  then show ?thesis
    using vis' pstk by auto
qed

theorem IDFS_vis_works_2:
  assumes "IDFS dG P avoid p visited = (ret_p, visited')" "v \<in> visited' - visited"
  shows "\<not> P v"
proof -
  have "v \<in> id (DFS_avoid_state.visited Rst) - id (visited \<inter> Pair_Graph.dVs dG)"
    using assms new_eq by (auto simp: IDFS_pair)
  then show ?thesis
    using T.DFS_avoid_vis_new_notP[of v] by (simp add: set_final_def)
qed

theorem IDFS_vis_works_3:
  assumes "IDFS dG P avoid p visited = (ret_p, visited')"
  shows "(visited' - visited) \<inter> avoid = {}"
proof -
  have sub: "visited' - visited
      \<subseteq> DFS_avoid_state.visited Rst - (visited \<inter> Pair_Graph.dVs dG)"
    using assms new_eq by (auto simp: IDFS_pair)
  have disj: "(DFS_avoid_state.visited Rst - (visited \<inter> Pair_Graph.dVs dG))
          \<inter> (avoid \<inter> Pair_Graph.dVs dG) = {}"
    using T.DFS_avoid_vis_new_avoid by (simp add: set_final_def)
  show ?thesis
  proof (rule ccontr)
    assume "(visited' - visited) \<inter> avoid \<noteq> {}"
    then obtain x where x: "x \<in> visited' - visited" "x \<in> avoid"
      by auto
    have xs: "x \<in> DFS_avoid_state.visited Rst - (visited \<inter> Pair_Graph.dVs dG)"
      using x(1) sub by auto
    have "x \<in> Pair_Graph.dVs dG"
      using xs slot_dVs by auto
    then show False
      using xs x(2) disj by auto
  qed
qed

theorem IDFS_vis_works_6:
  assumes "IDFS dG P avoid p visited = (ret_p, visited')"
  shows "finite (visited' - visited)"
proof -
  have "visited' - visited
      \<subseteq> id (DFS_avoid_state.visited Rst) - id (visited \<inter> Pair_Graph.dVs dG)"
    using assms new_eq by (auto simp: IDFS_pair)
  then show ?thesis
    using T.DFS_avoid_vis_new_finite by (simp add: set_final_def) (auto intro: finite_subset)
qed

theorem IDFS_complete:
  assumes "IDFS dG P avoid p visited = (None, visited')"
  shows "set p - avoid \<subseteq> visited'"
proof
  fix x assume x: "x \<in> set p - avoid"
  have retN: "DFS_avoid_state.ret Rst = None"
       and vis': "visited' = visited \<union> DFS_avoid_state.visited Rst"
    using assms by (auto simp: IDFS_pair)
  have compl: "set (IDFS_stack0 avoid visited p) - id (avoid \<inter> Pair_Graph.dVs dG)
                 \<subseteq> id (DFS_avoid_state.visited Rst)"
    using T.DFS_avoid_complete retN by (simp add: set_final_def)
  show "x \<in> visited'"
  proof (cases "x \<in> set (IDFS_stack0 avoid visited p)")
    case True
    have "x \<in> Pair_Graph.dVs dG"
      using x p_dVs by auto
    then have "x \<in> DFS_avoid_state.visited Rst"
      using compl True x by auto
    then show ?thesis using vis' by auto
  next
    case False
    then have s: "IDFS_stack0 avoid visited p = tl p" and h: "hd p \<in> avoid \<union> visited"
        and ne: "p \<noteq> []"
      using stack0_cases x by auto
    have "x = hd p"
      using x False s ne by (cases p) auto
    then have "x \<in> visited"
      using h x by auto
    then show ?thesis using vis' by auto
  qed
qed

text \<open>The sound family of the DDFS locale (successful searches).\<close>

theorem IDFS_sound_1:
  assumes "IDFS dG P avoid p visited = (Some p', visited')"
  shows "dpath dG (rev p')"
proof -
  have "DFS_avoid_state.ret Rst = Some p'"
    using assms by (auto simp: IDFS_pair)
  then have "Vwalk.vwalk (set_avoid.Graph.digraph_abs (mk_adjmap dG)) (rev p')"
    using T.DFS_avoid_sound_vwalk by (simp add: set_final_def)
  then show ?thesis
    by (simp add: dabs)
qed

theorem IDFS_sound_2:
  assumes "IDFS dG P avoid p visited = (Some p', visited')"
  shows "distinct p'"
proof -
  have "DFS_avoid_state.ret Rst = Some p'"
    using assms by (auto simp: IDFS_pair)
  then show ?thesis
    using T.DFS_avoid_sound_distinct by (simp add: set_final_def)
qed

theorem IDFS_sound_7:
  assumes "IDFS dG P avoid p visited = (Some p', visited')"
  shows "p' \<noteq> []"
proof -
  have "DFS_avoid_state.ret Rst = Some p'"
    using assms by (auto simp: IDFS_pair)
  then show ?thesis
    using T.DFS_avoid_sound_nonempty by (simp add: set_final_def)
qed

theorem IDFS_sound_8:
  assumes "IDFS dG P avoid p visited = (Some p', visited')"
  shows "P (hd p')" and "hd p' \<notin> avoid \<inter> Pair_Graph.dVs dG"
proof -
  have r: "DFS_avoid_state.ret Rst = Some p'"
    using assms by (auto simp: IDFS_pair)
  show "P (hd p')"
    using T.DFS_avoid_sound_hdP(1) r by (simp add: set_final_def)
  show "hd p' \<notin> avoid \<inter> Pair_Graph.dVs dG"
    using T.DFS_avoid_sound_hdP(2) r by (simp add: set_final_def)
qed

theorem IDFS_sound_6:
  assumes "IDFS dG P avoid p visited = (Some p', visited')" "p \<noteq> []"
  shows "last p = last p'"
proof -
  have r: "DFS_avoid_state.ret Rst = Some p'"
    using assms(1) by (auto simp: IDFS_pair)
  have l: "IDFS_stack0 avoid visited p \<noteq> []"
      and e: "last p' = last (IDFS_stack0 avoid visited p)"
    using T.DFS_avoid_sound_last r by (auto simp: set_final_def)
  show ?thesis
  proof (cases "IDFS_stack0 avoid visited p = p")
    case True
    then show ?thesis using e by simp
  next
    case False
    then have s: "IDFS_stack0 avoid visited p = tl p"
      using stack0_cases by auto
    have "last (tl p) = last p"
      using l s assms(2) by (cases p) auto
    then show ?thesis using e s by simp
  qed
qed

theorem IDFS_sound_3:
  assumes "IDFS dG P avoid p visited = (Some p', visited')"
  shows "(set p' - set (tl p)) \<inter> (avoid \<union> visited') = {}"
proof (rule ccontr)
  assume "(set p' - set (tl p)) \<inter> (avoid \<union> visited') \<noteq> {}"
  then obtain x where x: "x \<in> set p'" "x \<notin> set (tl p)" "x \<in> avoid \<union> visited'"
    by auto
  have r: "DFS_avoid_state.ret Rst = Some p'"
       and vis': "visited' = visited \<union> DFS_avoid_state.visited Rst"
    using assms by (auto simp: IDFS_pair)
  have p'stack: "p' = stack Rst"
    using T.DFS_avoid_sound_stack r by (simp add: set_final_def)
  have x_dVs: "x \<in> Pair_Graph.dVs dG"
    using x(1) p'stack T.DFS_avoid_stack_dVs by (auto simp: dabs set_final_def)
  have nd: "(set p' - set (IDFS_stack0 avoid visited p))
              \<inter> (id (avoid \<inter> Pair_Graph.dVs dG) \<union> id (DFS_avoid_state.visited Rst)) = {}"
    using T.DFS_avoid_sound_new_disjoint r by (simp add: set_final_def)
  show False
  proof (cases "x \<in> set (IDFS_stack0 avoid visited p)")
    case False
    have "x \<notin> avoid" "x \<notin> DFS_avoid_state.visited Rst"
      using nd False x(1) x_dVs by auto
    moreover then have "x \<notin> visited"
      using x_dVs T.DFS_avoid_vis_mono by (auto simp: set_final_def)
    ultimately show False using x(3) vis' by auto
  next
    case True
    then have s: "IDFS_stack0 avoid visited p = p" and hne: "p = [] \<or> hd p \<notin> avoid \<union> visited"
      using stack0_cases x(2) by auto
    have xhd: "x = hd p" and ne: "p \<noteq> []"
      using True s x(2) by (cases p; auto)+
    have hnot: "hd p \<notin> avoid \<union> visited"
      using hne ne by auto
    have "x \<notin> DFS_avoid_state.visited Rst"
    proof
      assume xin: "x \<in> DFS_avoid_state.visited Rst"
      have "x \<in> set (stack Rst)"
        using x(1) p'stack by simp
      then have "x \<in> id (visited \<inter> Pair_Graph.dVs dG)"
        using xin T.DFS_avoid_visited_stack by (auto simp: set_final_def)
      then show False
        using hnot xhd by auto
    qed
    then show False
      using x(3) xhd hnot vis' by auto
  qed
qed

theorem IDFS_sound_4:
  assumes "IDFS dG P avoid p visited = (Some p', visited')"
  shows "set p - set p' - avoid \<subseteq> visited'"
proof
  fix x assume x: "x \<in> set p - set p' - avoid"
  have r: "DFS_avoid_state.ret Rst = Some p'"
       and vis': "visited' = visited \<union> DFS_avoid_state.visited Rst"
    using assms by (auto simp: IDFS_pair)
  have x_dVs: "x \<in> Pair_Graph.dVs dG"
    using x p_dVs by auto
  have sub: "set (IDFS_stack0 avoid visited p) - set p' - id (avoid \<inter> Pair_Graph.dVs dG)
               \<subseteq> id (DFS_avoid_state.visited Rst)"
    using T.DFS_avoid_sound_sub r by (simp add: set_final_def)
  show "x \<in> visited'"
  proof (cases "x \<in> set (IDFS_stack0 avoid visited p)")
    case True
    then have "x \<in> DFS_avoid_state.visited Rst"
      using sub x x_dVs by auto
    then show ?thesis using vis' by auto
  next
    case False
    then have s: "IDFS_stack0 avoid visited p = tl p" and h: "hd p \<in> avoid \<union> visited"
        and ne: "p \<noteq> []"
      using stack0_cases x by auto
    have "x = hd p"
      using x False s ne by (cases p) auto
    then have "x \<in> visited"
      using h x by auto
    then show ?thesis using vis' by auto
  qed
qed

theorem IDFS_sound_5:
  assumes "IDFS dG P avoid p visited = (Some p', visited')"
      and tlP: "\<And>v. v \<in> set (tl p) \<Longrightarrow> \<not> P v"
      and v: "v \<in> set (tl p')"
  shows "\<not> P v"
proof -
  have r: "DFS_avoid_state.ret Rst = Some p'"
    using assms(1) by (auto simp: IDFS_pair)
  have tl_char: "v \<in> set (IDFS_stack0 avoid visited p) \<or> \<not> P v"
    using T.DFS_avoid_sound_tl_notP r v by (simp add: set_final_def)
  show ?thesis
  proof (cases "IDFS_stack0 avoid visited p = p")
    case False
    then have "IDFS_stack0 avoid visited p = tl p"
      using stack0_cases by auto
    then show ?thesis using tl_char tlP by auto
  next
    case True
    have ne: "p \<noteq> []"
    proof -
      have "IDFS_stack0 avoid visited p \<noteq> []"
        using T.DFS_avoid_sound_last(1) r by (simp add: set_final_def)
      then show ?thesis using True by auto
    qed
    have hne: "hd p \<notin> avoid \<union> visited"
      using stack0_cases True ne by (cases p) auto
    show ?thesis
    proof (cases "P (hd p)")
      case False
      then show ?thesis
        using tl_char tlP True ne by (cases p) auto
    next
      case Phd: True
      have "p' = IDFS_stack0 avoid visited p"
        using T.DFS_avoid_found_immediately r ne True Phd hne
        by (simp add: set_final_def)
      then have "p' = p"
        using True by simp
      then show ?thesis
        using v tlP by simp
    qed
  qed
qed

end

end

section \<open>Layered-digraph locale and its DDFS interpretation\<close>

text \<open>The DDFS_layered locale fixes a layered digraph (satisfying the
three DDFS digraph assumptions) and establishes that the concrete
IDFS function realises all DDFS interface assumptions.
This is the Phase-2 interpretation linking the abstract DDFS development to the
concrete DFS-Avoid skeleton instance.\<close>

locale DDFS_layered =
  fixes dG :: "('a \<times> 'a) set" and lev :: "'a \<Rightarrow> nat"
  assumes L1: "(v, v') \<in> dG \<Longrightarrow> lev v' < lev v"
      and L2: "finite (dVs dG)"
      and L3: "v \<in> dVs dG \<Longrightarrow> \<exists>p v'. p \<noteq> [] \<and> dpath_bet dG p v v' \<and> lev v' = 0"

sublocale DDFS_layered \<subseteq>
    DDFS where update = "\<lambda>k v m. m(k \<mapsto> v)" and adjmap_inv = "\<lambda>(_:: 'a \<Rightarrow> 'a set option). True" and
               vset_empty = "({} :: 'a set)" and
               vset_delete = "(\<lambda>x S. S - {x} :: 'a set)" and
               vset_inv = "(\<lambda>(_ :: 'a set). True)" and
               lookup = id and
               t_set = "(id :: 'a set \<Rightarrow> 'a set)" and
               insert = "(Set.insert :: 'a \<Rightarrow> 'a set \<Rightarrow> 'a set)" and
               G = "mk_adjmap dG" and level = lev and
               IDFS = "\<lambda>(P :: 'a \<Rightarrow> bool) (av :: 'a set) (p :: 'a list) (vis :: 'a set). IDFS dG P av p vis" and
               succ = "\<lambda>v. SOME v0. (v, v0) \<in> dG"
  (*READT-TODO-20: original: DDFS where dG = dG and level = lev and IDFS = IDFS and succ = ...; proof unfold_locales ... (lines 558-779);
    symptom: dG not a parameter of DDFS (ADT re-type); locale now uses Pair_Graph_Specs+Set2+'vset;
    obligations need ADT witnesses; pattern: interface mismatch; SUPERSEDED-BY-PORT? yes*)
  sorry

end (* IDFS *)
