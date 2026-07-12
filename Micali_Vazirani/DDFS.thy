theory DDFS
  imports Directed_Set_Graphs.Vwalk
          Directed_Set_Graphs.Pair_Graph_Specs
          Data_Structures.Set2_Addons
begin

text \<open>Some auxiliary theory about lists\<close>

lemma last_P_in_list'':
    "(\<And>p u. P2 (u # p) \<Longrightarrow>  P u \<Longrightarrow>
               ((\<exists>p' p'' u'. p = p' @ u' # p'' \<and> P u') \<or> p = [] \<or> P' u)) \<Longrightarrow>
      (\<And>p u. p \<noteq> [] \<Longrightarrow> P2 (u # p) \<Longrightarrow> P2 p) \<Longrightarrow>
      P2 p \<Longrightarrow> u \<in> set p \<Longrightarrow> P u \<Longrightarrow> (\<exists>u'. u' \<in> set p \<and> P' u') \<or> P (last p)"
proof (induction p arbitrary: u)
  case Nil then show ?case by simp
next
  case (Cons a p)
  show ?case
  proof (cases "p = []")
    case True then show ?thesis using Cons.prems by simp
  next
    case pne: False
    have P2p: "P2 p" using Cons.prems(2)[of p a] Cons.prems(3) pne by blast
    consider (hd_case) "u = a" | (tl_case) "u \<in> set p" using Cons.prems(4) by auto
    then show ?thesis
    proof cases
      case hd_case
      from Cons.prems(1)[of a p] Cons.prems(5) hd_case Cons.prems(3)
      have disj: "(\<exists>p' p'' u'. p = p' @ u' # p'' \<and> P u') \<or> p = [] \<or> P' a" by blast
      then show ?thesis
      proof (elim disjE)
        assume "\<exists>p' p'' u'. p = p' @ u' # p'' \<and> P u'"
        then obtain q1 u2 q2 where d: "p = q1 @ u2 # q2" "P u2" by blast
        have u2insp: "u2 \<in> set p" using d(1) by simp
        have ih: "(\<exists>u'. u' \<in> set p \<and> P' u') \<or> P (last p)"
          using Cons.IH[of u2] Cons.prems(1,2) P2p pne u2insp d(2) by fastforce
        then show ?thesis using pne by (auto simp: last_ConsR)
      next
        assume "p = []" then show ?thesis using pne by simp
      next
        assume "P' a" then show ?thesis by (auto simp: last_ConsR pne)
      qed
    next
      case tl_case
      then have ih2: "(\<exists>u'. u' \<in> set p \<and> P' u') \<or> P (last p)"
        using Cons.IH[of u] Cons.prems(1,2,5) P2p pne by blast
      then show ?thesis using pne by (auto simp: last_ConsR)
    qed
  qed
qed

lemma list_has_a_P:
  assumes "P x" "x \<in> set (x' # xs)"
  shows "(P x' \<or> (\<exists>xs1 xs2. xs = xs1 @ x # xs2))"
proof (cases "P x'")
  case True then show ?thesis by blast
next
  case False
  then have "x \<noteq> x'" using assms(1) by auto
  then have xinxs: "x \<in> set xs" using assms(2) by auto
  then have "\<exists>xs1 xs2. xs = xs1 @ x # xs2" by (rule split_list)
  then obtain xs1 xs2 where "xs = xs1 @ x # xs2" by blast
  then show ?thesis by blast
qed

lemma list_has_a_P':
  assumes "P x" "x \<in> set xs" "xs \<noteq> []"
  shows "\<exists>xs1 xs2 x. xs = xs1 @ x # xs2 \<and> P x"
proof -
  from assms(2) have "\<exists>xs1 xs2. xs = xs1 @ x # xs2" by (rule split_list)
  then obtain xs1 xs2 where "xs = xs1 @ x # xs2" by blast
  then show ?thesis using assms(1) by blast
qed

lemma distinct_decomp: 
  "(\<And>xs' x xs''. xs = xs' @ x # xs'' \<Longrightarrow> \<forall>x'\<in> set xs''. x \<noteq> x') \<Longrightarrow> distinct xs"
  using not_distinct_decomp
  by force

text \<open>Theory about digraphs\<close>

abbreviation "dpath \<equiv> Vwalk.vwalk"

abbreviation "dpath_bet dG p v v' \<equiv> Vwalk.vwalk_bet dG v p v'"

lemma path_then_edge: "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> v \<noteq> v' \<Longrightarrow> (\<exists>v''. (v, v'') \<in> dG)"
  by (force simp: vwalk_bet_def neq_Nil_conv split: if_splits)

lemma path_then_in_Vs: "dpath dG p \<Longrightarrow> v \<in> set p \<Longrightarrow> v \<in> dVs dG"
  using vwalk_then_in_dVs .

lemma dpath_cons: "dpath dG (v1#v2#p) \<Longrightarrow> (v1,v2) \<in> dG"
  by simp

lemma hd_of_dpath_bet:
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> \<exists>p'. p = v # p'"
  by (auto simp: vwalk_bet_def neq_Nil_conv)

lemma hd_of_dpath_bet': 
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> v = hd p"
  by (auto simp: vwalk_bet_def)

lemma last_of_dpath_bet: 
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> v' = last p"
  by (auto simp: vwalk_bet_def)

lemma induct_pcpl:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. P zs \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_pcpl_2:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x,y]; \<And>x y z. P [x,y,z]; \<And>w x y z zs. P zs \<Longrightarrow> P (w # x # y # z # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma dVsI1:
assumes "(a, v) \<in> dG" shows "a \<in> dVs dG"
using Pair_Graph.dVsI(1)[OF assms] .

(*thm dpath.cases

lemma append_dpath_1: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p1"
apply (induction p1)
apply (auto intro: dpath.intros; fail)
apply simp
apply (drule dpath.cases)
apply (auto intro: dpath.intros simp: dVsI1 append_eq_Cons_conv)*)

lemma append_dpath_1: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p1"
  using append_vwalk_pref .

(*lemma append_dpath_1: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p1"
apply (induction p1)
apply (auto intro: dpath.intros; fail)
apply simp
apply (subst (asm) dpath.simps)
apply (auto intro: dpath.intros simp: append_eq_Cons_conv dVsI1)
done*)

lemma append_dpath_pref: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p1"
  using append_vwalk_pref .

lemma append_dpath_suff: "dpath dG (p1 @ p2) \<Longrightarrow> dpath dG p2"
  using append_vwalk_suff .

lemma append_dpath: "dpath dG p1 \<Longrightarrow> dpath dG p2 \<Longrightarrow> (last p1, hd p2) \<in> dG \<Longrightarrow> dpath dG (p1 @ p2)"
  using append_vwalk .

(*lemma append_dpath_suff: "v1 \<noteq> v2 \<Longrightarrow> dpath_bet dG p1 v1 v2 \<Longrightarrow> dpath_bet dG p2 v2 v3 \<Longrightarrow>
                          dpath_bet dG (p1 @ (tl p2)) v1 v3"
  apply(induction p1)
   apply (auto simp: split: if_splits)
  apply (case_tac p1)
    apply (auto simp: dVs_def split: if_splits)*)

lemma split_dpath:
  "dpath_bet dG (p1 @ v2 # p2) v1 v3 \<Longrightarrow> dpath_bet dG (v2 # p2) v2 v3"
  using split_vwalk .

lemma dpath_bet_cons:
  "dpath_bet dG (v # p) v u \<Longrightarrow> p \<noteq> [] \<Longrightarrow> dpath_bet dG p (hd p) u"
  using vwalk_bet_cons .

lemma dpath_bet_cons_2: 
  "dpath_bet dG p v v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> dpath_bet dG (v # tl p) v v'"
  using vwalk_bet_cons_2 .

lemma dpath_bet_snoc: 
  "dpath_bet dG (p @ [v]) v' v'' \<Longrightarrow> v = v''"
  using vwalk_bet_snoc .

lemma dpath_bet_dpath:
  "p \<noteq> [] \<Longrightarrow> dpath_bet dG p (hd p) (last p) \<longleftrightarrow> dpath dG p"
  by (auto simp: vwalk_bet_def vwalk_bet_vwalk)

lemma dpath_snoc_edge': "dpath dG (p @ [v]) \<Longrightarrow> (v, v') \<in> dG \<Longrightarrow> dpath dG ((p @ [v]) @ [v'])"
  using vwalk_snoc_edge' .

lemma dpath_snoc_edge: "dpath dG (p @ [v]) \<Longrightarrow> (v, v') \<in> dG \<Longrightarrow> dpath dG (p @ [v, v'])"
  using dpath_snoc_edge'
  by simp

lemma dpath_snoc_edge_2: "dpath dG (p @ [v, v']) \<Longrightarrow> (v, v') \<in> dG"
  using append_dpath_suff[where ?p2.0 = "[v, v']"]
  by auto

lemma dpath_append_edge: "dpath dG (p1 @ p2) \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> (last p1, hd p2) \<in> dG"
  by (induction p1) (auto simp: path_then_in_Vs neq_Nil_conv)

lemma dpath_transitive_rel:
  assumes "(\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z)" "(\<And>v1 v2. (v1, v2) \<in> dG \<Longrightarrow> R v1 v2)"
  shows "dpath dG (v#vs) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> R v v'"
proof(induction vs arbitrary: v v')
  case (Cons v'' vs)
  hence "R v v''"
    using assms(2)
    by simp
  thus ?case
  proof(cases "v' = v''")
    case False
    thus ?thesis
      apply(intro assms(1)[OF \<open>R v v''\<close>] Cons)
      using Cons.prems
      by auto
  qed simp
qed auto

lemma dpath_transitive_rel': 
  assumes "(\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z)" "(\<And>v1 v2. (v1, v2) \<in> dG \<Longrightarrow> R v1 v2)"
  shows "dpath dG (vs @ [v]) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> R v' v"
proof(induction vs arbitrary: v v' rule: rev_induct)
  case (snoc v'' vs)
  hence "R v'' v"
    by(auto intro: assms dpath_snoc_edge_2)    
  thus ?case
  proof(cases "v' = v''")
    case True
    then show ?thesis 
      by (simp add: \<open>R v'' v\<close>)
  next
    case False
    thus ?thesis
      using snoc(2,3)
      by(auto intro: assms(1)[OF _ \<open>R v'' v\<close>] snoc append_dpath_pref[where ?p1.0 = "vs @ [v'']"])
  qed
qed auto

text \<open>A locale and proof of validity for DDFS. It assumes the presence of an incremental DFS
      procedure IDFS.\<close>

definition "invar_0 dG P avoid visited \<equiv> (\<forall>v\<in>visited. \<forall>v'. (\<forall>p. p \<noteq> [] \<longrightarrow> dpath_bet dG (v # p) v v' \<longrightarrow> P v' \<longrightarrow> (set p \<inter> avoid \<noteq> {})))"

type_synonym 'a dpath = "'a list"

lemma invar_0_D:
  "invar_0 dG P avoid visited \<Longrightarrow> v \<in> visited \<Longrightarrow> p \<noteq> [] \<Longrightarrow>
   dpath_bet dG (v # p) v v' \<Longrightarrow> P v' \<Longrightarrow> set p \<inter> avoid \<noteq> {}"
  unfolding invar_0_def by blast

record ('v, 'vset) DDFS_state =
  curr1 :: 'v
  stack1 :: "'v list"
  vis1 :: 'vset
  curr2 :: 'v
  stack2 :: "'v list"
  done2 :: "'v list"
  vis2 :: 'vset

abbreviation "mk_st u1 p1 v1 u2 p2' p2 v2 \<equiv>
   \<lparr>curr1 = u1, stack1 = p1, vis1 = v1, curr2 = u2, stack2 = p2',
    done2 = p2, vis2 = v2\<rparr>"

lemmas mk_st_simps = DDFS_state.simps

locale DDFS =
  Graph: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes G :: "'adjmap" and
      level :: "'v \<Rightarrow> nat" and
      IDFS :: "('v \<Rightarrow> bool) \<Rightarrow> 'vset \<Rightarrow> 'v list \<Rightarrow> 'vset \<Rightarrow> ('v dpath option \<times> 'vset)" and
      succ :: "'v \<Rightarrow> 'v"
    assumes digraph: "(v,v') \<in> Graph.digraph_abs G \<Longrightarrow> level v' < level v"
                     "finite (dVs (Graph.digraph_abs G))"
                     "v \<in> dVs (Graph.digraph_abs G) \<Longrightarrow>
                      \<exists>p v'. p \<noteq> [] \<and> dpath_bet (Graph.digraph_abs G) p v v' \<and> level v' = 0"
                     "Graph.graph_inv G" "Graph.finite_graph G" and
      succ_works: "v \<in> dVs (Graph.digraph_abs G) \<Longrightarrow> level v \<noteq> 0 \<Longrightarrow>
                   (v, succ v) \<in> Graph.digraph_abs G" and
      (*Interface amendments (2026-07-03) -- see DDFS.tex, subsection "Amendments to
        the DFS interface", and the DFS derived from the generic skeleton in
        DFS_Avoid.thy / IDFS.thy which realises this interface.
        - the former fifth vis-works assumption ("every newly visited vertex equals
          last p") is DELETED (unsatisfiable jointly with IDFS_complete/sound(8)); the
          finiteness assumption is now IDFS_vis_works(4).
        - IDFS_sound(2) (distinctness) now has the premise "distinct p".
        - The former vis-works(1) (an invar_0-precondition form) is REPLACED by the
          CLOSURE assumptions IDFS_closed: a successor of a newly-visited vertex lands
          in avoid, in the new visited set, or (for a successful search) on the returned
          stack.  This is exactly what DFS_Avoid.thy/IDFS.thy prove
          (IDFS_closed_None / IDFS_closed_Some) and, unlike the invar_0-precondition
          form, it is maintainable by DDFS across the if1-branch recursion under the
          weak IDFS_sound(4).  The vis-works group is therefore 4 clauses now
          (\<not>P newly-visited; new-visited disjoint from avoid; visited monotone; finite);
          all citations are renumbered accordingly.
        - IDFS_sound(4) is weakened to the realisable form set p - set p' - avoid
          \<subseteq> visited' (a dropped avoid-head is recorded neither in visited' nor kept
          in p').*)
      IDFS_vis_works: "\<lbrakk>vset_inv avoid; vset_inv visited;
                         t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                         t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                         dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (ret_p, visited');
                         v \<in> t_set visited' - t_set visited\<rbrakk> \<Longrightarrow> \<not> P v"
                      "\<lbrakk>vset_inv avoid; vset_inv visited;
                        t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                        t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                        dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (ret_p, visited')\<rbrakk>
                       \<Longrightarrow> (t_set visited' - t_set visited) \<inter> t_set avoid = {}"
                      "\<lbrakk>vset_inv avoid; vset_inv visited;
                        t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                        t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                        dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (ret_p, visited')\<rbrakk>
                       \<Longrightarrow> t_set visited \<subseteq> t_set visited'"
                      "\<lbrakk>vset_inv avoid; vset_inv visited;
                        t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                        t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                        dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (ret_p, visited')\<rbrakk>
                       \<Longrightarrow> vset_inv visited'" and
      IDFS_closed: "\<lbrakk>vset_inv avoid; vset_inv visited;
                     t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                     t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                     dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (None, visited');
                     v \<in> t_set visited' - t_set visited; (v, w) \<in> Graph.digraph_abs G\<rbrakk>
                    \<Longrightarrow> w \<in> t_set avoid \<union> t_set visited'"
                   "\<lbrakk>vset_inv avoid; vset_inv visited;
                     t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                     t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                     dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (Some p', visited');
                     v \<in> t_set visited' - t_set visited; (v, w) \<in> Graph.digraph_abs G\<rbrakk>
                    \<Longrightarrow> w \<in> t_set avoid \<union> t_set visited' \<union> set p'" and
      IDFS_complete: "\<lbrakk>vset_inv avoid; vset_inv visited;
                      t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                      t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                      dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (None, visited')\<rbrakk>
                     \<Longrightarrow> set p - t_set avoid \<subseteq> t_set visited'" and
      IDFS_sound: "\<lbrakk>vset_inv avoid; vset_inv visited;
                    t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                    t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                    dpath (Graph.digraph_abs G) (rev p); IDFS P avoid p visited = (Some p', visited')\<rbrakk>
                   \<Longrightarrow> dpath (Graph.digraph_abs G) (rev p')"
                  "\<lbrakk>vset_inv avoid; vset_inv visited;
                    t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                    t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                    dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (Some p', visited')\<rbrakk>
                   \<Longrightarrow> distinct p'"
                  (*We have tl in the next assumption on idfs as the algorithm will always check
                    the head of the given list for not being in avoid or visited, and would
                    backtrack o/w*)
                  "\<lbrakk>vset_inv avoid; vset_inv visited;
                    t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                    t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                    dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (Some p', visited')\<rbrakk>
                   \<Longrightarrow> (set p' - set (tl p)) \<inter> (t_set avoid \<union> t_set visited') = {}"
                  "\<lbrakk>vset_inv avoid; vset_inv visited;
                    t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                    t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                    dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (Some p', visited')\<rbrakk>
                   \<Longrightarrow> set p - set p' - t_set avoid \<subseteq> t_set visited'"
                  "\<lbrakk>vset_inv avoid; vset_inv visited;
                    t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                    t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                    dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (Some p', visited');
                     (\<And> v. v \<in> set (tl p) \<Longrightarrow> \<not> P v); v \<in> set (tl p')\<rbrakk> \<Longrightarrow> \<not> P v"
                  "\<lbrakk>vset_inv avoid; vset_inv visited;
                    t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                    t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                    dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (Some p', visited');
                     p \<noteq> []\<rbrakk> \<Longrightarrow> last p = last p'"
                  "\<lbrakk>vset_inv avoid; vset_inv visited;
                    t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                    t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                    dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (Some p', visited')\<rbrakk>
                   \<Longrightarrow> p' \<noteq> []"
                  "\<lbrakk>vset_inv avoid; vset_inv visited;
                    t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                    t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                    dpath (Graph.digraph_abs G) (rev p); distinct p; IDFS P avoid p visited = (Some p', visited')\<rbrakk>
                   \<Longrightarrow> P (hd p')" and
      IDFS_dVs: "\<lbrakk>vset_inv avoid; vset_inv visited;
                  t_set avoid \<subseteq> dVs (Graph.digraph_abs G);
                  t_set visited \<subseteq> dVs (Graph.digraph_abs G);
                  dpath (Graph.digraph_abs G) (rev p);
                  distinct p; IDFS P avoid p visited = (ret_p, visited')\<rbrakk>
                 \<Longrightarrow> t_set visited' \<subseteq> dVs (Graph.digraph_abs G)"

begin

abbreviation "dG \<equiv> Graph.digraph_abs G"

definition "if1_cond u1 u2 \<longleftrightarrow> u1 = u2"

abbreviation (input) "level_leq \<equiv> (\<lambda>v' v. level v \<le> level v')"

definition "vset_of_list xs = foldr (\<lambda>x vs. insert x vs) xs vset_empty"
subsection \<open>P1.0 Abstraction lemma layer -- vset \<leftrightarrow> set boundary\<close>

context
includes set_ops.automation2
begin

private lemma vset_of_list_aux:
  "vset_inv (foldr (\<lambda>x vs. insert x vs) xs vset_empty) \<and>
   t_set (foldr (\<lambda>x vs. insert x vs) xs vset_empty) = set xs"
  by (induction xs) auto

lemma vset_of_list_inv [simp, intro]: "vset_inv (vset_of_list xs)"
  using vset_of_list_aux unfolding vset_of_list_def by blast

lemma vset_of_list_set [simp]: "t_set (vset_of_list xs) = set xs"
  using vset_of_list_aux unfolding vset_of_list_def by blast

text \<open>Union absorption: the two avoid-argument shapes used at the IDFS call sites.\<close>

lemma t_set_vset_union [simp]:
  "\<lbrakk>vset_inv A; vset_inv B\<rbrakk> \<Longrightarrow> t_set (A \<union>\<^sub>G B) = t_set A \<union> t_set B"
  by simp

lemma t_set_vset_of_list_union [simp]:
  "vset_inv V \<Longrightarrow> t_set (vset_of_list xs \<union>\<^sub>G V) = set xs \<union> t_set V"
  by simp

end

(*TODO the first call to IDFS should not avoid visited1! This was only neeed to prove invariant 13,
       which is not needed*)

function (domintros) DDFS :: "('v, 'vset) DDFS_state \<Rightarrow> ('v dpath \<times> 'v dpath)" where
  "DDFS st =
    (if curr1 st = curr2 st then
       (case IDFS (level_leq (curr2 st))
                  (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                  (curr2 st # stack2 st) (vis2 st) of
          (Some p, vis2') \<Rightarrow> DDFS (st\<lparr>curr2 := hd p, stack2 := tl p, vis2 := vis2'\<rparr>)
        | (None, vis2') \<Rightarrow>
            (case IDFS (level_leq (curr1 st))
                       (vset_of_list (curr2 st # stack2 st @ done2 st))
                       (curr1 st # stack1 st) (vis1 st) of
               (Some p, vis1') \<Rightarrow>
                 DDFS (st\<lparr>curr1 := hd p, stack1 := tl p, vis1 := vis1',
                          curr2 := curr2 st, stack2 := [],
                          done2 := stack2 st @ done2 st, vis2 := vis2'\<rparr>)
             | (None, vis1') \<Rightarrow>
                 (curr1 st # stack1 st, curr2 st # stack2 st @ done2 st)))
     else if level (curr1 st) = 0 \<and> level (curr2 st) = 0 then
       (curr1 st # stack1 st, curr2 st # stack2 st @ done2 st)
     else if level (curr2 st) \<le> level (curr1 st) then
       DDFS (st\<lparr>curr1 := succ (curr1 st), stack1 := curr1 st # stack1 st\<rparr>)
     else
       DDFS (st\<lparr>curr2 := succ (curr2 st), stack2 := curr2 st # stack2 st\<rparr>))"
  by pat_completeness auto

abbreviation "DDFS_run u1 p1 v1 u2 p2' p2 v2 \<equiv> DDFS (mk_st u1 p1 v1 u2 p2' p2 v2)"

subsection \<open>Skeleton-exact boilerplate (structure of DFS_Skeleton.thy)\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros

text \<open>The state is a DDFS_state record (curr1/stack1/vis1/curr2/stack2/done2/vis2). Per execution
path: a condition predicate, an update function, elim/intro rules; then DDFS_simps with
one equation per path, DDFS_cases, DDFS_induct and DDFS_domintros phrased through them --
exactly as DFS_skel_call_1_conds/DFS_skel_upd1/\<dots> in DFS_Skeleton.thy.\<close>

definition "DDFS_call_1_conds st =
    (curr1 st = curr2 st \<and>
     (\<exists>p vis'. IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                    (curr2 st # stack2 st) (vis2 st) = (Some p, vis')))"

definition "DDFS_upd1 st =
    (let (pr, vis2') = IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                            (curr2 st # stack2 st) (vis2 st);
         p = the pr
     in st\<lparr>curr2 := hd p, stack2 := tl p, vis2 := vis2'\<rparr>)"

definition "DDFS_call_2_conds st =
    (curr1 st = curr2 st \<and>
     (\<exists>vis2'. IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                   (curr2 st # stack2 st) (vis2 st) = (None, vis2')) \<and>
     (\<exists>p vis1'. IDFS (level_leq (curr1 st)) (vset_of_list (curr2 st # stack2 st @ done2 st))
                     (curr1 st # stack1 st) (vis1 st) = (Some p, vis1')))"

definition "DDFS_upd2 st =
    (let (_, vis2') = IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                           (curr2 st # stack2 st) (vis2 st);
         (pr, vis1') = IDFS (level_leq (curr1 st)) (vset_of_list (curr2 st # stack2 st @ done2 st))
                            (curr1 st # stack1 st) (vis1 st);
         p = the pr
     in st\<lparr>curr1 := hd p, stack1 := tl p, vis1 := vis1',
           stack2 := [], done2 := stack2 st @ done2 st, vis2 := vis2'\<rparr>)"

definition "DDFS_call_3_conds st =
    (curr1 st \<noteq> curr2 st \<and> \<not> (level (curr1 st) = 0 \<and> level (curr2 st) = 0) \<and>
     level (curr2 st) \<le> level (curr1 st))"

definition "DDFS_upd3 st = st\<lparr>curr1 := succ (curr1 st), stack1 := curr1 st # stack1 st\<rparr>"

definition "DDFS_call_4_conds st =
    (curr1 st \<noteq> curr2 st \<and> \<not> (level (curr1 st) = 0 \<and> level (curr2 st) = 0) \<and>
     \<not> level (curr2 st) \<le> level (curr1 st))"

definition "DDFS_upd4 st = st\<lparr>curr2 := succ (curr2 st), stack2 := curr2 st # stack2 st\<rparr>"

definition "DDFS_ret_1_conds st =
    (curr1 st = curr2 st \<and>
     (\<exists>vis2'. IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                   (curr2 st # stack2 st) (vis2 st) = (None, vis2')) \<and>
     (\<exists>vis1'. IDFS (level_leq (curr1 st)) (vset_of_list (curr2 st # stack2 st @ done2 st))
                   (curr1 st # stack1 st) (vis1 st) = (None, vis1')))"

definition "DDFS_ret1 st = (curr1 st # stack1 st, curr2 st # stack2 st @ done2 st)"

definition "DDFS_ret_2_conds st =
    (curr1 st \<noteq> curr2 st \<and> level (curr1 st) = 0 \<and> level (curr2 st) = 0)"

definition "DDFS_ret2 st = (curr1 st # stack1 st, curr2 st # stack2 st @ done2 st)"

lemma DDFS_call_1_conds[call_cond_elims]:
  "DDFS_call_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>curr1 st = curr2 st;
     \<exists>p vis'. IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                   (curr2 st # stack2 st) (vis2 st) = (Some p, vis')\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: DDFS_call_1_conds_def)

lemma DDFS_call_1_condsI[call_cond_intros]:
  "\<lbrakk>curr1 st = curr2 st;
    IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
         (curr2 st # stack2 st) (vis2 st) = (Some p, vis')\<rbrakk>
   \<Longrightarrow> DDFS_call_1_conds st"
  by (auto simp: DDFS_call_1_conds_def)

lemma DDFS_call_2_conds[call_cond_elims]:
  "DDFS_call_2_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>curr1 st = curr2 st;
     \<exists>vis2'. IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                  (curr2 st # stack2 st) (vis2 st) = (None, vis2');
     \<exists>p vis1'. IDFS (level_leq (curr1 st)) (vset_of_list (curr2 st # stack2 st @ done2 st))
                    (curr1 st # stack1 st) (vis1 st) = (Some p, vis1')\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: DDFS_call_2_conds_def)

lemma DDFS_call_3_conds[call_cond_elims]:
  "DDFS_call_3_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>curr1 st \<noteq> curr2 st; \<not> (level (curr1 st) = 0 \<and> level (curr2 st) = 0);
     level (curr2 st) \<le> level (curr1 st)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: DDFS_call_3_conds_def)

lemma DDFS_call_3_condsI[call_cond_intros]:
  "\<lbrakk>curr1 st \<noteq> curr2 st; \<not> (level (curr1 st) = 0 \<and> level (curr2 st) = 0);
    level (curr2 st) \<le> level (curr1 st)\<rbrakk> \<Longrightarrow> DDFS_call_3_conds st"
  by (auto simp: DDFS_call_3_conds_def)

lemma DDFS_call_4_conds[call_cond_elims]:
  "DDFS_call_4_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>curr1 st \<noteq> curr2 st; \<not> (level (curr1 st) = 0 \<and> level (curr2 st) = 0);
     \<not> level (curr2 st) \<le> level (curr1 st)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: DDFS_call_4_conds_def)

lemma DDFS_call_4_condsI[call_cond_intros]:
  "\<lbrakk>curr1 st \<noteq> curr2 st; \<not> (level (curr1 st) = 0 \<and> level (curr2 st) = 0);
    \<not> level (curr2 st) \<le> level (curr1 st)\<rbrakk> \<Longrightarrow> DDFS_call_4_conds st"
  by (auto simp: DDFS_call_4_conds_def)

lemma DDFS_ret_1_conds[call_cond_elims]:
  "DDFS_ret_1_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>curr1 st = curr2 st;
     \<exists>vis2'. IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                  (curr2 st # stack2 st) (vis2 st) = (None, vis2');
     \<exists>vis1'. IDFS (level_leq (curr1 st)) (vset_of_list (curr2 st # stack2 st @ done2 st))
                  (curr1 st # stack1 st) (vis1 st) = (None, vis1')\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: DDFS_ret_1_conds_def)

lemma DDFS_ret_2_conds[call_cond_elims]:
  "DDFS_ret_2_conds st \<Longrightarrow>
   \<lbrakk>\<lbrakk>curr1 st \<noteq> curr2 st; level (curr1 st) = 0; level (curr2 st) = 0\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: DDFS_ret_2_conds_def)

lemma DDFS_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>curr1 st \<noteq> curr2 st; level (curr1 st) = 0; level (curr2 st) = 0\<rbrakk>
   \<Longrightarrow> DDFS_ret_2_conds st"
  by (auto simp: DDFS_ret_2_conds_def)

lemma DDFS_cases:
  assumes "DDFS_call_1_conds st \<Longrightarrow> P" "DDFS_call_2_conds st \<Longrightarrow> P"
          "DDFS_call_3_conds st \<Longrightarrow> P" "DDFS_call_4_conds st \<Longrightarrow> P"
          "DDFS_ret_1_conds st \<Longrightarrow> P" "DDFS_ret_2_conds st \<Longrightarrow> P"
  shows "P"
proof -
  have "DDFS_call_1_conds st \<or> DDFS_call_2_conds st \<or> DDFS_call_3_conds st \<or>
        DDFS_call_4_conds st \<or> DDFS_ret_1_conds st \<or> DDFS_ret_2_conds st"
    by (cases "IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                    (curr2 st # stack2 st) (vis2 st)",
        cases "IDFS (level_leq (curr1 st)) (vset_of_list (curr2 st # stack2 st @ done2 st))
                    (curr1 st # stack1 st) (vis1 st)")
       (auto simp: DDFS_call_1_conds_def DDFS_call_2_conds_def DDFS_call_3_conds_def
                   DDFS_call_4_conds_def DDFS_ret_1_conds_def DDFS_ret_2_conds_def
             split: option.split_asm)
  then show ?thesis using assms by auto
qed

lemma DDFS_simps:
  assumes dom: "DDFS_dom st"
  shows "DDFS_call_1_conds st \<Longrightarrow> DDFS st = DDFS (DDFS_upd1 st)"
        "DDFS_call_2_conds st \<Longrightarrow> DDFS st = DDFS (DDFS_upd2 st)"
        "DDFS_call_3_conds st \<Longrightarrow> DDFS st = DDFS (DDFS_upd3 st)"
        "DDFS_call_4_conds st \<Longrightarrow> DDFS st = DDFS (DDFS_upd4 st)"
        "DDFS_ret_1_conds st \<Longrightarrow> DDFS st = DDFS_ret1 st"
        "DDFS_ret_2_conds st \<Longrightarrow> DDFS st = DDFS_ret2 st"
  using DDFS.psimps[OF dom]
  by (auto simp: DDFS_call_1_conds_def DDFS_upd1_def DDFS_call_2_conds_def DDFS_upd2_def
                 DDFS_call_3_conds_def DDFS_upd3_def DDFS_call_4_conds_def DDFS_upd4_def
                 DDFS_ret_1_conds_def DDFS_ret1_def DDFS_ret_2_conds_def DDFS_ret2_def
                 Let_def
          split: option.splits prod.splits if_splits)+

lemma DDFS_induct_paths:
  assumes "DDFS_dom st"
  assumes "\<And>st. \<lbrakk>DDFS_dom st;
                 DDFS_call_1_conds st \<Longrightarrow> P (DDFS_upd1 st);
                 DDFS_call_2_conds st \<Longrightarrow> P (DDFS_upd2 st);
                 DDFS_call_3_conds st \<Longrightarrow> P (DDFS_upd3 st);
                 DDFS_call_4_conds st \<Longrightarrow> P (DDFS_upd4 st)\<rbrakk> \<Longrightarrow> P st"
  shows "P st"
  apply(rule DDFS.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DDFS_call_1_conds_def DDFS_upd1_def DDFS_call_2_conds_def
                                 DDFS_upd2_def DDFS_call_3_conds_def DDFS_upd3_def
                                 DDFS_call_4_conds_def DDFS_upd4_def])
  by (auto simp: Let_def split: option.splits prod.splits if_splits)

lemma DDFS_domintros_paths:
  assumes "DDFS_call_1_conds st \<Longrightarrow> DDFS_dom (DDFS_upd1 st)"
          "DDFS_call_2_conds st \<Longrightarrow> DDFS_dom (DDFS_upd2 st)"
          "DDFS_call_3_conds st \<Longrightarrow> DDFS_dom (DDFS_upd3 st)"
          "DDFS_call_4_conds st \<Longrightarrow> DDFS_dom (DDFS_upd4 st)"
  shows "DDFS_dom st"
proof (rule DDFS.domintros, goal_cases)
  case (1 ya yaa x2)
  note case1 = this
  have c2: "DDFS_call_2_conds st"
    unfolding DDFS_call_2_conds_def
    using case1
    by (auto simp: eq_commute intro!: exI)
  then have dom: "DDFS_dom (DDFS_upd2 st)"
    by (rule assms(2))
  then show ?case
    unfolding DDFS_upd2_def
    using case1 c2
    by (auto simp: Let_def eq_commute DDFS_call_2_conds_def split: prod.splits option.splits)
next
  case (2 ya x2)
  note case2 = this
  have c1: "DDFS_call_1_conds st"
    unfolding DDFS_call_1_conds_def
    using case2
    by (auto simp: eq_commute intro!: exI)
  then have dom: "DDFS_dom (DDFS_upd1 st)"
    by (rule assms(1))
  then show ?case
    unfolding DDFS_upd1_def
    using case2 c1
    by (auto simp: Let_def eq_commute DDFS_call_1_conds_def split: prod.splits option.splits)
next
  case 3
  then show ?case
    using assms(3)[simplified DDFS_call_3_conds_def DDFS_upd3_def]
    by (auto simp: Let_def split: option.splits prod.splits)
next
  case 4
  then show ?case
    using assms(3)[simplified DDFS_call_3_conds_def DDFS_upd3_def]
    by (auto simp: Let_def split: option.splits prod.splits)
next
  case 5
  then show ?case
    using assms(4)[simplified DDFS_call_4_conds_def DDFS_upd4_def]
    by (auto simp: Let_def split: option.splits prod.splits)
qed

subsection \<open>Axioms as a definition (skeleton pattern)\<close>

definition "DDFS_axioms_def' =
  (Graph.graph_inv G \<and> Graph.finite_graph G \<and>
   (\<forall>v v'. (v, v') \<in> Graph.digraph_abs G \<longrightarrow> level v' < level v) \<and>
   finite (dVs (Graph.digraph_abs G)) \<and>
   (\<forall>v \<in> dVs (Graph.digraph_abs G). \<exists>p v'. p \<noteq> [] \<and>
      dpath_bet (Graph.digraph_abs G) p v v' \<and> level v' = 0) \<and>
   (\<forall>v. v \<in> dVs (Graph.digraph_abs G) \<longrightarrow> level v \<noteq> 0 \<longrightarrow> (v, succ v) \<in> Graph.digraph_abs G))"


partial_function (tailrec) DDFS_impl :: "('v, 'vset) DDFS_state \<Rightarrow> ('v dpath \<times> 'v dpath)" where
  "DDFS_impl st =
    (if curr1 st = curr2 st then
       (case IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
                  (curr2 st # stack2 st) (vis2 st) of
          (Some p, vis2') \<Rightarrow> DDFS_impl (st\<lparr>curr2 := hd p, stack2 := tl p, vis2 := vis2'\<rparr>)
        | (None, vis2') \<Rightarrow>
            (case IDFS (level_leq (curr1 st))
                       (vset_of_list (curr2 st # stack2 st @ done2 st))
                       (curr1 st # stack1 st) (vis1 st) of
               (Some p, vis1') \<Rightarrow>
                 DDFS_impl (st\<lparr>curr1 := hd p, stack1 := tl p, vis1 := vis1',
                               curr2 := curr2 st, stack2 := [],
                               done2 := stack2 st @ done2 st, vis2 := vis2'\<rparr>)
             | (None, vis1') \<Rightarrow>
                 (curr1 st # stack1 st, curr2 st # stack2 st @ done2 st)))
     else if level (curr1 st) = 0 \<and> level (curr2 st) = 0 then
       (curr1 st # stack1 st, curr2 st # stack2 st @ done2 st)
     else if level (curr2 st) \<le> level (curr1 st) then
       DDFS_impl (st\<lparr>curr1 := succ (curr1 st), stack1 := curr1 st # stack1 st\<rparr>)
     else
       DDFS_impl (st\<lparr>curr2 := succ (curr2 st), stack2 := curr2 st # stack2 st\<rparr>))"

lemma DDFS_impl_same:
  assumes "DDFS_dom st"
  shows "DDFS_impl st = DDFS st"
  by (induction rule: DDFS.pinduct[OF assms])
     (subst DDFS.psimps, simp,
      subst DDFS_impl.simps,
      auto split: prod.split option.split if_split simp add: Let_def)

definition "DFS_call_1_none u1 p1 visited1 u2 p2' visited2 visited2_new =
            ((None, visited2_new) = IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2)"

abbreviation "u2' \<equiv> (\<lambda>u2 p2'. last (u2 # p2'))"

lemma DFS_call_1_none_props:
  "DFS_call_1_none u1 p1 visited1 u2 p2' visited2 visited2_new \<Longrightarrow> 
     IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2 = (None, visited2_new)"
  by(auto simp: DFS_call_1_none_def)

definition "DFS_call_1_some u1 p1 visited1 u2 p2' visited2 p visited2_new =
            ((Some p, visited2_new) = IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2)"

lemma DFS_call_1_some_props:
  "DFS_call_1_some u1 p1 visited1 u2 p2' visited2 p visited2_new \<Longrightarrow>
     (IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2 = (Some p, visited2_new))"
  by(auto simp: DFS_call_1_some_def)

definition "DFS_call_2_none u1 p1 u2 p2_new visited1 visited1_new \<equiv>
            ((None, visited1_new) = IDFS (level_leq u1) (vset_of_list (u2 # p2_new)) (u1 # p1) visited1)"

lemma DFS_call_2_none_props:
  "DFS_call_2_none u1 p1 u2 p2_new visited1 visited1_new \<Longrightarrow> 
            (IDFS (level_leq u1) (vset_of_list (u2 # p2_new)) (u1 # p1) visited1 = (None, visited1_new))"
  by(auto simp: DFS_call_2_none_def)

definition "DFS_call_2_some u1 p1 u2 p2_new visited1 p visited1_new \<equiv>
            ((Some p, visited1_new) = IDFS (level_leq u1) (vset_of_list (u2 # p2_new)) (u1 # p1) visited1)"

lemma DFS_call_2_some_props: 
  "DFS_call_2_some u1 p1 u2 p2_new visited1 p visited1_new \<Longrightarrow>
            (IDFS (level_leq u1) (vset_of_list (u2 # p2_new)) (u1 # p1) visited1 = (Some p, visited1_new))"
  by(auto simp: DFS_call_2_some_def)

definition "DDFS_rec_call_2_cond u1 p1 visited1 u2 p2 p2' visited2 p2'_new p2_new visited2_new
            = (u1 = u2 \<and> DFS_call_1_none u1 p1 visited1 u2 p2' visited2 visited2_new)"

definition "DDFS_rec_call_2_asses u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p
            = (p2_new = p2' @ p2 \<and> p2'_new = [] \<and> 
               DFS_call_2_some u1 p1 u2 p2_new visited1 p visited1_new \<and>
               u1_new = hd p  \<and> p1_new = tl p)"

definition "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p
            = (u1 = u2 \<and> DFS_call_1_none u1 p1 visited1 u2 p2' visited2 visited2_new \<and>
               p2_new = p2' @ p2 \<and> p2'_new = [] \<and> 
               DFS_call_2_some u1 p1 u2 p2_new visited1 p visited1_new \<and>
               u1_new = hd p  \<and> p1_new = tl p)"

lemma DDFS_rec_call_2_props: 
  assumes "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
  shows "u1 = u2" "DFS_call_1_none u1 p1 visited1 u2 p2' visited2 visited2_new"
        "p2_new = p2' @ p2" "p2'_new = []"
        "DFS_call_2_some u1 p1 u2 p2_new visited1 p visited1_new"
        "u1_new = hd p" "p1_new = tl p"
  using assms
  by (auto simp: DDFS_rec_call_2_def)

definition "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p =
        (u1 = u2 \<and> DFS_call_1_some u1 p1 visited1 u2 p2' visited2 p visited2_new \<and>
        u2_new = hd p \<and> p2'_new = tl p)"

lemma DDFS_rec_call_1_props:
  assumes "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
  shows "u1 = u2" "DFS_call_1_some u1 p1 visited1 u2 p2' visited2 p visited2_new"
         "u2_new = hd p" "p2'_new = tl p"
  using assms
  by(auto simp: DDFS_rec_call_1_def)

definition "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new \<equiv>
        (u1 \<noteq> u2 \<and>
        \<not> (level u1 = 0 \<and> level u2 = 0) \<and>
          level u2 \<le> level u1 \<and> u1_new = succ u1 \<and>
          p1_new = u1 # p1)"

lemma DDFS_rec_call_3_props:
  assumes "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new"
  shows "u1 \<noteq> u2"
        "\<not> (level u1 = 0 \<and> level u2 = 0)"
        "level u2 \<le> level u1"
        "u1_new = succ u1"
        "p1_new = u1 # p1"
  using assms
  by(auto simp: DDFS_rec_call_3_def)

definition "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new \<equiv>
           (u1 \<noteq> u2 \<and>
          \<not> (level u1 = 0 \<and> level u2 = 0) \<and>
          level u1 < level u2 \<and> u2_new = succ u2 \<and>
            p2'_new = u2 # p2')"

lemma DDFS_rec_call_4_props:
assumes "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new"
shows "u1 \<noteq> u2"
      "\<not> (level u1 = 0 \<and> level u2 = 0)"
      "level u1 < level u2" "u2_new = succ u2"
      "p2'_new = u2 # p2'"
  using assms
  by (auto simp: DDFS_rec_call_4_def)

lemma DDFS_induct:
"DDFS_dom st \<Longrightarrow>
(\<And>st.
    DDFS_dom st \<Longrightarrow>
    (\<And>u2_new p2'_new visited2_new p.
        DDFS_rec_call_1 (curr1 st) (stack1 st) (vis1 st) (curr2 st) (stack2 st) (vis2 st)
                         u2_new p2'_new visited2_new p \<Longrightarrow>
        P (st\<lparr>curr2 := u2_new, stack2 := p2'_new, vis2 := visited2_new\<rparr>)) \<Longrightarrow>
    (\<And>u1_new p1_new visited1_new p2'_new p2_new visited2_new p.
       DDFS_rec_call_2 (curr1 st) (stack1 st) (vis1 st) (curr2 st) (done2 st) (stack2 st) (vis2 st)
                        u1_new p1_new visited1_new p2'_new p2_new visited2_new p
       \<Longrightarrow> P (st\<lparr>curr1 := u1_new, stack1 := p1_new, vis1 := visited1_new,
               stack2 := p2'_new, done2 := p2_new, vis2 := visited2_new\<rparr>)) \<Longrightarrow>
    (\<And>u1_new p1_new. DDFS_rec_call_3 (curr1 st) (stack1 st) (curr2 st) u1_new p1_new
                      \<Longrightarrow> P (st\<lparr>curr1 := u1_new, stack1 := p1_new\<rparr>)) \<Longrightarrow>
    (\<And>u2_new p2'_new. DDFS_rec_call_4 (curr1 st) (curr2 st) (stack2 st) u2_new p2'_new
                       \<Longrightarrow> P (st\<lparr>curr2 := u2_new, stack2 := p2'_new\<rparr>)) \<Longrightarrow>
    P st) \<Longrightarrow>
P st"
  apply(rule DDFS.pinduct; goal_cases)
  by (auto simp add: DDFS_rec_call_1_def DDFS_rec_call_2_def DDFS_rec_call_3_def DDFS_rec_call_4_def
                     DFS_call_1_none_def DFS_call_1_some_def DFS_call_2_some_def)

definition "DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new p2_new p2'_new visited2_new \<equiv>
        (u1 = u2 \<and> p2_new = p2' @ p2 \<and> p2'_new = [] \<and> 
         DFS_call_1_none u1 p1 visited1 u2 p2' visited2 visited2_new \<and>
         DFS_call_2_none u1 p1 u2 p2_new visited1 visited1_new)"

lemma DDFS_ret_1_props:
  assumes "DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new p2_new p2'_new visited2_new"
  shows "u1 = u2" "p2_new = p2' @ p2" "p2'_new = []"
      "DFS_call_1_none u1 p1 visited1 u2 p2' visited2 visited2_new"
      "DFS_call_2_none u1 p1 u2 p2_new visited1 visited1_new"
  using assms
  unfolding DDFS_ret_1_def
  by auto

definition "DDFS_ret_2 u1 u2 \<equiv>
        (u1 \<noteq> u2 \<and> level u1 = 0 \<and> level u2 = 0)"

lemma DDFS_ret_2_props:
  assumes "DDFS_ret_2 u1 u2"
  shows "u1 \<noteq> u2" "level u1 = 0" "level u2 = 0"
  using assms
  unfolding DDFS_ret_2_def
  by auto

subsection \<open>Bridges: skeleton-shape execution-path predicates to the relational layer\<close>

text \<open>Bridges for the state-typed (record) form. The state parameter is `st`.
For backward compatibility in the holds_upd lemmas, the old bridge lemmas also
remain (with `_compat` suffix) using `mk_st` to inject 7 args into the state.\<close>

(* State-typed bridge lemmas: take st :: DDFS_state, use DDFS_upd1 st etc. *)

lemma DDFS_call_1_bridge:
  assumes "DDFS_call_1_conds st"
  obtains p where
    "DDFS_rec_call_1 (curr1 st) (stack1 st) (vis1 st) (curr2 st) (stack2 st) (vis2 st)
                     (curr2 (DDFS_upd1 st)) (stack2 (DDFS_upd1 st)) (vis2 (DDFS_upd1 st)) p"
    "curr1 (DDFS_upd1 st) = curr1 st" "stack1 (DDFS_upd1 st) = stack1 st"
    "vis1 (DDFS_upd1 st) = vis1 st" "done2 (DDFS_upd1 st) = done2 st"
proof -
  from assms obtain p vis' where u1u2: "curr1 st = curr2 st" and
    idfs: "IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
           (curr2 st # stack2 st) (vis2 st) = (Some p, vis')"
    by (auto simp: DDFS_call_1_conds_def)
  have eqs: "curr1 (DDFS_upd1 st) = curr1 st" "stack1 (DDFS_upd1 st) = stack1 st"
            "vis1 (DDFS_upd1 st) = vis1 st" "done2 (DDFS_upd1 st) = done2 st"
            "curr2 (DDFS_upd1 st) = hd p" "stack2 (DDFS_upd1 st) = tl p"
            "vis2 (DDFS_upd1 st) = vis'"
    by (auto simp: DDFS_upd1_def Let_def idfs split: prod.splits)
  have "DDFS_rec_call_1 (curr1 st) (stack1 st) (vis1 st) (curr2 st) (stack2 st) (vis2 st)
                         (curr2 (DDFS_upd1 st)) (stack2 (DDFS_upd1 st)) (vis2 (DDFS_upd1 st)) p"
    using u1u2 idfs by (auto simp: DDFS_rec_call_1_def DFS_call_1_some_def eqs)
  then show ?thesis using eqs by (auto intro!: that[of p])
qed

lemma DDFS_call_2_bridge:
  assumes "DDFS_call_2_conds st"
  obtains p where
    "DDFS_rec_call_2 (curr1 st) (stack1 st) (vis1 st) (curr2 st) (done2 st) (stack2 st)
                     (vis2 st) (curr1 (DDFS_upd2 st)) (stack1 (DDFS_upd2 st))
                     (vis1 (DDFS_upd2 st)) (stack2 (DDFS_upd2 st)) (done2 (DDFS_upd2 st))
                     (vis2 (DDFS_upd2 st)) p"
    "curr2 (DDFS_upd2 st) = curr2 st"
proof -
  from assms obtain vis2' p vis1' where u1u2: "curr1 st = curr2 st" and
    idfs2: "IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
            (curr2 st # stack2 st) (vis2 st) = (None, vis2')" and
    idfs1: "IDFS (level_leq (curr1 st)) (vset_of_list (curr2 st # stack2 st @ done2 st))
            (curr1 st # stack1 st) (vis1 st) = (Some p, vis1')"
    by (auto simp: DDFS_call_2_conds_def)
  have eqs: "curr1 (DDFS_upd2 st) = hd p" "stack1 (DDFS_upd2 st) = tl p"
            "vis1 (DDFS_upd2 st) = vis1'" "curr2 (DDFS_upd2 st) = curr2 st"
            "stack2 (DDFS_upd2 st) = []" "done2 (DDFS_upd2 st) = stack2 st @ done2 st"
            "vis2 (DDFS_upd2 st) = vis2'"
    by (auto simp: DDFS_upd2_def Let_def idfs1 idfs2 split: prod.splits)
  have "DDFS_rec_call_2 (curr1 st) (stack1 st) (vis1 st) (curr2 st) (done2 st) (stack2 st)
                         (vis2 st) (curr1 (DDFS_upd2 st)) (stack1 (DDFS_upd2 st))
                         (vis1 (DDFS_upd2 st)) (stack2 (DDFS_upd2 st)) (done2 (DDFS_upd2 st))
                         (vis2 (DDFS_upd2 st)) p"
    using u1u2 idfs2 idfs1
    by (auto simp: DDFS_rec_call_2_def DFS_call_1_none_def DFS_call_2_some_def eqs)
  then show ?thesis using eqs by (auto intro!: that[of p])
qed

lemma DDFS_call_3_bridge:
  assumes "DDFS_call_3_conds st"
  shows "DDFS_rec_call_3 (curr1 st) (stack1 st) (curr2 st)
                         (curr1 (DDFS_upd3 st)) (stack1 (DDFS_upd3 st))"
        "vis1 (DDFS_upd3 st) = vis1 st" "curr2 (DDFS_upd3 st) = curr2 st"
        "stack2 (DDFS_upd3 st) = stack2 st" "done2 (DDFS_upd3 st) = done2 st"
        "vis2 (DDFS_upd3 st) = vis2 st"
  using assms
  by (auto simp: DDFS_call_3_conds_def DDFS_upd3_def DDFS_rec_call_3_def)

lemma DDFS_call_4_bridge:
  assumes "DDFS_call_4_conds st"
  shows "DDFS_rec_call_4 (curr1 st) (curr2 st) (stack2 st)
                         (curr2 (DDFS_upd4 st)) (stack2 (DDFS_upd4 st))"
        "curr1 (DDFS_upd4 st) = curr1 st" "stack1 (DDFS_upd4 st) = stack1 st"
        "vis1 (DDFS_upd4 st) = vis1 st" "done2 (DDFS_upd4 st) = done2 st"
        "vis2 (DDFS_upd4 st) = vis2 st"
  using assms
  by (auto simp: DDFS_call_4_conds_def DDFS_upd4_def DDFS_rec_call_4_def)

lemma DDFS_ret_1_bridge:
  assumes "DDFS_ret_1_conds st"
  obtains visited1_new visited2_new where
    "IDFS (level_leq (curr2 st)) (vset_of_list (curr1 st # stack1 st) \<union>\<^sub>G vis1 st)
           (curr2 st # stack2 st) (vis2 st) = (None, visited2_new)"
    "IDFS (level_leq (curr1 st)) (vset_of_list (curr2 st # stack2 st @ done2 st))
           (curr1 st # stack1 st) (vis1 st) = (None, visited1_new)"
    "DDFS_ret_1 (curr1 st) (stack1 st) (vis1 st) (curr2 st) (stack2 st) (done2 st)
               (vis2 st) visited1_new (stack2 st @ done2 st) [] visited2_new"
  using assms
  by (auto simp: DDFS_ret_1_conds_def DDFS_ret_1_def DFS_call_1_none_def DFS_call_2_none_def)

lemma DDFS_ret_2_bridge:
  "DDFS_ret_2_conds st \<Longrightarrow> DDFS_ret_2 (curr1 st) (curr2 st)"
  by (auto simp: DDFS_ret_2_conds_def DDFS_ret_2_def)

(* Backward-compatible bridge lemmas: take 7 separate args, used by holds_upd lemmas *)

lemma DDFS_call_1_bridge_7:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
  obtains p where
    "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
proof -
  let ?st = "mk_st u1 p1 visited1 u2 p2' p2 visited2"
  obtain p where brg1: "DDFS_rec_call_1 (curr1 ?st) (stack1 ?st) (vis1 ?st) (curr2 ?st) (stack2 ?st) (vis2 ?st)
                                        (curr2 (DDFS_upd1 ?st)) (stack2 (DDFS_upd1 ?st)) (vis2 (DDFS_upd1 ?st)) p"
    and brg2: "curr1 (DDFS_upd1 ?st) = curr1 ?st" "stack1 (DDFS_upd1 ?st) = stack1 ?st"
              "vis1 (DDFS_upd1 ?st) = vis1 ?st" "done2 (DDFS_upd1 ?st) = done2 ?st"
    using assms(1) by (rule DDFS_call_1_bridge)
  have st_eqs: "curr2 (DDFS_upd1 ?st) = u2_new" "stack2 (DDFS_upd1 ?st) = p2'_new"
               "vis2 (DDFS_upd1 ?st) = visited2_new"
    using assms(2) by (auto simp: mk_st_simps DDFS_state.ext_inject)
  have nams: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(2) brg2 by (auto simp: mk_st_simps)
  show ?thesis
    by (rule that[of p], use brg1 st_eqs in \<open>simp add: mk_st_simps\<close>, use nams in auto)
qed

lemma DDFS_call_2_bridge_7:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
  obtains p where
    "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    "u2_new = u2"
proof -
  let ?st = "mk_st u1 p1 visited1 u2 p2' p2 visited2"
  obtain p where brg1: "DDFS_rec_call_2 (curr1 ?st) (stack1 ?st) (vis1 ?st) (curr2 ?st) (done2 ?st) (stack2 ?st)
                                         (vis2 ?st) (curr1 (DDFS_upd2 ?st)) (stack1 (DDFS_upd2 ?st))
                                         (vis1 (DDFS_upd2 ?st)) (stack2 (DDFS_upd2 ?st)) (done2 (DDFS_upd2 ?st))
                                         (vis2 (DDFS_upd2 ?st)) p"
    and brg2: "curr2 (DDFS_upd2 ?st) = curr2 ?st"
    using assms(1) by (rule DDFS_call_2_bridge)
  have st_eqs: "curr1 (DDFS_upd2 ?st) = u1_new" "stack1 (DDFS_upd2 ?st) = p1_new"
               "vis1 (DDFS_upd2 ?st) = visited1_new" "stack2 (DDFS_upd2 ?st) = p2'_new"
               "done2 (DDFS_upd2 ?st) = p2_new" "vis2 (DDFS_upd2 ?st) = visited2_new"
    using assms(2) by (auto simp: mk_st_simps DDFS_state.ext_inject)
  have u2eq: "u2_new = u2"
    using assms(2) brg2 by (auto simp: mk_st_simps)
  show ?thesis
    by (rule that[of p], use brg1 st_eqs in \<open>simp add: mk_st_simps\<close>, use u2eq in auto)
qed

lemma DDFS_call_3_bridge_7:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
  shows "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new"
        "visited1_new = visited1" "u2_new = u2" "p2'_new = p2'"
        "p2_new = p2" "visited2_new = visited2"
  using assms
  by (auto simp: DDFS_call_3_conds_def DDFS_upd3_def DDFS_rec_call_3_def mk_st_simps)

lemma DDFS_call_4_bridge_7:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
  shows "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new"
        "u1_new = u1" "p1_new = p1" "visited1_new = visited1"
        "p2_new = p2" "visited2_new = visited2"
  using assms
  by (auto simp: DDFS_call_4_conds_def DDFS_upd4_def DDFS_rec_call_4_def mk_st_simps)

lemma DDFS_ret_1_bridge_7:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
  shows "DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new (p2' @ p2) [] visited2_new"
  using assms
  by (auto simp: DDFS_ret_1_conds_def DDFS_ret_1_def
                 DFS_call_1_none_def DFS_call_2_none_def mk_st_simps)

lemma DDFS_ret_1_conds_bridge_7:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  obtains visited1_new visited2_new where
    "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
       = (None, visited2_new)"
    "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
       = (None, visited1_new)"
    "DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new (p2' @ p2) [] visited2_new"
  using assms DDFS_ret_1_bridge_7[OF assms]
  by (auto simp: DDFS_ret_1_conds_def mk_st_simps)

lemma DDFS_ret_2_bridge_7:
  "DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2) \<Longrightarrow> DDFS_ret_2 u1 u2"
  by (auto simp: DDFS_ret_2_conds_def DDFS_ret_2_def mk_st_simps)

lemma not_Some_eq':
  "(None =x) = (\<forall>y. Some y \<noteq> x)"
  by (cases x) auto

lemma DDFS_induction_exhaust:
"(\<exists>u2_new p2'_new visited2_new p. DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p) \<or>
(\<exists>u1_new p1_new visited1_new p2'_new p2_new visited2_new p.
      DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p) \<or>
(\<exists>u1_new p1_new. DDFS_rec_call_3 u1 p1 u2 u1_new p1_new) \<or>
(\<exists>u2_new p2'_new. DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new) \<or>
(\<exists>visited1_new p2_new p2'_new visited2_new. 
   DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new p2_new p2'_new visited2_new) \<or> 
DDFS_ret_2 u1 u2
"
  by (auto simp: DDFS_rec_call_1_def DDFS_rec_call_2_def DDFS_rec_call_3_def DDFS_rec_call_4_def
                    DDFS_ret_1_def DDFS_ret_2_def DFS_call_1_none_def DFS_call_2_none_def
                    DFS_call_1_some_def DFS_call_2_some_def prod_eq_iff not_Some_eq')

(*
lemma DDFS_psimps: 
  assumes "DDFS_dom (u1, p1, visited1, u2, p2', p2, visited2)"
  shows "
local.DDFS u1 p1 visited1 u2 p2' p2 visited2 = 
(if (\<exists>u2_new p2'_new visited2_new p. DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p) then
  DDFS u1 p1 visited1 u2_new p2'_new p2 visited2_new
else if (\<exists>u1_new p1_new visited1_new p2'_new p2_new visited2_new p.
         DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p) then
  DDFS u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new
else if (\<exists>u1_new p1_new. DDFS_rec_call_3 u1 p1 u2 u1_new p1_new) then
  DDFS u1_new p1_new visited1 u2 p2' p2 visited2
else if (\<exists>u2_new p2'_new. DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new) then
  DDFS u1 p1 visited1 u2_new p2'_new p2 visited2
else if (\<exists>visited1_new p2_new p2'_new visited2_new. 
   DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new p2_new p2'_new visited2_new) then
  (u1 # p1, u2 # p2' @ p2)
else ([], []))
"
  using (*DDFS.pinduct[OF assms(1)] DDFS.psimps*) DDFS.psimps[OF assms(1)]
  apply (auto simp: DDFS_rec_call_1_def DDFS_rec_call_2_def DDFS_rec_call_3_def DDFS_rec_call_4_def
                 DDFS_ret_1_def DFS_call_1_none_def DFS_call_2_none_def DFS_call_1_some_def 
                 DFS_call_2_some_def Let_def prod_eq_iff not_Some_eq'
           split: if_splits if_split_asm prod.splits option.splits)
*)  

(*(if u1 = u2
 then let (p_ret2, visited2) = IDFS dG (level_leq u2) (set (u1 # p1) \<union> visited1) (u2 # p2') visited2
      in case p_ret2 of
         None \<Rightarrow>
           let p2 = p2' @ p2; p2' = []; (p_ret1, visited1) = IDFS dG (level_leq u1) (set (u2 # p2)) (u1 # p1) visited1
           in case p_ret1 of None \<Rightarrow> (u1 # p1, u2 # p2)
              | Some p \<Rightarrow> let u1 = hd p; p1 = tl p; return = local.DDFS u1 p1 visited1 u2 p2 p2' visited2 in return
         | Some p \<Rightarrow> let u2 = hd p; p2' = tl p; return = local.DDFS u1 p1 visited1 u2 p2 p2' visited2 in return
 else if level u1 = 0 \<and> level u2 = 0 then let return = (u1 # p1, u2 # p2' @ p2) in return
      else if level_leq u1 u2
           then let u1' = SOME u1'. (u1, u1') \<in> dG; return = local.DDFS u1' (u1 # p1) visited1 u2 p2 p2' visited2 in return
           else let u2' = SOME u2'. (u2, u2') \<in> dG; return = local.DDFS u1 p1 visited1 u2' p2 (u2 # p2') visited2 in return)"*)


(*definition "invar_1 p1 visited1 p2' p2 \<equiv>
    (set p1 \<union> visited1) \<inter> (set (p2' @ p2)) = {}"*)

definition "invar_1 st \<equiv>
    set (stack1 st) \<inter> set (stack2 st @ done2 st) = {}"

lemma invar_1_mk[simp]:
  "invar_1 (mk_st u1 p1 v1 u2 p2' p2 v2) = (set p1 \<inter> set (p2' @ p2) = {})"
  by (simp add: invar_1_def)

lemma invar_1_props_impl: "invar_1 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> set p1 \<inter> (set (p2' @ p2)) = {}"
  by (simp add: invar_1_def)

lemma invar_1_props[invar_props_elims]:
  "invar_1 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> (set p1 \<inter> set (p2' @ p2) = {} \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "set p1 \<inter> set (p2' @ p2) = {} \<Longrightarrow> invar_1 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_1_def)

abbreviation "dpath_bet' \<equiv> dpath_bet dG"

definition "invar_10 st \<equiv> (\<forall>v \<in> t_set (vis1 st). level v > level (curr1 st))"

lemma invar_10_mk[simp]:
  "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (\<forall>v \<in> t_set visited1. level v > level u1)"
  by (simp add: invar_10_def)

lemma invar_10_props_impl:
  "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2) \<Longrightarrow> v \<in> t_set visited1 \<Longrightarrow> level v > level u1"
  by (simp add: invar_10_def)

lemma invar_10_props[invar_props_elims]:
  "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2) \<Longrightarrow>
   ((\<forall>v \<in> t_set visited1. level v > level u1) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_10_def)

lemma invar_10_intro[invar_props_intros]:
  "(\<forall>v \<in> t_set visited1. level v > level u1) \<Longrightarrow>
   invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by (auto simp: invar_10_def)

definition "invar_11 st \<equiv> (\<forall>v \<in> t_set (vis2 st). level v > level (curr2 st))"

lemma invar_11_mk[simp]:
  "invar_11 (mk_st u1 p1 v1 u2 p2' p2 v2) = (\<forall>v \<in> t_set v2. level v > level u2)"
  by (simp add: invar_11_def)

lemma invar_11_props_impl:
  "invar_11 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> v \<in> t_set v2 \<Longrightarrow> level v > level u2"
  by (simp add: invar_11_def)

lemma invar_11_props[invar_props_elims]:
  "invar_11 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> ((\<forall>v \<in> t_set v2. level v > level u2) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_11_def)

lemma invar_11_intro[invar_props_intros]:
  "(\<forall>v \<in> t_set v2. level v > level u2) \<Longrightarrow> invar_11 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_11_def)

text \<open>Invariants on vset validity (P1.0 infrastructure -- moved early for availability).\<close>

definition "invar_12 st \<equiv> vset_inv (vis1 st)"

lemma invar_12_mk[simp]:
  "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = vset_inv visited1"
  by (simp add: invar_12_def)

lemma invar_12_props_impl [simp]:
  "invar_12 st \<Longrightarrow> vset_inv (vis1 st)"
  unfolding invar_12_def by auto

lemma invar_12_props[invar_props_elims]:
  "invar_12 st \<Longrightarrow> (vset_inv (vis1 st) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_12_def)

lemma invar_12_intro[invar_props_intros]:
  "vset_inv (vis1 st) \<Longrightarrow> invar_12 st"
  by (auto simp: invar_12_def)

definition "invar_13 st \<equiv> vset_inv (vis2 st)"

lemma invar_13_mk[simp]:
  "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = vset_inv visited2"
  by (simp add: invar_13_def)

lemma invar_13_props_impl [simp, intro]:
  "invar_13 st \<Longrightarrow> vset_inv (vis2 st)"
  unfolding invar_13_def by auto

lemma invar_13_props[invar_props_elims]:
  "invar_13 st \<Longrightarrow> (vset_inv (vis2 st) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_13_def)

lemma invar_13_intro[invar_props_intros]:
  "vset_inv (vis2 st) \<Longrightarrow> invar_13 st"
  by (auto simp: invar_13_def)

definition "invar_14 st \<equiv> t_set (vis1 st) \<subseteq> dVs dG"

lemma invar_14_mk[simp]:
  "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (t_set visited1 \<subseteq> dVs dG)"
  by (simp add: invar_14_def)

lemma invar_14_props_impl:
  "invar_14 st \<Longrightarrow> t_set (vis1 st) \<subseteq> dVs dG"
  unfolding invar_14_def by auto

lemma invar_14_props[invar_props_elims]:
  "invar_14 st \<Longrightarrow> (t_set (vis1 st) \<subseteq> dVs dG \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_14_def)

lemma invar_14_intro[invar_props_intros]:
  "t_set visited1 \<subseteq> dVs dG \<Longrightarrow> invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by (simp add: invar_14_def)

definition "invar_15 st \<equiv> t_set (vis2 st) \<subseteq> dVs dG"

lemma invar_15_mk[simp]:
  "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (t_set visited2 \<subseteq> dVs dG)"
  by (simp add: invar_15_def)

lemma invar_15_props_impl:
  "invar_15 st \<Longrightarrow> t_set (vis2 st) \<subseteq> dVs dG"
  unfolding invar_15_def by auto

lemma invar_15_props[invar_props_elims]:
  "invar_15 st \<Longrightarrow> (t_set (vis2 st) \<subseteq> dVs dG \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_15_def)

lemma invar_15_intro[invar_props_intros]:
  "t_set visited2 \<subseteq> dVs dG \<Longrightarrow> invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by (simp add: invar_15_def)

definition "IDFS_pre avoid vis \<longleftrightarrow>
  vset_inv avoid \<and> vset_inv vis \<and>
  t_set avoid \<subseteq> dVs dG \<and> t_set vis \<subseteq> dVs dG"

lemma IDFS_preI:
  "\<lbrakk>vset_inv avoid; vset_inv vis; t_set avoid \<subseteq> dVs dG; t_set vis \<subseteq> dVs dG\<rbrakk>
   \<Longrightarrow> IDFS_pre avoid vis"
  by (simp add: IDFS_pre_def)

(*invar_2 redefinition (2026-07-03), symmetric to invar_3: under the weak IDFS_sound(4)
  a walk from visited1 to a level-\<le>-u1 vertex may end on the u1-side stack u1 # p1 (the
  dropped avoid-head u1 = u2), so the target set also allows hits on the own (u1) side
  footprint.  At ret_1 the extra hits fall in set (u1 # p1) = patha.*)
definition "invar_2 st \<equiv>
                   (\<forall>v \<in> t_set (vis1 st). \<forall>p v'.
                                     p \<noteq> [] \<and> dpath_bet' (v # p) v v' \<and> level v' \<le>  level (curr1 st)
                                     \<longrightarrow> (set p) \<inter> (set ((u2' (curr2 st) (stack2 st)) # (done2 st)) \<union> t_set (vis1 st) \<union> set (curr1 st # stack1 st)) \<noteq> {})"

lemma invar_2_mk[simp]:
  "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 v2) =
   (\<forall>v \<in> t_set visited1. \<forall>p v'.
      p \<noteq> [] \<and> dpath_bet' (v # p) v v' \<and> level v' \<le> level u1
      \<longrightarrow> (set p) \<inter> (set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1)) \<noteq> {})"
  by (simp add: invar_2_def)

lemma invar2_props:
  "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 v2) \<Longrightarrow> v \<in> t_set visited1 \<Longrightarrow> p \<noteq> [] \<Longrightarrow> dpath_bet' (v # p) v v' \<Longrightarrow> level v' \<le>  level u1
   \<Longrightarrow> (set p) \<inter> (set ((last (u2 # p2')) # p2) \<union> t_set visited1 \<union> set (u1 # p1)) \<noteq> {}"
  unfolding invar_2_mk by blast

lemma invar_2_props[invar_props_elims]:
  "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 v2) \<Longrightarrow>
   ((\<forall>v \<in> t_set visited1. \<forall>p v'.
       p \<noteq> [] \<and> dpath_bet' (v # p) v v' \<and> level v' \<le> level u1
       \<longrightarrow> (set p) \<inter> (set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1)) \<noteq> {}) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
  "(\<forall>v \<in> t_set visited1. \<forall>p v'.
      p \<noteq> [] \<and> dpath_bet' (v # p) v v' \<and> level v' \<le> level u1
      \<longrightarrow> (set p) \<inter> (set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1)) \<noteq> {})
   \<Longrightarrow> invar_2 (mk_st u1 p1 visited1 u2 p2' p2 v2)"
  by (auto simp: invar_2_def)

lemma invar_2_then_invar_0:
  shows "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 v2) \<longleftrightarrow>
         invar_0 dG (level_leq u1) (set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1)) (t_set visited1)"
  by(auto simp: invar_0_def invar_2_def)

(*invar_3 redefinition (2026-07-03).  Under the realisable IDFS interface (weak
  IDFS_sound(4)) a returned path from visited2 may legitimately end at / pass through
  the merged u2-side stack u2 # p2' @ p2 (which contains u1 = u2 in the if1 branch and
  which the DFS neither keeps on the returned path nor records in visited1_new).  The
  invariant therefore allows hits on the u2-side stack as well; at ret_1 (p2' = []) the
  extra hits fall in set (u2 # p2), i.e. exactly pathb, which is what Lemma lem:ddfs:1
  consumes.*)
definition "invar_3 st \<equiv>
            (\<forall>v \<in> t_set (vis2 st). \<forall>p v'.
                 p \<noteq> [] \<longrightarrow> dpath_bet' (v # p) v v' \<and> level v' \<le>  level (curr2 st)
                 \<longrightarrow> (set p) \<inter> (set (curr1 st # stack1 st) \<union> t_set (vis1 st) \<union> set (curr2 st # stack2 st @ done2 st)) \<noteq> {})"

lemma invar_3_mk[simp]:
  "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2) =
   (\<forall>v \<in> t_set visited2. \<forall>p v'.
      p \<noteq> [] \<longrightarrow> dpath_bet' (v # p) v v' \<and> level v' \<le> level u2
      \<longrightarrow> (set p) \<inter> (set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)) \<noteq> {})"
  by (simp add: invar_3_def)

lemma invar3_props:
  "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2) \<Longrightarrow> p \<noteq> [] \<Longrightarrow> v \<in> t_set visited2 \<Longrightarrow>
   dpath_bet' (v # p) v v' \<Longrightarrow> level v' \<le>  level u2 \<Longrightarrow>
   (set p) \<inter> (set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)) \<noteq> {}"
  unfolding invar_3_mk by blast

lemma invar_3_props[invar_props_elims]:
  "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2) \<Longrightarrow>
   ((\<forall>v \<in> t_set visited2. \<forall>p v'.
       p \<noteq> [] \<longrightarrow> dpath_bet' (v # p) v v' \<and> level v' \<le> level u2
       \<longrightarrow> (set p) \<inter> (set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)) \<noteq> {}) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]:
  "(\<forall>v \<in> t_set visited2. \<forall>p v'.
      p \<noteq> [] \<longrightarrow> dpath_bet' (v # p) v v' \<and> level v' \<le> level u2
      \<longrightarrow> (set p) \<inter> (set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)) \<noteq> {})
   \<Longrightarrow> invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by (auto simp: invar_3_def)

lemma invar_3_then_invar_0:
  shows "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2) \<longleftrightarrow>
         invar_0 dG (level_leq u2) (set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)) (t_set visited2)"
  by(auto simp: invar_0_def invar_3_def)

abbreviation "dpath' \<equiv> dpath dG"

definition "invar_4 st \<equiv> dpath' (rev (curr1 st # stack1 st))"

lemma invar_4_mk[simp]:
  "invar_4 (mk_st u1 p1 v1 u2 p2' p2 v2) = dpath' (rev (u1 # p1))"
  by (simp add: invar_4_def)

lemma invar_4_props_impl:
  "invar_4 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> dpath' (rev (u1 # p1))"
  by (simp add: invar_4_def)

lemma invar_4_props[invar_props_elims]:
  "invar_4 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> (dpath' (rev (u1 # p1)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_4_def)

lemma invar_4_intro[invar_props_intros]:
  "dpath' (rev (u1 # p1)) \<Longrightarrow> invar_4 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_4_def)

lemma invar_4_then_in_Vs: "invar_4 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> u1 \<in> dVs dG"
  apply(rule path_then_in_Vs)
  by(auto simp add: invar_4_def)

lemma dpath'_distinct:
  assumes "dpath' p"
  shows "distinct p"
proof(intro distinct_decomp ballI)
  fix xs' x xs'' x'
  assume "p = xs' @ x # xs''"
  with assms have "dpath' (x # xs'')"
    by (simp add: append_dpath_suff)
  moreover assume "x' \<in> set xs''"
  ultimately have "level x' < level x"
    apply(subst dpath_transitive_rel[where R = "\<lambda>x x'. level x' < level x"])
    using digraph(1)
    by auto
  thus "x \<noteq> x'"
    by auto
qed

lemma invar_4_distinct: "invar_4 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> distinct(u1 # p1)"
  by(subst distinct_rev[symmetric], rule dpath'_distinct, simp add: invar_4_def)

definition "invar_5 st \<equiv> dpath' (rev (curr2 st # stack2 st @ done2 st))"

lemma invar_5_mk[simp]:
  "invar_5 (mk_st u1 p1 v1 u2 p2' p2 v2) = dpath' (rev (u2 # p2' @ p2))"
  by (simp add: invar_5_def)

lemma invar_5_props_impl:
  "invar_5 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> dpath' (rev (u2 # p2' @ p2))"
  unfolding invar_5_def
  by simp

lemma invar_5_props[invar_props_elims]:
  "invar_5 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> (dpath' (rev (u2 # p2' @ p2)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_5_def)

lemma invar_5_intro[invar_props_intros]:
  "dpath' (rev (u2 # p2' @ p2)) \<Longrightarrow> invar_5 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_5_def)

lemma invar_5_props':
  "invar_5 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> dpath' (rev (u2 # p2'))"
  by (simp add: invar_5_def append_dpath_suff)

lemma invar_5_then_in_Vs: "invar_5 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> u2 \<in> dVs dG"
  apply(rule path_then_in_Vs)
  by(auto simp add: invar_5_def)

lemma invar_5_distinct: "invar_5 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> distinct(u2 # p2' @ p2)"
  by(subst distinct_rev[symmetric], rule dpath'_distinct, simp add: invar_5_def)

lemma stack1_dVs:
  assumes "invar_4 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  shows "set (u1 # p1) \<subseteq> dVs dG"
proof
  fix x assume "x \<in> set (u1 # p1)"
  hence "x \<in> set (rev (u1 # p1))" by simp
  thus "x \<in> dVs dG"
    by (rule path_then_in_Vs[OF invar_4_props_impl[OF assms]])
qed

lemma stack2_dVs:
  assumes "invar_5 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  shows "set (u2 # p2' @ p2) \<subseteq> dVs dG"
proof
  fix x assume hx: "x \<in> set (u2 # p2' @ p2)"
  hence "x \<in> set (rev (u2 # p2' @ p2))" by (simp only: set_rev)
  thus "x \<in> dVs dG"
    by (rule path_then_in_Vs[OF invar_5_props_impl[OF assms]])
qed

lemma invar_4_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_4 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  show ?thesis using assms(3) by (simp add: eqs)
qed

lemma invar_4_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_4 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3)
  note rec_call_2 = DDFS_rec_call_2_props[OF ass] and
       call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF invars] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF invars] .
  have ivA4: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA4: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(4)] rec_call_2(3) by simp
  have ivV4: "vset_inv visited1" using invar_12_props_impl[OF assms(5)] by simp
  have dV4: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(6)] by simp
  have "dpath' (rev(u1 # p1))"
    using invar_4_props_impl[OF invars].
  hence dpath_p: "dpath' (rev p)"
    by(rule IDFS_sound(1)[OF ivA4 ivV4 dA4 dV4 _ call_2_some])
  from dpath_p have "dpath' (rev (u1_new # p1_new))"
    apply(subst rec_call_2)+
    using IDFS_sound(7)[OF ivA4 ivV4 dA4 dV4 pw dst call_2_some]
    by auto
  then show ?thesis
    by (auto simp: invar_4_def)
qed

lemma DDFS_rec_call_3_valid_edge[intro]:
  assumes "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new" "u1 \<in> dVs dG"
  shows "(u1, u1_new) \<in> dG"
proof -
  have "level u1 \<noteq> 0"
    using DDFS_rec_call_3_props[OF assms(1)] by auto
  hence "(u1, succ u1) \<in> dG"
    using succ_works[OF assms(2)] by auto
  then show ?thesis
    using DDFS_rec_call_3_props(4)[OF assms(1)] by simp
qed

lemma invar_4_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_4 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3)
  note rec_call_3 = DDFS_rec_call_3_props[OF ass(1)]
  have "dpath' (rev(u1 # p1))"
    using invar_4_props_impl[OF invars(1)].

  moreover have "u1 \<in> dVs dG"
    using invar_4_then_in_Vs[OF invars(1)] .

  hence "(u1, u1_new) \<in> dG"
    using DDFS_rec_call_3_valid_edge[OF ass(1)]
    by auto

  ultimately show ?thesis
    by (simp add: invar_4_def rec_call_3(5) dpath_snoc_edge)
qed

lemma invar_4_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_4 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_4_bridge_7[OF assms(1,2)] by simp

lemma invar_4_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  using assms(4) .

lemma invar_4_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk> \<Longrightarrow> invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma invar_5_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_5 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note invars = assms(3)
  note rec_call_1[simp] = DDFS_rec_call_1_props[OF ass]  and
       call_1_some = DFS_call_1_some_props[OF rec_call_1(2)]  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(5)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(6)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(4)] invar_14_props_impl[OF assms(7)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(8)] by simp
  have "dpath' (rev (u2 # p2' @ p2))"
    using invar_5_props_impl[OF invars] .
  hence "dpath' (rev p)"
    using IDFS_sound(1)[OF ivA vi2 dA dV _ call_1_some] append_dpath_suff
    by auto
  hence "dpath' (rev (u2_new # p2'_new))"
    apply(subst rec_call_1)+
    using IDFS_sound(7)[OF ivA vi2 dA dV pw dst call_1_some]
    by auto
  show ?thesis
  proof(cases "p2 = []")
    case True
    then show ?thesis
      using \<open>dpath' (rev (u2 # p2' @ p2))\<close> \<open>dpath' (rev (u2_new # p2'_new))\<close>
      by (auto simp: invar_5_def eqs)
  next
    case False
    hence "(last (rev p2), hd (rev (u2 # p2'))) \<in> dG"
      apply(intro dpath_append_edge[where ?p1.0 = "rev p2" and ?p2.0 = "rev (u2 # p2')"])
      using invar_5_props_impl[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>]
      by auto
    moreover have "hd (rev (u2 # p2')) = last p"
      using IDFS_sound(6,7)[OF ivA vi2 dA dV pw dst call_1_some]
      by(subst hd_rev, auto)
    ultimately have "(last (rev p2), hd (rev p)) \<in> dG"
      using IDFS_sound(7)[OF ivA vi2 dA dV pw dst call_1_some]
      by (simp add: hd_rev)
    with False have "dpath' (rev p2 @ rev p)"
      using \<open>dpath' (rev (u2 # p2' @ p2))\<close> \<open>dpath' (rev p)\<close>
      by (auto intro: append_dpath append_dpath_pref)
    moreover have "rev p = rev (tl p) @ [hd p]"
      using IDFS_sound(7)[OF ivA vi2 dA dV pw dst call_1_some]
      by (simp add: rev_swap)
    ultimately show ?thesis
      unfolding invar_5_def eqs
      by auto
  qed
qed

lemma invar_5_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_5 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3)
  note rec_call_2 = DDFS_rec_call_2_props[OF ass] and
       call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have "dpath' (rev (u2 # p2' @ p2))"
    using invar_5_props_impl[OF invars] .
  then show ?thesis
    by (auto simp: invar_5_def rec_call_2 eqs)
qed

lemma invar_5_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_5 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_3_bridge_7[OF assms(1,2)] by simp

lemma DDFS_rec_call_4_valid_edge:
  assumes "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new" "u2 \<in> dVs dG"
  shows "(u2, u2_new) \<in> dG"
proof -
  have "level u2 \<noteq> 0"
    using DDFS_rec_call_4_props[OF assms(1)] by auto
  hence "(u2, succ u2) \<in> dG"
    using succ_works[OF assms(2)] by auto
  then show ?thesis
    using DDFS_rec_call_4_props(4)[OF assms(1)] by simp
qed

lemma invar_5_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_5 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_4_bridge_7[OF assms(1,2)]
  note invars = assms(3)
  note rec_call_4 = DDFS_rec_call_4_props[OF ass(1)]
  have "dpath' (rev(u2 # p2' @ p2))"
    using invar_5_props_impl[OF invars].

  moreover have "u2 \<in> dVs dG"
    using invar_5_then_in_Vs[OF invars].

  hence "(u2, u2_new) \<in> dG"
    using DDFS_rec_call_4_valid_edge[OF ass(1)] 
    by auto

  ultimately show ?thesis
  proof -
    have h1: "dpath' ((rev p2 @ rev p2') @ [u2])"
      using \<open>dpath' (rev (u2 # p2' @ p2))\<close> by simp
    have snoc: "dpath' ((rev p2 @ rev p2') @ [u2, u2_new])"
      by (rule dpath_snoc_edge[OF h1 \<open>(u2, u2_new) \<in> dG\<close>])
    then show ?thesis
      unfolding invar_5_def rec_call_4(5) ass(2,5) by simp
  qed
qed

lemma invar_5_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_5 (mk_st u1 p1 visited1 u2 [] (p2' @ p2) visited2)"
  using assms(4) by (simp add: invar_5_def)

lemma invar_5_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

definition "invar_6 st \<equiv> (\<forall>v \<in> set (stack1 st). level (curr1 st) < level v)"

lemma invar_6_mk[simp]:
  "invar_6 (mk_st u1 p1 v1 u2 p2' p2 v2) = (\<forall>v \<in> set p1. level u1 < level v)"
  by (simp add: invar_6_def)

lemma invar_6_props_impl:
  "invar_6 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> v \<in> set p1 \<Longrightarrow> level u1 < level v"
  by (simp add: invar_6_def)

lemma invar_6_props[invar_props_elims]:
  "invar_6 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> ((\<forall>v \<in> set p1. level u1 < level v) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_6_def)

lemma invar_6_intro[invar_props_intros]:
  "(\<forall>v \<in> set p1. level u1 < level v) \<Longrightarrow> invar_6 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_6_def)

lemma invar_6_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  show ?thesis using assms(3) by (simp add: eqs)
qed

lemma dpath_level_lt: "dpath' (v#vs) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> level v' < level v"
  apply(rule dpath_transitive_rel[where R = "\<lambda>v1 v2. level v2 < level v1"])
  using digraph(1)
  by auto

lemma dpath_level_lt': "dpath' (vs @ [v]) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> level v < level v'"
  apply(rule dpath_transitive_rel'[where R = "\<lambda>v1 v2. level v2 < level v1"])
  using digraph(1)
  by auto

lemma invar_6_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3,4)  show ?thesis
    unfolding invar_6_mk
  proof
    fix v
    assume "v \<in> set p1_new"
    note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
         call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
    have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF invars(1)] .
    have dst: "distinct (u1 # p1)" using invar_4_distinct[OF invars(1)] .
    have ivA6: "vset_inv (vset_of_list (u2 # p2_new))" by simp
    have dA6: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
      using stack2_dVs[OF assms(5)] rec_call_2(3) by simp
    have ivV6: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
    have dV6: "t_set visited1 \<subseteq> dVs dG"
      using invar_14_props_impl[OF assms(7)] by simp
    have "p = hd p # tl p"
      using IDFS_sound(7)[OF ivA6 ivV6 dA6 dV6 pw dst call_2_some]
      by auto
    hence "dpath' (rev (hd p # tl p))"
      using IDFS_sound(1)[OF ivA6 ivV6 dA6 dV6 pw call_2_some] invar_4_props_impl[OF invars(1)]
      by fastforce
    moreover have "v \<in> set (rev (tl p))"
      using \<open>v \<in> set p1_new\<close>
      by auto
    ultimately show "level u1_new < level v"
      by(auto intro: dpath_level_lt'[where vs = "rev (tl p)"])
  qed
qed

lemma invar_6_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3,4)  show ?thesis
    unfolding invar_6_mk
  proof
    fix v
    assume "v \<in> set p1_new"
    note rec_call_3 = DDFS_rec_call_3_props[OF ass(1)]

    moreover have "u1 \<in> dVs dG"
      using invar_4_then_in_Vs[OF invars(1)] .

    hence "(u1, u1_new) \<in> dG"
      using DDFS_rec_call_3_valid_edge[OF ass(1)]
      by auto

    ultimately show "level u1_new < level v"
      using invar_6_props_impl[OF invars(2)] \<open>v \<in> set p1_new\<close> digraph(1)
      by fastforce
  qed
qed

lemma invar_6_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_4_bridge_7[OF assms(1,2)] by simp

lemma invar_6_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  using assms(4) .

lemma invar_6_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk> \<Longrightarrow> invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

definition "invar_7 st \<equiv> (\<forall>v \<in> set (stack2 st @ done2 st). level (curr2 st) < level v)"

lemma invar_7_mk[simp]:
  "invar_7 (mk_st u1 p1 v1 u2 p2' p2 v2) = (\<forall>v \<in> set (p2' @ p2). level u2 < level v)"
  by (simp add: invar_7_def)

lemma invar_7_props_impl:
  "invar_7 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> v \<in> set (p2' @ p2) \<Longrightarrow> level u2 < level v"
  by (simp add: invar_7_def)

lemma invar_7_props[invar_props_elims]:
  "invar_7 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> ((\<forall>v \<in> set (p2' @ p2). level u2 < level v) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_7_def)

lemma invar_7_intro[invar_props_intros]:
  "(\<forall>v \<in> set (p2' @ p2). level u2 < level v) \<Longrightarrow> invar_7 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_7_def)

lemma invar_7_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note invars = assms(3,4)
  show ?thesis
    unfolding invar_7_mk eqs
  proof
    fix v
    assume "v \<in> set (p2'_new @ p2)"
    note rec_call_1[simp] = DDFS_rec_call_1_props[OF ass] and
         call_1_some = DFS_call_1_some_props[OF rec_call_1(2)]
    have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars(1)] .
    have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars(1)] by simp
    have vi1_7: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
    have vi2_7: "vset_inv visited2" using invar_13_props_impl[OF assms(7)] by simp
    have ivA7: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
      using vi1_7 by (auto intro: set_ops.invar_union)
    have dA7: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
      using stack1_dVs[OF assms(5)] invar_14_props_impl[OF assms(8)] vi1_7
      by (auto simp: t_set_vset_of_list_union)
    have dV7: "t_set visited2 \<subseteq> dVs dG"
      using invar_15_props_impl[OF assms(9)] by simp
    have "p = hd p # tl p"
      using IDFS_sound(7)[OF ivA7 vi2_7 dA7 dV7 pw dst call_1_some]
      by auto
    moreover have "dpath' (rev (u2#p2'))"
      using invar_5_props'[OF invars(1)] .
    ultimately have "dpath' (rev (hd p # tl p))"
      using IDFS_sound(1)[OF ivA7 vi2_7 dA7 dV7 pw call_1_some] 
      by fastforce
    have inv5_new: "invar_5 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
      using invar_5_holds_1[OF assms(1) assms(2) invars(1) assms(5) assms(6) assms(7) assms(8) assms(9)] .
    hence "dpath' (rev (hd p # tl p @ p2))"
      using invar_5_props_impl[OF inv5_new] eqs
      by (simp add: rec_call_1)
    moreover have "v \<in> set (rev (tl p @ p2))"
      using \<open>v \<in> set (p2'_new @ p2)\<close>
      by auto
    ultimately show "level u2_new < level v"
      by(auto intro: dpath_level_lt'[where vs = "rev (tl p @ p2)"])
  qed
qed

lemma invar_7_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3)
  show ?thesis using invars
    by(simp add: invar_7_def DDFS_rec_call_2_props[OF ass] eqs)
qed

lemma invar_7_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_3_bridge_7[OF assms(1,2)] by simp

lemma invar_7_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_4_bridge_7[OF assms(1,2)]
  note invars = assms(3,4)
  show ?thesis
    unfolding invar_7_mk ass(5)
  proof
    fix v
    assume "v \<in> set (p2'_new @ p2)"
    note rec_call_4 = DDFS_rec_call_4_props[OF ass(1)]

    moreover have "u2 \<in> dVs dG"
      using invar_5_then_in_Vs[OF invars(1)] .

    hence "(u2, u2_new) \<in> dG"
      using DDFS_rec_call_4_valid_edge[OF ass(1)]
      by auto

    ultimately show "level u2_new < level v"
      using invar_7_props_impl[OF invars(2)] \<open>v \<in> set (p2'_new @ p2)\<close> digraph(1)
      by fastforce
  qed
qed

lemma invar_7_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7 (mk_st u1 p1 visited1_new u2 [] (p2' @ p2) visited2_new)"
  using assms(4) by (simp add: invar_7_def)

lemma invar_7_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

(*
lemma invar1_holds_1:
  assumes
   ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
        "u1 \<in> dVs dG" "u2 \<in> dVs dG"  and
   invars: "invar_1 p1 visited1 p2' p2" "invar_3 u1 p1 visited1 u2 visited2" "invar_6 p1 u2" 
           "invar_7 u1 p2' p2"
 shows "invar_1 p1 visited1 p2'_new p2"
proof-
  have \<open>u1 = u2\<close>
    using DDFS_rec_call_1_props(1)[OF ass(1)] .
  have "invar_0 dG (level_leq u2) (set p1 \<union> visited1) visited2"
    using invar_3_then_invar_0[OF invars(2)]
    by fastforce

  have "set p2' \<inter> (set p1 \<union> visited1) = {}"
    using \<open>invar_1 p1 visited1 p2' p2\<close>
    by (auto simp: invar_1_def)
  moreover have \<open>set p2' \<inter> visited2 = {}\<close>
  moreover have "u2 \<notin> set p2'"
    using \<open>invar_7 u1 p2' p2\<close>
          \<open>u1 = u2\<close>
    by (auto simp: invar_7_def)
  ultimately have "set p - set p2' \<inter> ((set p1 \<union> visited1) \<union> visited2_new) = {}"
    apply(intro IDFS_sound(3)[where avoid = "set p1 \<union> visited1" and visited = "insert u2 visited2"
                                    and visited' = "visited2_new" and p = p2'])
    using DFS_call_1_some_props(1)[OF DDFS_rec_call_1_props(2)[OF ass(1)]]
    by auto
  moreover have "set p2'_new \<subseteq> set p"
  proof -
    have "p2'_new = tl p"
      using DDFS_rec_call_1_props(4)[OF ass(1)] by simp
    then show ?thesis by (cases p) auto
  qed
  ultimately have "set p2'_new \<inter> ((set p1 \<union> visited1) \<union> visited2_new) = {}"
    by auto
  moreover have "set p2 \<inter> (set p1 \<union> visited1) = {}"
    using \<open>invar_1 p1 visited1 p2' p2\<close>
    by(auto simp: invar_1_def)
  ultimately show ?thesis
    unfolding invar_1_def    
    by auto
qed*)

lemma invar_1_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_1 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note invars = assms(3-)
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars(2)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars(2)] by simp
  have p2'_p1_disj: "set p2' \<inter> set p1 = {}"
    using \<open>invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>
    by (auto simp: invar_1_def)
  have sub: "set p2'_new \<subseteq> set p"
    using DDFS_rec_call_1_props(4)[OF ass(1)]
    by (cases p) auto
  have notin1: "u1 \<notin> set p1"
    using \<open>invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>
    by (auto simp: invar_6_def)
  hence notin2: "u2 \<notin> set p1"
    using DDFS_rec_call_1_props(1)[OF ass(1)]
    by simp
  have int1_set: "(set p - set (tl (u2 # p2'))) \<inter> set (u1 # p1) = {}"
  proof -
    note call_1_some = DFS_call_1_some_props[OF DDFS_rec_call_1_props(2)[OF ass]]
    have vis1_inv: "vset_inv visited1" using invars(5) by simp
    have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
      using vis1_inv by (auto intro: set_ops.invar_union)
    have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
      using stack1_dVs[OF invars(7)] invar_14_props_impl[OF invars(8)] vis1_inv
      by (auto simp: t_set_vset_of_list_union)
    have ivV: "vset_inv visited2" using invar_13_props_impl[OF invars(6)] by simp
    have dV: "t_set visited2 \<subseteq> dVs dG"
      using invar_15_props_impl[OF invars(9)] by simp
    have disj: "(set p - set (tl (u2 # p2'))) \<inter> (t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<union> t_set visited2_new) = {}"
      using IDFS_sound(3)[OF ivA ivV dA dV pw dst call_1_some] .
    moreover have "set (u1 # p1) \<subseteq> t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
      using t_set_vset_of_list_union[OF vis1_inv] by auto
    ultimately show ?thesis by auto
  qed
  have p2ne_disj: "set p2'_new \<inter> set p1 = {}"
    using int1_set sub notin2 p2'_p1_disj by auto
  have p2_disj: "set p2 \<inter> set p1 = {}"
    using \<open>invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>
    by(auto simp: invar_1_def)
  then show ?thesis using p2ne_disj p2_disj eqs
    unfolding invar_1_def
    by auto
qed
(*lemma invar1_holds_2:
  assumes
   ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2_new p2'_new p visited2_new"
        "u1 \<in> dVs dG" "u2 \<in> dVs dG"  and
   invars: "invar_1 p1 visited1 p2' p2" "invar_2 u1 visited1 u2 p2 p2'" "invar_6 p1 u2" 
           "invar_7 u1 p2' p2" "invar_11 p1 visited1"
 shows "invar_1 p1_new visited1_new p2'_new p2_new"
proof-
  have \<open>u1 = u2\<close>
    using DDFS_rec_call_2_props(1)[OF ass(1)] .

  have "(set p1 \<union> visited1) \<inter> set (p2' @ p2) = {}"
    using \<open>invar_1  p1 visited1 p2' p2\<close>
    unfolding invar_1_def .
  hence "(set p1 \<union> visited1) \<inter> set p2_new = {}"
    using DDFS_rec_call_2_props(3)[OF ass(1)]
    by simp
  moreover have "u2 \<notin> set p1"    
    using \<open>invar_6 p1 u2\<close> by (auto simp: invar_6_def)
  ultimately have "set p1 \<inter> set (u2 # p2_new) = {}"
    by auto
  moreover have \<open>set p1 \<inter> visited1 = {}\<close>
    using \<open>invar_11 p1 visited1\<close>
    by (auto simp: invar_11_def)
  moreover have "u1 \<notin> set p1"
    using \<open>invar_6 p1 u2\<close>
          \<open>u1 = u2\<close>
    by (auto simp: invar_6_def)
  ultimately have "set p \<inter> (set p2_new \<union> visited1_new) = {}"
    apply(intro IDFS_sound(3)[where avoid = "set p2_new" and visited = "insert u1 visited1"
                                    and visited' = "visited1_new" and p = p1 and P = "level_leq u1"])
    using DFS_call_2_some_props[OF DDFS_rec_call_2_props(5)[OF ass(1)]]
    by auto
  hence "set p \<inter> set p2_new = {}"
    by auto
  moreover have "set p1_new \<subseteq> set p"
  proof -
    have "p1_new = tl p"
      using DDFS_rec_call_2_props(7)[OF ass(1)] by simp
    then show ?thesis by (cases p) auto
  qed
  ultimately have "set p1_new \<inter> set p2_new = {}"
    by auto
  moreover have "visited1 \<inter> set (p2' @  p2) = {}"
    using \<open>invar_1 p1 visited1 p2' p2\<close>
    by (auto simp: invar_1_def)
  hence "visited1 \<inter> set p2_new = {}"
    using DDFS_rec_call_2_props(3)[OF ass(1)]
    by auto
  moreover have "(visited1_new - (insert u1 visited1)) \<inter> set p2_new = {}"
    using IDFS_vis_works(2)[OF DFS_call_2_some_props[OF DDFS_rec_call_2_props(5)[OF ass(1)]]]
    by auto
  moreover have "u1 \<notin> set p2_new"
    using \<open>invar_7 u1 p2' p2\<close> DDFS_rec_call_2_props(3)[OF ass(1)]
    by(auto simp: invar_7_def)
  moreover have "p2'_new = []"
    using DDFS_rec_call_2_props[OF ass(1)]
    by auto
  ultimately show ?thesis
    by(auto simp: invar_1_def)
qed*)

lemma invar_1_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_1 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note rec_call_2 = DDFS_rec_call_2_props[OF ass]
  note invars = assms(3-)
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF invars(2)] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF invars(2)] .
  note call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have p2n: "p2_new = p2' @ p2" using rec_call_2(3) .
  have p1n: "p1_new = tl p" using rec_call_2(7) .
  have p2'n: "p2'_new = []" using rec_call_2(4) .
  have p1_p2n: "set p1 \<inter> set p2_new = {}"
    using invars(1) by (simp add: p2n)
  have ivA: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF invars(5)] rec_call_2(3) by simp
  have ivV: "vset_inv visited1" using invar_12_props_impl[OF invars(6)] by simp
  have dV: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF invars(7)] by simp
  have sound3: "(set p - set p1) \<inter> (set (u2 # p2_new) \<union> t_set visited1_new) = {}"
    using IDFS_sound(3)[OF ivA ivV dA dV pw dst call_2_some] by simp
  have p_p2n: "(set p - set (u1 # p1)) \<inter> set p2_new = {}"
    using sound3 by auto
  have p1n_sub: "set p1_new \<subseteq> set p"
    using p1n by (cases p) auto
  have u2np2n: "u2 \<notin> set p2_new"
    using invars(4) by (auto simp: p2n)
  have u1np2n: "u1 \<notin> set p2_new"
    using u2np2n rec_call_2(1) by simp
  have p1n_p2n: "set p1_new \<inter> set p2_new = {}"
    using p_p2n p1_p2n u1np2n p1n_sub by auto
  show ?thesis using p1n_p2n p2'n eqs
    by (simp add: p2n)
qed
(*READT-TODO-03 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar1_holds_2[intro]:
  assumes
   ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p" and
   invars: "invar_1 p1 visited1 p2' p2" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 u1 p1" 
           "invar_7 u2 p2' p2"
 shows "invar_1 p1_new visited1_new p2'_new p2_new"
proof-
  have \<open>u1 = u2\<close>
    using DDFS_rec_call_2_props(1)[OF ass(1)] .
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF invars(2)] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF invars(2)] .
  have "set p1 \<inter> set (p2' @ p2) = {}"
    using \<open>invar_1  p1 visited1 p2' p2\<close>
    unfolding invar_1_def .
  hence "set p1 \<inter> set p2_new = {}"
    using DDFS_rec_call_2_props(3)[OF ass(1)]
    by simp
  (*moreover have "u1 \<notin> set p1"
    using \<open>invar_6 u1 p1\<close>
    by (auto simp: invar_6_def)
  hence "u2 \<notin> set p1"
    using DDFS_rec_call_2_props(1)[OF ass(1)]
    by simp
  ultimately have "set p1 \<inter> set (u2 # p2_new) = {}"
    by auto
  moreover have \<open>set p1 \<inter> visited1 = {}\<close>
    using \<open>invar_11 p1 visited1\<close>
    by (auto simp: invar_11_def)
  moreover have "u1 \<notin> set p1"
    using \<open>invar_6 p1 u2\<close>
          \<open>u1 = u2\<close>
    by (auto simp: invar_6_def)*)
  moreover have "(set p - set (tl (u1 # p1))) \<inter> (set (u2 # p2_new) \<union> visited1_new) = {}"
    using IDFS_sound(3)[OF pw dst DFS_call_2_some_props[OF DDFS_rec_call_2_props(5)[OF ass(1)]]]
    by auto
  hence "(set p - set (u1 # p1)) \<inter> set p2_new = {}"
    by auto
  moreover have "set p1_new \<subseteq> set p"
    using DDFS_rec_call_2_props(7)[OF ass(1)]
    by (cases p) auto
  moreover have "u2 \<notin> set (p2' @ p2)"
    using \<open>invar_7 u2 p2' p2\<close>
    by(auto simp: invar_7_def)
  hence "u1 \<notin> set (p2' @ p2)"
    using DDFS_rec_call_2_props(1)[OF ass(1)]
    by simp    
  hence "u1 \<notin> set p2_new"
    using DDFS_rec_call_2_props(3)[OF ass(1)]
    by auto
  ultimately have "set p1_new \<inter> set p2_new = {}"
    by auto
  moreover have "p2'_new = []"
    using DDFS_rec_call_2_props[OF ass(1)]
    by auto
  ultimately show ?thesis
    by(auto simp: invar_1_def)
qed
*)

definition "invar_6' st \<equiv> (\<forall>v \<in> set (stack1 st). curr2 st \<noteq> v \<and> level (curr2 st) \<le> level v)"

lemma invar_6'_mk[simp]:
  "invar_6' (mk_st u1 p1 v1 u2 p2' p2 v2) = (\<forall>v \<in> set p1. u2 \<noteq> v \<and> level u2 \<le> level v)"
  by (simp add: invar_6'_def)

lemma invar_6'_props_impl:
  "invar_6' (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> v \<in> set p1 \<Longrightarrow> u2 \<noteq> v \<and> level u2 \<le> level v"
  by (simp add: invar_6'_def)

lemma invar_6'_props[invar_props_elims]:
  "invar_6' (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> ((\<forall>v \<in> set p1. u2 \<noteq> v \<and> level u2 \<le> level v) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_6'_def)

lemma invar_6'_intro[invar_props_intros]:
  "(\<forall>v \<in> set p1. u2 \<noteq> v \<and> level u2 \<le> level v) \<Longrightarrow> invar_6' (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_6'_def)

lemma invar_6'_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6' (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note invars = assms(3-)
  note rec_call_1[simp] = DDFS_rec_call_1_props[OF ass] and
       call_1_some = DFS_call_1_some_props[OF rec_call_1(2)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars(1)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars(1)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF invars(5)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF invars(4)] invar_14_props_impl[OF invars(7)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have ivV: "vset_inv visited2" using invar_13_props_impl[OF invars(6)] by simp
  have dV: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF invars(8)] by simp
  have "level (hd p) \<le> level u2"
    using IDFS_sound(8)[OF ivA ivV dA dV pw dst call_1_some] .
  hence "level u2_new \<le> level u2"
    by auto
  moreover have "u2_new \<notin> set p1"
    using IDFS_sound(3)[OF ivA ivV dA dV pw dst call_1_some] invar_6_props_impl[OF invars(2)] \<open>level_leq u2 (hd p)\<close>
    by fastforce
  moreover have "level (hd p) \<le> level u2"
    using IDFS_sound(8)[OF ivA ivV dA dV pw dst call_1_some] .
  hence "level u2_new \<le> level u1"
    by auto
  ultimately show ?thesis
    using invars eqs
    unfolding invar_6'_def
    by auto
qed

lemma invar_6'_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6' (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3-)
  note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
       call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF invars(1)] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF invars(1)] .
  have ivA: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF invars(4)] rec_call_2(3) by simp
  have ivV: "vset_inv visited1" using invar_12_props_impl[OF invars(5)] by simp
  have dV: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF invars(6)] by simp
  have "v \<in> set (tl (u1 # p1)) \<Longrightarrow> level u1 < level v" for v
    using invar_6_props_impl[OF invars(2)]
    by fastforce
  hence "v \<in> set p1_new \<Longrightarrow> level u1 < level v" for v
    using IDFS_sound(5)[OF ivA ivV dA dV pw dst call_2_some]
    by fastforce
  moreover have "v \<in> set (tl p) \<Longrightarrow> level u1 < level v" for v
    using IDFS_sound(5)[OF ivA ivV dA dV pw dst call_2_some]
          invar_6_props_impl[OF invars(2)]
    by force
  moreover have "level u2 \<le> level u1"
    by force
  ultimately show ?thesis
    using invars(2) eqs
    by (fastforce simp: invar_6'_def)
qed

lemma invar_6'_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6' (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3)
  note rec_call_3 = DDFS_rec_call_3_props[OF ass(1)]
  show ?thesis
    using invars rec_call_3(1)[symmetric] rec_call_3(3) rec_call_3(5) ass(3)
    by (auto simp add: invar_6'_def)
qed

lemma invar_6'_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6' (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_4_bridge_7[OF assms(1,2)]
  note invars = assms(3,4)
  have "level u2 \<le> level v" if "v \<in> set p1" for v
    using invar_6'_props_impl[OF \<open>invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close> that]
    by(rule conjunct2)
  moreover have "u2 \<in> dVs dG"
    using invar_5_then_in_Vs[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>].
  hence "(u2, u2_new) \<in> dG"
    using DDFS_rec_call_4_valid_edge[OF ass(1)]
    by auto
  hence "level u2_new < level u2"
    using digraph
    by simp
  ultimately show ?thesis
    using ass(3)
    by (fastforce simp: invar_6'_def)
qed

lemma invar_6'_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  using assms(4) .

lemma invar_6'_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk> \<Longrightarrow> invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

definition "invar_7' st \<equiv> (\<forall>v \<in> set (stack2 st @ done2 st). curr1 st \<noteq> v \<and> level (curr1 st) \<le> level v)"

lemma invar_7'_mk[simp]:
  "invar_7' (mk_st u1 p1 v1 u2 p2' p2 v2) = (\<forall>v \<in> set (p2' @ p2). u1 \<noteq> v \<and> level u1 \<le> level v)"
  by (simp add: invar_7'_def)

lemma invar_7'_props_impl:
  "invar_7' (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> v \<in> set (p2' @ p2) \<Longrightarrow> u1 \<noteq> v \<and> level u1 \<le> level v"
  by (simp add: invar_7'_def)

lemma invar_7'_props[invar_props_elims]:
  "invar_7' (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> ((\<forall>v \<in> set (p2' @ p2). u1 \<noteq> v \<and> level u1 \<le> level v) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_7'_def)

lemma invar_7'_intro[invar_props_intros]:
  "(\<forall>v \<in> set (p2' @ p2). u1 \<noteq> v \<and> level u1 \<le> level v) \<Longrightarrow> invar_7' (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_7'_def)

lemma invar_7'_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7' (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note invars = assms(3-)
  note rec_call_1[simp] = DDFS_rec_call_1_props[OF ass] and
       call_1_some = DFS_call_1_some_props[OF rec_call_1(2)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars(1)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars(1)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF invars(5)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF invars(4)] invar_14_props_impl[OF invars(7)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have ivV: "vset_inv visited2" using invar_13_props_impl[OF invars(6)] by simp
  have dV: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF invars(8)] by simp
  have "v \<in> set (tl (u2 # p2' @ p2)) \<Longrightarrow> level u1 < level v" for v
    using invar_7_props_impl[OF invars(2)]
    by fastforce
  hence "v \<in> set (p2'_new @ p2) \<Longrightarrow> level u1 < level v" for v
    using IDFS_sound(5)[OF ivA ivV dA dV pw dst call_1_some]
    by fastforce
  moreover have "v \<in> set (tl p) \<Longrightarrow> level u1 < level v" for v
    using IDFS_sound(5)[OF ivA ivV dA dV pw dst call_1_some]
          invar_7_props_impl[OF invars(2)]
    by force
  moreover have "level u2 \<le> level u1"
    by force
  ultimately show ?thesis
    using eqs
    by (fastforce simp: invar_7'_def)
qed

lemma invar_7'_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7' (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3-)
  note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
       call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF invars(1)] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF invars(1)] .
  have ivA: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF invars(4)] rec_call_2(3) by simp
  have ivV: "vset_inv visited1" using invar_12_props_impl[OF invars(5)] by simp
  have dV: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF invars(6)] by simp
  have "level (hd p) \<le> level u1"
    using IDFS_sound(8)[OF ivA ivV dA dV pw dst call_2_some] .
  hence "level u1_new \<le> level u2"
    by auto
  moreover have "u1_new \<notin> set (p2' @ p2)"
    using IDFS_sound(3)[OF ivA ivV dA dV pw dst call_2_some] invar_7_props_impl[OF invars(2)] \<open>level_leq u1 (hd p)\<close>
    by fastforce
  moreover have "level (hd p) \<le> level u1"
    using IDFS_sound(8)[OF ivA ivV dA dV pw dst call_2_some] .
  hence "level u1_new \<le> level u1"
    by auto
  ultimately show ?thesis
    using invars(1,3)
    unfolding invar_7'_def
    using dual_order.trans
    by auto
qed

lemma invar_7'_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7' (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3,4)
  have "level u1 \<le> level v" if "v \<in> set (p2' @ p2)" for v
    using invar_7'_props_impl[OF \<open>invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close> that]
    by(rule conjunct2)
  moreover have "u1 \<in> dVs dG"
    using invar_4_then_in_Vs[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>].
  hence "(u1, u1_new) \<in> dG"
    using DDFS_rec_call_3_valid_edge[OF ass(1)]
    by auto
  hence "level u1_new < level u1"
    using digraph
    by simp
  ultimately show ?thesis
    using ass(4,5)
    by (fastforce simp: invar_7'_def)
qed

lemma invar_7'_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7' (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_4_bridge_7[OF assms(1,2)]
  note invars = assms(3)
  note rec_call_4[simp] = DDFS_rec_call_4_props[OF ass(1)]
  show ?thesis
    using invars ass(2,5)
    by (auto simp add: less_or_eq_imp_le invar_7'_def)
qed

lemma invar_7'_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_7' (mk_st u1 p1 visited1_new u2 [] (p2' @ p2) visited2_new)"
  using assms(4) by (simp add: invar_7'_def)

lemma invar_7'_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma invar_1_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_1 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3-)
  have "u1 \<notin> set (p2' @ p2)"
    using \<open>invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>
    unfolding invar_7'_def
    by fastforce
  then show ?thesis
    using \<open>invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>
      DDFS_rec_call_3_props(5)[OF ass(1)] ass(2,4,5,6)
    by (auto simp: invar_1_def)
qed

lemma invar_1_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_1 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_4_bridge_7[OF assms(1,2)]
  note invars = assms(3-)
  have "level u1 < level u2"
    using DDFS_rec_call_4_props(3)[OF ass(1)]
    .
  hence "u2 \<notin> set p1"
    using \<open>invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>
    unfolding invar_6'_def
    by fastforce
  then show ?thesis
    using \<open>invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>
          DDFS_rec_call_4_props(5)[OF ass(1)] ass(3,4,5,6)
    by (auto simp: invar_1_def)
qed

lemma invar_1_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_1 (mk_st u1 p1 visited1_new u2 [] (p2' @ p2) visited2_new)"
  using assms(4) by (auto simp: invar_1_def)

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma DDFS_rec_call_1_last_p_same:
  assumes ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
          and inv5: "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          and inv4: "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          and inv12: "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          and inv13: "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          and inv14: "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          and inv15: "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "u2' u2_new p2'_new = u2' u2 p2'"
proof-
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF inv5] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF inv5] by simp
  note call_1_some = DFS_call_1_some_props[OF DDFS_rec_call_1_props(2)[OF ass(1)]]
  have vi1r: "vset_inv visited1" using invar_12_props_impl[OF inv12] by simp
  have vi2r: "vset_inv visited2" using invar_13_props_impl[OF inv13] by simp
  have ivAr: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1r by (auto intro: set_ops.invar_union)
  have dAr: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF inv4] invar_14_props_impl[OF inv14] vi1r
    by (auto simp: t_set_vset_of_list_union)
  have dVr: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF inv15] by simp
  have pne_in: "u2 # p2' \<noteq> []" by simp
  have "last (u2 # p2') = last p"
    using IDFS_sound(6)[OF ivAr vi2r dAr dVr pw dst call_1_some pne_in] .
  moreover have "p \<noteq> []"
    using IDFS_sound(7)[OF ivAr vi2r dAr dVr pw dst call_1_some] .
  hence "u2' u2_new p2'_new = last p"
    using DDFS_rec_call_1_props(3,4)[OF ass(1)]
    by fastforce
  ultimately show ?thesis
    by auto
qed

lemma invar_2_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_2 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note invars = assms(3,4)
  have "invar_2 (mk_st u1 p1 visited1 u2_new p2'_new p2 visited2_new)"
    using DDFS_rec_call_1_last_p_same[OF ass invars(2) assms(5) assms(6) assms(7) assms(8) assms(9)] invars(1)
    by (auto simp: invar_2_def)
  then show ?thesis by (simp add: eqs)
qed

lemma ivnar_0_avoid_subset: "avoid \<subseteq> avoid' \<Longrightarrow> invar_0 dG P avoid vis \<Longrightarrow> invar_0 dG P avoid' vis"
  unfolding invar_0_def
  by force

lemma ivnar_0_visited_union: "invar_0 dG P avoid vis \<Longrightarrow> invar_0 dG P avoid vis2'' \<Longrightarrow> invar_0 dG P avoid (vis \<union> vis2'')"
  unfolding invar_0_def
  by (auto simp: invar_0_def)

lemma invar_0_imp:
  "invar_0 dG P' avoid vis \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P' x) \<Longrightarrow> invar_0 dG P avoid vis"
  unfolding invar_0_def
  by auto

text \<open>Helper lemmas for the amended IDFS interface (2026-07-03).\<close>

lemma dpath_level_decreasing:
  "dpath dG (v # vs) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> level v' < level v"
  by (rule dpath_transitive_rel[where R = "\<lambda>x y. level y < level x"])
     (auto intro: digraph(1))

lemma dpath_distinct:
  "dpath dG q \<Longrightarrow> distinct q"
proof (rule distinct_decomp)
  fix xs' x xs''
  assume dec: "q = xs' @ x # xs''"
  assume "dpath dG q"
  hence "dpath dG (x # xs'')"
    using dec by (auto intro: append_dpath_suff)
  thus "\<forall>x'\<in>set xs''. x \<noteq> x'"
    using dpath_level_decreasing[of x xs''] by fastforce
qed

lemma invar_0_absorb:
  assumes "invar_0 dG P (X \<union> W) V" "W \<subseteq> V" "\<forall>w\<in>W. \<not> P w"
  shows "invar_0 dG P X V"
  unfolding invar_0_def
proof (intro ballI allI impI)
  fix v v' p
  assume v: "v \<in> V" and pne: "p \<noteq> []"
     and pb: "dpath_bet dG (v # p) v v'" and Pv': "P v'"
  show "set p \<inter> X \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> set p \<inter> X \<noteq> {}"
    hence noX: "set p \<inter> X = {}" by simp
    have hit: "set p \<inter> (X \<union> W) \<noteq> {}"
      using assms(1) v pne pb Pv' unfolding invar_0_def by blast
    then obtain w0 where "w0 \<in> set p" "w0 \<in> W" using noX by auto
    then obtain a w b where decomp: "p = a @ w # b" "w \<in> W" "\<forall>x\<in>set b. x \<notin> W"
      using split_list_last_prop[where P = "\<lambda>x. x \<in> W" and xs = p] by blast
    have wV: "w \<in> V" using decomp(2) assms(2) by auto
    have suf: "dpath_bet dG (w # b) w v'"
    proof -
      have "dpath_bet dG ((v # a) @ w # b) v v'" using pb decomp(1) by simp
      thus ?thesis by (rule split_dpath)
    qed
    have "w \<noteq> v'"
      using decomp(2) assms(3) Pv' by blast
    hence bne: "b \<noteq> []"
      using suf by (cases b) (auto simp: last_of_dpath_bet vwalk_bet_def)
    have "set b \<inter> (X \<union> W) \<noteq> {}"
      using assms(1) wV bne suf Pv' unfolding invar_0_def by blast
    moreover have "set b \<inter> W = {}" using decomp(3) by auto
    moreover have "set b \<subseteq> set p" using decomp(1) by auto
    ultimately show False using noX by auto
  qed
qed

text \<open>Closure-to-invar_0 bridge: if every out-edge of a newly-visited vertex lands in a
target set T, then any nonempty walk from a newly-visited vertex hits T with its very
first step, so invar_0 holds for the newly-visited set (no \<not>P / history needed -- the
tail's head is already an out-neighbour of a newly-visited vertex).\<close>
lemma closed_walk_invar_0:
  assumes "\<And>v w. v \<in> X \<Longrightarrow> (v, w) \<in> dG \<Longrightarrow> w \<in> T"
  shows "invar_0 dG P T X"
  unfolding invar_0_def
proof (intro ballI allI impI)
  fix v v' p
  assume v: "v \<in> X" and pne: "p \<noteq> []" and pb: "dpath_bet dG (v # p) v v'"
  obtain a as where p_eq: "p = a # as" using pne by (cases p) auto
  have "dpath dG (v # a # as)" using pb p_eq by (auto simp: vwalk_bet_def)
  hence "(v, a) \<in> dG" by (rule dpath_cons)
  hence "a \<in> T" using assms v by blast
  thus "set p \<inter> T \<noteq> {}" using p_eq by auto
qed

text \<open>Inductive closure-to-invar_0 bridge (the Some/None u2-side case): if out-edges of
newly-visited vertices land in the target T or stay in the newly-visited set N, the
newly-visited vertices are \<not>P, and the OLD visited set already satisfies invar_0 for T,
then the whole set (old \<union> new) satisfies invar_0 for T.  A walk from a new vertex to a
P-vertex stays in N until it steps into T (it cannot end in N because N is \<not>P); a walk
from an old vertex is covered by the old invariant.\<close>
lemma closed_walk_invar_0_ind:
  assumes clo: "\<And>v w. v \<in> N \<Longrightarrow> (v, w) \<in> dG \<Longrightarrow> w \<in> T \<union> N \<union> V0"
      and nP:  "\<And>v. v \<in> N \<union> V0 \<Longrightarrow> \<not> P v"
      and old: "invar_0 dG P T V0"
  shows "invar_0 dG P T (V0 \<union> N)"
  unfolding invar_0_def
proof (intro ballI allI impI)
  have key: "set p \<inter> T \<noteq> {}"
    if "v \<in> V0 \<union> N" "p \<noteq> []" "dpath_bet dG (v # p) v v'" "P v'" for v p v'
    using that
  proof (induction p arbitrary: v v' rule: length_induct)
    case (1 p)
    show ?case
    proof (cases "v \<in> N")
      case False
      hence "v \<in> V0" using 1(2) by simp
      thus ?thesis using old 1(3,4,5) unfolding invar_0_def by blast
    next
      case vN: True
      obtain a as where p_eq: "p = a # as" using 1(3) by (cases p) auto
      have "dpath dG (v # a # as)" using 1(4) p_eq by (auto simp: vwalk_bet_def)
      hence edge: "(v, a) \<in> dG" by (rule dpath_cons)
      hence aTN: "a \<in> T \<union> N \<union> V0" using clo vN by blast
      show ?thesis
      proof (cases "a \<in> T")
        case True
        thus ?thesis using p_eq by auto
      next
        case aT: False
        show ?thesis
        proof (cases "as = []")
          case True
          have av': "a = v'" using 1(4) p_eq True by (auto simp: last_of_dpath_bet vwalk_bet_def)
          have "a \<in> N \<union> V0" using aTN aT by simp
          hence "\<not> P a" using nP by simp
          thus ?thesis using 1(5) av' by simp
        next
          case asne: False
          have suf: "dpath_bet dG (a # as) a v'"
            using 1(4) p_eq by (auto intro: split_dpath[where ?p1.0 = "[v]" and ?v1.0 = a])
          have "set as \<inter> T \<noteq> {}"
          proof (cases "a \<in> N")
            case True
            show ?thesis using 1(1) p_eq asne True suf 1(5) by fastforce
          next
            case False
            hence "a \<in> V0" using aTN aT by simp
            thus ?thesis using old asne suf 1(5) unfolding invar_0_def by blast
          qed
          thus ?thesis using p_eq by auto
        qed
      qed
    qed
  qed
  fix v v'' p
  assume a: "v \<in> V0 \<union> N" "p \<noteq> []" "dpath_bet dG (v # p) v v''" "P v''"
  show "set p \<inter> T \<noteq> {}" using key[of v p v''] a by blast
qed

lemma invar_2_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_2 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and u2eq: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note rc2 = DDFS_rec_call_2_props[OF ass]
  note DFS_call_2_props = DFS_call_2_some_props[OF rc2(5)]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF assms(4)] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF assms(4)] .
  have ivA: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(9)] rc2(3) by simp
  have ivV: "vset_inv visited1" using invar_12_props_impl[OF assms(10)] by simp
  have dV: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(11)] by simp
  have u12: "u1 = u2" using rc2(1) .
  have pne: "p \<noteq> []" using IDFS_sound(7)[OF ivA ivV dA dV pw dst DFS_call_2_props] .
  have p_eq: "u1_new # p1_new = p" using rc2(6,7) pne by simp
  have p2nw: "p2'_new = []" "p2_new = p2' @ p2" using rc2(3,4) by auto
  have lvl: "level u1_new \<le> level u1"
    using IDFS_sound(8)[OF ivA ivV dA dV pw dst DFS_call_2_props] rc2(6) by simp
  let ?A = "set (u2 # p2_new)"
  let ?OLDT = "set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1)"
  let ?NEWT = "set ((u2' u2 p2'_new) # p2_new) \<union> t_set visited1_new \<union> set (u1_new # p1_new)"
  have newt_eq: "?NEWT = ?A \<union> t_set visited1_new \<union> set p"
    using p2nw p_eq by simp
  have nP: "\<And>v. v \<in> (t_set visited1_new - t_set visited1) \<union> t_set visited1 \<Longrightarrow> \<not> level_leq u1_new v"
  proof -
    fix v assume "v \<in> (t_set visited1_new - t_set visited1) \<union> t_set visited1"
    then consider (a) "v \<in> t_set visited1_new - t_set visited1" | (b) "v \<in> t_set visited1" by auto
    then show "\<not> level_leq u1_new v"
    proof cases
      case a
      hence "v \<in> t_set visited1_new" "v \<notin> t_set visited1" by auto
      hence "\<not> level_leq u1 v" using IDFS_vis_works(1)[OF ivA ivV dA dV pw dst DFS_call_2_props] by blast
      thus ?thesis using lvl by linarith
    next
      case b
      hence "level u1 < level v" using invar_10_props_impl[OF assms(8)] by blast
      thus ?thesis using lvl by linarith
    qed
  qed
  have i0old: "invar_0 dG (level_leq u1) ?OLDT (t_set visited1)"
    using assms(3)[unfolded invar_2_then_invar_0] .
  have v1sub: "t_set visited1 \<subseteq> t_set visited1_new"
    using IDFS_vis_works(3)[OF ivA ivV dA dV pw dst DFS_call_2_props] .
  have oldsub: "?OLDT \<subseteq> ?NEWT"
  proof
    fix x assume "x \<in> ?OLDT"
    then consider "x \<in> set ((u2' u2 p2') # p2)" | "x \<in> t_set visited1" | "x \<in> set (u1 # p1)" by auto
    then show "x \<in> ?NEWT"
    proof cases
      case 1
      hence "x = last (u2 # p2') \<or> x \<in> set p2" by auto
      hence "x \<in> set (u2 # p2_new)"
        using p2nw by (cases "p2' = []") auto
      thus ?thesis using newt_eq by auto
    next
      case 2 thus ?thesis using v1sub newt_eq by auto
    next
      case 3
      show ?thesis
      proof (cases "x = u1")
        case True thus ?thesis using u12 p2nw newt_eq by auto
      next
        case False
        hence xp1: "x \<in> set p1" using 3 by auto
        hence "x \<notin> set (u2 # p2_new)"
          using invar_1_props_impl[OF assms(6)] invar_6'_props_impl[OF assms(7) xp1] p2nw
          by auto
        moreover have "set (u1 # p1) - set p - set (u2 # p2_new) \<subseteq> t_set visited1_new"
          using IDFS_sound(4)[OF ivA ivV dA dV pw dst DFS_call_2_props] p2nw by simp
        ultimately have "x \<in> set p \<or> x \<in> t_set visited1_new" using xp1 3 by auto
        thus ?thesis using newt_eq by auto
      qed
    qed
  qed
  have oldB: "invar_0 dG (level_leq u1_new) ?NEWT (t_set visited1)"
  proof (rule invar_0_imp[where P' = "level_leq u1"])
    show "invar_0 dG (level_leq u1) ?NEWT (t_set visited1)"
      by (rule ivnar_0_avoid_subset[OF oldsub i0old])
  next
    fix x assume "level_leq u1_new x" thus "level_leq u1 x" using lvl by simp
  qed
  have clo: "\<And>v w. v \<in> t_set visited1_new - t_set visited1 \<Longrightarrow> (v, w) \<in> dG
                \<Longrightarrow> w \<in> ?NEWT \<union> (t_set visited1_new - t_set visited1) \<union> t_set visited1"
  proof -
    fix v w assume vN: "v \<in> t_set visited1_new - t_set visited1" and e: "(v, w) \<in> dG"
    have "w \<in> t_set (vset_of_list (u2 # p2_new)) \<union> t_set visited1_new \<union> set p"
      using IDFS_closed(2)[OF ivA ivV dA dV pw dst DFS_call_2_props vN e] p2nw by simp
    hence "w \<in> ?A \<union> t_set visited1_new \<union> set p" by simp
    thus "w \<in> ?NEWT \<union> (t_set visited1_new - t_set visited1) \<union> t_set visited1"
      using newt_eq by auto
  qed
  have "invar_0 dG (level_leq u1_new) ?NEWT (t_set visited1 \<union> (t_set visited1_new - t_set visited1))"
    by (rule closed_walk_invar_0_ind[OF clo nP oldB])
  hence "invar_0 dG (level_leq u1_new) ?NEWT (t_set visited1_new)"
    using v1sub by (simp add: Un_absorb1 sup_commute)
  hence "invar_2 (mk_st u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new)"
    unfolding invar_2_then_invar_0 by simp
  then show ?thesis by (simp add: u2eq)
qed

lemma non_zero_has_succ: "v \<in> dVs dG \<Longrightarrow> level v \<noteq> 0 \<Longrightarrow> \<exists>v'. (v, v') \<in> dG"
proof -
  assume vVs: "v \<in> dVs dG" and lev: "level v \<noteq> 0"
  obtain q v'' where q: "q \<noteq> []" "dpath_bet dG q v v''" "level v'' = 0"
    using digraph(3)[OF vVs] by blast
  have "v \<noteq> v''" using lev q(3) by auto
  then show "\<exists>v'. (v, v') \<in> dG"
    using path_then_edge[OF q(2) q(1)] by blast
qed

lemma DDFS_rec_call_3_u1_new_exists:
  assumes
   ass: "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new" "u1 \<in> dVs dG"
 shows "(u1, u1_new) \<in> dG" "level u1_new < level u1"
proof -
  have lne: "level u1 \<noteq> 0"
    using DDFS_rec_call_3_props[OF ass(1)] by auto
  show "(u1, u1_new) \<in> dG"
    using succ_works[OF ass(2) lne] DDFS_rec_call_3_props(4)[OF ass(1)] by simp
  then show "level u1_new < level u1"
    by (simp add: digraph(1))
qed

lemma invar_2_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_2 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3,4)
  have u1Vs: "u1 \<in> dVs dG" using invars(2) by (rule invar_4_then_in_Vs)
  have lt: "level u1_new < level u1"
    using DDFS_rec_call_3_u1_new_exists(2)[OF ass(1) u1Vs] .
  have pn: "p1_new = u1 # p1" using DDFS_rec_call_3_props(5)[OF ass(1)] .
  have base: "invar_0 dG (level_leq u1) (set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1)) (t_set visited1)"
    using invars(1)[unfolded invar_2_then_invar_0] .
  have sub: "set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1)
          \<subseteq> set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1_new # p1_new)"
    by (auto simp: pn)
  from ivnar_0_avoid_subset[OF sub base]
  have i0new: "invar_0 dG (level_leq u1) (set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1_new # p1_new)) (t_set visited1)" .
  have i0wk: "invar_0 dG (level_leq u1_new) (set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1_new # p1_new)) (t_set visited1)"
    using i0new by (rule invar_0_imp[where P' = "level_leq u1"]) (use lt in simp)
  show ?thesis using ass(2,3,4,5,6) i0wk
    unfolding invar_2_then_invar_0
    by simp
qed
(*READT-TODO-05 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_2_holds_3[intro]:
  assumes
   ass: "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new" "u1 \<in> dVs dG" and
   invars: "invar_2 u1 p1 visited1 u2 p2' p2"
 shows "invar_2 u1_new p1_new visited1 u2 p2' p2"
proof-
  have lt: "level u1_new < level u1"
    using DDFS_rec_call_3_u1_new_exists(2)[OF ass] .
  have pn: "p1_new = u1 # p1" using DDFS_rec_call_3_props(5)[OF ass(1)] .
  have base: "invar_0 dG (level_leq u1) (set ((u2' u2 p2') # p2) \<union> visited1 \<union> set (u1 # p1)) (visited1)"
    using invars[unfolded invar_2_then_invar_0] .
  have "set ((u2' u2 p2') # p2) \<union> visited1 \<union> set (u1 # p1)
          \<subseteq> set ((u2' u2 p2') # p2) \<union> visited1 \<union> set (u1_new # p1_new)"
    by (auto simp: pn)
  from ivnar_0_avoid_subset[OF this base]
  have "invar_0 dG (level_leq u1) (set ((u2' u2 p2') # p2) \<union> visited1 \<union> set (u1_new # p1_new)) (visited1)" .
  hence "invar_0 dG (level_leq u1_new) (set ((u2' u2 p2') # p2) \<union> visited1 \<union> set (u1_new # p1_new)) (visited1)"
    by (rule invar_0_imp[where P' = "level_leq u1"]) (use lt in simp)
  then show ?thesis
    by (simp add: invar_2_then_invar_0)
qed
*)


lemma DDFS_rec_call_4_u2_new_exists:
  assumes
   ass: "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new" "u2 \<in> dVs dG"
 shows "(u2, u2_new) \<in> dG" "level u2_new < level u2"
proof -
  have lne: "level u2 \<noteq> 0"
    using DDFS_rec_call_4_props[OF ass(1)] by auto
  show "(u2, u2_new) \<in> dG"
    using succ_works[OF ass(2) lne] DDFS_rec_call_4_props(4)[OF ass(1)] by simp
  then show "level u2_new < level u2"
    by (simp add: digraph(1))
qed

lemma invar_2_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_2 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_4_bridge_7[OF assms(1,2)]
  have u2Vs: "u2 \<in> dVs dG" using assms(4) by (rule invar_5_then_in_Vs)
  show ?thesis
    using assms(3) DDFS_rec_call_4_props(3,5)[OF ass(1)] ass(2,3,4,5)
    unfolding invar_2_def
    by auto
qed

lemma invar_2_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_2 (mk_st u1 p1 visited1_new u2 [] (p2' @ p2) visited2_new)"
proof -
  note call_2_none = assms(3)
  have pw: "dpath dG (rev (u1 # p1))"
    using invar_4_props_impl[OF assms(5)] .
  have dst: "distinct (u1 # p1)"
    using invar_4_distinct[OF assms(5)] .
  have vi1: "vset_inv visited1"
    using invar_12_props_impl[OF assms(8)] by simp
  have ivA: "vset_inv (vset_of_list (u2 # p2' @ p2))" by simp
  have dA: "t_set (vset_of_list (u2 # p2' @ p2)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(7)] by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(9)] by simp
  let ?A = "set (u2 # p2' @ p2)"
  let ?NEWT = "set ((u2' u2 []) # (p2' @ p2)) \<union> t_set visited1_new \<union> set (u1 # p1)"
  have newt_eq: "?NEWT = ?A \<union> t_set visited1_new \<union> set (u1 # p1)"
    by simp
  have nP: "\<And>v. v \<in> (t_set visited1_new - t_set visited1) \<union> t_set visited1 \<Longrightarrow> \<not> level_leq u1 v"
  proof -
    fix v assume "v \<in> (t_set visited1_new - t_set visited1) \<union> t_set visited1"
    then consider "v \<in> t_set visited1_new - t_set visited1" | "v \<in> t_set visited1" by auto
    then show "\<not> level_leq u1 v"
    proof cases
      case 1 thus ?thesis using IDFS_vis_works(1)[OF ivA vi1 dA dV1 pw dst call_2_none] by blast
    next
      case 2
      hence "level u1 < level v" using invar_10_props_impl[OF assms(6)] by blast
      thus ?thesis by (simp add: not_le)
    qed
  qed
  have i0old: "invar_0 dG (level_leq u1)
                 (set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1)) (t_set visited1)"
    using assms(4)[unfolded invar_2_then_invar_0] .
  have v1sub: "t_set visited1 \<subseteq> t_set visited1_new"
    using IDFS_vis_works(3)[OF ivA vi1 dA dV1 pw dst call_2_none] .
  have lastin: "last (u2 # p2') \<in> ?A"
    by (cases "p2' = []") auto
  have oldsub: "set ((u2' u2 p2') # p2) \<union> t_set visited1 \<union> set (u1 # p1) \<subseteq> ?NEWT"
    using v1sub lastin by (auto simp: newt_eq)
  have oldB: "invar_0 dG (level_leq u1) ?NEWT (t_set visited1)"
    by (rule ivnar_0_avoid_subset[OF oldsub i0old])
  have clo: "\<And>v w. v \<in> t_set visited1_new - t_set visited1 \<Longrightarrow> (v, w) \<in> dG
                \<Longrightarrow> w \<in> ?NEWT \<union> (t_set visited1_new - t_set visited1) \<union> t_set visited1"
  proof -
    fix v w assume vN: "v \<in> t_set visited1_new - t_set visited1" and e: "(v, w) \<in> dG"
    have "w \<in> t_set (vset_of_list (u2 # p2' @ p2)) \<union> t_set visited1_new"
      using IDFS_closed(1)[OF ivA vi1 dA dV1 pw dst call_2_none vN e] .
    hence "w \<in> ?A \<union> t_set visited1_new" by simp
    thus "w \<in> ?NEWT \<union> (t_set visited1_new - t_set visited1) \<union> t_set visited1"
      using newt_eq by auto
  qed
  have "invar_0 dG (level_leq u1) ?NEWT (t_set visited1 \<union> (t_set visited1_new - t_set visited1))"
    by (rule closed_walk_invar_0_ind[OF clo nP oldB])
  hence "invar_0 dG (level_leq u1) ?NEWT (t_set visited1_new)"
    using v1sub by (simp add: Un_absorb1 sup_commute)
  then show ?thesis
    unfolding invar_2_then_invar_0 by simp
qed

lemma invar_2_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma invar_3_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_3 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note rc1 = DDFS_rec_call_1_props[OF ass]
  note DFS_call_1_props = DFS_call_1_some_props[OF rc1(2)]
  have pw: "dpath dG (rev (u2 # p2'))"
    using invar_5_props'[OF assms(4)] .
  have dst: "distinct (u2 # p2')"
    using invar_5_distinct[OF assms(4)] by simp
  have vi1: "vset_inv visited1"
    using invar_12_props_impl[OF assms(7)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(8)] invar_14_props_impl[OF assms(10)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have ivV: "vset_inv visited2" using invar_13_props_impl[OF assms(9)] by simp
  have dV: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(11)] by simp
  have u2n: "u2_new = hd p" and p2n: "p2'_new = tl p" using rc1(3,4) by auto
  have pne: "p \<noteq> []"
    using IDFS_sound(7)[OF ivA ivV dA dV pw dst DFS_call_1_props] .
  have p_eq: "u2_new # p2'_new = p"
    using u2n p2n pne by simp
  have lvl: "level u2_new \<le> level u2"
    using IDFS_sound(8)[OF ivA ivV dA dV pw dst DFS_call_1_props] u2n by simp
  let ?A = "set (u1 # p1) \<union> t_set visited1"
  let ?OLDT = "?A \<union> set (u2 # p2' @ p2)"
  let ?NEWT = "?A \<union> set (u2_new # p2'_new @ p2)"
  let ?BIGT = "?OLDT \<union> set p"
  have nP: "\<And>v. v \<in> (t_set visited2_new - t_set visited2) \<union> t_set visited2 \<Longrightarrow> \<not> level_leq u2_new v"
  proof -
    fix v assume "v \<in> (t_set visited2_new - t_set visited2) \<union> t_set visited2"
    then consider (a) "v \<in> t_set visited2_new - t_set visited2" | (b) "v \<in> t_set visited2" by auto
    then show "\<not> level_leq u2_new v"
    proof cases
      case a
      hence "\<not> level_leq u2 v" using IDFS_vis_works(1)[OF ivA ivV dA dV pw dst DFS_call_1_props] by blast
      thus ?thesis using lvl by linarith
    next
      case b
      hence "level u2 < level v" using invar_11_props_impl[OF assms(6)] by blast
      thus ?thesis using lvl by (simp add: not_le)
    qed
  qed
  have i0old: "invar_0 dG (level_leq u2) ?OLDT (t_set visited2)"
    using assms(3)[unfolded invar_3_then_invar_0] .
  have oldB: "invar_0 dG (level_leq u2_new) ?BIGT (t_set visited2)"
  proof (rule invar_0_imp[where P' = "level_leq u2"])
    show "invar_0 dG (level_leq u2) ?BIGT (t_set visited2)"
      by (rule ivnar_0_avoid_subset[OF _ i0old]) auto
  next
    fix x assume "level_leq u2_new x" thus "level_leq u2 x" using lvl by simp
  qed
  have clo: "\<And>v w. v \<in> t_set visited2_new - t_set visited2 \<Longrightarrow> (v, w) \<in> dG
                \<Longrightarrow> w \<in> ?BIGT \<union> (t_set visited2_new - t_set visited2) \<union> t_set visited2"
  proof -
    fix v w assume vN: "v \<in> t_set visited2_new - t_set visited2" and e: "(v, w) \<in> dG"
    have "w \<in> t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<union> t_set visited2_new \<union> set p"
      using IDFS_closed(2)[OF ivA ivV dA dV pw dst DFS_call_1_props vN e] .
    hence "w \<in> ?A \<union> t_set visited2_new \<union> set p"
      by (simp add: vi1)
    thus "w \<in> ?BIGT \<union> (t_set visited2_new - t_set visited2) \<union> t_set visited2" by auto
  qed
  have combB: "invar_0 dG (level_leq u2_new) ?BIGT (t_set visited2 \<union> (t_set visited2_new - t_set visited2))"
    by (rule closed_walk_invar_0_ind[OF clo nP oldB])
  have vsub: "t_set visited2 \<subseteq> t_set visited2_new"
    using IDFS_vis_works(3)[OF ivA ivV dA dV pw dst DFS_call_1_props] .
  hence combB': "invar_0 dG (level_leq u2_new) ?BIGT (t_set visited2_new)"
    using combB by (simp add: Un_absorb1 sup_commute)
  have Wsub: "set (u2 # p2') - ?NEWT \<subseteq> t_set visited2_new"
  proof -
    have "set (u2 # p2') - set p - ?A \<subseteq> t_set visited2_new"
      using IDFS_sound(4)[OF ivA ivV dA dV pw dst DFS_call_1_props] vi1 by auto
    moreover have "set p \<subseteq> ?NEWT" using p_eq by auto
    ultimately show ?thesis by auto
  qed
  have WnP: "\<forall>w\<in> set (u2 # p2') - ?NEWT. \<not> level_leq u2_new w"
  proof
    fix w assume w: "w \<in> set (u2 # p2') - ?NEWT"
    show "\<not> level_leq u2_new w"
    proof (cases "w = u2")
      case True
      have u2A: "u2 \<notin> ?A" using True w by auto
      have u2p: "u2 \<notin> set p" using True w p_eq by auto
      have u2in2: "u2 \<in> t_set visited2_new"
        using IDFS_sound(4)[OF ivA ivV dA dV pw dst DFS_call_1_props] vi1 u2A u2p by auto
      then have "u2 \<in> t_set visited2_new - t_set visited2 \<or> u2 \<in> t_set visited2" by auto
      then have False
      proof
        assume "u2 \<in> t_set visited2_new - t_set visited2"
        then have "\<not> level_leq u2 u2"
          using IDFS_vis_works(1)[OF ivA ivV dA dV pw dst DFS_call_1_props] by blast
        thus False by simp
      next
        assume "u2 \<in> t_set visited2"
        then have "level u2 < level u2"
          using invar_11_props_impl[OF assms(6)] by blast
        thus False by simp
      qed
      thus ?thesis ..
    next
      case False
      hence "w \<in> set p2'" using w by auto
      hence "level u2 < level w" using invar_7_props_impl[OF assms(5)] by simp
      thus ?thesis using lvl by simp
    qed
  qed
  have "?BIGT = ?NEWT \<union> (set (u2 # p2') - ?NEWT)"
    using p_eq by auto
  hence "invar_0 dG (level_leq u2_new) ?NEWT (t_set visited2_new)"
    using invar_0_absorb[OF _ Wsub WnP] combB' by simp
  hence "invar_3 (mk_st u1 p1 visited1 u2_new p2'_new p2 visited2_new)"
    unfolding invar_3_then_invar_0 by simp
  then show ?thesis by (simp add: eqs)
qed

lemma invar_3_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_3 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and u2eq: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note rc2 = DDFS_rec_call_2_props[OF ass]
  note DFS_call_1_props = DFS_call_1_none_props[OF rc2(2)]
  note DFS_call_2_props = DFS_call_2_some_props[OF rc2(5)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF assms(6)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF assms(6)] by simp
  have pw2: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF assms(5)] .
  have dst2: "distinct (u1 # p1)" using invar_4_distinct[OF assms(5)] .
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(9)] by simp
  have vi2: "vset_inv visited2"
    using invar_13_props_impl[OF assms(10)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(5)] invar_14_props_impl[OF assms(11)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(12)] by simp
  have u12: "u1 = u2" using rc2(1) .
  have ivA3: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA3: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(6)] rc2(3) by simp
  have ivV3: "vset_inv visited1" using invar_12_props_impl[OF assms(9)] by simp
  have dV3: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(11)] by simp
  have pne: "p \<noteq> []" using IDFS_sound(7)[OF ivA3 ivV3 dA3 dV3 pw2 dst2 DFS_call_2_props] .
  have p_eq: "u1_new # p1_new = p" using rc2(6,7) pne by simp
  have p2nw: "p2'_new = []" "p2_new = p2' @ p2" using rc2(3,4) by auto
  let ?A = "set (u1 # p1) \<union> t_set visited1"
  let ?OLDT = "?A \<union> set (u2 # p2' @ p2)"
  have nP: "\<And>v. v \<in> (t_set visited2_new - t_set visited2) \<union> t_set visited2 \<Longrightarrow> \<not> level_leq u2 v"
  proof -
    fix v assume "v \<in> (t_set visited2_new - t_set visited2) \<union> t_set visited2"
    then consider "v \<in> t_set visited2_new - t_set visited2" | "v \<in> t_set visited2" by auto
    then show "\<not> level_leq u2 v"
    proof cases
      case 1 thus ?thesis using IDFS_vis_works(1)[OF ivA vi2 dA dV2 pw dst DFS_call_1_props] by blast
    next
      case 2
      hence "level u2 < level v" using invar_11_props_impl[OF assms(8)] by blast
      thus ?thesis by (simp add: not_le)
    qed
  qed
  have i0old: "invar_0 dG (level_leq u2) ?OLDT (t_set visited2)"
    using assms(3)[unfolded invar_3_then_invar_0] .
  have clo: "\<And>v w. v \<in> t_set visited2_new - t_set visited2 \<Longrightarrow> (v, w) \<in> dG
                \<Longrightarrow> w \<in> ?OLDT \<union> (t_set visited2_new - t_set visited2) \<union> t_set visited2"
  proof -
    fix v w assume vN: "v \<in> t_set visited2_new - t_set visited2" and e: "(v, w) \<in> dG"
    have "w \<in> t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<union> t_set visited2_new"
      using IDFS_closed(1)[OF ivA vi2 dA dV2 pw dst DFS_call_1_props vN e] .
    hence "w \<in> ?A \<union> t_set visited2_new" by (simp add: vi1)
    thus "w \<in> ?OLDT \<union> (t_set visited2_new - t_set visited2) \<union> t_set visited2" by auto
  qed
  have "invar_0 dG (level_leq u2) ?OLDT (t_set visited2 \<union> (t_set visited2_new - t_set visited2))"
    by (rule closed_walk_invar_0_ind[OF clo nP i0old])
  moreover have vsub: "t_set visited2 \<subseteq> t_set visited2_new"
    using IDFS_vis_works(3)[OF ivA vi2 dA dV2 pw dst DFS_call_1_props] .
  ultimately have i0nw: "invar_0 dG (level_leq u2) ?OLDT (t_set visited2_new)"
    by (simp add: Un_absorb1 sup_commute)
  have v1sub: "t_set visited1 \<subseteq> t_set visited1_new"
    using IDFS_vis_works(3)[OF ivA3 ivV3 dA3 dV3 pw2 dst2 DFS_call_2_props] .
  let ?NEWT = "set (u1_new # p1_new) \<union> t_set visited1_new \<union> set (u2 # p2'_new @ p2_new)"
  have "?OLDT \<subseteq> ?NEWT"
  proof
    fix x assume "x \<in> ?OLDT"
    then consider "x \<in> set (u1 # p1)" | "x \<in> t_set visited1" | "x \<in> set (u2 # p2' @ p2)" by auto
    then show "x \<in> ?NEWT"
    proof cases
      case 1
      show ?thesis
      proof (cases "x = u1")
        case True thus ?thesis using u12 p2nw by auto
      next
        case False
        hence xp1: "x \<in> set p1" using 1 by auto
        hence xnavoid: "x \<notin> set (u2 # p2_new)"
          using invar_1_props_impl[OF assms(4)] invar_6'_props_impl[OF assms(7) xp1] p2nw
          by auto
        have "set (u1 # p1) - set p - set (u2 # p2_new) \<subseteq> t_set visited1_new"
          using IDFS_sound(4)[OF ivA3 ivV3 dA3 dV3 pw2 dst2 DFS_call_2_props] by simp
        hence "x \<in> set p \<or> x \<in> t_set visited1_new" using xp1 xnavoid 1 by auto
        thus ?thesis using p_eq p2nw by auto
      qed
    next
      case 2 thus ?thesis using v1sub by auto
    next
      case 3 thus ?thesis using p2nw by auto
    qed
  qed
  hence "invar_0 dG (level_leq u2) ?NEWT (t_set visited2_new)"
    using ivnar_0_avoid_subset i0nw by blast
  hence "invar_3 (mk_st u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new)"
    unfolding invar_3_then_invar_0 by simp
  then show ?thesis by (simp add: u2eq)
qed

lemma invar_3_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_3 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3)
  have pn: "p1_new = u1 # p1" using DDFS_rec_call_3_props(5)[OF ass(1)] .
  have base: "invar_0 dG (level_leq u2) (set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)) (t_set visited2)"
    using invars[unfolded invar_3_then_invar_0] .
  have sub: "set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)
          \<subseteq> set (u1_new # p1_new) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)"
    by (auto simp: pn)
  from ivnar_0_avoid_subset[OF sub base]
  show ?thesis using ass(2,3,4,5,6)
    unfolding invar_3_then_invar_0
    by simp
qed
(*READT-TODO-08 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_3_holds_3[intro]:
  assumes
    ass: "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new" and
    invars: "invar_3 u1 p1 visited1 u2 p2' p2 visited2"
  shows "invar_3 u1_new p1_new visited1 u2 p2' p2 visited2"
proof -
  have pn: "p1_new = u1 # p1" using DDFS_rec_call_3_props(5)[OF ass(1)] .
  have base: "invar_0 dG (level_leq u2) (set (u1 # p1) \<union> visited1 \<union> set (u2 # p2' @ p2)) (visited2)"
    using invars[unfolded invar_3_then_invar_0] .
  have "set (u1 # p1) \<union> visited1 \<union> set (u2 # p2' @ p2)
          \<subseteq> set (u1_new # p1_new) \<union> visited1 \<union> set (u2 # p2' @ p2)"
    by (auto simp: pn)
  from ivnar_0_avoid_subset[OF this base]
  show ?thesis
    by (simp add: invar_3_then_invar_0)
qed
*)


lemma invar_3_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_3 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_4_bridge_7[OF assms(1,2)]
  note invars = assms(3,4)
  have u2Vs: "u2 \<in> dVs dG" using invars(2) by (rule invar_5_then_in_Vs)
  have lt: "level u2_new < level u2"
    using DDFS_rec_call_4_u2_new_exists(2)[OF ass(1) u2Vs] .
  have pn: "p2'_new = u2 # p2'" using DDFS_rec_call_4_props(5)[OF ass(1)] .
  have base: "invar_0 dG (level_leq u2) (set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)) (t_set visited2)"
    using invars(1)[unfolded invar_3_then_invar_0] .
  have sub: "set (u1 # p1) \<union> t_set visited1 \<union> set (u2 # p2' @ p2)
          \<subseteq> set (u1 # p1) \<union> t_set visited1 \<union> set (u2_new # p2'_new @ p2)"
    by (auto simp: pn)
  from ivnar_0_avoid_subset[OF sub base]
  have i0new: "invar_0 dG (level_leq u2) (set (u1 # p1) \<union> t_set visited1 \<union> set (u2_new # p2'_new @ p2)) (t_set visited2)" .
  have i0wk: "invar_0 dG (level_leq u2_new) (set (u1 # p1) \<union> t_set visited1 \<union> set (u2_new # p2'_new @ p2)) (t_set visited2)"
    using i0new by (rule invar_0_imp[where P' = "level_leq u2"]) (use lt in simp)
  show ?thesis using ass(2,3,4,5,6) i0wk
    unfolding invar_3_then_invar_0
    by simp
qed
(*READT-TODO-09 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_3_holds_4[intro]:
  assumes
    ass: "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new" "u2 \<in> dVs dG" and
    invars: "invar_3 u1 p1 visited1 u2 p2' p2 visited2"
  shows "invar_3 u1 p1 visited1 u2_new p2'_new p2 visited2"
proof-
  have lt: "level u2_new < level u2"
    using DDFS_rec_call_4_u2_new_exists(2)[OF ass] .
  have pn: "p2'_new = u2 # p2'" using DDFS_rec_call_4_props(5)[OF ass(1)] .
  have base: "invar_0 dG (level_leq u2) (set (u1 # p1) \<union> visited1 \<union> set (u2 # p2' @ p2)) (visited2)"
    using invars[unfolded invar_3_then_invar_0] .
  have "set (u1 # p1) \<union> visited1 \<union> set (u2 # p2' @ p2)
          \<subseteq> set (u1 # p1) \<union> visited1 \<union> set (u2_new # p2'_new @ p2)"
    by (auto simp: pn)
  from ivnar_0_avoid_subset[OF this base]
  have "invar_0 dG (level_leq u2) (set (u1 # p1) \<union> visited1 \<union> set (u2_new # p2'_new @ p2)) (visited2)" .
  hence "invar_0 dG (level_leq u2_new) (set (u1 # p1) \<union> visited1 \<union> set (u2_new # p2'_new @ p2)) (visited2)"
    by (rule invar_0_imp[where P' = "level_leq u2"]) (use lt in simp)
  then show ?thesis
    by (simp add: invar_3_then_invar_0)
qed
*)


lemma invar_3_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_3 (mk_st u1 p1 visited1_new u2 p2' p2 visited2_new)"
proof -
  note call_1_none = assms(2)
  note call_2_none = assms(3)
  have pw: "dpath dG (rev (u2 # p2'))"
    using invar_5_props'[OF assms(5)] .
  have dst: "distinct (u2 # p2')"
    using invar_5_distinct[OF assms(5)] by simp
  have pw2: "dpath dG (rev (u1 # p1))"
    using invar_4_props_impl[OF assms(7)] .
  have dst2: "distinct (u1 # p1)"
    using invar_4_distinct[OF assms(7)] .
  have vi1: "vset_inv visited1"
    using invar_12_props_impl[OF assms(8)] by simp
  have vi2: "vset_inv visited2"
    using invar_13_props_impl[OF assms(9)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(7)] invar_14_props_impl[OF assms(10)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(11)] by simp
  let ?A = "set (u1 # p1) \<union> t_set visited1"
  let ?OLDT = "?A \<union> set (u2 # p2' @ p2)"
  have nP: "\<And>v. v \<in> (t_set visited2_new - t_set visited2) \<union> t_set visited2 \<Longrightarrow> \<not> level_leq u2 v"
  proof -
    fix v assume "v \<in> (t_set visited2_new - t_set visited2) \<union> t_set visited2"
    then consider "v \<in> t_set visited2_new - t_set visited2" | "v \<in> t_set visited2" by auto
    then show "\<not> level_leq u2 v"
    proof cases
      case 1 thus ?thesis using IDFS_vis_works(1)[OF ivA vi2 dA dV2 pw dst call_1_none] by blast
    next
      case 2
      hence "level u2 < level v" using invar_11_props_impl[OF assms(6)] by blast
      thus ?thesis by (simp add: not_le)
    qed
  qed
  have i0old: "invar_0 dG (level_leq u2) ?OLDT (t_set visited2)"
    using assms(4)[unfolded invar_3_then_invar_0] .
  have clo: "\<And>v w. v \<in> t_set visited2_new - t_set visited2 \<Longrightarrow> (v, w) \<in> dG
                \<Longrightarrow> w \<in> ?OLDT \<union> (t_set visited2_new - t_set visited2) \<union> t_set visited2"
  proof -
    fix v w assume vN: "v \<in> t_set visited2_new - t_set visited2" and e: "(v, w) \<in> dG"
    have "w \<in> t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<union> t_set visited2_new"
      using IDFS_closed(1)[OF ivA vi2 dA dV2 pw dst call_1_none vN e] .
    hence "w \<in> ?A \<union> t_set visited2_new"
      by (simp add: vi1)
    thus "w \<in> ?OLDT \<union> (t_set visited2_new - t_set visited2) \<union> t_set visited2" by auto
  qed
  have "invar_0 dG (level_leq u2) ?OLDT (t_set visited2 \<union> (t_set visited2_new - t_set visited2))"
    by (rule closed_walk_invar_0_ind[OF clo nP i0old])
  moreover have "t_set visited2 \<subseteq> t_set visited2_new"
    using IDFS_vis_works(3)[OF ivA vi2 dA dV2 pw dst call_1_none] .
  ultimately have i0nw: "invar_0 dG (level_leq u2) ?OLDT (t_set visited2_new)"
    by (simp add: Un_absorb1 sup_commute)
  have ivA2: "vset_inv (vset_of_list (u2 # p2' @ p2))" by simp
  have dA2: "t_set (vset_of_list (u2 # p2' @ p2)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(5)] by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(10)] by simp
  have "t_set visited1 \<subseteq> t_set visited1_new"
    using IDFS_vis_works(3)[OF ivA2 vi1 dA2 dV1 pw2 dst2 call_2_none] .
  hence "?OLDT \<subseteq> set (u1 # p1) \<union> t_set visited1_new \<union> set (u2 # p2' @ p2)" by auto
  hence "invar_0 dG (level_leq u2)
           (set (u1 # p1) \<union> t_set visited1_new \<union> set (u2 # p2' @ p2)) (t_set visited2_new)"
    using ivnar_0_avoid_subset i0nw by blast
  thus ?thesis
    unfolding invar_3_then_invar_0 by simp
qed

lemma invar_3_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2);
    invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

definition "invar_8 st \<equiv> set (done2 st) - (set (curr1 st # stack1 st) \<union> t_set (vis1 st)) \<subseteq> t_set (vis2 st)"

lemma invar_8_mk[simp]:
  "invar_8 (mk_st u1 p1 v1 u2 p2' p2 v2) = (set p2 - (set (u1 # p1) \<union> t_set v1) \<subseteq> t_set v2)"
  by (simp add: invar_8_def)

lemma invar_8_props_impl:
  "invar_8 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow> set p2 - (set (u1 # p1) \<union> t_set v1) \<subseteq> t_set v2"
  by (simp add: invar_8_def)

lemma invar_8_props[invar_props_elims]:
  "invar_8 (mk_st u1 p1 v1 u2 p2' p2 v2) \<Longrightarrow>
   ((set p2 - (set (u1 # p1) \<union> t_set v1) \<subseteq> t_set v2) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_8_def)

lemma invar_8_intro[invar_props_intros]:
  "set p2 - (set (u1 # p1) \<union> t_set v1) \<subseteq> t_set v2 \<Longrightarrow> invar_8 (mk_st u1 p1 v1 u2 p2' p2 v2)"
  by (auto simp: invar_8_def)

lemma invar_8_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_8 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF assms(4)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF assms(4)] by simp
  note call_1_some = DFS_call_1_some_props[OF DDFS_rec_call_1_props(2)[OF ass]]
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(5)] invar_14_props_impl[OF assms(8)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have ivV: "vset_inv visited2" using invar_13_props_impl[OF assms(7)] by simp
  have dV: "t_set visited2 \<subseteq> dVs dG" using invar_15_props_impl[OF assms(9)] by simp
  have vsub: "t_set visited2 \<subseteq> t_set visited2_new"
    using IDFS_vis_works(3)[OF ivA ivV dA dV pw dst call_1_some] .
  thus ?thesis using assms(3) eqs vsub by (fastforce simp add: invar_8_def)
qed
(*READT-TODO-11 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_8_holds_1[intro]:
  assumes
   ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p" and
   invars: "invar_8 u1 p1 visited1 p2 visited2" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "invar_8 u1 p1 visited1 p2 visited2_new"
proof -

  note rec_call_1[simp] = DDFS_rec_call_1_props[OF ass] and
       call_1_some = DFS_call_1_some_props[OF rec_call_1(2)]

  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
  show ?thesis
    using invars IDFS_vis_works(3)[OF pw dst call_1_some]
    by(fastforce simp add: invar_8_def)
qed
*)

lemma invar_8_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_8 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note rec_call_2 = DDFS_rec_call_2_props[OF ass] and
       call_1_none = DFS_call_1_none_props[OF DDFS_rec_call_2_props(2)[OF ass]] and
       call_2_some = DFS_call_2_some_props[OF DDFS_rec_call_2_props(5)[OF ass]]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF assms(5)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF assms(5)] by simp
  have pw2: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF assms(8)] .
  have dst2: "distinct (u1 # p1)" using invar_4_distinct[OF assms(8)] .
  have vis1_inv: "vset_inv visited1" using assms(9) by simp
  have u12: "u1 = u2" using rec_call_2(1) .
  have p2n: "p2_new = p2' @ p2" using rec_call_2(3) .
  have p2n2: "p2'_new = []" using rec_call_2(4) .
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(10)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vis1_inv by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(8)] invar_14_props_impl[OF assms(11)] vis1_inv
    by (auto simp: t_set_vset_of_list_union)
  have dV: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(12)] by simp
  have v2sub: "t_set visited2 \<subseteq> t_set visited2_new"
    using IDFS_vis_works(3)[OF ivA vi2 dA dV pw dst call_1_none] .
  have ivA2: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA2: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(5)] rec_call_2(3) by simp
  have dV_1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(11)] by simp
  have v1sub: "t_set visited1 \<subseteq> t_set visited1_new"
    using IDFS_vis_works(3)[OF ivA2 vis1_inv dA2 dV_1 pw2 dst2 call_2_some] .
  have p2_cov: "set p2 - (set (u1 # p1) \<union> t_set visited1) \<subseteq> t_set visited2"
    using assms(3) by (simp add: invar_8_def)
  have p2'_cov: "set (u2 # p2') - t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> t_set visited2_new"
    using IDFS_complete[OF ivA vi2 dA dV pw dst call_1_none] .
  have p2n_cov: "set p2_new - (set (u1 # p1) \<union> t_set visited1) \<subseteq> t_set visited2_new"
    using p2_cov v2sub p2'_cov p2n
    by (auto simp: t_set_vset_of_list_union[OF vis1_inv])
  have u1np2: "u1 \<notin> set p2_new"
    using u12 assms(7) p2n by (auto simp: invar_7_def)
  have p1np2: "set p1 \<inter> set p2_new = {}"
    using assms(4) p2n by (auto simp: invar_1_def)
  show ?thesis
  proof (rule invar_8_intro)
    show "set p2_new - (set (u1_new # p1_new) \<union> t_set visited1_new) \<subseteq> t_set visited2_new"
    proof
      fix x assume xh: "x \<in> set p2_new - (set (u1_new # p1_new) \<union> t_set visited1_new)"
      have xp2: "x \<in> set p2_new" using xh by auto
      have xnv: "x \<notin> t_set visited1_new" using xh by auto
      have xnv1: "x \<notin> t_set visited1" using xnv v1sub by auto
      have xnp: "x \<notin> set (u1 # p1)" using xp2 u1np2 p1np2 by auto
      have "x \<in> set p2_new - (set (u1 # p1) \<union> t_set visited1)"
        using xp2 xnv1 xnp by auto
      thus "x \<in> t_set visited2_new" using p2n_cov by auto
    qed
  qed
qed
(*READT-TODO-12 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_8_holds_2[intro]:
  assumes
   ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p" and
   invars: "invar_8 u1 p1 visited1 p2 visited2" "invar_1 p1 visited1 p2' p2"
           "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6' p1 u2" "invar_7 u2 p2' p2" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "invar_8 u1_new p1_new visited1_new p2_new visited2_new"
proof -
  note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
       call_1_none = DFS_call_1_none_props[OF rec_call_2(2)] and
       call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
  have pw2: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst2: "distinct (u1 # p1)" using invar_4_distinct[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have u12: "u1 = u2" using rec_call_2(1) .
  have p2n: "p2_new = p2' @ p2" using rec_call_2(3) .
  have "set p2 - (set (u1 # p1) \<union> visited1) \<subseteq> visited2"
    using invar_8_props_impl[OF \<open>invar_8 u1 p1 visited1 p2 visited2\<close>] .
  moreover have "visited2 \<subseteq> visited2_new"
    using IDFS_vis_works(3)[OF pw dst call_1_none] .
  ultimately have "set p2 - (set (u1 # p1) \<union> visited1) \<subseteq> visited2_new"
    by auto
  moreover have "set (u2 # p2') - (set (u1 # p1) \<union> visited1) \<subseteq> visited2_new"
    using IDFS_complete[OF pw dst call_1_none] by auto
  ultimately have p2new_cov: "set p2_new - (set (u1 # p1) \<union> visited1) \<subseteq> visited2_new"
    using p2n by auto
  have v1sub: "visited1 \<subseteq> visited1_new"
    using IDFS_vis_works(3)[OF pw2 dst2 call_2_some] .
  have u1np2: "u1 \<notin> set p2_new"
    using u12 \<open>invar_7 u2 p2' p2\<close> p2n by (auto simp: invar_7_def)
  have p1np2: "set p1 \<inter> set p2_new = {}"
    using \<open>invar_1 p1 visited1 p2' p2\<close> p2n by (auto simp: invar_1_def)
  show ?thesis
    unfolding invar_8_def
  proof
    fix x assume x: "x \<in> set p2_new - (set (u1_new # p1_new) \<union> visited1_new)"
    have "x \<notin> set (u1 # p1)"
      using x u1np2 p1np2 by auto
    hence "x \<in> set p2_new - (set (u1 # p1) \<union> visited1)"
      using x v1sub by auto
    thus "x \<in> visited2_new" using p2new_cov by auto
  qed
qed
*)

lemma invar_8_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_8 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3)
  note rec_call_3[simp] = DDFS_rec_call_3_props[OF ass(1)]
  show ?thesis
    using invars ass(2,4,5,6)
    unfolding invar_8_def
    by auto
qed

lemma invar_8_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_8 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_4_bridge_7[OF assms(1,2)] by simp

lemma invar_8_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2_new)"
proof -
  note ret_1 = DDFS_ret_1_props[OF DDFS_ret_1_bridge_7[OF assms(1,2,3)]]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF assms(5)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF assms(5)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(7)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(6)] invar_14_props_impl[OF assms(9)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have ivV: "vset_inv visited2" using invar_13_props_impl[OF assms(8)] by simp
  have dV: "t_set visited2 \<subseteq> dVs dG" using invar_15_props_impl[OF assms(10)] by simp
  have vsub: "t_set visited2 \<subseteq> t_set visited2_new"
    using IDFS_vis_works(3)[OF ivA ivV dA dV pw dst DFS_call_1_none_props[OF ret_1(4)]] .
  thus ?thesis using assms(4) by (fastforce simp add: invar_8_def)
qed
(*READT-TODO-13 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_8_ret_1[intro]:
  assumes ass: "DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new p2_new p2'_new visited2_new" and
   invars: "invar_8 u1 p1 visited1 p2 visited2" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "invar_8 u1 p1 visited1 p2 visited2_new"
proof-

  note ret_1[simp] = DDFS_ret_1_props[OF ass] and
       call_1_none = DFS_call_1_none_props[OF ret_1(4)] and
       call_2_none = DFS_call_2_none_props[OF ret_1(5)]
  
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
  show ?thesis
    using IDFS_vis_works(3)[OF pw dst call_1_none] invars
    by (simp add: invar_8_def)
qed
*)

lemma invar_8_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2);
    invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma DDFS_val_rec_1:
  assumes
   in_dom: "DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)" and
   ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
 shows "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = DDFS (mk_st u1 p1 visited1 u2_new p2'_new p2 visited2_new)"
  using DDFS.psimps[OF in_dom] ass
  by (auto simp: DDFS_rec_call_1_def DFS_call_1_some_def Let_def
           split: if_splits prod.splits option.splits)

lemma DDFS_val_rec_1_last_p:
  assumes
   ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
   and inv5: "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
   and inv4: "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
   and inv12: "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
   and inv13: "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
   and inv14: "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
   and inv15: "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "last (u2 # p2' @ p2) = last (u2_new # p2'_new @ p2)"
proof (cases "p2 = []")
  case True
  then show ?thesis
    using DDFS_rec_call_1_last_p_same[OF ass inv5 inv4 inv12 inv13 inv14 inv15] by simp
next
  case False
  then have "last (u2 # p2' @ p2) = last p2" "last (u2_new # p2'_new @ p2) = last p2"
    by (simp_all add: last_appendR)
  then show ?thesis by simp
qed

lemma DDFS_val_rec_2:
  assumes
   in_dom: "DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)" and
   ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
 shows "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = DDFS (mk_st u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new)"
  using DDFS.psimps[OF in_dom] ass
  by (auto simp: DDFS_rec_call_2_def DFS_call_2_some_def DFS_call_1_none_def Let_def
            split: if_splits prod.splits option.splits)

lemma DDFS_val_rec_2_last_p:
  assumes ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
          and inv4: "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          and inv5: "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          and inv12: "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          and inv14: "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "last (u2 # p2' @ p2) = last (u2 # p2'_new @ p2_new)" (is ?g1)
        "last (u1 # p1) = last (u1_new # p1_new)" (is ?g2)
proof-
  show ?g1
    using DDFS_rec_call_2_props[OF ass]
    by auto
  note rc2 = DDFS_rec_call_2_props[OF ass]
  note call_2_some = DFS_call_2_some_props[OF rc2(5)]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF inv4] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF inv4] .
  have ivA2: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA2: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF inv5] rc2(3) by simp
  have ivV2: "vset_inv visited1" using invar_12_props_impl[OF inv12] by simp
  have dV2: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF inv14] by simp
  have pne_in: "u1 # p1 \<noteq> []" by simp
  have "last (u1 # p1) = last p"
    using IDFS_sound(6)[OF ivA2 ivV2 dA2 dV2 pw dst call_2_some pne_in] .
  moreover have "p \<noteq> []"
    using IDFS_sound(7)[OF ivA2 ivV2 dA2 dV2 pw dst call_2_some] .
  hence "u2' u1_new p1_new = last p"
    using DDFS_rec_call_2_props(6,7)[OF ass(1)]
    by fastforce
  ultimately show "u2' u1 p1 = u2' u1_new p1_new"
    by auto
qed

lemma DDFS_val_rec_3:
  assumes
    in_dom: "DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)" and
    ass: "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new"
 shows "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = DDFS (mk_st u1_new p1_new visited1 u2 p2' p2 visited2)"
  using DDFS.psimps[OF in_dom] ass
  by (auto simp: DDFS_rec_call_3_def
           split: if_splits prod.splits option.splits)

lemma DDFS_val_rec_3_last_p:
  assumes ass: "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new"
  shows "last (u1 # p1) = last (u1_new # p1_new)"
  using DDFS_rec_call_3_props[OF ass]
  by auto

lemma DDFS_val_rec_4:
  assumes
    in_dom: "DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)" and
    ass: "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new"
 shows "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = DDFS (mk_st u1 p1 visited1 u2_new p2'_new p2 visited2)"
  using DDFS.psimps[OF in_dom] ass
  by (auto simp: DDFS_rec_call_4_def
           split: if_splits prod.splits option.splits)

lemma DDFS_val_rec_4_last_p:
  assumes ass: "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new"
  shows "last (u2 # p2' @ p2) = last (u2_new # p2'_new @ p2)"
  using DDFS_rec_call_4_props[OF ass]
  by auto

lemma DDFS_val_ret_1:
  assumes
    in_dom: "DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)" and
    ass: "DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new p2_new p2'_new visited2_new"
 shows "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (u1 # p1, u2 # p2_new)"
  using DDFS.psimps[OF in_dom] ass
  by (auto simp: DDFS_ret_1_def DFS_call_1_none_def DFS_call_2_none_def Let_def
           split: if_splits prod.splits option.splits)

lemma DDFS_val_ret_2:
  assumes
    in_dom: "DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)" and
    ass: "DDFS_ret_2 u1 u2"
 shows "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (u1 # p1, u2 # p2' @ p2)"
  using DDFS.psimps[OF in_dom] ass
  by (auto simp: DDFS_ret_2_def split: if_splits prod.splits option.splits)

(*lemma DDFS_ret_1_p2_visited:
  assumes ass: "DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new p2_new p2'_new visited2_new"
  shows "set (u2 # p2_new) \<subseteq> visited2_new"
  using assms
  sorry*)

lemma invar_10_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_10 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  show ?thesis using assms(3) by (simp add: eqs)
qed
  
lemma invar_10_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_10 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and u2eq: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3,4)
  note rec_call_2 = DDFS_rec_call_2_props[OF ass] and
       call_2_some = DFS_call_2_some_props[OF DDFS_rec_call_2_props(5)[OF ass]]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF invars(2)] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF invars(2)] .
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
  have ivA: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(5)] rec_call_2(3) by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(7)] by simp
  have lvl: "level u1_new \<le> level u1"
    using IDFS_sound(8)[OF ivA vi1 dA dV1 pw dst call_2_some] rec_call_2(6) by simp
  have new_vis: "v \<in> t_set visited1_new - t_set visited1 \<Longrightarrow> level v > level u1" for v
    using IDFS_vis_works(1)[OF ivA vi1 dA dV1 pw dst call_2_some]
    by (simp add: not_le_imp_less)
  have old_vis: "v \<in> t_set visited1 \<Longrightarrow> level v > level u1_new" for v
    using invar_10_props_impl[OF invars(1)] lvl by fastforce
  have sub: "t_set visited1 \<subseteq> t_set visited1_new"
    using IDFS_vis_works(3)[OF ivA vi1 dA dV1 pw dst call_2_some] .
  show ?thesis
    using new_vis old_vis sub lvl rec_call_2(6)
    by (fastforce simp: invar_10_def invar_10_mk)
qed
(*READT-TODO-14 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_10_holds_2[intro]:
  assumes ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p" and
   invars: "invar_10 u1 visited1" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "invar_10 u1_new visited1_new"
proof-
  note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
       call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have "v \<in> visited1_new - visited1 \<Longrightarrow> level u1 < level v" for v
    using IDFS_vis_works(1)[OF pw dst call_2_some]
    by (simp add: not_le_imp_less)
  moreover have "level u1_new \<le> level u1"
    using IDFS_sound(8)[OF pw dst call_2_some]
    by simp
  ultimately have "v \<in> visited1_new - visited1 \<Longrightarrow> level u1_new < level v" for v
    by fastforce
  moreover have "v \<in> visited1 \<Longrightarrow> level u1_new < level v" for v
    using \<open>level u1_new \<le> level u1\<close> invar_10_props_impl[OF \<open>invar_10 u1 visited1\<close>]
    by fastforce
  moreover have "visited1 \<union> (visited1_new - visited1) = visited1_new"
    using IDFS_vis_works(3)[OF pw dst call_2_some] by auto
  ultimately show ?thesis
    unfolding invar_10_def
    by auto
qed
*)

lemma invar_10_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_10 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_3_bridge_7[OF assms(1,2)]
  note invars = assms(3,4)
  have "u1 \<in> dVs dG"
    using invar_4_then_in_Vs[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>].
  hence "(u1, u1_new) \<in> dG"
    using DDFS_rec_call_3_valid_edge[OF ass(1)]
    by auto
  hence "level u1_new < level u1"
    using digraph
    by simp
  then show ?thesis
    using invars ass(2)
    by (fastforce simp: invar_10_def invar_10_mk)
qed

lemma invar_10_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_10 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_4_bridge_7[OF assms(1,2)] by simp

lemma invar_10_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_10 (mk_st u1 p1 visited1_new u2 p2' p2 visited2)"
proof -
  note ret_1 = DDFS_ret_1_props[OF DDFS_ret_1_bridge_7[OF assms(1,2,3)]]
  note invars = assms(4,5)
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
  have ivA: "vset_inv (vset_of_list (u2 # p2' @ p2))" by simp
  have dA: "t_set (vset_of_list (u2 # p2' @ p2)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(7)] by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(8)] by simp
  note call_2_none = DFS_call_2_none_props[OF ret_1(5)]
  show ?thesis
    using IDFS_vis_works(1)[OF ivA vi1 dA dV1 pw dst call_2_none] invar_10_props_impl[OF invars(1)]
    by (force simp: invar_10_def invar_10_mk)
qed

lemma invar_10_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma invar_11_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_11 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note invars = assms(3,4)
  note rec_call_1 = DDFS_rec_call_1_props[OF ass] and
       call_1_some = DFS_call_1_some_props[OF DDFS_rec_call_1_props(2)[OF ass]]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars(2)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars(2)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(7)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(5)] invar_14_props_impl[OF assms(8)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(9)] by simp
  have lvl: "level u2_new \<le> level u2"
    using IDFS_sound(8)[OF ivA vi2 dA dV2 pw dst call_1_some] rec_call_1(3) by simp
  have new_vis: "v \<in> t_set visited2_new - t_set visited2 \<Longrightarrow> level v > level u2" for v
    using IDFS_vis_works(1)[OF ivA vi2 dA dV2 pw dst call_1_some]
    by (simp add: not_le_imp_less)
  have old_vis: "v \<in> t_set visited2 \<Longrightarrow> level v > level u2_new" for v
    using invar_11_props_impl[OF invars(1)] lvl by fastforce
  have sub: "t_set visited2 \<subseteq> t_set visited2_new"
    using IDFS_vis_works(3)[OF ivA vi2 dA dV2 pw dst call_1_some] .
  show ?thesis
    using new_vis old_vis sub lvl rec_call_1(3)
    by (fastforce simp: invar_11_def)
qed
(*READT-TODO-15 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_11_holds_1[intro]:
  assumes
   ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p" and
   invars: "invar_11 u2 visited2" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "invar_11 u2_new visited2_new"
proof-
  note rec_call_1[simp] = DDFS_rec_call_1_props[OF ass] and
       call_1_some = DFS_call_1_some_props[OF rec_call_1(2)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
  have "v \<in> visited2_new - visited2 \<Longrightarrow> level u2 < level v" for v
    using IDFS_vis_works(1)[OF pw dst call_1_some]
    by (simp add: not_le_imp_less)
  moreover have "level u2_new \<le> level u2"
    using IDFS_sound(8)[OF pw dst call_1_some]
    by simp
  ultimately have "v \<in> visited2_new - visited2 \<Longrightarrow> level u2_new < level v" for v
    by fastforce
  moreover have "v \<in> visited2 \<Longrightarrow> level u2_new < level v" for v
    using \<open>level u2_new \<le> level u2\<close> invar_11_props_impl[OF \<open>invar_11 u2 visited2\<close>]
    by fastforce
  moreover have "visited2 \<union> (visited2_new - visited2) = visited2_new"
    using IDFS_vis_works(3)[OF pw dst call_1_some] by auto
  ultimately show ?thesis
    unfolding invar_11_def
    by auto
qed
*)

lemma invar_11_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_11 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and u2eq: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3,4)
  note rec_call_2 = DDFS_rec_call_2_props[OF ass] and
       call_1_none = DFS_call_1_none_props[OF DDFS_rec_call_2_props(2)[OF ass]]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars(2)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars(2)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(7)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(5)] invar_14_props_impl[OF assms(8)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(9)] by simp
  have new_vis: "v \<in> t_set visited2_new - t_set visited2 \<Longrightarrow> level v > level u2" for v
    using IDFS_vis_works(1)[OF ivA vi2 dA dV2 pw dst call_1_none]
    by (simp add: not_le_imp_less)
  have old_vis: "v \<in> t_set visited2 \<Longrightarrow> level v > level u2" for v
    using invar_11_props_impl[OF invars(1)] .
  have sub: "t_set visited2 \<subseteq> t_set visited2_new"
    using IDFS_vis_works(3)[OF ivA vi2 dA dV2 pw dst call_1_none] .
  show ?thesis
    using new_vis old_vis sub u2eq
    by (fastforce simp: invar_11_def)
qed
(*READT-TODO-16 ORIGINAL (HOL-set form, pre-ADT statement+proof):
lemma invar_11_holds_2[intro]:
  assumes ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p" and
   invars: "invar_11 u2 visited2" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "invar_11 u2 visited2_new"
proof-
  note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
       call_1_none = DFS_call_1_none_props[OF rec_call_2(2)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
  have "v \<in> visited2_new - visited2 \<Longrightarrow> level u2 < level v" for v
    using IDFS_vis_works(1)[OF pw dst call_1_none]
    by (simp add: not_le_imp_less)
  moreover have "v \<in> visited2 \<Longrightarrow> level u2 < level v" for v
    using invar_11_props_impl[OF \<open>invar_11 u2 visited2\<close>].
  moreover have "visited2 \<subseteq> visited2_new"
    using IDFS_vis_works(3)[OF pw dst call_1_none] .
  ultimately show ?thesis
    by(auto simp add: invar_11_def)
qed
*)

lemma invar_11_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_11 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_3_bridge_7[OF assms(1,2)] by simp

lemma invar_11_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_11 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  note ass = DDFS_call_4_bridge_7[OF assms(1,2)]
  note invars = assms(3,4)
  have "u2 \<in> dVs dG"
    using invar_5_then_in_Vs[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>].
  hence "(u2, u2_new) \<in> dG"
    using DDFS_rec_call_4_valid_edge[OF ass(1)]
    by auto
  hence "level u2_new < level u2"
    using digraph
    by simp
  then show ?thesis
    using invars ass(6)
    by (fastforce simp: invar_11_def)
qed

lemma invar_11_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_11 (mk_st u1 p1 visited1_new u2 p2' p2 visited2_new)"
proof -
  note ret_1 = DDFS_ret_1_props[OF DDFS_ret_1_bridge_7[OF assms(1,2,3)]]
  note invars = assms(4,5)
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(7)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(8)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(6)] invar_14_props_impl[OF assms(9)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(10)] by simp
  note call_1_none = DFS_call_1_none_props[OF ret_1(4)]
  show ?thesis
    using IDFS_vis_works(1)[OF ivA vi2 dA dV2 pw dst call_1_none] invar_11_props_impl[OF invars(1)]
    by (force simp: invar_11_def)
qed

lemma invar_11_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

(*definition "invar_13 p2' p2 visited1 \<equiv> (set (p2' @ p2) \<inter> visited1 = {})"

definition "invar_13' u2 p2' p2 visited1 \<equiv> (p2' @ p2 = [] \<longrightarrow> u2 \<notin> visited1)"
(*The proof of 13' should depend on
  the deleted fifth vis-works assumption (removed 2026-07-03, unsatisfiable) and the fact that since we start at a bridge, last (u2 # p2' @ p2) cannot be
  reached from last (u1 # p1). *)

lemma invar_13_props:
  "invar_13 p2' p2 visited1 \<Longrightarrow> set (p2' @ p2) \<inter> visited1 = {}"
  unfolding invar_13_def
  by auto

lemma invar_13'_props:
  "invar_13' u2 p2' p2 visited1 \<Longrightarrow> p2' @ p2 = [] \<Longrightarrow> u2 \<notin> visited1"
  unfolding invar_13'_def
  by auto*)

(* \<midarrow>\<midarrow> invar_12 and invar_13 holds families (Phase B, plans 15/16) \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

lemma invar_12_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_12 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  show ?thesis using assms(3) by (simp add: eqs)
qed

lemma invar_12_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_12 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3,4)
  note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
       call_1_none = DFS_call_1_none_props[OF rec_call_2(2)] and
       call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF invars(2)] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF invars(2)] .
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(3)] by simp
  have ivA: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(5)] rec_call_2(3) by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(6)] by simp
  show ?thesis
    using IDFS_vis_works(4)[OF ivA vi1 dA dV1 pw dst call_2_some]
    by (auto simp add: invar_12_def)
qed

lemma invar_12_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_12 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_3_bridge_7[OF assms(1,2)] by simp

lemma invar_12_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_12 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_4_bridge_7[OF assms(1,2)] by simp

lemma invar_12_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_12 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  have pw: "dpath dG (rev (u1 # p1))"
    using assms(5) by (auto simp: invar_4_def)
  have dst: "distinct (u1 # p1)"
    using assms(5) by (rule invar_4_distinct)
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(4)] by simp
  have ivA: "vset_inv (vset_of_list (u2 # p2' @ p2))" by simp
  have dA: "t_set (vset_of_list (u2 # p2' @ p2)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(6)] by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(7)] by simp
  show ?thesis
    using IDFS_vis_works(4)[OF ivA vi1 dA dV1 pw dst assms(3)]
    by (auto intro!: invar_props_intros)
qed

lemma invar_12_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma invar_13_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_13 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note invars = assms(3,4)
  note rec_call_1[simp] = DDFS_rec_call_1_props[OF ass] and
       call_1_some = DFS_call_1_some_props[OF rec_call_1(2)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars(2)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars(2)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(3)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(5)] invar_14_props_impl[OF assms(7)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(8)] by simp
  show ?thesis
    using IDFS_vis_works(4)[OF ivA vi2 dA dV2 pw dst call_1_some]
    by (auto simp add: invar_13_def)
qed

lemma invar_13_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_13 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and eqs: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note invars = assms(3,4)
  note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
       call_1_none = DFS_call_1_none_props[OF rec_call_2(2)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF invars(2)] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF invars(2)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(3)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(5)] invar_14_props_impl[OF assms(7)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(8)] by simp
  show ?thesis
    using IDFS_vis_works(4)[OF ivA vi2 dA dV2 pw dst call_1_none]
    by (auto simp add: invar_13_def)
qed

lemma invar_13_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_13 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_3_bridge_7[OF assms(1,2)] by simp

lemma invar_13_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_13 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_4_bridge_7[OF assms(1,2)] by simp

lemma invar_13_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_13 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  have pw: "dpath dG (rev (u2 # p2'))"
    using invar_5_props'[OF assms(5)] .
  have dst: "distinct (u2 # p2')"
    using invar_5_distinct[OF assms(5)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(7)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(4)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(6)] invar_14_props_impl[OF assms(8)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(9)] by simp
  show ?thesis
    using IDFS_vis_works(4)[OF ivA vi2 dA dV2 pw dst assms(2)]
    by (auto intro!: invar_props_intros)
qed

lemma invar_13_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2); invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma invar_14_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_14 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  show ?thesis using assms(3) by (simp add: eqs)
qed

lemma invar_14_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_14 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and u2eq: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note rc2 = DDFS_rec_call_2_props[OF ass]
  note eq1 = DFS_call_2_some_props[OF rc2(5)]
  have pw1: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF assms(5)] .
  have dst1: "distinct (u1 # p1)" using invar_4_distinct[OF assms(5)] .
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(4)] by simp
  have ivA: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(6)] rc2(3) by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(3)] by simp
  have "t_set visited1_new \<subseteq> dVs dG"
    using IDFS_dVs[OF ivA vi1 dA dV1 pw1 dst1 eq1] .
  thus ?thesis by (simp add: invar_14_def)
qed

lemma invar_14_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_14 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_3_bridge_7[OF assms(1,2)] by simp

lemma invar_14_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_14 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_4_bridge_7[OF assms(1,2)] by simp

lemma invar_14_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_14 (mk_st u1 p1 visited1_new u2 [] (p2' @ p2) visited2_new)"
proof -
  have pw1: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF assms(6)] .
  have dst1: "distinct (u1 # p1)" using invar_4_distinct[OF assms(6)] .
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(5)] by simp
  have ivA: "vset_inv (vset_of_list (u2 # p2' @ p2))" by simp
  have dA: "t_set (vset_of_list (u2 # p2' @ p2)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(7)] by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(4)] by simp
  have "t_set visited1_new \<subseteq> dVs dG"
    using IDFS_dVs[OF ivA vi1 dA dV1 pw1 dst1 assms(3)] .
  thus ?thesis by (simp add: invar_14_def)
qed

lemma invar_14_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2);
    invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma invar_15_holds_1[invar_holds_intros]:
  assumes "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_15 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    and eqs: "u1_new = u1" "p1_new = p1" "visited1_new = visited1" "p2_new = p2"
    using assms(1,2) by (rule DDFS_call_1_bridge_7)
  note rc1 = DDFS_rec_call_1_props[OF ass]
  note eq1 = DFS_call_1_some_props[OF rc1(2)]
  have pw2: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF assms(8)] .
  have dst2: "distinct (u2 # p2')" using invar_5_distinct[OF assms(8)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(5)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(6)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(7)] invar_14_props_impl[OF assms(4)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(3)] by simp
  have "t_set visited2_new \<subseteq> dVs dG"
    using IDFS_dVs[OF ivA vi2 dA dV2 pw2 dst2 eq1] .
  thus ?thesis by (simp add: invar_15_def)
qed

lemma invar_15_holds_2[invar_holds_intros]:
  assumes "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_15 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
proof -
  obtain p where ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    and u2eq: "u2_new = u2"
    using assms(1,2) by (rule DDFS_call_2_bridge_7)
  note rc2 = DDFS_rec_call_2_props[OF ass]
  note eq2 = DFS_call_1_none_props[OF rc2(2)]
  have pw2: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF assms(8)] .
  have dst2: "distinct (u2 # p2')" using invar_5_distinct[OF assms(8)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(5)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(6)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(7)] invar_14_props_impl[OF assms(4)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(3)] by simp
  have "t_set visited2_new \<subseteq> dVs dG"
    using IDFS_dVs[OF ivA vi2 dA dV2 pw2 dst2 eq2] .
  thus ?thesis by (simp add: invar_15_def)
qed

lemma invar_15_holds_3[invar_holds_intros]:
  assumes "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_15 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_3_bridge_7[OF assms(1,2)] by simp

lemma invar_15_holds_4[invar_holds_intros]:
  assumes "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_15 (mk_st u1_new p1_new visited1_new u2_new p2'_new p2_new visited2_new)"
  using assms(3) DDFS_call_4_bridge_7[OF assms(1,2)] by simp

lemma invar_15_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2);
    invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<rbrakk>
   \<Longrightarrow> invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  by simp

lemma invar_15_holds_ret_1[invar_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "invar_15 (mk_st u1 p1 visited1_new u2 [] (p2' @ p2) visited2_new)"
proof -
  have pw2: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF assms(9)] .
  have dst2: "distinct (u2 # p2')" using invar_5_distinct[OF assms(9)] by simp
  have vi1: "vset_inv visited1" using invar_12_props_impl[OF assms(6)] by simp
  have vi2: "vset_inv visited2" using invar_13_props_impl[OF assms(7)] by simp
  have ivA: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have dA: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(8)] invar_14_props_impl[OF assms(5)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(4)] by simp
  have "t_set visited2_new \<subseteq> dVs dG"
    using IDFS_dVs[OF ivA vi2 dA dV2 pw2 dst2 assms(2)] .
  thus ?thesis by (simp add: invar_15_def)
qed


abbreviation "bottleneck v1 v2 \<equiv> 
 (\<forall>v p. p \<noteq> [] \<longrightarrow> dpath_bet' p v1 v \<longrightarrow> level v \<le> level v2 \<longrightarrow> v2 \<in> set p)"


lemma DDFS_ret_2_holds[ret_holds_intros]:
  assumes "DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "last (u1 # p1) = last (u1 # p1) \<and> last (u2 # p2' @ p2) = last (u2 # p2' @ p2) \<and>
         set (tl (u1 # p1)) \<inter> set (tl (u2 # p2' @ p2)) = {} \<and>
         (hd (u1 # p1) = hd (u2 # p2' @ p2) \<longrightarrow>
            (bottleneck (last (u1 # p1)) (hd (u1 # p1)) \<and>
             bottleneck (last (u2 # p2' @ p2)) (hd (u2 # p2' @ p2)))) \<and>
         (hd (u1 # p1) \<noteq> hd (u2 # p2' @ p2) \<longrightarrow>
            (level (hd (u1 # p1)) = 0 \<and> level (hd (u2 # p2' @ p2)) = 0))"
proof -
  note ass = DDFS_ret_2_bridge_7[OF assms(1)]
  have ne: "u1 \<noteq> u2" and l1: "level u1 = 0" and l2: "level u2 = 0"
    using DDFS_ret_2_props[OF ass] by auto
  have disj: "set (tl (u1 # p1)) \<inter> set (tl (u2 # p2' @ p2)) = {}"
    using invar_1_props_impl[OF assms(2)] by auto
  show ?thesis using ne l1 l2 disj by auto
qed

lemma DDFS_ret_1_holds[ret_holds_intros]:
  assumes "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
             = (None, visited2_new)"
          "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
             = (None, visited1_new)"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "last (u1 # p1) = last (u1 # p1) \<and> last (u2 # p2' @ p2) = last (u2 # p2' @ p2) \<and>
         set (tl (u1 # p1)) \<inter> set (tl (u2 # p2' @ p2)) = {} \<and>
         (hd (u1 # p1) = hd (u2 # p2' @ p2) \<longrightarrow>
            (bottleneck (last (u1 # p1)) (hd (u1 # p1)) \<and>
             bottleneck (last (u2 # p2' @ p2)) (hd (u2 # p2' @ p2)))) \<and>
         (hd (u1 # p1) \<noteq> hd (u2 # p2' @ p2) \<longrightarrow>
            (level (hd (u1 # p1)) = 0 \<and> level (hd (u2 # p2' @ p2)) = 0))"
proof -
  note call_1_none = assms(2)
  note call_2_none = assms(3)
  have u12: "u1 = u2"
    using assms(1) by (auto simp: DDFS_ret_1_conds_def)
  have vi1: "vset_inv visited1"
    using invar_12_props_impl[OF assms(16)] by simp
  define p2n where "p2n = p2' @ p2"
  have pw1: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF assms(7)] .
  have dst1: "distinct (u1 # p1)" using invar_4_distinct[OF assms(7)] .
  have pw2: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF assms(8)] .
  have dst2: "distinct (u2 # p2')" using invar_5_distinct[OF assms(8)] by simp
  have i2new: "invar_2 (mk_st u1 p1 visited1_new u2 [] p2n visited2_new)"
    unfolding p2n_def
    by (rule invar_2_holds_ret_1[OF assms(1,2,3) assms(5) assms(7) assms(14) assms(8) assms(16) assms(18)])
  have i3new: "invar_3 (mk_st u1 p1 visited1_new u2 p2' p2 visited2_new)"
    by (rule invar_3_holds_ret_1[OF assms(1,2,3) assms(6) assms(8) assms(15) assms(7) assms(16) assms(17) assms(18) assms(19)])
  have p1_disj_p2n: "set p1 \<inter> set p2n = {}"
    using invar_1_props_impl[OF assms(4)] by (auto simp: p2n_def)
  have u1_not_p2n: "u1 \<notin> set p2n"
    using invar_7'_props_impl[OF assms(12)] by (fastforce simp: p2n_def)
  have ivA1: "vset_inv (vset_of_list (u2 # p2' @ p2))" by simp
  have dA1: "t_set (vset_of_list (u2 # p2' @ p2)) \<subseteq> dVs dG"
    using stack2_dVs[OF assms(8)] by simp
  have dV1: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF assms(18)] by simp
  have ivA2: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1 by (auto intro: set_ops.invar_union)
  have ivV2: "vset_inv visited2" using invar_13_props_impl[OF assms(17)] by simp
  have dA2: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF assms(7)] invar_14_props_impl[OF assms(18)] vi1
    by (auto simp: t_set_vset_of_list_union)
  have dV2: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF assms(19)] by simp
  have p1_sub_vis1: "set p1 \<subseteq> t_set visited1_new"
  proof-
    have sub: "set (u1 # p1) - set (u2 # p2n) \<subseteq> t_set visited1_new"
      using IDFS_complete[OF ivA1 vi1 dA1 dV1 pw1 dst1 call_2_none]
      by (auto simp: p2n_def)
    have eq2: "set (u1 # p1) - set (u2 # p2n) = set p1 - set (u2 # p2n)"
      using u12 by auto
    have notin: "u2 \<notin> set p1"
      using invar_6'_props_impl[OF assms(10)] by fastforce
    have eq3: "set p1 - set (u2 # p2n) = set p1"
      using notin p1_disj_p2n by auto
    show ?thesis using sub eq2 eq3 by auto
  qed
  have nolq: "\<And>w. w \<in> t_set visited1_new \<Longrightarrow> \<not> level_leq u2 w"
  proof -
    fix w assume win: "w \<in> t_set visited1_new"
    then consider "w \<in> t_set visited1_new - t_set visited1" | "w \<in> t_set visited1"
      using IDFS_vis_works(3)[OF ivA1 vi1 dA1 dV1 pw1 dst1 call_2_none] by auto
    then show "\<not> level_leq u2 w"
    proof cases
      case 1
      hence "\<not> level_leq u1 w"
        using IDFS_vis_works(1)[OF ivA1 vi1 dA1 dV1 pw1 dst1 call_2_none] by blast
      thus ?thesis using u12 by simp
    next
      case 2
      hence "level u1 < level w"
        using invar_10_props_impl[OF assms(14)] by blast
      thus ?thesis using u12 by simp
    qed
  qed
  have p2_sub_vis2: "set p2n - t_set visited1 \<subseteq> t_set visited2_new"
  proof-
    have mono2: "t_set visited2 \<subseteq> t_set visited2_new"
      using IDFS_vis_works(3)[OF ivA2 ivV2 dA2 dV2 pw2 dst2 call_1_none] by auto
    moreover have "set p2 - t_set visited1 \<subseteq> t_set visited2"
    proof-
      have "u1 \<notin> set p2"
        using u1_not_p2n by (auto simp: p2n_def)
      moreover have "set p1 \<inter> set p2 = {}"
        using p1_disj_p2n by (auto simp: p2n_def)
      moreover have "set p2 - (set (u1 # p1) \<union> t_set visited1) \<subseteq> t_set visited2"
        using assms(13) by (auto simp: invar_8_def)
      ultimately show ?thesis
        by auto
    qed
    moreover have "set p2' - t_set visited1 \<subseteq> t_set visited2_new"
    proof -
      have "u1 \<notin> set p2'"
        using u1_not_p2n by (auto simp: p2n_def)
      moreover have "set p1 \<inter> set p2' = {}"
        using p1_disj_p2n by (auto simp: p2n_def)
      moreover have "set (u2 # p2') - (set (u1 # p1) \<union> t_set visited1) \<subseteq> t_set visited2_new"
        using IDFS_complete[OF ivA2 ivV2 dA2 dV2 pw2 dst2 call_1_none]
        by (auto simp: t_set_vset_of_list_union[OF vi1])
      ultimately show ?thesis
        using u12 by auto
    qed
    ultimately show ?thesis
      by (auto simp: p2n_def)
  qed
  {
    fix v1 pb u
    assume "v1 \<in> t_set visited1_new"
    moreover assume "dpath_bet' (v1 # pb) v1 u" "pb \<noteq> []" "level u \<le> level (u2)"
    ultimately have
      "set pb \<inter> set (u2 # p2n) \<noteq> {}"
    proof -
      have nolq_p1: "\<forall>w \<in> set p1. \<not> level_leq u2 w"
        using invar_6_props_impl[OF assms(9)] u12 by fastforce
      have i0big: "invar_0 dG (level_leq u2) (set (u2 # p2n) \<union> t_set visited1_new \<union> set p1) (t_set visited1_new)"
      proof -
        have big2: "invar_0 dG (level_leq u1)
                      (set (u2' u2 [] # p2n) \<union> t_set visited1_new \<union> set (u1 # p1)) (t_set visited1_new)"
          using i2new[unfolded invar_2_then_invar_0] .
        have eq: "set (u2' u2 [] # p2n) \<union> t_set visited1_new \<union> set (u1 # p1) =
                  set (u2 # p2n) \<union> t_set visited1_new \<union> set p1"
          using u12 by auto
        have leq_eq: "level_leq u1 = level_leq u2"
          using u12 by auto
        show ?thesis using big2[unfolded eq leq_eq] .
      qed
      have i0: "invar_0 dG (level_leq u2) (set (u2 # p2n)) (t_set visited1_new)"
      proof (rule invar_0_absorb[where W = "t_set visited1_new \<union> set p1"])
        show "invar_0 dG (level_leq u2) (set (u2 # p2n) \<union> (t_set visited1_new \<union> set p1)) (t_set visited1_new)"
          using ivnar_0_avoid_subset[where avoid = "set (u2 # p2n) \<union> t_set visited1_new \<union> set p1"
                                         and avoid' = "set (u2 # p2n) \<union> (t_set visited1_new \<union> set p1)"
                                         and vis = "t_set visited1_new", OF _ i0big]
          by auto
        show "t_set visited1_new \<union> set p1 \<subseteq> t_set visited1_new"
          using p1_sub_vis1 by auto
        show "\<forall>w \<in> t_set visited1_new \<union> set p1. \<not> level_leq u2 w"
          using nolq nolq_p1 by auto
      qed
      show ?thesis
        using invar_0_D[OF i0 \<open>v1 \<in> t_set visited1_new\<close> \<open>pb \<noteq> []\<close>
                           \<open>dpath_bet' (v1 # pb) v1 u\<close>]
              \<open>level u \<le> level (u2)\<close>
        by auto
    qed
    then obtain v2 where "v2 \<in> set (pb)" "v2 \<in> set (u2 # p2n)"
      by blast
    hence "\<exists>pc pd v2. pb = pc @ v2 # pd \<and> v2 \<in> set (u2 # p2n)"
      apply(intro list_has_a_P'[where x = v2])
      by auto
  } note in_vis1_hits_p2 = this
  {
    fix v u p
    assume vup_ass: "v \<in> set (u2 # p2n)" "dpath_bet' p v u" "p \<noteq> []" "level u \<le> level (u2)"
    have subg: "\<And>w ea q. w \<in> set (u2 # p2n) \<Longrightarrow> dpath_bet' (w # q) w ea \<Longrightarrow>
                 level ea \<le> level u2 \<Longrightarrow>
                 (\<exists>p' p'' v'. q = p' @ v' # p'' \<and> v' \<in> set (u2 # p2n)) \<or> q = [] \<or> w = u2"
    proof -
      fix w ea q
      assume wass1: "w \<in> set (u2 # p2n)"
         and wass2: "dpath_bet' (w # q) w ea"
         and wass3: "level ea \<le> level u2"
      show "(\<exists>p' p'' v'. q = p' @ v' # p'' \<and> v' \<in> set (u2 # p2n)) \<or> q = [] \<or> w = u2"
      proof(cases "q \<noteq> []")
        case p_nempty: True
        have "w = u2 \<or> w \<in> t_set visited1 \<or> w \<in> t_set visited2_new"
          using wass1 p2_sub_vis2
          by auto
        then consider (equ2) "w = u2" | (in_vis1) "w \<in> t_set visited1" | (in_vis2) "w \<in> t_set visited2_new"
          by auto
        then show ?thesis
        proof cases
          case equ2
          then show ?thesis
            by auto
        next
          case in_vis1
          moreover have "t_set visited1 \<subseteq> t_set visited1_new"
            using IDFS_vis_works(3)[OF ivA1 vi1 dA1 dV1 pw1 dst1 call_2_none]
            by auto
          ultimately obtain pa pb v1 where "q = pa @ v1 # pb" "v1 \<in> set (u2 # p2n)"
            using in_vis1_hits_p2[OF _ _ _ wass3] p_nempty wass2
            by blast
          hence "\<exists>p' p'' v'. q = p' @ v' # p'' \<and> v' \<in> set (u2 # p2n)"
            using \<open>q = pa @ v1 # pb\<close>
            by auto
          then show ?thesis
            by blast
        next
          case in_vis2
          have mono2: "t_set visited2 \<subseteq> t_set visited2_new"
            using IDFS_vis_works(3)[OF ivA2 ivV2 dA2 dV2 pw2 dst2 call_1_none]
            by auto
          have big: "set q \<inter> (set (u1 # p1) \<union> t_set visited1_new \<union> set (u2 # p2' @ p2)) \<noteq> {}"
            using wass2 wass3 p_nempty in_vis2 mono2
            by (intro invar3_props[OF i3new])
               auto
          show ?thesis
          proof (cases "set q \<inter> set (u2 # p2n) = {}")
            case notu2: True
            hence i: "set q \<inter> (set (u1 # p1) \<union> t_set visited1_new) \<noteq> {}"
              using big by (auto simp: p2n_def)
            have ii: "set p1 \<subseteq> t_set visited1_new"
              using p1_sub_vis1 .
            from i ii obtain v1 where v1: "v1 \<in> set q" "v1 \<in> t_set visited1_new \<or> v1 = u1"
              using p_nempty by fastforce
            hence "(\<exists>pa pb. q = pa @ v1 # pb)"
              by (simp add: split_list)
            then obtain pa pb where papb: "q = pa @ v1 # pb"
              by blast
            consider "v1 \<in> t_set visited1_new" | "v1 = u1"
              using v1 by auto
            then show ?thesis
            proof cases
              case 1
              show ?thesis
              proof(cases "pb = []")
                case p'_empty: True
                hence "v1 = ea"
                proof -
                  have "dpath_bet' ((w # pa) @ [v1]) w ea"
                    using wass2 papb p'_empty by simp
                  thus ?thesis by (simp add: vwalk_bet_def)
                qed
                hence "level v1 \<le> level u2"
                  using wass3
                  by auto
                moreover have "\<not> level_leq u2 v1"
                  using nolq[OF 1] .
                ultimately show ?thesis
                  by auto
              next
                case pb_nempty: False
                have "w # q = w # pa @ v1 # pb"
                  using papb v1
                  by auto
                have "dpath_bet' (v1 # pb) v1 ea"
                  apply(intro split_dpath[where ?p1.0 = "w # pa" and ?v1.0 = w])
                  using wass2[unfolded \<open>w # q = w # pa @ v1 # pb\<close>]
                  by simp
                then obtain pc pd v2 where "pb = pc @ v2 # pd" "v2 \<in> set (u2 # p2n)"
                  using \<open>v1 \<in> t_set visited1_new\<close> in_vis1_hits_p2[OF _ _ _ wass3] pb_nempty
                  by blast
                have "q = (pa @ v1 # pc) @ v2 # pd"
                  using \<open>q = pa @ v1 # pb\<close> \<open>pb = pc @ v2 # pd\<close> by simp
                hence "\<exists>p' p'' v'. q = p' @ v' # p'' \<and> v' \<in> set (u2 # p2n)"
                  using \<open>v2 \<in> set (u2 # p2n)\<close> by blast
                then show ?thesis
                  using \<open>dpath_bet' (v1 # pb) v1 ea\<close>
                  by auto
              qed
            next
              case 2
              then show ?thesis
                using u12 papb
                by auto
            qed
          next
            case False
            then obtain v1 where v1: "v1 \<in> set q" "v1 \<in> set (u2 # p2n)" by auto
            then obtain pa pb where "q = pa @ v1 # pb" using split_list[OF v1(1)] by blast
            thus ?thesis using v1(2) by blast
          qed
        qed
      next
        case False
        then show ?thesis by auto
      qed
    qed
    have hd_eq: "hd p = v"
      using \<open>dpath_bet' p v u\<close> \<open>p \<noteq> []\<close> by (auto simp: vwalk_bet_def)
    moreover have "\<exists>u. dpath_bet' p (hd p) u \<and> level u \<le> level u2"
      using \<open>dpath_bet' p v u\<close> \<open>level u \<le> level (u2)\<close> hd_eq by auto
    moreover have "\<exists>ua. dpath_bet' (u # p) (hd (u # p)) ua \<and> level ua \<le> level u2 \<Longrightarrow> p \<noteq> []
                       \<Longrightarrow> \<exists>u. dpath_bet' p (hd p) u \<and> level u \<le> level u2"
      for p u
    proof -
      assume hyp: "\<exists>ua. dpath_bet' (u # p) (hd (u # p)) ua \<and> level ua \<le> level u2"
         and pne: "p \<noteq> []"
      from hyp pne obtain ua where bet: "dpath_bet' (u # p) u ua" and lev: "level ua \<le> level u2"
        by (auto simp: vwalk_bet_def)
      from bet pne have "dpath_bet' p (hd p) ua" by (rule dpath_bet_cons)
      with lev show ?thesis by auto
    qed
    moreover have "v \<in> set p"
    proof -
      have "hd p \<in> set p" using \<open>p \<noteq> []\<close> by (rule hd_in_set)
      then show ?thesis using hd_eq by simp
    qed
    ultimately have "(\<exists>u'. u' \<in> set p \<and> u' = u2) \<or> last p \<in> set (u2 # p2n)"
    proof (intro last_P_in_list''[where P = "\<lambda>v. v \<in> set (u2 # p2n)" and
                                         P' = "\<lambda>v. v = u2" and
                                         ?P2.0 = "\<lambda>p. \<exists>u. dpath_bet' p (hd p) u \<and> level u \<le> level u2" and
                                         u = v]
                  \<open>v \<in> set (u2 # p2n)\<close>)
      fix q w assume P2: "\<exists>ua. dpath_bet' (w # q) (hd (w # q)) ua \<and> level ua \<le> level u2"
                 and Pw: "w \<in> set (u2 # p2n)"
      obtain ua where wbua: "dpath_bet' (w # q) w ua" and lev: "level ua \<le> level u2"
        using P2 by auto
      from subg[OF Pw wbua lev]
      show "(\<exists>p' p'' v'. q = p' @ v' # p'' \<and> v' \<in> set (u2 # p2n)) \<or> q = [] \<or> w = u2" by auto
    qed
    moreover have "last p = u2" if "last p \<in> set (u2 # p2n)"
    proof -
      have last_eq: "u = last p"
        using last_of_dpath_bet[OF \<open>dpath_bet' p v u\<close> \<open>p \<noteq> []\<close>] .
      have lev7: "\<And>w. w \<in> set (p2' @ p2) \<Longrightarrow> level u2 < level w"
        using invar_7_props_impl[OF assms(11)] .
      have "last p = u2 \<or> last p \<in> set p2n"
        using that by (auto simp: set_ConsD)
      then consider "last p = u2" | "last p \<in> set p2n" by auto
      then show ?thesis
      proof cases
        case 1 then show ?thesis .
      next
        case 2
        then have "level u2 < level (last p)"
          using lev7 by (auto simp: p2n_def)
        then have "\<not> level (last p) \<le> level u2"
          using not_less by blast
        then show ?thesis
          using \<open>level u \<le> level (u2)\<close> last_eq by blast
      qed
    qed
    ultimately have "u2 \<in> set p"
      using \<open>p \<noteq> []\<close>
      by (fastforce simp: last_in_set)
  } note 4 = this
  have tl_disj: "set (tl (u1 # p1)) \<inter> set (tl (u2 # p2' @ p2)) = {}"
    using invar_1_props_impl[OF assms(4)] by auto
  have bneck_b: "bottleneck (last (u2 # p2' @ p2)) u2"
  proof (intro allI impI)
    fix v p
    assume a: "p \<noteq> []" "dpath_bet' p (last (u2 # p2' @ p2)) v" "level v \<le> level u2"
    have last_in: "last (u2 # p2' @ p2) \<in> set (u2 # p2n)"
    proof (unfold p2n_def)
      show "last (u2 # p2' @ p2) \<in> set (u2 # p2' @ p2)"
        by (rule last_in_set) simp
    qed
    show "u2 \<in> set p"
      using 4[OF last_in a(2) a(1) a(3)] .
  qed
  have bneck_a: "bottleneck (last (u1 # p1)) u1"
  proof (intro allI impI)
    fix v p
    assume a: "p \<noteq> []" "dpath_bet' p (last (u1 # p1)) v" "level v \<le> level u1"
    show "u1 \<in> set p"
    proof (cases "p1 = []")
      case True
      then show ?thesis
        using a(1) a(2) by (auto simp: vwalk_bet_def)
    next
      case p1ne: False
      have vis_in: "last (u1 # p1) \<in> t_set visited1_new"
      proof -
        have "last (u1 # p1) = last p1" using p1ne by simp
        moreover have "last p1 \<in> set p1" using p1ne by (simp add: last_in_set)
        ultimately show ?thesis using p1_sub_vis1 by auto
      qed
      obtain p' where pform: "p = (last (u1 # p1)) # p'"
      proof -
        obtain q where q: "p = (hd p) # q"
          using a(1) list.exhaust_sel by blast
        have "hd p = last (u1 # p1)"
          using hd_of_dpath_bet'[OF a(2) a(1)] by simp
        then show ?thesis using q that by auto
      qed
      show ?thesis
      proof (cases "p' = []")
        case True
        hence "last (u1 # p1) = v"
          using a(2) pform by (auto simp: vwalk_bet_def)
        hence "v \<in> set p1"
          using p1ne by (fastforce simp: last_in_set)
        then have "level u1 < level v"
          using invar_6_props_impl[OF assms(9)] by blast
        then show ?thesis using a(3) by linarith
      next
        case pd_nempty: False
        have betP: "dpath_bet' ((last (u1 # p1)) # p') (last (u1 # p1)) v"
          using pform a(2) by simp
        have lvq: "level_leq u2 v"
          using a(3) u12 by fastforce
        from in_vis1_hits_p2[OF vis_in betP pd_nempty lvq]
        obtain pc pd v2 where pcd: "p' = pc @ v2 # pd" "v2 \<in> set (u2 # p2n)"
          by auto
        have bet_v2: "dpath_bet' (v2 # pd) v2 v"
        proof -
          have "dpath_bet' ((last (u1 # p1) # pc) @ v2 # pd) (last (u1 # p1)) v"
            using betP pcd(1) by simp
          then show ?thesis by (rule split_dpath)
        qed
        show ?thesis
        proof (cases "pd = []")
          case True
          hence "v2 = v"
            using bet_v2 by (auto simp: vwalk_bet_def)
          hence "v \<in> set (u2 # p2n)" using pcd(2) by simp
          then consider "v = u2" | "v \<in> set p2n" by auto
          then show ?thesis
          proof cases
            case 1
            then show ?thesis
              using u12 pcd(1) pform \<open>v2 = v\<close> pcd(2)
              by auto
          next
            case 2
            hence "level u2 < level v"
              using invar_7_props_impl[OF assms(11)] by (auto simp: p2n_def)
            then show ?thesis using a(3) u12 by simp
          qed
        next
          case pd_nempty2: False
          have "u2 \<in> set (v2 # pd)"
            by (intro 4[OF pcd(2) bet_v2 _ lvq]) (use pd_nempty2 in auto)
          then show ?thesis
            using u12 pcd(1) pform by auto
        qed
      qed
    qed
  qed
  show ?thesis
    using u12 tl_disj bneck_a bneck_b
    by auto
qed





(*Termination measure (amended 2026-07-03).  The realisable IDFS interface does NOT
  record the search's input head in visited when that head lies in avoid, so the old
  card(dVs - visited) argument for rec_call_1/2 (which needed u \<in> visited_new for the
  avoid-head u) is not available.  Instead we terminate lexicographically on
  (level u1 + level u2, [u1 = u2]), encoded as a single nat:
    - rec_call_3/4 strictly drop the level sum (edge + digraph(1));
    - rec_call_1/2 fire only from u1 = u2 states and never raise the level sum
      (IDFS_sound(8)); their successor has new tip = hd p, which is NOT in avoid
      (IDFS_sound(3) + IDFS_sound(8) against invar_7/invar_6), hence differs from the
      unchanged other tip, so the [u1 = u2] flag drops 1 -> 0.*)
definition "DDFS_measure u1 p1 visited1 u2 p2' p2 visited2 \<equiv>
                  (level u1 + level u2) * 2 + (if u1 = u2 then 1 else 0)"

lemma measure_less_1[intro]:
  assumes
   ass[intro]: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p" and
   invars[intro]: "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "DDFS_measure u1 p1 visited1 u2_new p2'_new p2 visited2_new < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
proof- 
  note rec_call_1[simp] = DDFS_rec_call_1_props[OF ass] and
       call_1_some = DFS_call_1_some_props[OF rec_call_1(2)]
  have pw: "dpath dG (rev (u2 # p2'))" using invar_5_props'[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u2 # p2')" using invar_5_distinct[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
  have vi1o: "vset_inv visited1" using invar_12_props_impl[OF invars(4)] by simp
  have ivAo: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
    using vi1o by (auto intro: set_ops.invar_union)
  have dAo: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
    using stack1_dVs[OF invars(5)] invar_14_props_impl[OF invars(7)] vi1o
    by (auto simp: t_set_vset_of_list_union)
  have vi2o: "vset_inv visited2" using invar_13_props_impl[OF invars(6)] by simp
  have dVo: "t_set visited2 \<subseteq> dVs dG"
    using invar_15_props_impl[OF invars(8)] by simp
  have u12: "u1 = u2"
    using rec_call_1(1) .
  have "level u2_new \<le> level u2"
    using IDFS_sound(8)[OF ivAo vi2o dAo dVo pw dst call_1_some] rec_call_1(3)
    by simp
  moreover have "u1 \<noteq> u2_new"
  proof
    assume "u1 = u2_new"
    hence hdp: "hd p = u1"
      using rec_call_1(3) by simp
    have vi1m: "vset_inv visited1" using invar_12_props_impl[OF invars(4)] by simp
    have vi2m: "vset_inv visited2" using invar_13_props_impl[OF invars(6)] by simp
    have ivAm: "vset_inv (vset_of_list (u1 # p1) \<union>\<^sub>G visited1)"
      using vi1m by (auto intro: set_ops.invar_union)
    have dAm: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<subseteq> dVs dG"
      using stack1_dVs[OF invars(5)] invar_14_props_impl[OF invars(7)] vi1m
      by (auto simp: t_set_vset_of_list_union)
    have dVm: "t_set visited2 \<subseteq> dVs dG"
      using invar_15_props_impl[OF invars(8)] by simp
    have "hd p \<in> set p"
      using IDFS_sound(7)[OF ivAm vi2m dAm dVm pw dst call_1_some] by (cases p) auto
    moreover have "hd p \<notin> set p2'"
    proof
      assume "hd p \<in> set p2'"
      hence "level u2 < level (hd p)"
        using invar_7_props_impl[OF \<open>invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
      moreover have "level (hd p) \<le> level u2"
        using IDFS_sound(8)[OF ivAm vi2m dAm dVm pw dst call_1_some] by simp
      ultimately show False by simp
    qed
    ultimately have "hd p \<in> set p - set p2'" by simp
    have hdp_notin_avoid: "hd p \<notin> set (u1 # p1) \<union> t_set visited1"
    proof -
      have vi1: "vset_inv visited1"
        using \<open>invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>
        by (simp add: invar_12_def)
      have avoid_eq: "t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) = set (u1 # p1) \<union> t_set visited1"
        using t_set_vset_of_list_union[OF vi1] by simp
      have s3: "(set p - set (tl (u2 # p2'))) \<inter> (t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<union> t_set visited2_new) = {}"
        using IDFS_sound(3)[OF ivAm vi2m dAm dVm pw dst call_1_some] .
      have hdp_in: "hd p \<in> set p - set p2'" using \<open>hd p \<in> set p - set p2'\<close> .
      have tl_eq: "set (tl (u2 # p2')) = set p2'" by simp
      then have "hd p \<notin> t_set (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) \<union> t_set visited2_new"
        using s3 hdp_in by auto
      then show ?thesis using avoid_eq by auto
    qed
    thus False using hdp by simp
  qed
  ultimately show ?thesis
    unfolding DDFS_measure_def using u12 by simp
qed

lemma measure_less_2[intro]:
  assumes
   ass[intro]: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p" and
   invars[intro]: "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "DDFS_measure u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
proof- 
  note rec_call_2[simp] = DDFS_rec_call_2_props[OF ass] and
       call_1_none = DFS_call_1_none_props[OF rec_call_2(2)] and
       call_2_some = DFS_call_2_some_props[OF rec_call_2(5)]
  have pw: "dpath dG (rev (u1 # p1))" using invar_4_props_impl[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have dst: "distinct (u1 # p1)" using invar_4_distinct[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] .
  have ivA2o: "vset_inv (vset_of_list (u2 # p2_new))" by simp
  have dA2o: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
    using stack2_dVs[OF invars(4)] rec_call_2(3) by simp
  have ivV2o: "vset_inv visited1" using invar_12_props_impl[OF invars(5)] by simp
  have dV2o: "t_set visited1 \<subseteq> dVs dG"
    using invar_14_props_impl[OF invars(6)] by simp
  have u12: "u1 = u2"
    using rec_call_2(1) .
  have "level u1_new \<le> level u1"
    using IDFS_sound(8)[OF ivA2o ivV2o dA2o dV2o pw dst call_2_some] rec_call_2(6)
    by simp
  moreover have "u1_new \<noteq> u2"
  proof
    assume "u1_new = u2"
    hence hdp: "hd p = u2"
      using rec_call_2(6) by simp
    have ivA2m: "vset_inv (vset_of_list (u2 # p2_new))" by simp
    have dA2m: "t_set (vset_of_list (u2 # p2_new)) \<subseteq> dVs dG"
      using stack2_dVs[OF invars(4)] rec_call_2(3) by simp
    have ivV2m: "vset_inv visited1" using invar_12_props_impl[OF invars(5)] by simp
    have dV2m: "t_set visited1 \<subseteq> dVs dG"
      using invar_14_props_impl[OF invars(6)] by simp
    have "hd p \<in> set p"
      using IDFS_sound(7)[OF ivA2m ivV2m dA2m dV2m pw dst call_2_some] by (cases p) auto
    moreover have "hd p \<notin> set p1"
    proof
      assume "hd p \<in> set p1"
      hence "level u1 < level (hd p)"
        using invar_6_props_impl[OF \<open>invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>] by simp
      moreover have "level (hd p) \<le> level u1"
        using IDFS_sound(8)[OF ivA2m ivV2m dA2m dV2m pw dst call_2_some] by simp
      ultimately show False by simp
    qed
    ultimately have "hd p \<in> set p - set p1" by simp
    hence "hd p \<notin> set (u2 # p2_new)"
      using IDFS_sound(3)[OF ivA2m ivV2m dA2m dV2m pw dst call_2_some] by auto
    thus False using hdp by simp
  qed
  ultimately show ?thesis
    unfolding DDFS_measure_def using u12 by simp
qed

lemma measure_less_3[intro]:
  assumes
   ass[intro]: "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new" and
   invars[intro]: "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "DDFS_measure u1_new p1_new visited1 u2 p2' p2_new visited2 < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
proof-
  have "u1 \<in> dVs dG"
    using invar_4_then_in_Vs[OF \<open>invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>].

  hence "(u1, u1_new) \<in> dG"
    using DDFS_rec_call_3_valid_edge[OF ass] 
    by auto
  hence "level u1_new < level u1"
    using digraph
    by simp
  thus ?thesis
    using DDFS_rec_call_3_props(1)[OF ass]
    by (auto simp: DDFS_measure_def split: if_splits)
qed

lemma measure_less_4[intro]:
  assumes
   ass[intro]: "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new" and
   invars: "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
 shows "DDFS_measure u1 p1 visited1 u2_new p2'_new p2 visited2 < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
proof-       
  have "u2 \<in> dVs dG"
    using invar_5_then_in_Vs[OF \<open>invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)\<close>].

  hence "(u2, u2_new) \<in> dG"
    using DDFS_rec_call_4_valid_edge[OF ass] 
    by auto
  hence "level u2_new < level u2"
    using digraph
    by simp
  thus ?thesis
    using DDFS_rec_call_4_props(1)[OF ass]
    by (auto simp: DDFS_measure_def split: if_splits)
qed

lemma DDFS_dom_intros: 
  "(\<And>u2_new p2'_new visited2_new p.
        DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p \<Longrightarrow>
        DDFS_dom (mk_st u1 p1 visited1 u2_new p2'_new p2 visited2_new)) \<Longrightarrow>
   (\<And>u1_new p1_new visited1_new p2_new p2'_new visited2_new p.
       DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p
       \<Longrightarrow> DDFS_dom (mk_st u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new)) \<Longrightarrow>
   (\<And>u1_new p1_new. DDFS_rec_call_3 u1 p1 u2 u1_new p1_new \<Longrightarrow>
                     DDFS_dom (mk_st u1_new p1_new visited1 u2 p2' p2 visited2)) \<Longrightarrow>
   (\<And>u2_new p2'_new. DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new \<Longrightarrow> 
                      DDFS_dom (mk_st u1 p1 visited1 u2_new p2'_new p2 visited2)) \<Longrightarrow>
    DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  apply(rule DDFS.domintros)
  by (fastforce simp add: DDFS_rec_call_1_def DDFS_rec_call_2_def DDFS_rec_call_3_def
                DDFS_rec_call_4_def DFS_call_1_none_def DFS_call_1_some_def DFS_call_2_some_def)+

lemma DDFS_dom:
  assumes invars: "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)" "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
                  "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  using assms
proof(induction "DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
                   arbitrary: u1 p1 visited1 u2 p2' p2 visited2
                   rule: less_induct)
  case less
  note [intro] = less
  note invars = less.prems
  show ?case
  proof (rule DDFS_dom_intros)
    (* Goal 1: call_1 *)
    fix u2_new p2'_new visited2_new p_aux
    assume ass1: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p_aux"
    have conds1: "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      unfolding DDFS_call_1_conds_def
      using DDFS_rec_call_1_props(1)[OF ass1]
            DFS_call_1_some_props[OF DDFS_rec_call_1_props(2)[OF ass1]]
      by (auto simp: mk_st_simps)
    have upd1: "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = mk_st u1 p1 visited1 u2_new p2'_new p2 visited2_new"
      using DFS_call_1_some_props[OF DDFS_rec_call_1_props(2)[OF ass1]]
            DDFS_rec_call_1_props(3,4)[OF ass1]
      by (auto simp: DDFS_upd1_def mk_st_simps DDFS_state.ext_inject split: prod.splits)
    have dec1: "DDFS_measure u1 p1 visited1 u2_new p2'_new p2 visited2_new
                 < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
      using measure_less_1[OF ass1 invars(2) invars(4) invars(6) invars(7) invars(1) invars(9) invars(8) invars(10)] .
    show "DDFS_dom (mk_st u1 p1 visited1 u2_new p2'_new p2 visited2_new)"
      by (rule less,
          rule dec1, rule invar_4_holds_1[OF conds1 upd1 invars(1)],
          rule invar_5_holds_1[OF conds1 upd1 invars(2) invars(1) invars(7) invars(9) invars(8) invars(10)],
          rule invar_6_holds_1[OF conds1 upd1 invars(3)],
          rule invar_7_holds_1[OF conds1 upd1 invars(2) invars(4) invars(1) invars(7) invars(9) invars(8) invars(10)],
          rule invar_10_holds_1[OF conds1 upd1 invars(5)],
          rule invar_11_holds_1[OF conds1 upd1 invars(6) invars(2) invars(1) invars(7) invars(9) invars(8) invars(10)],
          rule invar_12_holds_1[OF conds1 upd1 invars(7)],
          rule invar_14_holds_1[OF conds1 upd1 invars(8)],
          rule invar_13_holds_1[OF conds1 upd1 invars(9) invars(2) invars(1) invars(7) invars(8) invars(10)],
          rule invar_15_holds_1[OF conds1 upd1 invars(10) invars(8) invars(7) invars(9) invars(1) invars(2)])
  next
    (* Goal 2: call_2 *)
    fix u1_new p1_new visited1_new p2_new and p2'_new :: "'v list" and visited2_new p_aux
    assume ass2: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p_aux"
    have conds2: "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      unfolding DDFS_call_2_conds_def
      using DDFS_rec_call_2_props(1)[OF ass2]
            DFS_call_1_none_props[OF DDFS_rec_call_2_props(2)[OF ass2]]
            DFS_call_2_some_props[OF DDFS_rec_call_2_props(5)[OF ass2]]
            DDFS_rec_call_2_props(3)[OF ass2]
      by (auto simp: mk_st_simps)
    have upd2: "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = mk_st u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new"
      using DFS_call_1_none_props[OF DDFS_rec_call_2_props(2)[OF ass2]]
            DFS_call_2_some_props[OF DDFS_rec_call_2_props(5)[OF ass2]]
            DDFS_rec_call_2_props(3,4,6,7)[OF ass2]
      by (auto simp: DDFS_upd2_def Let_def split: prod.splits)
    have dec2: "DDFS_measure u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new
                 < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
      using measure_less_2[OF ass2 invars(1) invars(3) invars(5) invars(2) invars(7) invars(8)] .
    show "DDFS_dom (mk_st u1_new p1_new visited1_new u2 p2'_new p2_new visited2_new)"
      by (rule less,
          rule dec2,
          rule invar_4_holds_2[OF conds2 upd2 invars(1) invars(2) invars(7) invars(8)],
          rule invar_5_holds_2[OF conds2 upd2 invars(2)],
          rule invar_6_holds_2[OF conds2 upd2 invars(1) invars(3) invars(2) invars(7) invars(8)],
          rule invar_7_holds_2[OF conds2 upd2 invars(4)],
          rule invar_10_holds_2[OF conds2 upd2 invars(5) invars(1) invars(2) invars(7) invars(8)],
          rule invar_11_holds_2[OF conds2 upd2 invars(6) invars(2) invars(1) invars(7) invars(9) invars(8) invars(10)],
          rule invar_12_holds_2[OF conds2 upd2 invars(7) invars(1) invars(2) invars(8)],
          rule invar_14_holds_2[OF conds2 upd2 invars(8) invars(7) invars(1) invars(2)],
          rule invar_13_holds_2[OF conds2 upd2 invars(9) invars(2) invars(1) invars(7) invars(8) invars(10)],
          rule invar_15_holds_2[OF conds2 upd2 invars(10) invars(8) invars(7) invars(9) invars(1) invars(2)])
  next
    (* Goal 3: call_3 *)
    fix u1_new p1_new
    assume ass3: "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new"
    have conds3: "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      using DDFS_rec_call_3_props(1,2,3)[OF ass3]
      by (auto simp: DDFS_call_3_conds_def)
    have upd3: "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = mk_st u1_new p1_new visited1 u2 p2' p2 visited2"
      using DDFS_rec_call_3_props(4,5)[OF ass3]
      by (auto simp: DDFS_upd3_def)
    have dec3: "DDFS_measure u1_new p1_new visited1 u2 p2' p2 visited2
                 < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
      using measure_less_3[OF ass3 invars(1)] .
    show "DDFS_dom (mk_st u1_new p1_new visited1 u2 p2' p2 visited2)"
      by (rule less,
          rule dec3,
          rule invar_4_holds_3[OF conds3 upd3 invars(1)],
          rule invar_5_holds_3[OF conds3 upd3 invars(2)],
          rule invar_6_holds_3[OF conds3 upd3 invars(1) invars(3)],
          rule invar_7_holds_3[OF conds3 upd3 invars(4)],
          rule invar_10_holds_3[OF conds3 upd3 invars(1) invars(5)],
          rule invar_11_holds_3[OF conds3 upd3 invars(6)],
          rule invar_12_holds_3[OF conds3 upd3 invars(7)],
          rule invar_14_holds_3[OF conds3 upd3 invars(8)],
          rule invar_13_holds_3[OF conds3 upd3 invars(9)],
          rule invar_15_holds_3[OF conds3 upd3 invars(10)])
  next
    (* Goal 4: call_4 *)
    fix u2_new p2'_new
    assume ass4: "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new"
    have conds4: "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      using DDFS_rec_call_4_props(1,2,3)[OF ass4]
      by (auto simp: DDFS_call_4_conds_def)
    have upd4: "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2) = mk_st u1 p1 visited1 u2_new p2'_new p2 visited2"
      using DDFS_rec_call_4_props(4,5)[OF ass4]
      by (auto simp: DDFS_upd4_def)
    have dec4: "DDFS_measure u1 p1 visited1 u2_new p2'_new p2 visited2
                 < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
      using measure_less_4[OF ass4 invars(2)] .
    show "DDFS_dom (mk_st u1 p1 visited1 u2_new p2'_new p2 visited2)"
      by (rule less,
          rule dec4, rule invar_4_holds_4[OF conds4 upd4 invars(1)],
          rule invar_5_holds_4[OF conds4 upd4 invars(2)],
          rule invar_6_holds_4[OF conds4 upd4 invars(3)],
          rule invar_7_holds_4[OF conds4 upd4 invars(2) invars(4)],
          rule invar_10_holds_4[OF conds4 upd4 invars(5)],
          rule invar_11_holds_4[OF conds4 upd4 invars(2) invars(6)],
          rule invar_12_holds_4[OF conds4 upd4 invars(7)],
          rule invar_14_holds_4[OF conds4 upd4 invars(8)],
          rule invar_13_holds_4[OF conds4 upd4 invars(9)],
          rule invar_15_holds_4[OF conds4 upd4 invars(10)])
  qed
qed

theorem DDFS_correct:
  assumes "DDFS_dom (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (pa, pb)"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
         
         
          (*"invar_13 p2' p2 visited1"
          "invar_13' u2 p2' p2 visited1"*)
  shows "last pa = last (u1 # p1) \<and> last pb = last (u2 # p2' @ p2) \<and>
         set (tl pa) \<inter> set (tl pb) = {} \<and>
         (hd pa = hd pb \<longrightarrow> (bottleneck (last pa) (hd pa) \<and> bottleneck (last pb) (hd pb))) \<and>
         (hd pa \<noteq> hd pb \<longrightarrow> (level (hd pa) = 0 \<and> level (hd pb) = 0))"
  using assms
proof(induction "DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
               arbitrary: u1 p1 visited1 u2 p2' p2 visited2
               rule: less_induct)
  case less
  note in_dom = less.prems(1)
  note ret_val = less.prems(2)
  note inv1  = less.prems(3)  and inv2  = less.prems(4)  and inv3  = less.prems(5)
  note inv6  = less.prems(6)  and inv6' = less.prems(7)  and inv7  = less.prems(8)
  note inv7' = less.prems(9)  and inv8  = less.prems(10) and inv4  = less.prems(11)
  note inv5  = less.prems(12) and inv10 = less.prems(13) and inv11 = less.prems(14)
  note inv12 = less.prems(15) and inv13 = less.prems(16)
  note inv14 = less.prems(17) and inv15 = less.prems(18)
  note allinvs = inv1 inv2 inv3 inv6 inv6' inv7 inv7' inv8 inv4 inv5 inv10 inv11 inv12 inv13 inv14 inv15
  \<comment> \<open>rec_call_1 case\<close>
  have g_rec1: "last pa = last (u1 # p1) \<and> last pb = last (u2 # p2' @ p2) \<and>
               set (tl pa) \<inter> set (tl pb) = {} \<and>
               (hd pa = hd pb \<longrightarrow> bottleneck (last pa) (hd pa) \<and> bottleneck (last pb) (hd pb)) \<and>
               (hd pa \<noteq> hd pb \<longrightarrow> level (hd pa) = 0 \<and> level (hd pb) = 0)"
    if ass: "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2n p2n' v2n p"
    for u2n p2n' v2n p
  proof -
    note rc1 = DDFS_rec_call_1_props[OF ass]
    note idfs_eq1 = DFS_call_1_some_props[OF rc1(2)]
    have conds1: "DDFS_call_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      using rc1(1) idfs_eq1 by (auto simp: DDFS_call_1_conds_def mk_st_simps)
    have upd1: "DDFS_upd1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
                  = mk_st u1 p1 visited1 u2n p2n' p2 v2n"
      using idfs_eq1 rc1(3,4)
      by (auto simp: DDFS_upd1_def mk_st_simps)
    have val: "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = DDFS (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      using DDFS_simps(1)[OF in_dom conds1] upd1 by simp
    have h1:  "invar_1  (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_1_holds_1[OF conds1 upd1] allinvs)
    have h2:  "invar_2  (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_2_holds_1[OF conds1 upd1] allinvs)
    have h3:  "invar_3  (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_3_holds_1[OF conds1 upd1] allinvs)
    have h4:  "invar_4  (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_4_holds_1[OF conds1 upd1] allinvs)
    have h5:  "invar_5  (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_5_holds_1[OF conds1 upd1] allinvs)
    have h6:  "invar_6  (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_6_holds_1[OF conds1 upd1] allinvs)
    have h6': "invar_6' (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_6'_holds_1[OF conds1 upd1] allinvs)
    have h7:  "invar_7  (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_7_holds_1[OF conds1 upd1] allinvs)
    have h7': "invar_7' (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_7'_holds_1[OF conds1 upd1] allinvs)
    have h8:  "invar_8  (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_8_holds_1[OF conds1 upd1] allinvs)
    have h10: "invar_10 (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_10_holds_1[OF conds1 upd1] allinvs)
    have h11: "invar_11 (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_11_holds_1[OF conds1 upd1] allinvs)
    have h12: "invar_12 (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_12_holds_1[OF conds1 upd1] allinvs)
    have h13: "invar_13 (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_13_holds_1[OF conds1 upd1] allinvs)
    have h14: "invar_14 (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_14_holds_1[OF conds1 upd1] allinvs)
    have h15: "invar_15 (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (intro invar_15_holds_1[OF conds1 upd1] allinvs)
    have lastp: "last (u2n # p2n' @ p2) = last (u2 # p2' @ p2)"
      using DDFS_val_rec_1_last_p[OF ass inv5 inv4 inv12 inv13 inv14 inv15, symmetric] .
    have ret_new: "DDFS (mk_st u1 p1 visited1 u2n p2n' p2 v2n) = (pa, pb)"
      using val ret_val by simp
    have new_dom1: "DDFS_dom (mk_st u1 p1 visited1 u2n p2n' p2 v2n)"
      by (rule DDFS_dom[OF h4 h5 h6 h7 h10 h11 h12 h14 h13 h15])
    have dec1: "DDFS_measure u1 p1 visited1 u2n p2n' p2 v2n
                  < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
      by (rule measure_less_1[OF ass inv5 inv7 inv11 inv12 inv4 inv13 inv14 inv15])
    show ?thesis
      using less.hyps[rule_format, OF dec1 new_dom1 ret_new h1 h2 h3 h6 h6' h7 h7' h8 h4 h5 h10 h11 h12 h13 h14 h15] lastp
      by simp
  qed
  \<comment> \<open>rec_call_2 case\<close>
  have g_rec2: "last pa = last (u1 # p1) \<and> last pb = last (u2 # p2' @ p2) \<and>
               set (tl pa) \<inter> set (tl pb) = {} \<and>
               (hd pa = hd pb \<longrightarrow> bottleneck (last pa) (hd pa) \<and> bottleneck (last pb) (hd pb)) \<and>
               (hd pa \<noteq> hd pb \<longrightarrow> level (hd pa) = 0 \<and> level (hd pb) = 0)"
    if conds2: "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  proof -
    obtain v2n where idfs2n: "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2 = (None, v2n)"
      using conds2 by (auto simp: DDFS_call_2_conds_def mk_st_simps)
    obtain p v1n where idfs2s: "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1 = (Some p, v1n)"
      using conds2 by (auto simp: DDFS_call_2_conds_def mk_st_simps)
    define p2n where "p2n = p2' @ p2"
    define u1n where "u1n = hd p"
    define p1n where "p1n = tl p"
    have u12x: "u1 = u2"
      using conds2 by (auto simp: DDFS_call_2_conds_def mk_st_simps)
    have ass: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1n p1n v1n [] p2n v2n p"
      using u12x idfs2n idfs2s
      by (auto simp: DDFS_rec_call_2_def DFS_call_1_none_def DFS_call_2_some_def
                     u1n_def p1n_def p2n_def)
    have upd2: "DDFS_upd2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
                  = mk_st u1n p1n v1n u2 [] p2n v2n"
      using idfs2n idfs2s
      by (auto simp: DDFS_upd2_def mk_st_simps u1n_def p1n_def p2n_def)
    have val: "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = DDFS (mk_st u1n p1n v1n u2 [] p2n v2n)"
      using DDFS_simps(2)[OF in_dom conds2] upd2 by simp
    have h1:  "invar_1  (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_1_holds_2[OF conds2 upd2] allinvs)
    have h2:  "invar_2  (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_2_holds_2[OF conds2 upd2] allinvs)
    have h3:  "invar_3  (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_3_holds_2[OF conds2 upd2] allinvs)
    have h4:  "invar_4  (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_4_holds_2[OF conds2 upd2] allinvs)
    have h5:  "invar_5  (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_5_holds_2[OF conds2 upd2] allinvs)
    have h6:  "invar_6  (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_6_holds_2[OF conds2 upd2] allinvs)
    have h6': "invar_6' (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_6'_holds_2[OF conds2 upd2] allinvs)
    have h7:  "invar_7  (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_7_holds_2[OF conds2 upd2] allinvs)
    have h7': "invar_7' (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_7'_holds_2[OF conds2 upd2] allinvs)
    have h8:  "invar_8  (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_8_holds_2[OF conds2 upd2] allinvs)
    have h10: "invar_10 (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_10_holds_2[OF conds2 upd2] allinvs)
    have h11: "invar_11 (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_11_holds_2[OF conds2 upd2] allinvs)
    have h12: "invar_12 (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_12_holds_2[OF conds2 upd2] allinvs)
    have h13: "invar_13 (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_13_holds_2[OF conds2 upd2] allinvs)
    have h14: "invar_14 (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_14_holds_2[OF conds2 upd2] allinvs)
    have h15: "invar_15 (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (intro invar_15_holds_2[OF conds2 upd2] allinvs)
    have lastps: "last (u1n # p1n) = last (u1 # p1)"
                 "last (u2 # p2n) = last (u2 # p2' @ p2)"
      using DDFS_val_rec_2_last_p[OF ass inv4 inv5 inv12 inv14] by auto
    have ret_new: "DDFS (mk_st u1n p1n v1n u2 [] p2n v2n) = (pa, pb)"
      using val ret_val by simp
    have new_dom2: "DDFS_dom (mk_st u1n p1n v1n u2 [] p2n v2n)"
      by (rule DDFS_dom[OF h4 h5 h6 h7 h10 h11 h12 h14 h13 h15])
    have dec2: "DDFS_measure u1n p1n v1n u2 [] p2n v2n
                  < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
      by (rule measure_less_2[OF ass inv4 inv6 inv10 inv5 inv12 inv14])
    show ?thesis
      using less.hyps[rule_format, OF dec2 new_dom2 ret_new h1 h2 h3 h6 h6' h7 h7' h8 h4 h5 h10 h11 h12 h13 h14 h15] lastps
      by simp
  qed

  \<comment> \<open>rec_call_3 case\<close>
  have g_rec3: "last pa = last (u1 # p1) \<and> last pb = last (u2 # p2' @ p2) \<and>
               set (tl pa) \<inter> set (tl pb) = {} \<and>
               (hd pa = hd pb \<longrightarrow> bottleneck (last pa) (hd pa) \<and> bottleneck (last pb) (hd pb)) \<and>
               (hd pa \<noteq> hd pb \<longrightarrow> level (hd pa) = 0 \<and> level (hd pb) = 0)"
    if ass: "DDFS_rec_call_3 u1 p1 u2 u1n p1n"
    for u1n p1n
  proof -
    have conds3: "DDFS_call_3_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      using ass by (auto simp: DDFS_call_3_conds_def DDFS_rec_call_3_def)
    have upd3: "DDFS_upd3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
                  = mk_st u1n p1n visited1 u2 p2' p2 visited2"
      using DDFS_rec_call_3_props[OF ass]
      by (auto simp: DDFS_upd3_def mk_st_simps)
    have val: "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = DDFS (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      using DDFS_simps(3)[OF in_dom conds3] upd3 by simp
    have h1:  "invar_1  (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_1_holds_3[OF conds3 upd3] allinvs)
    have h2:  "invar_2  (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_2_holds_3[OF conds3 upd3] allinvs)
    have h3:  "invar_3  (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_3_holds_3[OF conds3 upd3] allinvs)
    have h4:  "invar_4  (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_4_holds_3[OF conds3 upd3] allinvs)
    have h5:  "invar_5  (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_5_holds_3[OF conds3 upd3] allinvs)
    have h6:  "invar_6  (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_6_holds_3[OF conds3 upd3] allinvs)
    have h6': "invar_6' (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_6'_holds_3[OF conds3 upd3] allinvs)
    have h7:  "invar_7  (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_7_holds_3[OF conds3 upd3] allinvs)
    have h7': "invar_7' (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_7'_holds_3[OF conds3 upd3] allinvs)
    have h8:  "invar_8  (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_8_holds_3[OF conds3 upd3] allinvs)
    have h10: "invar_10 (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_10_holds_3[OF conds3 upd3] allinvs)
    have h11: "invar_11 (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_11_holds_3[OF conds3 upd3] allinvs)
    have h12: "invar_12 (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_12_holds_3[OF conds3 upd3] allinvs)
    have h13: "invar_13 (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_13_holds_3[OF conds3 upd3] allinvs)
    have h14: "invar_14 (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_14_holds_3[OF conds3 upd3] allinvs)
    have h15: "invar_15 (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (intro invar_15_holds_3[OF conds3 upd3] allinvs)
    have lastp: "last (u1n # p1n) = last (u1 # p1)"
      using DDFS_val_rec_3_last_p[OF ass, symmetric] .
    have ret_new: "DDFS (mk_st u1n p1n visited1 u2 p2' p2 visited2) = (pa, pb)"
      using val ret_val by simp
    have new_dom3: "DDFS_dom (mk_st u1n p1n visited1 u2 p2' p2 visited2)"
      by (rule DDFS_dom[OF h4 h5 h6 h7 h10 h11 h12 h14 h13 h15])
    have dec3: "DDFS_measure u1n p1n visited1 u2 p2' p2 visited2
                  < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
      by (rule measure_less_3[OF ass inv4])
    show ?thesis
      using less.hyps[rule_format, OF dec3 new_dom3 ret_new h1 h2 h3 h6 h6' h7 h7' h8 h4 h5 h10 h11 h12 h13 h14 h15] lastp
      by simp
  qed
  \<comment> \<open>rec_call_4 case\<close>
  have g_rec4: "last pa = last (u1 # p1) \<and> last pb = last (u2 # p2' @ p2) \<and>
               set (tl pa) \<inter> set (tl pb) = {} \<and>
               (hd pa = hd pb \<longrightarrow> bottleneck (last pa) (hd pa) \<and> bottleneck (last pb) (hd pb)) \<and>
               (hd pa \<noteq> hd pb \<longrightarrow> level (hd pa) = 0 \<and> level (hd pb) = 0)"
    if ass: "DDFS_rec_call_4 u1 u2 p2' u2n p2n'"
    for u2n p2n'
  proof -
    have conds4: "DDFS_call_4_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      using DDFS_rec_call_4_props[OF ass] by (auto simp: DDFS_call_4_conds_def mk_st_simps)
    have upd4: "DDFS_upd4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)
                  = mk_st u1 p1 visited1 u2n p2n' p2 visited2"
      using DDFS_rec_call_4_props[OF ass]
      by (auto simp: DDFS_upd4_def mk_st_simps)
    have val: "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2)
             = DDFS (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      using DDFS_simps(4)[OF in_dom conds4] upd4 by simp
    have h1:  "invar_1  (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_1_holds_4[OF conds4 upd4] allinvs)
    have h2:  "invar_2  (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_2_holds_4[OF conds4 upd4] allinvs)
    have h3:  "invar_3  (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_3_holds_4[OF conds4 upd4] allinvs)
    have h4:  "invar_4  (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_4_holds_4[OF conds4 upd4] allinvs)
    have h5:  "invar_5  (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_5_holds_4[OF conds4 upd4] allinvs)
    have h6:  "invar_6  (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_6_holds_4[OF conds4 upd4] allinvs)
    have h6': "invar_6' (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_6'_holds_4[OF conds4 upd4] allinvs)
    have h7:  "invar_7  (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_7_holds_4[OF conds4 upd4] allinvs)
    have h7': "invar_7' (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_7'_holds_4[OF conds4 upd4] allinvs)
    have h8:  "invar_8  (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_8_holds_4[OF conds4 upd4] allinvs)
    have h10: "invar_10 (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_10_holds_4[OF conds4 upd4] allinvs)
    have h11: "invar_11 (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_11_holds_4[OF conds4 upd4] allinvs)
    have h12: "invar_12 (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_12_holds_4[OF conds4 upd4] allinvs)
    have h13: "invar_13 (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_13_holds_4[OF conds4 upd4] allinvs)
    have h14: "invar_14 (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_14_holds_4[OF conds4 upd4] allinvs)
    have h15: "invar_15 (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (intro invar_15_holds_4[OF conds4 upd4] allinvs)
    have lastp: "last (u2n # p2n' @ p2) = last (u2 # p2' @ p2)"
      using DDFS_val_rec_4_last_p[OF ass, symmetric] .
    have ret_new: "DDFS (mk_st u1 p1 visited1 u2n p2n' p2 visited2) = (pa, pb)"
      using val ret_val by simp
    have new_dom4: "DDFS_dom (mk_st u1 p1 visited1 u2n p2n' p2 visited2)"
      by (rule DDFS_dom[OF h4 h5 h6 h7 h10 h11 h12 h14 h13 h15])
    have dec4: "DDFS_measure u1 p1 visited1 u2n p2n' p2 visited2
                  < DDFS_measure u1 p1 visited1 u2 p2' p2 visited2"
      by (rule measure_less_4[OF ass inv5])
    show ?thesis
      using less.hyps[rule_format, OF dec4 new_dom4 ret_new h1 h2 h3 h6 h6' h7 h7' h8 h4 h5 h10 h11 h12 h13 h14 h15] lastp
      by simp
  qed

  \<comment> \<open>ret_1 case\<close>
  have g_ret1: "last pa = last (u1 # p1) \<and> last pb = last (u2 # p2' @ p2) \<and>
               set (tl pa) \<inter> set (tl pb) = {} \<and>
               (hd pa = hd pb \<longrightarrow> bottleneck (last pa) (hd pa) \<and> bottleneck (last pb) (hd pb)) \<and>
               (hd pa \<noteq> hd pb \<longrightarrow> level (hd pa) = 0 \<and> level (hd pb) = 0)"
    if ass: "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  proof -
    obtain v2n v1n where
      idfs1: "IDFS (level_leq u2) (vset_of_list (u1 # p1) \<union>\<^sub>G visited1) (u2 # p2') visited2
                = (None, v2n)"
      and idfs2: "IDFS (level_leq u1) (vset_of_list (u2 # p2' @ p2)) (u1 # p1) visited1
                = (None, v1n)"
      using ass by (auto simp: DDFS_ret_1_conds_def mk_st_simps)
    have val: "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (u1 # p1, u2 # p2' @ p2)"
      using DDFS_simps(5)[OF in_dom ass] by (simp add: DDFS_ret1_def mk_st_simps)
    have paeq: "pa = u1 # p1" and pbeq: "pb = u2 # p2' @ p2"
      using ret_val val by auto
    show ?thesis
      using DDFS_ret_1_holds[OF ass idfs1 idfs2 inv1 inv2 inv3 inv4 inv5 inv6 inv6' inv7 inv7' inv8 inv10 inv11 inv12 inv13 inv14 inv15]
            paeq pbeq by simp
  qed
  \<comment> \<open>ret_2 case\<close>
  have g_ret2: "last pa = last (u1 # p1) \<and> last pb = last (u2 # p2' @ p2) \<and>
               set (tl pa) \<inter> set (tl pb) = {} \<and>
               (hd pa = hd pb \<longrightarrow> bottleneck (last pa) (hd pa) \<and> bottleneck (last pb) (hd pb)) \<and>
               (hd pa \<noteq> hd pb \<longrightarrow> level (hd pa) = 0 \<and> level (hd pb) = 0)"
    if ass: "DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  proof -
    have val: "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (u1 # p1, u2 # p2' @ p2)"
      using DDFS_simps(6)[OF in_dom ass] by (simp add: DDFS_ret2_def mk_st_simps)
    have paeq: "pa = u1 # p1" and pbeq: "pb = u2 # p2' @ p2"
      using ret_val val by auto
    show ?thesis
      using DDFS_ret_2_holds[OF ass inv1] paeq pbeq by simp
  qed
  \<comment> \<open>Conclude by exhaustion\<close>
  from DDFS_induction_exhaust[of u1 p1 visited1 u2 p2' visited2 p2]
  show ?case
  proof (elim disjE exE)
    fix u2_new p2'_new visited2_new p
    assume "DDFS_rec_call_1 u1 p1 visited1 u2 p2' visited2 u2_new p2'_new visited2_new p"
    then show ?case using g_rec1 by blast
  next
    fix u1_new p1_new visited1_new p2'_new p2_new visited2_new p
    assume F2: "DDFS_rec_call_2 u1 p1 visited1 u2 p2 p2' visited2 u1_new p1_new visited1_new p2'_new p2_new visited2_new p"
    note rc2x = DDFS_rec_call_2_props[OF F2]
    have "DDFS_call_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      using rc2x(1,3) DFS_call_1_none_props[OF rc2x(2)] DFS_call_2_some_props[OF rc2x(5)]
      by (auto simp: DDFS_call_2_conds_def mk_st_simps)
    then show ?case by (rule g_rec2)
  next
    fix u1_new p1_new
    assume "DDFS_rec_call_3 u1 p1 u2 u1_new p1_new"
    then show ?case using g_rec3 by blast
  next
    fix u2_new p2'_new
    assume "DDFS_rec_call_4 u1 u2 p2' u2_new p2'_new"
    then show ?case using g_rec4 by blast
  next
    fix visited1_new p2_new p2'_new visited2_new
    assume F5: "DDFS_ret_1 u1 p1 visited1 u2 p2' p2 visited2 visited1_new p2_new p2'_new visited2_new"
    note rt = DDFS_ret_1_props[OF F5]
    have "DDFS_ret_1_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      using rt(1,2) DFS_call_1_none_props[OF rt(4)] DFS_call_2_none_props[OF rt(5)]
      by (auto simp: DDFS_ret_1_conds_def mk_st_simps)
    then show ?case by (rule g_ret1)
  next
    assume F6: "DDFS_ret_2 u1 u2"
    have "DDFS_ret_2_conds (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
      using DDFS_ret_2_props[OF F6] by (auto simp: DDFS_ret_2_conds_def mk_st_simps)
    then show ?case by (rule g_ret2)
  qed
qed


lemma DDFS_works_and_terminates:
  assumes "DDFS (mk_st u1 p1 visited1 u2 p2' p2 visited2) = (pa, pb)"
          "invar_1 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_2 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_3 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_6 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_6' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_7 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_7' (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_8 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_4 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_5 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_10 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_11 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_12 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_13 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_14 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
          "invar_15 (mk_st u1 p1 visited1 u2 p2' p2 visited2)"
  shows "last pa = last (u1 # p1) \<and> last pb = last (u2 # p2' @ p2) \<and>
         set (tl pa) \<inter> set (tl pb) = {} \<and>
         (hd pa = hd pb \<longrightarrow> (bottleneck (last pa) (hd pa) \<and> bottleneck (last pb) (hd pb))) \<and>
         (hd pa \<noteq> hd pb \<longrightarrow> (level (hd pa) = 0 \<and> level (hd pb) = 0))"
  apply(intro DDFS_correct)
  apply (rule DDFS_dom assms invar_12_props_impl invar_13_props_impl)+
  done

end

end
