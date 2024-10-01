(*
  Author: Mohammad Abdulaziz, TUM
  Author: Martin Molzer, TUM improved the automation
*)

theory Berge
imports Main "HOL-Library.Extended_Nat"
begin

subsection\<open>Paths, connected components, and symmetric differences\<close>

text\<open>Some basic definitions about the above concepts. One interesting point is the use of the
     concepts of connected components, which partition the set of vertices, and the analogous
     partition of edges. Juggling around between the two partitions, we get a much shorter proof for
     the first direction of Berge's lemma, which is the harder one.\<close>

definition Vs where "Vs E \<equiv> \<Union> E"

lemma vs_member[iff?]: "v \<in> Vs E \<longleftrightarrow> (\<exists>e \<in> E. v \<in> e)"
  unfolding Vs_def by simp

lemma vs_member_elim[elim?]:
  assumes "v \<in> Vs E"
  obtains e where "v \<in> e" "e \<in> E"
  using assms
  by(auto simp: vs_member)

lemma vs_member_intro[intro]:
  assumes "v \<in> e" "e \<in> E"
  shows "v \<in> Vs E"
  by (meson vs_member assms)

lemma vs_transport[intro?]:
  assumes "u \<in> Vs E"
  assumes "\<And>e. u \<in> e \<Longrightarrow> e \<in> E \<Longrightarrow> \<exists>g \<in> F. u \<in> g"
  shows "u \<in> Vs F"
  by (meson assms vs_member)

lemma edges_are_Vs:
  assumes "{v, v'} \<in> E"
  shows "v \<in> Vs E" "v' \<in> Vs E"
  using assms by blast+

locale graph_defs =
  fixes E :: "'a set set"

abbreviation "graph_invar E \<equiv> (\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v) \<and> finite (Vs E)"

locale graph_abs =
  graph_defs +
  assumes graph: "graph_invar E"
begin

lemma finite_E: "finite E"
  using finite_UnionD graph
  unfolding Vs_def
  by blast

end

context fixes X :: "'a set set" begin
inductive path where
  path0: "path []" |
  path1: "v \<in> Vs X \<Longrightarrow> path [v]" |
  path2: "{v,v'} \<in> X \<Longrightarrow> path (v'#vs) \<Longrightarrow> path (v#v'#vs)"
end

value[nbe] "path {{1::nat, 2}, {2, 3}, {3, 4}} [1, 4, 3] = True"

declare path0[simp]

inductive_simps path_1[simp]: "path X [v]"

inductive_simps path_2[simp]: "path X (v # v' # vs)"

text\<open>
  If a set of edges cannot be partitioned in paths, then it has a junction of 3 or more edges.
  In particular, an edge from one of the two matchings belongs to the path
  equivalent to one connected component. Otherwise, there will be a vertex whose degree is
  more than 2.
\<close>


text\<open>
  Every edge lies completely in a connected component.
\<close>

fun edges_of_path where
"edges_of_path [] = []" |
"edges_of_path [v] = []" |
"edges_of_path (v#v'#l) = {v,v'} # (edges_of_path (v'#l))"

lemma path_ball_edges: "path E p \<Longrightarrow> b \<in> set (edges_of_path p) \<Longrightarrow> b \<in> E"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_index:
  "Suc i < length p \<Longrightarrow> edges_of_path p ! i = {p ! i, p ! Suc i}"
proof(induction i arbitrary: p)
  case 0
  then obtain u v ps where "p = u#v#ps" by (metis Suc_leI Suc_le_length_iff)
  thus ?case by simp
next
  case (Suc i)
  then obtain u v ps where "p = u#v#ps" by (metis Suc_leI Suc_le_length_iff)
  hence "edges_of_path (v#ps) ! i = {(v#ps) ! i, (v#ps) ! Suc i}" using Suc.IH Suc.prems by simp
  thus ?case using \<open>p = u#v#ps\<close> by simp
qed

lemma edges_of_path_length: "length (edges_of_path p) = length p - 1"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_for_inner:
  assumes "v = p ! i" "Suc i < length p"
  obtains u w where "{u, v} = edges_of_path p ! (i - 1)" "{v, w} = edges_of_path p ! i"
proof(cases "i = 0")
  case True thus ?thesis 
    by (metis assms diff_is_0_eq' edges_of_path_index insert_commute nat_le_linear not_one_le_zero that)
next
  case False thus ?thesis by (simp add: Suc_lessD assms(1) assms(2) edges_of_path_index that)
qed

lemma path_vertex_has_edge:
  assumes "length p \<ge> 2" "v \<in> set p"
  obtains e where "e \<in> set (edges_of_path p)" "v \<in> e"
proof-
  obtain i where idef: "v = p ! i" "i < length p" by (metis assms(2) in_set_conv_nth)
  have eoplength': "Suc (length (edges_of_path p)) = length p"
    using assms(1) by (auto simp: edges_of_path_length)
  hence eoplength: "length (edges_of_path p) \<ge> 1" using assms(1) by simp

  from idef consider (nil) "i = 0" | (gt) "i > 0" "Suc i < length p" | (last) "Suc i = length p"
    by linarith
  thus ?thesis
  proof cases
    case nil
    hence "edges_of_path p ! 0 = {p ! 0, p ! 1}" using edges_of_path_index assms(1) by force
    thus ?thesis using nil eoplength idef(1)
      by (metis One_nat_def Suc_le_lessD insertI1 nth_mem that)
  next
    case last
    hence "edges_of_path p ! (i -1) = {p ! (i - 1), p ! i}"
      by (metis Suc_diff_le eoplength' diff_Suc_1 edges_of_path_index eoplength idef(2))
    thus ?thesis using last eoplength eoplength' idef(1)
      by (metis Suc_inject diff_less insertCI less_le_trans nth_mem that zero_less_one)
  next
    case gt
    thus ?thesis using edges_of_path_for_inner idef(1) eoplength'
      by (metis Suc_less_SucD in_set_conv_nth insertI1 that)
  qed
qed

lemma v_in_edge_in_path:
  assumes "{u, v} \<in> set (edges_of_path p)"
  shows "u \<in> set p"
  using assms
  by (induction p rule: edges_of_path.induct, auto)

lemma v_in_edge_in_path_inj:
  assumes "e \<in> set (edges_of_path p)"
  obtains u v where "e = {u, v}"
  using assms
  by (induction p rule: edges_of_path.induct, auto)

lemma v_in_edge_in_path_gen:
  assumes "e \<in> set (edges_of_path p)" "u \<in> e"
  shows "u \<in> set p"
proof-
  obtain u v where "e = {u, v}" using assms(1) v_in_edge_in_path_inj by blast
  thus ?thesis by (metis assms empty_iff insert_commute insert_iff v_in_edge_in_path)
qed

lemma distinct_edges_of_vpath:
  "distinct p \<Longrightarrow> distinct (edges_of_path p)"
  using v_in_edge_in_path
  by (induction p rule: edges_of_path.induct) fastforce+

lemma distinct_edges_of_paths_cons:
  assumes "distinct (edges_of_path (v # p))"
  shows "distinct (edges_of_path p)"
  using assms
  by(cases "p"; simp)

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

lemma edges_of_path_append_2:
  assumes "p' \<noteq> []"
  shows "edges_of_path (p @ p') = edges_of_path (p @ [hd p']) @ edges_of_path p'"
  using assms
proof(induction p rule: induct_list012)
  case 2
  obtain a p's where "p' = a # p's" using assms list.exhaust_sel by blast
  thus ?case by simp
qed simp_all

lemma edges_of_path_append_3:
  assumes "p \<noteq> []"
  shows "edges_of_path (p @ p') = edges_of_path p @ edges_of_path (last p # p')"
proof-
  from assms
  have "edges_of_path (p @ p') = edges_of_path (butlast p @ last p # p')"
    by (metis append.assoc append_Cons append_Nil append_butlast_last_id)
  also have "... = edges_of_path (butlast p @ [last p]) @ edges_of_path (last p # p')"
    using edges_of_path_append_2 by fastforce
  also have "... = edges_of_path p @ edges_of_path (last p # p')"
    by (simp add: assms)
  finally show ?thesis .
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

lemma edges_of_path_append: "\<exists>ep. edges_of_path (p @ p') = ep @ edges_of_path p'"
proof(cases p')
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis using edges_of_path_append_2 by blast
qed

lemma last_v_in_last_e: 
  assumes "length p \<ge> 2"
  shows "last p \<in> last (edges_of_path p)"
  using assms
proof(induction "p" rule: induct_list012)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case p: (3 a b p)
  then show ?case apply (auto split: if_splits)
    subgoal using edges_of_path.elims by blast
    subgoal by (simp add: Suc_leI)
    done
qed

lemma hd_v_in_hd_e: 
  assumes "length p \<ge> 2"
  shows "hd p \<in> hd (edges_of_path p)"
proof-
  obtain a b ps where "p = a # b # ps"
    by (metis Suc_le_length_iff assms numeral_2_eq_2)
  thus ?thesis by simp
qed

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

lemma edges_of_path_append_subset:
  shows  "set (edges_of_path p') \<subseteq> set (edges_of_path (p @ p'))"
  using edges_of_path_append
  by (metis eq_iff le_supE set_append)

lemma path_edges_subset:
  assumes "path E p"
  shows "set (edges_of_path p) \<subseteq> E"
  using assms
  by (induction, simp_all)

lemma induct_list0123[consumes 0, case_names nil list1 list2 list3]:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x, y]; \<And>x y z zs. \<lbrakk> P zs; P (z # zs); P (y # z # zs) \<rbrakk> \<Longrightarrow> P (x # y # z # zs)\<rbrakk> \<Longrightarrow> P xs"
by induction_schema (pat_completeness, lexicographic_order)

lemma tl_path_is_path: "path E p \<Longrightarrow> path E (tl p)"
  by (induction p rule: path.induct) (simp_all)

lemma path_concat:
  assumes "path E p" "path E q" "q \<noteq> []" "p \<noteq> [] \<Longrightarrow> last p = hd q"
  shows "path E (p @ tl q)"
  using assms
  by (induction) (simp_all add: tl_path_is_path)

lemma path_append:
  assumes "path E p1" "path E p2" "p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> {last p1, hd p2} \<in> E"
  shows "path E (p1 @ p2)"
proof-
  have "path E (last p1 # p2)" if "p1 \<noteq> []" and "p2 \<noteq> []"
    by (metis assms(2) assms(3) hd_Cons_tl path_2 that(1) that(2))
  thus ?thesis using assms(1) assms(2) path_concat by fastforce
qed

lemma mem_path_Vs: 
  assumes "path E p" "a\<in>set p" 
  shows "a \<in> Vs E"
  using assms edges_are_Vs
  by (induction, simp_all) fastforce

lemma path_suff:
  assumes "path E (p1 @ p2)"
  shows "path E p2"
  using assms
proof(induction p1)
  case (Cons a p1)
  then show ?case using Cons tl_path_is_path by force
qed simp

lemma path_pref:
  assumes "path E (p1 @ p2)"
  shows "path E p1"
  using assms
proof(induction p1)
  case (Cons a p1)
  then show ?case using Cons by (cases p1; auto simp add: mem_path_Vs)
qed simp

lemma rev_path_is_path:
  assumes "path E p"
  shows "path E (rev p)"
  using assms
proof(induction)
  case (path2 v v' vs)
  hence "{last (rev vs @ [v']), hd [v]} \<in> E" by (simp add: insert_commute)
  then show ?case using path2.IH path2.hyps(1) path_append
    by (metis edges_are_Vs path1 rev.simps(2))
qed simp_all

lemma Vs_subset:
  assumes "E \<subseteq> E'"
  shows "Vs E \<subseteq> Vs E'"
  using assms
  unfolding Vs_def
  by auto

lemma path_subset:
  assumes "path E p" "E \<subseteq> E'"
  shows "path E' p"
  using assms Vs_subset
  by (induction, auto)

lemma path_edges_of_path_refl: "length p \<ge> 2 \<Longrightarrow> path (set (edges_of_path p)) p"
proof (induction p rule: edges_of_path.induct)
  case (3 v v' l)
  thus ?case
    apply (cases l)
    by (auto intro: path_subset simp add: edges_are_Vs insert_commute path2)
qed simp_all

lemma edges_of_path_Vs: "Vs (set (edges_of_path p)) \<subseteq> set p"
  by (meson subsetI v_in_edge_in_path_gen vs_member_elim)

subsection \<open>walks, and connected components\<close>

definition "walk_betw E u p v \<equiv> (p \<noteq> [] \<and> path E p \<and> hd p = u \<and> last p = v)"

lemma nonempty_path_walk_between[intro?]:
  assumes "path E p" "p \<noteq> []" "hd p = u" "last p = v"
  shows "walk_betw E u p v"
  unfolding walk_betw_def using assms by simp

lemma walk_nonempty:
  assumes "walk_betw E u p v"
  shows [simp]: "p \<noteq> []"
  using assms walk_betw_def by fastforce

lemma walk_between_nonempty_path[elim]:
  assumes "walk_betw E u p v"
  shows "path E p" "p \<noteq> []" "hd p = u" "last p = v"
  using assms unfolding walk_betw_def by simp_all

lemma walk_reflexive:
  assumes "w \<in> Vs E"
  shows "walk_betw E w [w] w"
  by (simp add: assms nonempty_path_walk_between)

lemma walk_symmetric:
  assumes "walk_betw E u p v"
  shows "walk_betw E v (rev p) u"
  by (metis assms  Nil_is_rev_conv hd_rev rev_path_is_path rev_rev_ident walk_betw_def)

lemma walk_transitive:
  assumes "walk_betw E u p v" "walk_betw E v q w"
  shows "walk_betw E u (p @ tl q) w"
  using assms unfolding walk_betw_def
  using path_concat append_is_Nil_conv
  by (metis hd_append last_ConsL last_appendR last_tl list.exhaust_sel self_append_conv)

lemma walk_in_Vs:
  assumes "walk_betw E a p b"
  shows "set p \<subseteq> Vs E"
  by (meson assms mem_path_Vs subset_code(1) walk_betw_def)

lemma walk_endpoints:
  assumes "walk_betw E u p v"
  shows [simp]: "u \<in> Vs E"
  and   [simp]: "v \<in> Vs E"
  using assms mem_path_Vs walk_betw_def by fastforce+

lemma walk_pref:
  assumes "walk_betw E u (pr @ [x] @ su) v"
  shows "walk_betw E u (pr @ [x]) x"
  by (metis append.assoc assms hd_append path_pref snoc_eq_iff_butlast walk_betw_def)

lemma walk_suff:
  assumes "walk_betw E u (pr @ [x] @ su) v"
  shows "walk_betw E x (x # su) v"
  by (metis append_Cons append_Nil assms last_appendR list.distinct(1) list.sel(1) path_suff walk_betw_def)

lemma edges_are_walks:
  assumes "{v, w} \<in> E"
  shows "walk_betw E v [v, w] w"
  using assms edges_are_Vs nonempty_path_walk_between path1 path2
  by (metis insert_commute last.simps list.sel(1) list.simps(3))

lemma walk_subset:
  assumes "E \<subseteq> E'"
  assumes "walk_betw E u p v"
  shows "walk_betw E' u p v"
  using assms unfolding walk_betw_def
  using path_subset by blast

lemma induct_walk_betw[case_names path1 path2, consumes 1, induct set: walk_betw]:
  assumes "walk_betw E a p b"
  assumes Path1: "\<And>v. v \<in> Vs E \<Longrightarrow> P v [v] v"
  assumes Path2: "\<And>v v' vs b. {v, v'} \<in> E \<Longrightarrow> walk_betw E v' (v' # vs) b \<Longrightarrow> P v' (v' # vs) b \<Longrightarrow> P v (v # v' # vs) b"
  shows "P a p b"
proof-
  have "path E p" "p \<noteq> []" "hd p = a" "last p = b" using assms(1) by auto
  thus ?thesis
  proof(induction arbitrary: a b)
    case path0 thus ?case by simp
  next
    case path1 thus ?case using Path1 by fastforce
  next
    case path2 thus ?case
      by (metis Path2 last_ConsR list.distinct(1) list.sel(1) nonempty_path_walk_between)
  qed
qed

definition connected_component where
  "connected_component E v = {v'. v' = v \<or> (\<exists>p. walk_betw E v p v')}"

definition connected_components where
  "connected_components E \<equiv> {vs. \<exists>v. vs = connected_component E v \<and> v \<in> (Vs E)}"

lemma in_own_connected_component: "v \<in> connected_component E v"
  unfolding connected_component_def by simp

lemma in_connected_component_has_path:
  assumes "v \<in> connected_component E w" "w \<in> Vs E"
  obtains p where "walk_betw E w p v"
proof(cases "v = w")
  case True thus ?thesis using that assms(2) walk_reflexive by metis
next
  case False
  then obtain p where "walk_betw E w p v"
    using assms(1) unfolding connected_component_def by blast
  thus ?thesis using that by blast
qed

lemma has_path_in_connected_component[intro]:
  assumes "walk_betw E u p v"
  shows "v \<in> connected_component E u"
  unfolding connected_component_def using assms by blast

lemma connected_components_notE_singletons:
  assumes "x \<notin> Vs E"
  shows "connected_component E x = {x}"
proof(standard; standard)
  fix y assume yconnected: "y \<in> connected_component E x"
  {
    assume "x \<noteq> y"
    then obtain p where "walk_betw E x p y"
      using yconnected unfolding connected_component_def by blast
    hence "x \<in> Vs E" by simp
    hence False using assms by blast
  }
  thus "y \<in> {x}" by blast
next
  fix y assume "y \<in> {x}"
  hence "x = y" by blast
  thus "y \<in> connected_component E x" by (simp add: connected_component_def)
qed

lemma connected_components_member_sym:
  assumes "v \<in> connected_component E w"
  shows "w \<in> connected_component E v"
proof-
  {
    assume "v \<noteq> w"
    hence "w \<in> Vs E" using connected_components_notE_singletons assms by fastforce
    hence ?thesis
      by (meson assms has_path_in_connected_component in_connected_component_has_path walk_symmetric)
  }
  thus ?thesis using assms by blast
qed

lemma connected_components_member_trans:
  assumes "x \<in> connected_component E y" "y \<in> connected_component E z"
  shows "x \<in> connected_component E z"
proof-
  {
    assume "x \<noteq> y" "y \<noteq> z"
    hence "y \<in> Vs E" "z \<in> Vs E" using assms connected_components_notE_singletons by fastforce+
    hence "x \<in> connected_component E z"
      by (meson assms has_path_in_connected_component in_connected_component_has_path walk_transitive)
  }
  thus ?thesis using assms by blast
qed

lemma connected_components_member_eq:
  assumes "v \<in> connected_component E w"
  shows "connected_component E v = connected_component E w"
  using assms connected_components_member_sym connected_components_member_trans
  by (metis dual_order.antisym subsetI)

lemma connected_components_closed:
  assumes v1_in_C: "v1 \<in> connected_component E v4" and
    v3_in_C: "v3 \<in> connected_component E v4"
  shows "v3 \<in> connected_component E v1"
  using connected_components_member_eq v1_in_C v3_in_C by fastforce

lemma connected_components_closed':
  assumes C_is_comp: "C \<in> connected_components E"
  assumes v_in_C: "v \<in> C"
  shows "C = connected_component E v"
proof-
  from C_is_comp
  obtain v4 where v4: "C = connected_component E v4" "v4 \<in> Vs E"
    unfolding connected_components_def by blast
  thus ?thesis using connected_components_member_eq v_in_C by metis
qed

lemma connected_components_disj:
  assumes "C \<noteq> C'" "C \<in> connected_components E" "C' \<in> connected_components E"
  shows "C \<inter> C' = {}"
  by (metis assms connected_components_closed' disjoint_iff_not_equal)

lemma own_connected_component_unique:
  assumes "x \<in> Vs E"
  shows "\<exists>!C \<in> connected_components E. x \<in> C"
proof(standard, intro conjI)
  show "connected_component E x \<in> connected_components E"
    using assms connected_components_def by blast
  show "x \<in> connected_component E x" using in_own_connected_component by fastforce
  fix C assume "C \<in> connected_components E \<and> x \<in> C"
  thus "C = connected_component E x" by (simp add: connected_components_closed')
qed

lemma edge_in_component:
  assumes "{x,y} \<in> E"
  shows "\<exists>C. C \<in> connected_components E \<and> {x,y} \<subseteq> C"
proof-
  have "y \<in> connected_component E x"
  proof(standard, standard)
    show "path E [x, y]" by (metis assms edges_are_Vs insert_commute path1 path2)
  qed simp_all
  moreover have "x \<in> Vs E" by (meson assms edges_are_Vs)
  ultimately show ?thesis
    unfolding connected_components_def
    using in_own_connected_component
    by fastforce
qed

lemma edge_in_unique_component:
  assumes "{x,y} \<in> E"
  shows "\<exists>!C. C \<in> connected_components E \<and> {x,y} \<subseteq> C"
  using edge_in_component connected_components_closed'
  by (metis assms insert_subset)

lemma connected_component_set[intro]:
  assumes "u \<in> Vs E"
  assumes "\<And>x. x \<in> C \<Longrightarrow> \<exists>p. walk_betw E u p x"
  assumes "\<And>x p. walk_betw E u p x \<Longrightarrow> x \<in> C"
  shows "connected_component E u = C"
proof(standard; standard)
  fix x
  assume "x \<in> connected_component E u"
  thus "x \<in> C" by (meson assms(1) assms(3) in_connected_component_has_path)
next
  fix x
  assume "x \<in> C"
  thus "x \<in> connected_component E u" by (meson assms(2) has_path_in_connected_component)
qed

text\<open>
  Now we should be able to partition the set of edges into equivalence classes
  corresponding to the connected components.\<close>

definition component_edges where
"component_edges E C = {{x, y} | x y.  {x, y} \<subseteq> C \<and> {x, y} \<in> E}"

lemma component_edges_disj_edges:
  assumes "C \<in> connected_components E" "C' \<in> connected_components E" "C \<noteq> C'"
  assumes "v \<in> component_edges E C" "w \<in> component_edges E C'"
  shows "v \<inter> w = {}"
proof(intro equals0I)
  fix x assume "x \<in> v \<inter> w"
  hence "x \<in> C" "x \<in> C'" using assms(4, 5) unfolding component_edges_def by blast+
  thus False by (metis assms(1-3) connected_components_closed')
qed

lemma component_edges_disj:
  assumes "C \<in> connected_components E" "C' \<in> connected_components E" "C \<noteq> C'"
  shows "component_edges E C \<inter> component_edges E C' = {}"
proof(intro equals0I, goal_cases)
  case (1 y)
  hence "y = {}" using assms component_edges_disj_edges by (metis IntD1 IntD2 Int_absorb)
  thus False using 1 unfolding component_edges_def by blast
qed

lemma connected_component_subs_Vs:
  assumes "C \<in> connected_components E"
  shows "C \<subseteq> Vs E"
proof(safe)
  fix x assume "x \<in> C"
  from assms
  obtain y where "C = connected_component E y" "y \<in> Vs E"
    by (smt connected_components_def mem_Collect_eq)
  thus "x \<in> Vs E" by (metis \<open>x \<in> C\<close> in_connected_component_has_path walk_endpoints(2))
qed

definition components_edges where
"components_edges E = {component_edges E C| C. C \<in> connected_components E}"

lemma connected_comp_nempty:
  assumes "C \<in> connected_components E"
  shows "C \<noteq> {}"
  using assms unfolding connected_components_def
  using in_own_connected_component by fastforce

lemma connected_comp_verts_in_verts:
  assumes "v \<in> C" "C \<in> connected_components E"
  shows "v \<in> Vs E"
  using assms connected_component_subs_Vs by blast

lemma connected_comp_has_vert:
  assumes "C \<in> connected_components E"
  obtains w where "w \<in> Vs E" "C = connected_component E w"
  by (metis assms connected_comp_nempty connected_comp_verts_in_verts connected_components_closed' ex_in_conv)

lemma component_edges_partition:
  shows "\<Union> (components_edges E) = E \<inter> {{x,y}| x y. True}"
  unfolding components_edges_def
proof(safe)
  fix x y
  assume "{x, y} \<in> E"
  then obtain C where "{x, y} \<subseteq> C" "C \<in> connected_components E" by (meson edge_in_component)
  moreover then have "{x, y} \<in> component_edges E C"
    using \<open>{x, y} \<in> E\<close> component_edges_def by fastforce
  ultimately show "{x, y} \<in> \<Union> {component_edges E C |C. C \<in> connected_components E}" by blast
qed (auto simp add: component_edges_def)

text\<open>Since one of the matchings is bigger, there must be one edge equivalence class
  that has more edges from the bigger matching.\<close>

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

(*
  The edges in that bigger equivalence class can be ordered in a path, since the degree of any
  vertex cannot exceed 2. Also that path should start and end with edges from the bigger matching.
*)

subsection\<open>Alternating lists and auxilliary theory about them\<close>

inductive alt_list where
"alt_list P1 P2 []" |
"P1 x \<Longrightarrow> alt_list P2 P1 l \<Longrightarrow> alt_list P1 P2 (x#l)"

inductive_simps alt_list_empty: "alt_list P1 P2 []"
inductive_simps alt_list_step: "alt_list P1 P2 (x#l)"

lemma induct_list012:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. \<lbrakk> P zs; P (y # zs) \<rbrakk> \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_alt_list012[consumes 1, case_names nil single sucsuc]:
  assumes "alt_list P1 P2 l"
  assumes "T []"
  assumes "\<And>x. P1 x \<Longrightarrow> T [x]"
  assumes "\<And>x y zs. P1 x \<Longrightarrow> P2 y \<Longrightarrow> T zs \<Longrightarrow> T (x#y#zs)"
  shows "T l"
  using assms(1)
proof(induction l rule: induct_list012)
  case 1 thus ?case using assms(2) by simp
next
  case (2 x) thus ?case
    by (simp add: alt_list_step assms(3))
next
  case (3 x y zs)
  hence "T zs" by (simp add: alt_list_step)
  thus ?case by (metis "3.prems" alt_list_step assms(4))
qed

lemma alternating_length:
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length l = length (filter P1 l) + length (filter P2 l)"
  using assms by (induction l) auto

lemma alternating_length_balanced:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) \<or>
         length (filter P1 l) = length (filter P2 l) + 1"
  using assms by (induction l) auto

lemma alternating_eq_iff_even:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) \<longleftrightarrow> even (length l)"
proof
  assume "length (filter P1 l) = length (filter P2 l)"
  thus "even (length l)" using assms alternating_length by force
next
  assume "even (length l)"
  thus "length (filter P1 l) = length (filter P2 l)"
    using assms alternating_length_balanced
    by (metis (no_types, lifting) alternating_length even_add odd_one)
qed

lemma alternating_eq_iff_odd:
  assumes "alt_list P1 P2 l" "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "length (filter P1 l) = length (filter P2 l) + 1 \<longleftrightarrow> odd (length l)"
proof
  assume "length (filter P1 l) = length (filter P2 l) + 1"
  thus "odd (length l)" using assms alternating_length by force
next
  assume "odd (length l)"
  thus "length (filter P1 l) = length (filter P2 l) + 1"
    using assms alternating_length_balanced alternating_eq_iff_even by blast
qed

lemma alternating_list_odd_index:
  assumes "alt_list P1 P2 l" "odd n" "n < length l"
  shows "P2 (l ! n)"
  using assms
proof(induction arbitrary: n rule: induct_alt_list012)
  case (sucsuc x y zs)
  consider (l) "n = 1" | (h) "n \<ge> 2" using odd_pos sucsuc.prems(1) by fastforce
  thus ?case
  proof cases
    case l thus ?thesis by (simp add: sucsuc.hyps(2))
  next
    case h
    then obtain m where "n = Suc (Suc m)" using add_2_eq_Suc le_Suc_ex by blast
    hence "P2 (zs ! m)" using sucsuc.IH sucsuc.prems(1, 2) by fastforce
    thus ?thesis by (simp add: \<open>n = Suc (Suc m)\<close>)
  qed
qed simp_all

lemma alternating_list_even_index:
  assumes "alt_list P1 P2 l" "even n" "n < length l"
  shows "P1 (l ! n)"
  using assms
proof(induction arbitrary: n rule: induct_alt_list012)
  case (sucsuc x y zs)
  consider (l) "n = 0" | (h) "n \<ge> 2" using odd_pos sucsuc.prems(1) by fastforce
  thus ?case
  proof cases
    case l thus ?thesis by (simp add: sucsuc.hyps(1))
  next
    case h
    then obtain m where "n = Suc (Suc m)" using add_2_eq_Suc le_Suc_ex by blast
    hence "P1 (zs ! m)" using sucsuc.IH sucsuc.prems(1, 2) by fastforce
    thus ?thesis by (simp add: \<open>n = Suc (Suc m)\<close>)
  qed
qed simp_all

lemma alternating_list_even_last:
  assumes "alt_list P1 P2 l" "even (length l)" "l \<noteq> []"
  shows "P2 (last l)"
proof-
  have "odd (length l - 1)" by (simp add: assms(2) assms(3))
  hence "P2 (l ! (length l - 1))" using alternating_list_odd_index
    by (metis assms(1) assms(3) diff_less length_greater_0_conv odd_one odd_pos)
  thus ?thesis using assms(3) by (simp add: last_conv_nth)
qed

lemma alternating_list_odd_last:
  assumes "alt_list P1 P2 l" "odd (length l)"
  shows "P1 (last l)"
proof-
  have "even (length l - 1)" by (simp add: assms(2))
  hence "P1 (l ! (length l - 1))" using alternating_list_even_index
    using assms(1) assms(2) odd_pos by fastforce
  thus ?thesis using assms(2) last_conv_nth odd_pos by force
qed

lemma alternating_list_gt_odd:
  assumes "length (filter P1 l) > length (filter P2 l)"
  assumes "alt_list P1 P2 l"
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "odd (length l)"
  using assms alternating_eq_iff_even by fastforce

lemma alternating_list_eq_even:
  assumes "length (filter P1 l) = length (filter P2 l)"
  assumes "alt_list P1 P2 l" (* not actually used but complements gt_odd *)
  assumes "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "even (length l)"
  using assms alternating_eq_iff_even by fastforce

lemma alternating_list_eq_last':
  assumes "length (filter P1 l) = length (filter P2 l)"
          "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
          "l \<noteq> []"
          "P2 (last l)"
        shows "\<not> alt_list P2 P1 l"
  by (metis alternating_eq_iff_even alternating_list_even_last assms last_in_set)

lemma alternating_list_gt:
  assumes "length (filter P1 l) > length (filter P2 l)"
          "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
          "alt_list P1 P2 l"
  shows "P1 (hd l) \<and> P1 (last l)"
  using alternating_list_odd_last assms
  by (metis alt_list_step alternating_list_gt_odd filter.simps(1) list.exhaust_sel nat_neq_iff)

lemma alt_list_not_commute:
  assumes "alt_list P1 P2 l"
          "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
          "l \<noteq> []"
    shows "\<not> alt_list P2 P1 l"
  using assms
  apply(cases "l = []"; simp)
  by (metis alt_list.cases list.inject list.set_intros(1))

lemma alternating_list_gt_or:
  assumes "length (filter P1 l) > length (filter P2 l)"
          "\<forall>x\<in>set l. P1 x \<longleftrightarrow> \<not> P2 x"
    shows "\<not> alt_list P2 P1 l"
  using alternating_length_balanced assms by fastforce

lemma alt_list_cong_1:
  assumes "alt_list P1 P2 l" "\<forall>x \<in> set l. P2 x \<longrightarrow> P3 x"
  shows "alt_list P1 P3 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_cong_2:
  assumes "alt_list P1 P2 l" "\<forall>x \<in> set l. P1 x \<longrightarrow> P3 x"
  shows "alt_list P3 P2 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_cong:
  assumes "alt_list P1 P2 l" "\<forall>x \<in> set l. P1 x \<longrightarrow> P3 x" "\<forall>x \<in> set l. P2 x \<longrightarrow> P4 x"
  shows "alt_list P3 P4 l"
  using assms
  by (induction rule: induct_alt_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_append_1:
  assumes "alt_list P1 P2 (l1 @ l2)"
  shows "alt_list P1 P2 l1  \<and> (alt_list P1 P2 l2 \<or> alt_list P2 P1 l2)"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_empty alt_list_step)

lemma alt_list_append_2:
  assumes "alt_list P1 P2 l1" "alt_list P2 P1 l2" "odd (length l1)"
  shows "alt_list P1 P2 (l1 @ l2)"
  using assms
proof (induction l1 rule: induct_list012)
  case (3 x y zs)
  hence "zs \<noteq> []" by force
  hence "alt_list P1 P2 (zs @ l2)"
    by (metis "3.IH"(1) "3.prems" alt_list_step even_Suc_Suc_iff length_Cons)
  thus ?case by (metis "3.prems"(1) alt_list_step append_Cons)
qed (simp_all add: alt_list_step)

lemma alt_list_append_3:
  assumes "alt_list P1 P2 l1" "alt_list P1 P2 l2" "even (length l1)"
  shows "alt_list P1 P2 (l1 @ l2)"
  using assms
proof (induction l1 rule: induct_list012)
  case (3 x y zs)
  hence "alt_list P1 P2 (zs @ l2)" by (simp add: alt_list_step)
  thus ?case by (metis "3.prems"(1) alt_list_step append_Cons)
qed (simp_all add: alt_list_step)

lemma alt_list_split_1:
  assumes "alt_list P1 P2 (l1 @ l2)" "even (length l1)"
  shows "alt_list P1 P2 l2"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_step)

lemma alt_list_split_2:
  assumes "alt_list P1 P2 (l1 @ l2)" "odd (length l1)"
  shows "alt_list P2 P1 l2"
  using assms
  by (induction l1 rule: induct_list012)
     (simp_all add: alt_list_step)

lemma alt_list_append_1':
  assumes "alt_list P1 P2 (l1 @ l2)" "l1 \<noteq> []" "\<forall>x\<in>set l1. P1 x = (\<not> P2 x)"
  shows "(alt_list P1 P2 l1  \<and> ((P2 (last l1) \<and> alt_list P1 P2 l2) \<or> (P1 (last l1) \<and> alt_list P2 P1 l2)))"
  using assms
  by (smt alt_list_append_1 alt_list_step append.assoc append_Cons append_Nil append_butlast_last_id)

lemma
  assumes "alt_list P1 P2 (l1 @ a # a' # l2)" "\<forall>x\<in> {a, a'}. P1 x = (\<not> P2 x)"
  shows alt_list_append_1'': "P1 a \<Longrightarrow> P2 a'"
    and alt_list_append_1''': "P1 a' \<Longrightarrow> P2 a"
    and alt_list_append_1'''': "P2 a' \<Longrightarrow> P1 a"
    and alt_list_append_1''''': "P2 a \<Longrightarrow> P1 a'"
proof-
  have "alt_list P1 P2 ((l1 @ [a, a']) @ l2)" by (simp add: assms(1))
  hence list_pref: "alt_list P1 P2 (l1 @ [a, a'])" using alt_list_append_1 by blast
  { assume "P1 a" thus "P2 a'" using list_pref alt_list_append_1 alt_list_step assms(2)
      by (metis insert_iff)
  }
  { assume "P2 a" thus "P1 a'" using list_pref alt_list_append_1 alt_list_step assms(2)
      by (metis insert_iff)
  }
  { assume "P1 a'" thus "P2 a" using \<open>P1 a \<Longrightarrow> P2 a'\<close> assms(2) by blast
  }
  { assume "P2 a'" thus "P1 a" using \<open>P2 a \<Longrightarrow> P1 a'\<close> assms(2) by blast
  }
qed

lemma alt_list_rev_even:
  assumes "alt_list P1 P2 l" "even (length l)"
  shows "alt_list P2 P1 (rev l)"
  using assms
proof(induction rule: induct_alt_list012)
  case (sucsuc x y zs)
  hence "alt_list P2 P1 (rev zs)" by simp
  moreover have "alt_list P2 P1 [y, x]"
    by (simp add: alt_list_empty alt_list_step sucsuc.hyps(1) sucsuc.hyps(2))
  ultimately have "alt_list P2 P1 (rev zs @ [y, x])"
    using alt_list_append_3 sucsuc.prems by fastforce
  thus ?case by simp
qed (simp_all add: alt_list_empty)

lemma alt_list_rev:
  assumes "alt_list P1 P2 l" "odd (length l)"
  shows "alt_list P1 P2 (rev l)" 
  using assms
proof-
  obtain x zs where "l = x # zs" using assms(2) by (cases l, fastforce+)
  hence "alt_list P1 P2 (rev zs)" using alt_list_rev_even
    by (metis alt_list_step assms(1) assms(2) even_Suc length_Cons)
  moreover have "alt_list P1 P2 [x]"
    by (metis \<open>l = x # zs\<close> alt_list_empty alt_list_step assms(1))
  ultimately show ?thesis using alt_list_append_3 \<open>l = x # zs\<close> assms(2) by fastforce
qed

subsection\<open>Every connected component can be linearised in a path.\<close>

lemma path_subset_conn_comp:
  assumes "path E p"
  shows "set p \<subseteq> connected_component E (hd p)"
  using assms
proof(induction)
  case path0
  then show ?case by simp
next
  case path1
  then show ?case using in_own_connected_component by simp
next
  case (path2 v v' vs)
  hence "path E [v', v]" by (metis edges_are_Vs insert_commute path1 path_2)
  hence "v \<in> connected_component E v'"
    by (metis connected_components_closed' edge_in_component insert_subset path2.hyps(1))
  moreover hence "connected_component E v = connected_component E v'"
    by (simp add: connected_components_member_eq)
  ultimately show ?case using path2.IH by fastforce
qed

lemma path_in_connected_component:
  assumes "path E p" "hd p \<in> connected_component E x"
  shows "set p \<subseteq> connected_component E x"
  using assms connected_components_member_eq path_subset_conn_comp
  by metis

lemma component_has_path:
  assumes "finite C'" "C' \<subseteq> C" "C \<in> connected_components E"
  shows "\<exists>p. path E p \<and> C' \<subseteq> (set p) \<and> (set p) \<subseteq> C"
  using assms
proof(induction C')
  case empty thus ?case
    using path0 by fastforce
next
  case ass: (insert x F)
  then obtain p where p: "path E p" "F \<subseteq> set p" "set p \<subseteq> C"
    by (meson insert_subset)
  have "x \<in> C" using ass.prems(1) by blast
  hence C_def: "C = connected_component E x"
    by (simp add: assms(3) connected_components_closed')

  show ?case
  proof(cases "p = []")
    case True
    have "path E [x]" using ass connected_comp_verts_in_verts by force
    then show ?thesis using True p ass.prems(1) by fastforce
  next
    case F1: False
    then obtain h t where "p = h # t" using list.exhaust_sel by blast
    hence walkhp: "walk_betw E h p (last p)" using p(1) walk_betw_def by fastforce

    have "h \<in> C" using \<open>p = h # t\<close> p(3) by fastforce
    then obtain q where walkxh: "walk_betw E x q h"
      by (metis C_def \<open>x \<in> C\<close> assms(3) connected_comp_verts_in_verts in_connected_component_has_path)
    hence walkxp: "walk_betw E x (q @ tl p) (last p)" by (meson walk_transitive walkhp)

    hence "path E (q @ tl p)" by fastforce
    moreover from walkxp have "set (q @ tl p) \<subseteq> C" by (metis C_def path_subset_conn_comp walk_betw_def)
    moreover {
      from walkxh have "last q = h" "hd q = x" by fastforce+
      then have "insert x F \<subseteq> set (q @ tl p)" using \<open>p = h # t\<close> walkxh p(2) by fastforce
    }
    ultimately show ?thesis by blast
  qed
qed

lemma component_has_path':
  assumes "finite C" "C \<in> connected_components E"
  shows "\<exists>p. path E p \<and> C = (set p)"
  using assms component_has_path
  by (metis subset_antisym subset_refl)

subsection\<open>Every connected component can be linearised in a simple path\<close>

text\<open>An important part of this proof is setting up and indeuction on the graph, i.e. on a set of
     edges, and the different cases that could arise.\<close>

definition card' :: "'a set \<Rightarrow> enat" where
  "card' A \<equiv> (if infinite A then \<infinity> else card A)"
lemma card'_finite: "finite A \<Longrightarrow> card' A = card A"
  unfolding card'_def by simp
lemma card'_mono: "A \<subseteq> B \<Longrightarrow> card' A \<le> card' B"
  by (metis card'_def card_mono enat_ord_code(3) enat_ord_simps(1) finite_subset)
lemma card'_empty[iff]: "(card' A = 0) \<longleftrightarrow> A = {}"
  unfolding card'_def using enat_0_iff(2) by auto
lemma card'_finite_nat[iff]: "(card' A = numeral m) \<longleftrightarrow> (finite A \<and> card A = numeral m)"
  unfolding card'_def
  by (simp add: numeral_eq_enat)
declare one_enat_def[iff]
declare zero_enat_def[iff]
lemma card'_finite_enat[iff]: "(card' A = enat m) \<longleftrightarrow> (finite A \<and> card A = m)"
  unfolding card'_def by simp

lemma card'_1_singletonE:
  assumes "card' A = 1"
  obtains x where "A = {x}"
  using assms unfolding card'_def
  by (metis card_1_singletonE enat_1_iff(1) infinity_ne_i1)

lemma card'_insert: "card' (insert a A) = (if a \<in> A then id else eSuc) (card' A)"
  unfolding card'_def using card_insert_if finite_insert
  by (simp add: card_insert_if eSuc_enat)

definition degree where
  "degree E v \<equiv> card' ({e. v \<in> e} \<inter> E)"

lemma degree_def2: "degree E v \<equiv> card' {e \<in> E. v \<in> e}"
  unfolding degree_def
  by (simp add: Collect_conj_eq Int_commute)

lemma degree_Vs: "degree E v \<ge> 1" if "v \<in> Vs E"
proof-
  obtain e where "e \<in> E" "v \<in> e" by (metis UnionE Vs_def \<open>v \<in> Vs E\<close>)
  hence "{e} \<subseteq> {e \<in> E. v \<in> e}" by simp
  moreover have "card' {e} = 1" by simp
  ultimately show ?thesis unfolding degree_def2 by (metis card'_mono)
qed

lemma degree_not_Vs: "degree E v = 0" if "v \<notin> Vs E"
  using that unfolding Vs_def degree_def by blast

lemma degree_insert: "v \<in> a \<Longrightarrow> a \<notin> E \<Longrightarrow> degree (insert a E) v = eSuc (degree E v)"
  unfolding degree_def by (simp add: card'_insert)

lemma degree_empty[simp]: "degree {} a = 0"
  unfolding degree_def by simp

lemma degree_card_all:
  assumes "card E \<ge> numeral m"
  assumes "\<forall>e \<in> E. a \<in> e"
  assumes "finite E"
  shows "degree E a \<ge> numeral m"
  using assms unfolding degree_def
  by (simp add: card'_finite inf.absorb2 subsetI)

lemma subset_edges_less_degree:
  assumes "E' \<subseteq> E"
  shows "degree E' v \<le> degree E v"
  unfolding degree_def using card'_mono
  by (metis Int_mono assms subset_refl)

lemma less_edges_less_degree:
  shows "degree (E - E') v \<le> degree E v"
  by (intro subset_edges_less_degree)
     (simp add: subset_edges_less_degree)

lemma in_edges_of_path':
  assumes "v \<in> set p" "length p \<ge> 2"
  shows "v \<in> Vs (set (edges_of_path p))"
  unfolding Vs_def using assms
  by (meson Union_iff path_vertex_has_edge)

lemma in_edges_of_path:
  assumes "v \<in> set p" "v \<noteq> hd p"
  shows "v \<in> Vs (set (edges_of_path p))"
proof-
  have "length p \<ge> 2" using assms(1) assms(2) hd_conv_nth in_set_conv_nth length_pos_if_in_set
    by (metis One_nat_def Suc_1 Suc_leI Suc_lessI length_greater_0_conv less_Suc0)
  thus ?thesis by (simp add: assms(1) in_edges_of_path')
qed

lemma degree_edges_of_path_hd:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (hd p) = 1"
proof-
  obtain h nxt rest where p_def: "p = h # nxt # rest" using assms(2)
    by (metis One_nat_def Suc_1 Suc_le_length_iff)
  have calc: "{e. hd (h # nxt # rest) \<in> e} \<inter> set (edges_of_path (h # nxt # rest)) = {{h, nxt}}"
  proof(standard; standard)
    fix e assume "e \<in> {e. hd (h # nxt # rest) \<in> e} \<inter> set (edges_of_path (h # nxt # rest))"
    hence "e = {h, nxt} \<or> e \<in> set (edges_of_path (nxt # rest))" "h \<in> e" by fastforce+
    hence "e = {h, nxt}" using assms(1) v_in_edge_in_path_gen unfolding p_def by fastforce
    then show "e \<in> {{h, nxt}}" by simp
  qed simp
  show ?thesis unfolding p_def degree_def calc by simp
qed

lemma degree_edges_of_path_last:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (last p) = 1"
proof-
  have "distinct (rev p)" using assms(1) by simp
  moreover have "length (rev p) \<ge> 2" using assms(2) by simp
  ultimately have "degree (set (edges_of_path (rev p))) (hd (rev p)) = 1"
    using degree_edges_of_path_hd by blast
  then show ?thesis using edges_of_path_rev set_rev hd_rev \<open>2 \<le> length (rev p)\<close>
    by (metis length_0_conv length_rev not_numeral_le_zero)
qed

lemma degree_edges_of_path_ge_2:
  assumes "distinct p" "v\<in>set p" "v \<noteq> hd p" "v \<noteq> last p"
  shows "2 = degree (set (edges_of_path p)) v"
  using assms
proof(induction p arbitrary: v rule: induct_list012)
  case 1 then show ?case by simp
next
  case 2 then show ?case by simp
next
  case Cons: (3 a a' p v)
  thus ?case
  proof(cases p)
    case Nil thus ?thesis using Cons.prems by simp
  next
    case p: (Cons a'' p')
    let ?goalset = "{e. a' \<in> e} \<inter> set (edges_of_path (a # a' # a'' # p'))"
    {
      have anotaa: "{a, a'} \<noteq> {a', a''}" using p Cons.prems(1) by fastforce
      moreover have "?goalset = {{a, a'}, {a', a''}}"
      proof(standard; standard)
        fix e assume "e \<in> ?goalset"
        moreover have "a' \<notin> f" if "f \<in> set (edges_of_path (a'' # p'))" for f
          using Cons.prems(1) p that v_in_edge_in_path_gen by fastforce
        ultimately show "e \<in> {{a, a'}, {a', a''}}" by force
      qed fastforce
      moreover have "card {{a, a'}, {a', a''}} = 2" using anotaa by simp
      ultimately have "2 = degree (set (edges_of_path (a # a' # p))) a'"
        unfolding degree_def p by simp
    }
    moreover {
      fix w assume "w \<in> set (a' # p)" "w \<noteq> hd (a' # p)" "w \<noteq> last (a' # p)"
      hence "2 = degree (set (edges_of_path (a' # p))) w"
        using Cons.IH(2) Cons.prems(1) by fastforce
      moreover have "w \<notin> {a, a'}"
        using Cons.prems(1) \<open>w \<in> set (a' # p)\<close> \<open>w \<noteq> hd (a' # p)\<close> by auto
      ultimately have "2 = degree (set (edges_of_path (a # a' # p))) w" unfolding degree_def by simp
    }
    ultimately show ?thesis using Cons.prems(2-4) by auto
  qed
qed

lemma path_repl_edge:
  assumes "path (insert {w, x} E) p" "p \<noteq> []" "walk_betw E w puv x"
  shows "\<exists>p'. walk_betw E (hd p) p' (last p)"
  using assms
proof(induction)
  case path0
  then show ?case
    using path0
    by fastforce
next
  case (path1 v)
  hence "v \<in> Vs E" by (metis Sup_insert UnE Vs_def empty_iff insert_iff walk_endpoints)
  then show ?case using walk_reflexive by fastforce
next
  case (path2 v v' vs)
  then obtain p' where p': "walk_betw E v' p' (last (v' # vs))" by force
  consider (wx) "{v, v'} = {w, x}" | (E) "{v, v'} \<in> E" using path2.hyps(1) by blast
  then obtain q' where q': "walk_betw E v q' v'"
  proof cases
    case wx
    then consider "v = w" "v' = x" | "v = x" "v' = w" by force
    thus ?thesis using that assms(3) walk_symmetric by fast
  next
    case E
    hence "walk_betw E v [v, v'] v'" by (simp add: edges_are_Vs insert_commute walk_betw_def)
    thus ?thesis using that by blast
  qed
  show ?case using p' q' walk_transitive by fastforce
qed

lemma same_con_comp_walk:
  assumes "C \<in> connected_components E" "w \<in> C" "x \<in> C"
  obtains pwx where "walk_betw E w pwx x"
proof-
  have "C = connected_component E w" by (simp add: assms(1) assms(2) connected_components_closed')
  thus ?thesis by (metis assms connected_comp_verts_in_verts in_connected_component_has_path that)
qed

lemma in_con_compI:
  assumes "walk_betw E u puv v" "u \<in> C" "C \<in> connected_components E"
  shows "v \<in> C"
  using assms connected_components_closed' by fastforce

lemma path_can_be_split:
  assumes "walk_betw (insert {w, x} E) u p v" "w \<in> Vs E" "x \<in> Vs E"
  shows "(\<exists>p. walk_betw E u p v) \<or>
         (\<exists>p1 p2. walk_betw E u p1 w \<and> walk_betw E x p2 v) \<or>
         (\<exists>p1 p2. walk_betw E u p1 x \<and> walk_betw E w p2 v)"
  using assms
proof(induction)
  case (path1 v)
  thus ?case
    by (metis Sup_insert Vs_def empty_subsetI insert_subset subset_Un_eq walk_reflexive)
next
  case (path2 v v' vs b)
  consider "{v, v'} = {w, x}" | "{v, v'} \<in> E" using path2.hyps(1) by blast
  then show ?case
  proof cases
    case 1 thus ?thesis
      by (metis doubleton_eq_iff path2.IH path2.prems walk_reflexive)
  next
    case 2 thus ?thesis
      by (metis Vs_def edges_are_walks path2.IH path2.prems walk_symmetric walk_transitive)
  qed
qed

lemma path_can_be_split_2:
  assumes "walk_betw (insert {w, x} E) u p v" "w \<in> Vs E" "x \<notin> Vs E"
  shows "(\<exists>p'. walk_betw E u p' v) \<or>
         (\<exists>p'. walk_betw E u p' w \<and> v = x) \<or>
         (\<exists>p'. walk_betw E w p' v \<and> u = x) \<or>
         (u = x \<and> v = x)"
  using assms
proof(induction)
  case path1
  then show ?case by (metis Sup_insert Un_insert_left Vs_def insertE insert_is_Un walk_reflexive)
next
  case (path2 u u' us v)
  hence walku'v: "(\<exists>p'. walk_betw E u' p' v) \<or>
         (\<exists>p'. walk_betw E u' p' w \<and> v = x) \<or>
         (\<exists>p'. walk_betw E w p' v \<and> u' = x) \<or>
         (u' = x \<and> v = x)" by simp
  consider (u'x) "u' = x" | (unx) "u' \<in> Vs E" "u = x" | (uunx) "u' \<in> Vs E" "u \<in> Vs E"
    by (metis doubleton_eq_iff edges_are_Vs insertE path2.hyps(1) path2.prems(1))
  thus ?case
  proof cases
    case u'x
    hence "u = w" by (metis doubleton_eq_iff edges_are_Vs insertE path2.hyps(1) path2.prems(2))
    thus ?thesis using u'x walku'v by (meson path2.prems(1, 2) walk_endpoints(1) walk_reflexive)
  next
    case unx
    thus ?thesis by (metis doubleton_eq_iff edges_are_Vs insertE path2.IH path2.hyps(1) path2.prems(2))
  next
    case uunx
    hence "u \<noteq> x" "u' \<noteq> x" using path2.prems(2) by blast+
    hence "\<exists>p. walk_betw E u p u'" using edges_are_walks path2.hyps(1) by fastforce
    thus ?thesis using walku'v by (meson \<open>u' \<noteq> x\<close> walk_transitive)
  qed
qed

lemma path_can_be_split_3:
  assumes "walk_betw (insert {w, x} E) u p v" "w \<notin> Vs E" "x \<notin> Vs E"
  shows "walk_betw E u p v \<or> walk_betw {{w, x}} u p v"
  using assms
proof(induction)
  case path1
  then show ?case
    by (metis Sup_insert Un_iff Vs_def walk_reflexive)
next
  case (path2 u u' us v)
  then consider "walk_betw E u' (u' # us) v" | "walk_betw {{w, x}} u' (u' # us) v" by blast
  thus ?case
  proof cases
    case 1
    have "{u, u'} \<in> E"
      by (metis "1" doubleton_eq_iff insertE path2.hyps(1) path2.prems(1) path2.prems(2) walk_endpoints(1))
    hence "walk_betw E u (u # u' # us) v"
      by (metis "1" last_ConsR list.sel(1) list.simps(3) path.path2 walk_betw_def)
    then show ?thesis by blast
  next
    case 2
    have "u' \<in> Vs {{w, x}}" using "2" by fastforce
    hence "{u, u'} \<notin> E"
      by (metis DiffD2 Diff_insert_absorb UnionI Vs_def ccpo_Sup_singleton insert_iff path2.prems(1) path2.prems(2))
    hence "{u, u'} \<in> {{w, x}}" using path2.hyps(1) by blast
    hence "walk_betw {{w, x}} u (u # u' # us) v"
      by (metis "2" last_ConsR list.sel(1) list.simps(3) path.path2 walk_betw_def)
    then show ?thesis by blast
  qed
qed

lemma connected_component_transport[intro]:
  assumes ass: "C \<in> connected_components E"
  assumes "\<And>u v p. u \<in> C \<Longrightarrow> v \<in> C \<Longrightarrow> walk_betw E u p v \<Longrightarrow> \<exists>q. walk_betw E' u q v"
  assumes "\<And>u v p. u \<in> C \<Longrightarrow> walk_betw E' u p v \<Longrightarrow> v \<in> C"
  shows "C \<in> connected_components E'"
proof-
  from ass
  obtain w where "w \<in> Vs E" "C = connected_component E w" using connected_comp_has_vert by blast
  hence "w \<in> Vs E'"
    by (metis ass assms(2) in_own_connected_component same_con_comp_walk walk_endpoints(2))
  hence "connected_component E' w = C"
    unfolding connected_components_def
  proof(standard, goal_cases)
    case (1 x)
    then obtain p where "walk_betw E' w p x" using in_own_connected_component same_con_comp_walk
      by (metis \<open>C = connected_component E w\<close> ass assms(2))
    thus ?case by blast
  next
    case (2 x)
    thus ?case using \<open>C = connected_component E w\<close> assms(3) in_own_connected_component by metis
  qed
  thus "C \<in> connected_components E'"
    by (metis \<open>w \<in> Vs E'\<close> connected_components_closed' own_connected_component_unique)
qed

lemma unchanged_con_comp_1:
  assumes "u \<notin> C" "v \<notin> C" "u \<in> Vs E" "v \<in> Vs E"
  shows "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u, v} E)"
proof(standard)
  assume ass: "C \<in> connected_components E"
  thus "C \<in> connected_components (insert {u, v} E)"
  proof (rule connected_component_transport, goal_cases)
    case 1 thus ?case by (meson subset_insertI walk_subset)
  next
    case 2 thus ?case by (meson ass assms in_con_compI path_can_be_split)
  qed
next
  assume ass: "C \<in> connected_components (insert {u, v} E)"
  thus "C \<in> connected_components E"
  proof (standard, goal_cases)
    case (1 x y p)
    have "\<not> walk_betw E u q y" for q
      by (meson "1"(2) ass assms(1) in_con_compI subset_insertI walk_subset walk_symmetric)
    moreover have "\<not> walk_betw E v q y" for q
      by (meson "1"(2) ass assms(2) in_con_compI subset_insertI walk_subset walk_symmetric)
    ultimately show ?case
      by (meson "1"(3) assms(3, 4) path_can_be_split)
  next
    case 2 thus ?case by (meson ass in_con_compI subset_insertI walk_subset)
  qed
qed

lemma unchanged_con_comp_2:
  assumes "u \<notin> C" "v \<notin> C" "u \<in> Vs E" "v \<notin> Vs E"
  shows "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u, v} E)"
proof
  show "C \<in> connected_components (insert {u, v} E)" if "C \<in> connected_components E"
    using that
  proof(standard, goal_cases)
    case 1 thus ?case by (meson subset_insertI walk_subset)
  next
    case (2 x y p)
    hence "\<exists>r. walk_betw E x r y" by (metis assms in_con_compI path_can_be_split_2 that)
    thus ?case by (meson "2"(1) in_con_compI that)
  qed
  show "C \<in> connected_components E" if "C \<in> connected_components (insert {u, v} E)"
    using that
  proof(standard, goal_cases)
    case 1 thus ?case using assms(2-4) path_can_be_split_2 by fastforce
  next
    case 2 thus ?case by (meson in_con_compI subset_insertI that walk_subset)
  qed
qed

lemma unchanged_con_comp_3:
  assumes "u \<notin> C" "v \<notin> C" "u \<notin> Vs E" "v \<notin> Vs E"
  shows "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u, v} E)"
proof(standard)
  assume ass: "C \<in> connected_components E"
  thus "C \<in> connected_components (insert {u, v} E)"
  proof (standard, goal_cases)
    case 1 thus ?case by (meson subset_insertI walk_subset)
  next
    case (2 x y p)
    have "x \<noteq> u" "x \<noteq> v"
      using "2"(1) assms(1, 2) by blast+
    thus ?case using path_can_be_split_3[OF "2"(2) assms(3, 4)]
      by (metis "2"(1) Vs_def ass ccpo_Sup_singleton in_con_compI insertE singleton_iff walk_endpoints(1))
  qed
next
  assume ass: "C \<in> connected_components (insert {u, v} E)"
  thus "C \<in> connected_components E"
  proof (standard, goal_cases)
    case (1 x y p)
    have "x \<noteq> u" "x \<noteq> v"
      using "1"(1) assms(1, 2) by blast+
    thus ?case using path_can_be_split_3[OF "1"(3) assms(3, 4)]
      by (metis Vs_def ccpo_Sup_singleton insert_iff singletonD walk_endpoints(1))
  next
    case 2 thus ?case by (meson ass in_con_compI subset_insertI walk_subset)
  qed
qed

lemma unchanged_connected_component:
  assumes "u \<notin> C" "v \<notin> C"
  shows "C \<in> connected_components E \<longleftrightarrow> C \<in> connected_components (insert {u, v} E)"
  using assms unchanged_con_comp_1 unchanged_con_comp_2 unchanged_con_comp_3
  by (metis doubleton_eq_iff)

lemma connected_components_union:
  assumes "Cu \<in> connected_components E" "Cv \<in> connected_components E"
  assumes "u \<in> Cu" "v \<in> Cv"
  shows "Cu \<union> Cv \<in> connected_components (insert {u, v} E)"
proof-
  have "u \<in> Vs (insert {u, v} E)" using assms(1) by (simp add: Vs_def)
  have "v \<in> Vs (insert {u, v} E)" using assms(1) by (simp add: Vs_def)
  hence "connected_component (insert {u, v} E) v = Cu \<union> Cv"
  proof(standard, goal_cases)
    case (1 x)
    hence "\<exists>p. walk_betw E u p x \<or> walk_betw E v p x" by (meson Un_iff assms(1-4) same_con_comp_walk)
    hence "\<exists>p. walk_betw (insert {u, v} E) u p x \<or> walk_betw (insert {u, v} E) v p x"
      by (meson subset_insertI walk_subset)
    then show ?case by (metis (full_types) edges_are_walks insert_commute insert_iff walk_transitive)
  next
    case (2 x p)
    then obtain p where "walk_betw (insert {u, v} E) v p x"
      by (meson \<open>v \<in> Vs (insert {u, v} E)\<close> in_connected_component_has_path)
    hence "\<exists>q. walk_betw E v q x \<or> walk_betw E u q x"
      by (meson assms(1-4) connected_comp_verts_in_verts empty_subsetI insert_subset path_can_be_split)
    then show ?case by (meson UnI1 UnI2 assms(1-4) in_con_compI)
  qed
  thus ?thesis
    by (metis \<open>v \<in> Vs (insert {u, v} E)\<close> connected_components_closed' own_connected_component_unique)
qed

lemma connected_components_insert_2:
  assumes "Cu \<in> connected_components E" "Cv \<in> connected_components E"
  assumes "u \<in> Cu" "v \<in> Cv"
  shows "connected_components (insert {u, v} E) = insert (Cu \<union> Cv) ((connected_components E) - {Cu, Cv})"
proof-
  have Cuvins: "Cu \<union> Cv \<in> connected_components (insert {u, v} E)"
    by (simp add: assms(1-4) connected_components_union)

  show ?thesis
  proof(standard; standard)
    fix C assume "C \<in> insert (Cu \<union> Cv) (connected_components E - {Cu, Cv})"
    then consider (Cuv) "C = (Cu \<union> Cv)" | (other) "C \<in> connected_components E" "C \<noteq> Cu" "C \<noteq> Cv"
      by blast

    thus "C \<in> connected_components (insert {u, v} E)"
      by (metis Cuvins assms connected_components_closed' unchanged_connected_component)
  next
    fix C assume ass: "C \<in> connected_components (insert {u, v} E)"
    have "C = Cu \<union> Cv" if "u \<in> C"
      by (metis Cuvins Un_upper1 ass assms(3) connected_components_closed' insert_Diff insert_subset that)
    moreover have "C = Cu \<union> Cv" if "v \<in> C"
      by (metis Cuvins Un_upper2 ass assms(4) connected_components_closed' subsetD that)
    moreover have "C \<in> connected_components E" if "u \<notin> C"
      by (metis UnCI ass assms(3) calculation(2) that unchanged_connected_component)
    ultimately show "C \<in> insert (Cu \<union> Cv) ((connected_components E) - {Cu, Cv})"
      using assms(3, 4) by blast
  qed
qed

lemma connected_components_insert_1:
  assumes "C \<in> connected_components E" "u \<in> C" "v \<in> C"
  shows "connected_components (insert {u, v} E) = connected_components E"
  using assms connected_components_insert_2 by fastforce

lemma in_connected_component_in_edges: "v \<in> connected_component E u \<Longrightarrow> v \<in> Vs E \<or> u = v"
  by(auto simp: connected_component_def Vs_def dest: walk_endpoints(2) elim: vs_member_elim)

lemma in_con_comp_has_walk: assumes "v \<in> connected_component E u" "v \<noteq> u"
  obtains p where "walk_betw E u p v"
  using assms
  by(auto simp: connected_component_def)

lemma con_comp_subset: "E1 \<subseteq> E2 \<Longrightarrow> connected_component E1 u \<subseteq> connected_component E2 u"
  by (auto dest: walk_subset simp: connected_component_def)

lemma in_con_comp_insert: "v \<in> connected_component (insert {u, v} E) u"
  using edges_are_walks[OF insertI1]
  by (force simp add: connected_component_def)

lemma connected_components_insert:
  assumes "C \<in> connected_components E" "u \<in> C" "v \<notin> Vs E"
  shows "insert v C \<in> connected_components (insert {u, v} E)"
proof-
  have "u \<in> Vs (insert {u, v} E)" by (simp add: Vs_def)
  moreover have "connected_component (insert {u, v} E) u = insert v C"
  proof(standard, goal_cases)
    case 1
    thus ?case
      apply auto
      using assms
      by (fastforce elim: in_con_comp_has_walk dest!: path_can_be_split_2
                    simp add: in_con_compI connected_comp_verts_in_verts)
  next
    case 2
    have "C = connected_component E u"
      by (simp add: assms connected_components_closed')
    then show ?case
      by(auto intro!: insert_subsetI con_comp_subset[simplified]
              simp add: in_con_comp_insert)
  qed
  ultimately show ?thesis by (metis connected_components_closed' own_connected_component_unique)
qed

lemma connected_components_insert_3:
  assumes "C \<in> connected_components E" "u \<in> C" "v \<notin> Vs E"
  shows "connected_components (insert {u, v} E) = insert (insert v C) (connected_components E - {C})"
proof-
  have un_con_comp: "insert v C \<in> connected_components (insert {u, v} E)"
    by (simp add: assms connected_components_insert)
  {
    fix D assume "D \<in> insert (insert v C) (connected_components E - {C})"
    then consider (ins) "D = insert v C" | (other) "D \<in> connected_components E" "D \<noteq> C" by blast
    hence "D \<in> connected_components (insert {u, v} E)"
      by (metis assms connected_comp_verts_in_verts connected_components_closed' un_con_comp unchanged_connected_component)
  } moreover
  {
    fix D assume ass: "D \<in> connected_components (insert {u, v} E)"
    have "D = insert v C" if "u \<in> D"
      by (metis ass assms(2) connected_components_closed' insert_iff that un_con_comp)
    moreover have "D \<in> connected_components E" if "v \<notin> D"
      by (metis ass calculation insertI1 that unchanged_connected_component)
    ultimately have "D \<in> insert (insert v C) (connected_components E - {C})"
      by (metis ass assms(1, 2) connected_components_closed' insert_Diff insert_iff un_con_comp)
  }
  ultimately show ?thesis by blast
qed

lemma connected_components_small:
  assumes "u \<notin> Vs E" "v \<notin> Vs E"
  shows "{u, v} \<in> connected_components (insert {u, v} E)"
proof-
  have "u \<in> Vs (insert {u, v} E)" by (simp add: Vs_def)
  moreover then have "connected_component (insert {u, v} E) u = {u, v}"
  proof(standard, goal_cases)
    case 1 thus ?case
      by (metis calculation edges_are_walks insert_iff singletonD walk_reflexive)
  next
    case 2 thus ?case
      by (metis Vs_def assms ccpo_Sup_singleton path_can_be_split_3 walk_endpoints)
  qed
  ultimately show ?thesis
    by (metis connected_components_closed' own_connected_component_unique)
qed

lemma connected_components_insert_4:
  assumes "u \<notin> Vs E" "v \<notin> Vs E"
  shows "connected_components (insert {u, v} E) = insert {u, v} (connected_components E)"
proof-
  have uv_comp_in: "{u, v} \<in> connected_components (insert {u, v} E)"
    by (simp add: assms connected_components_small)
  thus ?thesis
    apply(intro equalityI subsetI)
    subgoal by (metis connected_components_closed' insertI1 insertI2 unchanged_connected_component)
    subgoal by (metis assms connected_comp_verts_in_verts insert_iff unchanged_connected_component)
    done
qed

lemma connected_components_insert_1':
  assumes "u \<in> Vs E" "v \<in> Vs E"
  shows "connected_components (insert {u, v} E)
          = insert (connected_component E u \<union> connected_component E v)
                   ((connected_components E) - {connected_component E u, connected_component E v})"
  by (smt assms connected_components_closed' connected_components_insert_2 own_connected_component_unique)

lemma connected_components_insert_2':
  assumes "u \<in> Vs E" "v \<notin> Vs E"
  shows "connected_components (insert {u, v} E)
          = insert (insert v (connected_component E u)) (connected_components E - {connected_component E u})"
  by (smt assms connected_components_closed' connected_components_insert_3 own_connected_component_unique)

lemma connected_components_insert_3':
  assumes "u \<notin> Vs E" "v \<notin> Vs E"
  shows "connected_components (insert {u, v} E) = insert {u, v} (connected_components E)"
  using assms connected_components_insert_4 by metis

lemma degree_one_unique:
  assumes "degree E v = 1"
  shows "\<exists>!e \<in> E. v \<in> e"
proof-
  from assms obtain e where "{e} = {e. v \<in> e} \<inter> E" unfolding degree_def
    by (metis card'_1_singletonE)
  thus ?thesis by (metis Int_iff mem_Collect_eq singletonD singletonI)
qed

lemma complete_path_degree_one_head_or_tail:
  assumes "path E p" "distinct p"
  assumes "v \<in> set p" "degree E v = 1"
  shows "v = hd p \<or> v = last p"
proof(rule ccontr)
  assume "\<not> (v = hd p \<or> v = last p)"
  hence "v \<noteq> hd p" "v \<noteq> last p" by simp_all
  hence "2 = degree (set (edges_of_path p)) v"
    by (simp add: degree_edges_of_path_ge_2 assms(2) assms(3))
  hence "2 \<le> degree E v" using path_edges_subset subset_edges_less_degree assms(1)
    by metis
  then show False using assms(4) by simp
qed

(*
  The proof of the following theorem should be improved by devising an induction principle for
  edges and connected components.
*)

theorem component_has_path_distinct:
  assumes "finite E" and
          "C \<in> connected_components E" and
          "\<forall>v\<in>Vs E. degree E v \<le> 2" and
          "\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "\<exists>p. path E p \<and> C = (set p) \<and> distinct p"
  using assms
proof(induction "card E" arbitrary: C E rule: nat_less_induct)
  case (1 E C)
  then have IH: "\<exists>p. path E' p \<and> C' = set p \<and> distinct p"
    if "C' \<in> connected_components E'" "E' \<subset> E" for E' C'
  proof-
    have "\<forall>v\<in>Vs E'. degree E' v \<le> 2" using "1.prems"(3) that(2)
      by (meson Vs_subset less_imp_le order_trans subset_edges_less_degree subset_iff)
    moreover have "\<forall>e\<in>E'. \<exists>u v. e = {u, v} \<and> u \<noteq> v" using that(2) "1.prems"(4) by blast
    moreover have "finite E'" using "1.prems"(1) infinite_super that(2) by blast
    ultimately show ?thesis using "1.hyps"
      by (metis "1.prems"(1) psubset_card_mono that)
  qed

  obtain u v where uv: "{u, v} \<in> E" "u \<in> C" "v \<in> C" "u \<noteq> v"
    "(degree E u = 1 \<and> degree E v = 1) \<or>
     (degree E u = 1 \<and> degree E v = 2) \<or>
     (degree E u = 2 \<and> degree E v = 2)"
  proof-
    obtain x where x: "x \<in> C" "x \<in> Vs E"
      by (metis "1.prems"(2) connected_comp_nempty connected_comp_verts_in_verts ex_in_conv)
    then obtain e where e: "e \<in> E" "x \<in> e" unfolding degree_def
      by (metis Union_iff Vs_def)
    then obtain y where "e = {x, y}" using "1.prems"(4) by fastforce
    hence yE: "y \<in> Vs E" by (metis e(1) edges_are_Vs insert_commute)
    have y: "y \<in> C" using "1.prems"(2) \<open>e = {x, y}\<close> e(1) edges_are_walks in_con_compI x(1) by fastforce
    have xy: "x \<noteq> y" using "1.prems"(4) \<open>e = {x, y}\<close> doubleton_eq_iff e(1) by fastforce
    have e: "{x, y} \<in> E" using \<open>e = {x, y}\<close> e(1) by blast
    hence ealt: "{y, x} \<in> E" by (simp add: insert_commute)

    have "1 \<le> degree E x" by (metis degree_Vs one_eSuc x(2))
    moreover have "degree E x \<le> 2" by (simp add: x(2) "1.prems"(3))
    ultimately consider (one) "degree E x = 1" | (two) "degree E x = 2"
      by (smt Set.set_insert antisym_conv degree_Vs degree_insert degree_not_Vs e eSuc_ile_mono eSuc_numeral insertI1 numeral_One one_eSuc semiring_norm(2))
    note uoneortwo = this
  
    have "1 \<le> degree E y" by (metis degree_Vs one_eSuc yE)
    moreover have "degree E y \<le> 2" by (simp add: yE "1.prems"(3))
    ultimately consider (one) "degree E y = 1" | (two) "degree E y = 2"
      by (smt Set.set_insert Set.insert_commute antisym_conv degree_Vs degree_insert degree_not_Vs e eSuc_ile_mono eSuc_numeral insertI1 numeral_One one_eSuc semiring_norm(2))
    note voneortwo = this

    consider (one) "degree E x = 1" "degree E y = 1"
      | (two) "degree E x = 1" "degree E y = 2"
      | (four) "degree E x = 2" "degree E y = 2"
      | (three) "degree E x = 2" "degree E y = 1"
      using uoneortwo voneortwo by argo
    thus ?thesis using that e ealt x(1) y(1) xy
      by (cases, blast+)
  qed

  obtain E' where E': "E = insert {u, v} E'" "{u, v} \<notin> E'"
    by (meson Set.set_insert uv(1))
  have degUE': "degree E' u = degree E u - 1" using E' degree_insert
    by (metis eSuc_minus_1 insertI1)
  have degVE': "degree E' v = degree E v - 1" using E' degree_insert
    by (metis eSuc_minus_1 insertI1 insert_commute)

  consider (u1v1) "degree E u = 1" "degree E v = 1"
    | (u1v2) "degree E u = 1" "degree E v = 2"
    | (u2v2) "degree E u = 2" "degree E v = 2" using uv(5) by blast
  then show ?case
  proof cases
    case u1v1
    from u1v1(1) have uVsE': "u \<notin> Vs E'" by (metis degUE' degree_Vs eSuc_minus_1 not_one_le_zero one_eSuc)
    from u1v1(2) have vVsE': "v \<notin> Vs E'" by (metis degVE' degree_Vs eSuc_minus_1 not_one_le_zero one_eSuc)
    hence "C = {u, v}" using connected_components_insert_3'[OF uVsE' vVsE']
      using "1.prems"(2) E'(1) connected_comp_verts_in_verts uv(3) by fastforce

    moreover have "path E [u, v]"
      by (meson edges_are_walks uv(1) walk_betw_def)
    ultimately show ?thesis
      by (metis distinct_length_2_or_more distinct_singleton empty_set list.simps(15) uv(4))
  next
    case u1v2
    define C' where "C' \<equiv> connected_component E' v"
    have degVE': "degree E' v = 1" using E' uv(1) u1v2(2) unfolding degree_def by fastforce
    from u1v2(1) have uVsE': "u \<notin> Vs E'" by (metis degUE' degree_Vs eSuc_minus_1 not_one_le_zero one_eSuc)
    from u1v2(2) have vVsE': "v \<in> Vs E'" by (metis UnionI Vs_def degVE' degree_one_unique)
    have CCEE: "connected_components E = insert (insert u C') (connected_components E' - {C'})"
      using connected_components_insert_2'[OF vVsE' uVsE'] C'_def E'(1)
      by (simp add: insert_commute)
    have C': "C \<equiv> insert u C'" using CCEE "1.prems"(2) uv(2)
      by (smt connected_components_closed' insertI1)
    have uC': "u \<notin> C'"
      by (metis C'_def in_connected_component_has_path uVsE' vVsE' walk_endpoints(2))
    have "C' \<in> connected_components E'"
      by (metis C'_def connected_components_closed' own_connected_component_unique vVsE')
    hence "\<exists>p. path E' p \<and> C' = set p \<and> distinct p" using IH E' by blast
    then obtain p where p: "path E' p" "C' = set p" "distinct p" by blast

    then consider "hd p = v" | "last p = v"
      using complete_path_degree_one_head_or_tail C' degVE' uv(3, 4) by fastforce
    thus ?thesis
    proof cases
      case 1
      hence "path E (u # p)" using C' E'(1) p(1, 2) uv(3) uv(1, 4) edges_are_Vs
        by (metis hd_Cons_tl path.simps path_subset subset_insertI)
      thus ?thesis using C' uC' p(2, 3) by fastforce
    next
      case 2
      hence "path E (p @ [u])" using C' E'(1) p(1, 2) uv(3) uv(1, 4) edges_are_Vs
        by (smt insert_commute list.sel(1) path1 path_append path_subset subset_insertI)
      thus ?thesis using C' uC' p(2, 3) by fastforce
    qed
  next
    case u2v2
    define Cu where "Cu \<equiv> connected_component E' u"
    define Cv where "Cv \<equiv> connected_component E' v"
    have degUE': "degree E' u = 1" using E' uv(1) u2v2(1) unfolding degree_def by fastforce
    have degVE': "degree E' v = 1" using E' uv(1) u2v2(2) unfolding degree_def by fastforce
    from u2v2(1) have uVsE': "u \<in> Vs E'" by (metis UnionI Vs_def degUE' degree_one_unique)
    from u2v2(2) have vVsE': "v \<in> Vs E'" by (metis UnionI Vs_def degVE' degree_one_unique)
    have CCEE: "connected_components E = insert (Cu \<union> Cv) (connected_components E' - {Cu, Cv})"
      using connected_components_insert_1'[OF uVsE' vVsE'] Cu_def Cv_def E'(1) by simp
    have C': "C \<equiv> Cu \<union> Cv" using CCEE "1.prems"(2) uv(2)
      by (smt Cu_def DiffE connected_components_closed' insertE insertI1)
    have "Cu \<in> connected_components E'" using Cu_def connected_components_def uVsE' by blast
    hence exp: "\<exists>p. path E' p \<and> Cu = set p \<and> distinct p" using IH E' by blast
    obtain p where p: "path E' p" "Cu = set p" "distinct p" "hd p = u"
    proof-
      obtain p where p: "path E' p" "Cu = set p" "distinct p" using exp by blast
      then consider "hd p = u" | "last p = u" using complete_path_degree_one_head_or_tail degUE'
        using Cu_def in_own_connected_component by fastforce
      thus ?thesis
      proof cases
        case 1
        then show ?thesis using p that by blast
      next
        case 2
        have "path E' (rev p)" by (simp add: p(1) rev_path_is_path)
        moreover have "hd (rev p) = u" using 2
          by (metis Cu_def equals0D hd_rev in_own_connected_component p(2) set_empty)
        ultimately show ?thesis using that p(2, 3) by simp
      qed
    qed

    have "Cv \<in> connected_components E'" using Cv_def connected_components_def vVsE' by blast
    hence exq: "\<exists>p. path E' p \<and> Cv = set p \<and> distinct p" using IH E' by blast
    then obtain q where q: "path E' q" "Cv = set q" "distinct q" "hd q = v"
    proof-
      obtain q where q: "path E' q" "Cv = set q" "distinct q" using exq by blast
      then consider "hd q = v" | "last q = v" using complete_path_degree_one_head_or_tail degVE'
        using Cv_def in_own_connected_component by fastforce
      thus ?thesis
      proof cases
        case 1
        then show ?thesis using q that by blast
      next
        case 2
        have "path E' (rev q)" by (simp add: q(1) rev_path_is_path)
        moreover have "hd (rev q) = v" using 2
          by (metis Cv_def equals0D hd_rev in_own_connected_component q(2) set_empty)
        ultimately show ?thesis using that q(2, 3) by simp
      qed
    qed

    consider (different) "Cu \<inter> Cv = {}" | (same) "Cu = Cv"
      by (meson \<open>Cu \<in> connected_components E'\<close> \<open>Cv \<in> connected_components E'\<close> connected_components_disj)
    thus ?thesis
    proof cases
      case different
      have "path E p" "path E q" using E'(1) p(1) q(1) path_subset by blast+
      hence "path E (rev p @ q)" using path_append p(4) q(4) uv(1)
        by (metis last_rev rev_is_Nil_conv rev_path_is_path)
      thus ?thesis using C' different p(2) p(3) q(2) q(3) by fastforce
    next
      case same
      thus ?thesis
        using C' E'(1) p(1) p(2) p(3) path_subset by blast
    qed
  qed
qed

subsection \<open>matchings and symmetric difference + accompanying auxiliary theory\<close>

definition matching where
  "matching M \<longleftrightarrow> (\<forall>e1 \<in> M. \<forall>e2 \<in> M. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {})"

lemma matching_def2:
  "matching M \<longleftrightarrow> (\<forall>v \<in> Vs M. \<exists>!e\<in>M. v \<in> e)"
  unfolding matching_def Vs_def by blast

lemma matching_unique_match:
  assumes "matching M" "v \<in> e" "v \<in> f" "e \<in> M" "f \<in> M"
  shows "e = f"
  using assms
  by (metis IntI assms(1) equals0D matching_def)

definition symmetric_diff (infixl "\<oplus>" 65) where
  "symmetric_diff s t \<equiv> (s - t) \<union> (t - s)"

lemma sym_diff_subset:
  "s \<oplus> s' \<subseteq> s \<union> s'"
  unfolding symmetric_diff_def
  by auto
                       
lemma card3_subset:
  assumes "card s \<ge> 3"
  shows "\<exists>x y z. {x, y, z} \<subseteq> s \<and> x \<noteq> y  \<and> x \<noteq> z  \<and> y \<noteq> z"
  using assms by(auto simp: numeral_3_eq_3 card_le_Suc_iff)

lemma finite_symm_diff:
  assumes "finite s" "finite t"
  shows "finite (s \<oplus> t)"
  using assms
  unfolding symmetric_diff_def
  by auto

lemma degree_matching_in_M:
  assumes "matching M" "v \<in> Vs M"
  shows "degree M v = 1"
proof-
  obtain e where edef: "v \<in> e" "e \<in> M" by (meson assms(1,2) matching_def2)
  have "{e} = {e. v \<in> e} \<inter> M"
  proof((standard; standard), goal_cases)
    case (2 x)
    hence "x = e" using assms matching_def2 by (metis IntD1 IntD2 assms(2) edef mem_Collect_eq)
    thus ?case by simp
  next
    case (1 x)
    thus ?case using edef by blast
  qed
  moreover have "card' {e} = 1" unfolding card'_def by simp
  ultimately show ?thesis unfolding degree_def by simp
qed

lemma degree_matching:
  assumes "matching M"
  shows "degree M v \<le> 1"
proof(cases "v \<in> Vs M")
  case True thus ?thesis
    by (simp add: assms degree_matching_in_M)
next
  case False thus ?thesis
    by (simp add: degree_not_Vs)
qed

lemma degree_symm_diff:
  assumes "matching M" "matching M'"
  shows "degree (M \<oplus> M') v \<le> 2"
proof-
  have "card' ({e. v \<in> e} \<inter> M) \<le> 1"  using assms(1) degree_matching unfolding degree_def by metis
  hence "finite ({e. v \<in> e} \<inter> M)"
    by (metis card'_1_singletonE card'_def enat_ord_simps(3) finite.simps order_class.order.antisym)
    
  have "{e. v \<in> e} \<inter> ((M - M') \<union> (M' - M)) \<subseteq> ({e. v \<in> e} \<inter> M) \<union> ({e. v \<in> e} \<inter> M')"
    by blast
  hence "degree (M \<oplus> M') v \<le> degree (M \<union> M') v" unfolding degree_def symmetric_diff_def
    by (simp add: card'_mono Int_Un_distrib)
  also have "... \<le> degree M v + degree M' v" unfolding degree_def
    by (simp add: Int_Un_distrib card'_def card_Un_le)
  also have "... \<le> degree M v + 1" by (meson add_left_mono assms(2) degree_matching)
  also have "... \<le> 2" by (metis add_right_mono assms(1) degree_matching one_add_one)
  finally show ?thesis .
qed

subsection\<open>Direction 1 of Berge\<close>
text\<open>If there is a bigger matching, then there is an augmenting path\<close>

lemma smaller_matching_less_members:
  assumes "finite E" "card E < card E'"
  shows "card ((E \<oplus> E') \<inter> E) < card ((E \<oplus> E') \<inter> E')"
proof-
  have "card ((E \<oplus> E') \<inter> E) = card (E - E')" unfolding symmetric_diff_def
    by (metis Diff_disjoint Int_Un_distrib2 Un_Diff_Int inf_sup_absorb sup_bot.right_neutral)
  moreover have "card ((E \<oplus> E') \<inter> E') = card (E' - E)" unfolding symmetric_diff_def
    by (metis Diff_disjoint Int_Un_distrib2 Un_Diff_Int inf_sup_absorb sup_bot.right_neutral)
  ultimately show "card ((E \<oplus> E') \<inter> E) < card ((E \<oplus> E') \<inter> E')"
    by (metis assms card.infinite card_less_sym_Diff not_less_zero)
qed

lemma one_unbalanced_comp_edges:
  assumes finite: "finite E" and
          card_lt: "card E < card E'" and
          finite_conn_comps: "finite (connected_components (E \<oplus> E'))" and
          doubleton_edges: "\<forall>e\<in>(E \<oplus> E'). \<exists>u v. e = {u, v}"
  shows "\<exists>eC \<in> components_edges (E \<oplus> E'). card (eC \<inter> E) < card (eC \<inter> E')"
proof(intro Union_lt assms)
  have *: "(E \<oplus> E') \<inter> {{x, y} |x y. True} = (E \<oplus> E')" 
    using doubleton_edges
    by auto
  show "card (\<Union> (components_edges (E \<oplus> E')) \<inter> E) < card (\<Union> (components_edges (E \<oplus> E')) \<inter> E')"
    unfolding component_edges_partition *
    by(intro smaller_matching_less_members finite card_lt)
  show "\<forall>eC\<in>components_edges (E \<oplus> E'). \<forall>s'\<in>components_edges (E \<oplus> E'). eC \<noteq> s' \<longrightarrow> eC \<inter> s' = {}"
    unfolding components_edges_def
    using component_edges_disj
    by auto
  show "finite E'"
    using finite card_lt
    using card_gt_0_iff by fastforce
qed(auto simp add: components_edges_def finite_conn_comps)

lemma matchings_in_diff:
  assumes "matching M" "matching M'" "{a, b} \<in> M \<oplus> M'" "{b, c} \<in> M \<oplus> M'" "a \<noteq> c"
  shows "{a, b} \<in> M \<longleftrightarrow> {b, c} \<in> M'"
proof-
  have sym_def: "x \<in> M \<oplus> M' \<Longrightarrow> x \<in> M \<or> x \<in> M' \<and> (x \<in> M \<longrightarrow> x \<notin> M') \<and> (x \<in> M' \<longrightarrow> x \<notin> M)" for x
    unfolding symmetric_diff_def by blast
  have aneqc: "{a, b} \<noteq> {b, c}" using assms(5)by (metis doubleton_eq_iff)
  hence notbothM: "\<not> ({a, b} \<in> M \<and> {b, c} \<in> M)" using assms(1) unfolding matching_def by fast
  from aneqc
  have notbothM': "\<not> ({a, b} \<in> M' \<and> {b, c} \<in> M')" using assms(2) unfolding matching_def by fast
  show ?thesis
  proof
    assume "{a, b} \<in> M"
    then show "{b, c} \<in> M'" using sym_def[OF assms(4)] notbothM by simp
  next
    assume "{b, c} \<in> M'"
    then show "{a, b} \<in> M" using sym_def[OF assms(3)] notbothM' by simp
  qed
qed

lemma matching_paths_alternate:
  assumes "path (M \<oplus> M') p" "matching M" "matching M'" "distinct (edges_of_path p)"
  shows "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path p) \<or> alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path p)"
  using assms
proof(induction p rule: induct_list0123)
  case (list2 v v')
  then show ?case
    apply (simp add: alt_list_empty alt_list_step split: if_splits)
    using distinct_edges_of_paths_cons sym_diff_subset by fastforce
next
  case (list3 v v' v'' vs)
  have "v \<noteq> v''" using list3.prems(4) by auto
  from list3 consider
    "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path (v'#v''#vs))"
    | "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path (v'#v''#vs))"
    by fastforce
  then show ?case
  proof cases
    case 1
    hence "{v', v''} \<in> M" by (simp add: alt_list_step)
    hence "{v, v'} \<in> M'" using matchings_in_diff path_2 list3.prems
      by (smt \<open>v \<noteq> v''\<close> insert_commute)
    thus ?thesis using "1" alt_list.simps by force
  next
    case 2
    hence "{v', v''} \<in> M'" by (simp add: alt_list_step)
    hence "{v, v'} \<in> M" using matchings_in_diff path_2 list3.prems
      by (smt \<open>v \<noteq> v''\<close> insert_commute)
    thus ?thesis using "2" alt_list.simps by force
  qed
qed (simp_all add: alt_list_empty)

(*
  Every edge in the set of edges belonging to the connected component with more edges from M'
  belongs to the edge path representing that connected component.
*)

definition component_path' where
"component_path' E C \<equiv> (SOME p. path E p \<and> C = set p \<and> distinct p)"

lemma component_path'_works':
  assumes "finite E" "C \<in> connected_components E" "\<forall>v\<in>Vs E. degree E v \<le> 2" "\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "path E (component_path' E C) \<and> C = set (component_path' E C) \<and> distinct (component_path' E C)"
  unfolding component_path'_def
  apply(rule someI_ex)
  using component_has_path_distinct[OF assms] .

lemma component_path'_works:
  assumes "finite E" "C \<in> connected_components E" "\<forall>v\<in>Vs E. degree E v \<le> 2" "\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "path E (component_path' E C)" "set (component_path' E C) = C" "distinct (component_path' E C)"
  using component_path'_works'[OF assms]
  by auto

lemma rev_component_path'_works:
  assumes "finite E" "C \<in> connected_components E" "\<forall>v\<in>Vs E. degree E v \<le> 2" "\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "path E (rev (component_path' E C))" "set (rev (component_path' E C)) = C" "distinct (rev (component_path' E C))"
  unfolding set_rev distinct_rev
  using component_path'_works[OF assms]
  by (auto intro: rev_path_is_path)

lemma component_edges_subset:
  shows "component_edges E C \<subseteq> E"
  unfolding component_edges_def
  by auto

lemma symm_diff_mutex:
  assumes "x \<in> (s \<oplus> t)" "x \<in> s"
  shows "x \<notin> t"
  using assms
  unfolding symmetric_diff_def
  by auto

lemma edges_path_subset_edges:
  assumes "path E p" "set p \<subseteq> C"
  shows "set (edges_of_path p) \<subseteq> component_edges E C"
  using assms
  by (induction) (auto simp add: component_edges_def)

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
  moreover {
    have "last p \<noteq> a'" using assms(1) p by auto
    hence "{last p, a} \<noteq> {a, a'}" by (metis doubleton_eq_iff)
    hence "2 \<le> degree {{last p, a}, {a, a'}} a" by (simp add: degree_insert enat_defs(3))
    moreover have "{{last p, a}, {a, a'}} \<subseteq> set (edges_of_path (last p # p))" by (simp add: p)
    ultimately have "2 \<le> degree (set (edges_of_path (last p # p))) a"
      by (meson order.trans subset_edges_less_degree)
  }
  moreover {
    obtain u where u: "{u, last (a'' # p')} \<in> set (edges_of_path (a' # a'' # p'))" "u \<in> set (a' # a'' # p')"
      by (meson last_in_edge neq_Nil_conv)
    hence "{u, last (a'' # p')} \<noteq> {a, last (a'' # p')}"
      using assms(1) u
      by (auto simp add: p doubleton_eq_iff)
    hence "2 \<le> degree {{u, last (a'' # p')}, {a, last (a'' # p')}} (last (a'' # p'))"
      by (simp add: degree_insert enat_defs(3))
    moreover have "{{u, last (a'' # p')}, {a, last (a'' # p')}} \<subseteq> set (edges_of_path (last p # p))"
      using p u(1) by fastforce
    ultimately have "2 \<le> degree (set (edges_of_path (last p # p))) (last (a'' # p'))"
      by (meson order.trans subset_edges_less_degree)
  }
  ultimately show ?thesis
    by fastforce
next
  case False
  hence "2 = degree (set (edges_of_path p)) v"
    by (meson assms(1) assms(3) degree_edges_of_path_ge_2)
  moreover have "set (edges_of_path p) \<subseteq> set (edges_of_path (last p # p))"
    by (cases p) fastforce+
  then show ?thesis
    by (simp add: \<open>2 = degree (set (edges_of_path p)) v\<close> subset_edges_less_degree)
qed

lemma all_edges_covered_long_proof:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<forall>e\<in>(M \<oplus> M').\<exists>u v. e = {u,v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "component_edges (M \<oplus> M') C \<subseteq> set (edges_of_path (component_path' (M \<oplus> M') C))"
proof(cases "C ={}")
  case True
  then show ?thesis
    using assms
    unfolding component_edges_def component_path'_def
    by simp
next
  case C_nempty: False
  show ?thesis
  proof(cases "card C = 1")
    case True
    then obtain u where "C = {u}"
      using card_1_singletonE by blast
    then show ?thesis
      using assms
      unfolding component_edges_def component_path'_def
      by auto
  next
    case False
    then have comp_ge_2: "card C \<ge> 2"
      using C_nempty
      by (metis One_nat_def Suc_1 Suc_leI card_gt_0_iff finite_comp le_less)
    show ?thesis
    proof(safe; rule ccontr)                                          
      fix e
      assume ass: 
        "e \<in> component_edges (M \<oplus> M') C"
        "e \<notin> set (edges_of_path (component_path' (M \<oplus> M') C))"
      define vs where "vs \<equiv> (component_path' (M \<oplus> M') C)"
      define es where "es \<equiv> (edges_of_path (component_path' (M \<oplus> M') C))"
      have doubleton_edges: "\<forall>e\<in>(M \<oplus> M').\<exists>u v. e = {u,v} \<and> u \<noteq> v"
        using doubleton_neq_edges
        by fastforce
      have deg_le_2: "\<forall>v\<in>Vs (M \<oplus> M'). degree (M \<oplus> M') v \<le> 2"
        using matchings
        by (simp add: degree_symm_diff)
      note finite_bla = finite_symm_diff
      note comp_works = component_path'_works[OF finite_bla con_comp deg_le_2 doubleton_edges]
      show False    
      proof(cases "hd vs \<in> e \<and> last vs \<in> e")
        case T1: True
        moreover have vpath_hd_neq_last: "hd vs \<noteq> last vs"
          unfolding vs_def
          using comp_ge_2 comp_works
          by (metis One_nat_def Suc_1 Suc_le_eq card.insert card.empty distinct.simps(2) empty_set finite.emptyI last_ConsR last_in_set lessI list.exhaust_sel list.simps(15) not_less_iff_gr_or_eq)
        ultimately have e: "e = {hd vs, last vs}"
          using doubleton_edges component_edges_subset ass(1)
          by fastforce
        show ?thesis
        proof(cases "(component_edges (M \<oplus> M') C = insert e (set es))")
          case T2: True
          have vs_ge2: "length vs \<ge> 2"
            using comp_ge_2 comp_works
            unfolding vs_def
            using distinct_card by fastforce
          define vs' where "vs' = (last vs # vs)"
          have *: "set (edges_of_path vs') = component_edges (M \<oplus> M') C"
            using T2 vs_ge2
            unfolding es_def e vs_def vs'_def
            apply (simp)
            by (smt One_nat_def Suc_1 Suc_le_eq edges_of_path.simps(3) insert_commute length_greater_0_conv lessI less_trans list.exhaust_sel list.simps(15))
          have horrid_lt_expr: "length (filter (\<lambda>x. x \<in> M) (edges_of_path vs')) < length (filter (\<lambda>e. e \<in> M') (edges_of_path vs'))"
          proof-
            have "distinct (edges_of_path vs')"
              unfolding vs'_def vs_def
              using comp_works
                ass(2)
              by (metis (no_types, opaque_lifting) One_nat_def Suc_1 Suc_le_eq card.empty comp_ge_2 distinct.simps(2) distinct_edges_of_vpath e edges_of_path.simps(3) empty_set insert_commute lessI list.exhaust_sel not_less_iff_gr_or_eq vs_def)
            then have "length (filter (\<lambda>x. x \<in> N) (edges_of_path vs')) = card (N \<inter> (component_edges (M \<oplus> M') C))" for N
              using *
              by (simp add: distinct_length_filter)
            then show ?thesis
              using more_M'_edges
              by auto
          qed
          moreover have horrid_eq_expr: "\<forall>x\<in>set (edges_of_path vs'). (x \<in> M') = (x \<notin> M)"
            unfolding vs'_def
            by (metis "*" UnE component_edges_subset contra_subsetD sym_diff_subset symm_diff_mutex vs'_def)
          moreover have "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs')"
          proof-
            have "path (M \<oplus> M') (last vs # vs)"
            proof-
              obtain a l where l: "vs = a # l"
                by (metis Suc_1 Suc_le_length_iff vs_ge2)
              show ?thesis
              proof(cases l)
                case Nil
                then show ?thesis 
                  using l comp_ge_2 comp_works
                  unfolding vs_def
                  by (auto)
              next
                case l': (Cons a' l')
                show ?thesis
                  using e 
                  unfolding l' l
                  apply(simp split: if_splits)
                  subgoal using ass(2) l l' vs_def by auto
                  subgoal apply(rule conjI)
                    subgoal using T2 component_edges_subset by fastforce
                    subgoal using e ass l l' vs_def comp_works
                      by (simp)
                    done
                  done
              qed
            qed
            moreover {
              have "distinct (edges_of_path vs)"
                by (simp add: component_path'_works(3) con_comp deg_le_2 distinct_edges_of_vpath doubleton_edges finite_bla vs_def)
              hence "distinct (edges_of_path (last vs # vs))"
                by (metis Suc_1 Suc_le_length_iff ass(2) distinct_insert e edges_of_path.simps(3) insert_commute list.sel(1) not_in_set_insert vs_def vs_ge2)
            }
            moreover with vs_ge2 have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path (last vs # vs)) \<or>
                 alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path  (last vs # vs))"
              by (intro calculation(1) matching_paths_alternate assms; simp add: vs_def )
            ultimately show ?thesis
              using alternating_list_gt_or horrid_eq_expr horrid_lt_expr vs'_def by blast
          qed
          ultimately have "hd (edges_of_path vs') \<in> M' \<and> last (edges_of_path vs') \<in> M'"
            by(intro alternating_list_gt; simp)
          moreover have "hd (edges_of_path vs') \<noteq> last (edges_of_path vs')"
            unfolding vs'_def
            apply(intro hd_edges_neq_last)
            subgoal using ass(2) e unfolding vs_def by simp
            subgoal using vpath_hd_neq_last by simp
            subgoal using comp_works unfolding vs_def
              using comp_ge_2 by auto
            done
          moreover have "last vs' \<in> hd (edges_of_path vs') \<and> last vs' \<in> last (edges_of_path vs')"
            by (metis (no_types, opaque_lifting) Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_le_eq
                Suc_le_length_iff eq_iff hd_v_in_hd_e last.simps last_v_in_last_e length_0_conv
                list.sel(1) list.sel(3) list.simps(3) nat_le_linear not_less_eq_eq vs'_def vs_ge2)
          ultimately have "degree M (last vs') \<ge> 2"
            by (metis Suc_le_length_iff edges_are_Vs edges_of_path.simps(3) last.simps list.sel(1)
                matching_def2 matchings(2) numeral_2_eq_2 vs'_def vs_ge2)
          then show ?thesis using degree_matching matchings(1) order_trans by fastforce
        next
          case F2: False
          show ?thesis
          proof(cases "card C \<ge> 3")
            case T3: True
            obtain e' where e': "e' \<in> component_edges (M \<oplus> M') C" "e' \<notin> insert e (set es)"
              using F2
              unfolding es_def
              using edges_path_subset_edges comp_works ass(1)
              by blast
            obtain u v where uv: "e' = {u, v}" "v \<in> C"
              using e'(1)[unfolded component_edges_def] doubleton_edges
              by auto
            have "3 \<le> degree (insert e' (insert e (set es))) v"
            proof-
              have "degree (insert e (set es)) x \<ge> 2" if "x \<in> C" for x
              proof-
                have rw: "insert e (set es) = set (edges_of_path((last vs) # vs))"
                proof-
                  obtain a l where "vs = a # l"
                    by (metis component_path'_works(2) con_comp deg_le_2 doubleton_edges empty_iff empty_set list.exhaust_sel finite_bla uv(2) vs_def)
                  then show ?thesis
                    unfolding es_def vs_def e
                    by auto
                qed
                show ?thesis
                  unfolding rw vs_def
                  apply(intro degree_edges_of_path_ge_2_all)
                  subgoal using comp_works
                    by simp
                  subgoal using comp_works T3 distinct_card
                    by fastforce
                  subgoal using comp_works that(1)
                    by fastforce
                  done
              qed
              then have "degree (insert e (set es)) v \<ge> 2"
                using uv
                by simp
              moreover have "v \<in> e'"
                using uv(1) by force
              ultimately show ?thesis
                using degree_insert
                by (metis e'(2) eSuc_ile_mono eSuc_numeral semiring_norm(5))
            qed
            moreover have "(insert e' (insert e (set es))) \<subseteq> component_edges (M \<oplus> M') C"
              using ass(1) e'
              unfolding es_def e vs_def
              using edges_path_subset_edges comp_works
              by auto
            ultimately have "3 \<le> degree (component_edges (M \<oplus> M') C) v"
              by (metis (no_types, lifting) dual_order.trans subset_edges_less_degree)
            moreover have "(component_edges (M \<oplus> M') C) \<subseteq> (M \<oplus> M')"
              unfolding component_edges_def
              by auto
            ultimately have "3 \<le> degree (M \<oplus> M') v"
              by (metis dual_order.trans subset_edges_less_degree)
            then have "(3 :: enat) \<le> 2" using deg_le_2
              by (meson degree_symm_diff matchings(1) matchings(2) order_trans)
            then show False by simp
          next
            case F3: False
            then have C2: "card C = 2"
              using comp_ge_2
              by simp
            moreover obtain u v where uv: "C = {u, v}" "u \<noteq> v"
              by (metis C2 Suc_1 card_1_singletonE card_eq_SucD singletonI)
            ultimately have "component_edges (M \<oplus> M') C = {{u, v}}"
              unfolding component_edges_def
              apply(intro equalityI)
              subgoal apply (intro subsetI; simp)
                by (metis doubleton_eq_iff doubleton_neq_edges)
              subgoal apply (intro subsetI; simp)
                by (metis C2 \<open>\<lbrakk>card C = 2; C = {u, v}; u \<noteq> v\<rbrakk> \<Longrightarrow> {{x, y} |x y. {x, y} \<subseteq> C \<and> {x, y} \<in> (M \<oplus> M')} \<subseteq> {{u, v}}\<close> all_not_in_conv ass(1) component_edges_def component_edges_subset insert_iff subset_eq)
              done
            then have "False"
              using comp_works uv
              unfolding component_path'_def uv
              apply simp
              by (metis (no_types, lifting) Diff_eq_empty_iff Diff_insert_absorb F2 \<open>path (M \<oplus> M') (component_path' (M \<oplus> M') C)\<close> \<open>set (component_path' (M \<oplus> M') C) = C\<close> ass(1) ass(2) edges_path_subset_edges es_def insert_Diff1 insert_absorb2 singletonD subset_insertI uv(1))
            then show ?thesis .
          qed
        qed
      next
        case False
        then obtain u v where uv: "e = {u, v}"" v \<in> C"" u \<in> C"" v \<noteq> hd vs" "v \<noteq> last vs"
          using ass[unfolded component_edges_def] doubleton_neq_edges
          apply (simp add: doubleton_eq_iff)
          by (metis doubleton_eq_iff insertI1)
        have "3 \<le> degree (insert e (set es)) v"
        proof-
          have "2 = degree (set es) x" if "x \<in> C" "x \<noteq> hd (component_path' (M \<oplus> M') C)" "x \<noteq> last (component_path' (M \<oplus> M') C)" for x
          proof-
            have rw: "(set es) = set (edges_of_path(vs))"
              unfolding es_def vs_def by simp
            show ?thesis
              unfolding rw vs_def
              apply(intro degree_edges_of_path_ge_2 that)
              subgoal using comp_works
                by simp
              subgoal using comp_works distinct_card that
                by fastforce
              done
          qed
          then have "degree (set es) v \<ge> 2"
            using uv
            by (simp add: vs_def)
          moreover have "v \<in> e"
            using uv(1) by force
          ultimately show ?thesis
            using degree_insert ass(2) es_def
            by (metis eSuc_ile_mono eSuc_numeral semiring_norm(5))
        qed
        moreover have "(insert e (set es)) \<subseteq> component_edges (M \<oplus> M') C"
          using ass(1) 
          unfolding es_def vs_def
          using edges_path_subset_edges comp_works
          by auto
        ultimately have "3 \<le> degree (component_edges (M \<oplus> M') C) v"
          by (metis (no_types, lifting) dual_order.trans subset_edges_less_degree)
        moreover have "(component_edges (M \<oplus> M') C) \<subseteq> (M \<oplus> M')"
          unfolding component_edges_def
          by auto
        ultimately have "3 \<le> degree (M \<oplus> M') v"
          by (metis dual_order.trans subset_edges_less_degree)
        then show False
          using deg_le_2
          by (metis con_comp connected_comp_verts_in_verts dual_order.refl dual_order.trans enat_ord_number(1) not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 uv(2))
      qed
    qed
  qed
qed

lemma all_edges_covered_long_proof_eq:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<forall>e\<in>(M \<oplus> M').\<exists>u v. e = {u,v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "component_edges (M \<oplus> M') C = set (edges_of_path (component_path' (M \<oplus> M') C))"
  apply(intro equalityI edges_path_subset_edges all_edges_covered_long_proof assms component_path'_works)
  subgoal by (simp add: degree_symm_diff matchings(1) matchings(2))
  subgoal apply (intro equalityD1 component_path'_works(2) assms)
    subgoal by (simp add: degree_symm_diff matchings(1) matchings(2))
    done
  done

lemma con_comp_card_2:
  assumes con_comp: "C \<in> connected_components E"
  assumes finite_comp: "finite C"
  assumes doubleton_edges: "\<forall>e\<in>E.\<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "card C \<ge> 2"
proof-
  obtain X where "X \<in> C" "X \<in> Vs E"
    using con_comp connected_comp_nempty connected_component_subs_Vs by blast
  then obtain F where "F \<in> E" "X \<in> F" unfolding Vs_def by blast
  then obtain Y where "X \<noteq> Y" "F = {X, Y}" using doubleton_edges by fastforce
  hence "Y \<in> C" using \<open>F \<in> E\<close> \<open>X \<in> C\<close> con_comp edges_are_walks in_con_compI by fastforce
  show "card C \<ge> 2" using finite_comp \<open>X \<in> C\<close> \<open>X \<noteq> Y\<close> \<open>Y \<in> C\<close>
    by (metis card_le_Suc0_iff_eq not_less_eq_eq numeral_2_eq_2)
qed

lemma augmenting_path_exists_1_1_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_edges: "\<forall>e\<in>(M \<oplus> M').\<exists>u v. e = {u, v} \<and> u \<noteq> v" and 
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')" and 
    comp_edges_contained: "set (edges_of_path (component_path' (M \<oplus> M') C)) = component_edges (M \<oplus> M') C"
  shows "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path (component_path' (M \<oplus> M') C))" (is ?g1)
    "hd (edges_of_path (component_path' (M \<oplus> M') C)) \<in> M' \<and> last (edges_of_path (component_path' (M \<oplus> M') C)) \<in> M'" (is ?g2)
proof-
  note comp_ge_2 = con_comp_card_2[OF con_comp finite_comp doubleton_edges]

  define vs where "vs = (component_path' (M \<oplus> M') C)"
  then have *: "set (edges_of_path vs) = component_edges (M \<oplus> M') C"
    using comp_edges_contained
    by simp
  have deg_le_2: "\<forall>v\<in>Vs (M \<oplus> M'). degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  note comp_works = component_path'_works[OF finite_bla con_comp deg_le_2 doubleton_edges]
  have vs_ge2: "length vs \<ge> 2"
    using comp_ge_2 comp_works
    unfolding vs_def
    using distinct_card by fastforce
  have horrid_lt_expr: "length (filter (\<lambda>x. x \<in> M) (edges_of_path vs)) < length (filter (\<lambda>e. e \<in> M') (edges_of_path vs))"
  proof-
    have "distinct (edges_of_path vs)"
      unfolding vs_def
      using comp_works
      using distinct_edges_of_vpath by blast                
    then have "length (filter (\<lambda>x. x \<in> N) (edges_of_path vs)) = card (N \<inter> (component_edges (M \<oplus> M') C))" for N
      using *
      by (simp add: distinct_length_filter)
    then show ?thesis
      using more_M'_edges
      by auto
  qed
  moreover have horrid_eq_expr: "\<forall>x\<in>set (edges_of_path vs). (x \<in> M') = (x \<notin> M)"
    unfolding vs_def
    by (metis "*" UnE component_edges_subset contra_subsetD sym_diff_subset symm_diff_mutex vs_def)
  moreover have "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs)"
  proof-
    have "path (M \<oplus> M') (vs)"
      unfolding vs_def
      using comp_works
      by simp
    moreover with vs_ge2 have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<in> M') (edges_of_path vs) \<or>
                 alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path  vs)"
      apply(intro matching_paths_alternate assms; simp add: vs_def )
      using tl_path_is_path component_path'_works(3)[OF finite_bla con_comp deg_le_2 doubleton_edges]
      by (simp add: distinct_edges_of_vpath)
    ultimately show ?thesis
      using *
      using alternating_list_gt_or horrid_eq_expr horrid_lt_expr by blast
  qed
  then show ?g1 
    unfolding vs_def
    by blast
  ultimately show ?g2
    unfolding vs_def
    by(intro alternating_list_gt; simp)
qed

text\<open>Defining an augmenting path\<close>

definition augmenting_path where
  "augmenting_path M p \<equiv> (length p \<ge> 2) \<and> alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)
                          \<and> hd p \<notin> Vs M \<and> last p \<notin> Vs M"
abbreviation "augpath E M p \<equiv> path E p \<and> distinct p \<and> augmenting_path M p"

lemma augmenting_path_feats:
  assumes "augmenting_path M p"
  shows "(length p \<ge> 2)" "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)" "hd p \<notin> Vs M" "last p \<notin> Vs M"
  using assms
  unfolding augmenting_path_def
  by auto

lemma augmenting_path_last_edge_nin:
  assumes "augmenting_path M p"
  shows "last (edges_of_path p) \<notin> M"
proof- 
  have "last p \<in> last (edges_of_path p)"
    using assms
    by (simp add: augmenting_path_def last_v_in_last_e)
  then show ?thesis
    using augmenting_path_feats(4)[OF assms]
    using Vs_def by fastforce
qed

lemma augmenting_path_odd_length:
  assumes "augmenting_path M p"
  shows "odd (length (edges_of_path p))"
  using assms augmenting_path_def augmenting_path_last_edge_nin edges_of_path_length alternating_list_even_last
  by (metis Suc_1 Suc_le_lessD length_greater_0_conv zero_less_diff)

lemma augmenting_path_exists_1_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_edges: "\<forall>e\<in>M\<oplus>M'.\<exists>u v. e = {u,v} \<and> u \<noteq> v" "\<forall>e\<in>M.\<exists>u v. e = {u,v} \<and> u \<noteq> v" and 
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')" and 
    comp_edges_contained: "set (edges_of_path (component_path' (M \<oplus> M') C)) = component_edges (M \<oplus> M') C"
  shows "augmenting_path M (component_path' (M \<oplus> M') C)"
proof-
  note comp_ge_2 = con_comp_card_2[OF con_comp finite_comp doubleton_edges(1)]

  have deg_le_2: "\<forall>v\<in>Vs (M \<oplus> M'). degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  define vs where "vs = (component_path' (M \<oplus> M') C)"
  then have f1: "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs)" and
            f2: "hd (edges_of_path vs) \<in> M'" "last (edges_of_path vs) \<in> M'"
    using augmenting_path_exists_1_1_1[OF assms(1-5,7-9), unfolded vs_def]
    by auto
  {
    fix vs
    assume ass: "path (M \<oplus> M') (vs)"
      "set vs = C"
      "distinct vs"
      "alt_list (\<lambda>e. e \<in> M') (\<lambda>e. e \<in> M) (edges_of_path vs)"
      "set (edges_of_path vs) = component_edges (M \<oplus> M') C"
    have "hd vs \<notin> Vs M"
    proof(rule ccontr)
      obtain u v vs' where uv: "vs = u # v # vs'"
        using ass
        by (metis (no_types, opaque_lifting) card.empty edges_of_path.cases edges_of_path.simps(1) edges_of_path.simps(2) inf_bot_right list.set(1) more_M'_edges nat_neq_iff)
      assume "\<not> hd vs \<notin> Vs M"
      then have "hd vs \<in> Vs M" by simp
      then obtain w e where we: "e = {w, u}" "e \<in> M"
        unfolding Vs_def
        apply (simp add: uv)
        using doubleton_edges 
        by (metis empty_iff insert_commute insert_iff)
      show False
      proof(cases "e \<in> M'")
        case T1: True
        then have "w = v"
          using uv we ass
          apply (simp add: alt_list_step)
          by (metis doubleton_eq_iff edges_are_Vs insertI1 matching_def2 matchings(2))
        moreover have "{u,v} \<in> (M \<oplus> M')"
          using uv ass(1)
          unfolding vs_def
          by (cases vs'; simp)
        ultimately show ?thesis
          using we T1
          unfolding symmetric_diff_def
          by (simp add: insert_commute)
      next
        case F1 :False
        then have "e \<in> (M \<oplus> M')"
          using we
          unfolding symmetric_diff_def
          by simp
        then have "e \<in> component_edges (M \<oplus> M') C"
          unfolding component_edges_def
          using we ass(2)
          apply simp
          by (metis con_comp connected_components_closed' edge_in_component insert_subset list.set_intros(1) uv)
        then have "e \<in> set (edges_of_path vs)"
          unfolding vs_def
          using we ass(5) 
          by simp
        then have "w = v"
          using uv we
          unfolding vs_def
          apply simp
          using ass(3)
          by (metis distinct.simps(2) doubleton_eq_iff v_in_edge_in_path)
        then show ?thesis
          using uv F1 ass(4) we
          unfolding vs_def
          by (simp add: alt_list_step insert_commute)
      qed    
    qed
  }note * = this
  have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path vs)"
    apply(intro alt_list_cong_2[OF f1])
    by (metis comp_edges_contained component_edges_subset contra_subsetD symm_diff_mutex vs_def)
  moreover have "hd vs \<notin> Vs M"
    using *[OF component_path'_works[OF finite_bla con_comp deg_le_2 doubleton_edges(1)] f1[unfolded vs_def] comp_edges_contained]
    unfolding vs_def
    by auto
  moreover have "last vs \<notin> Vs M"
  proof-
    have "hd (rev vs) \<notin> Vs M"
      unfolding vs_def
      apply(intro * rev_component_path'_works[OF finite_bla con_comp deg_le_2 doubleton_edges(1)])
      subgoal unfolding edges_of_path_rev[symmetric]
        apply(intro alt_list_rev f2[unfolded vs_def] f1[unfolded vs_def])
        subgoal by (metis alternating_list_even_last comp_edges_contained component_edges_subset disjoint_iff_not_equal empty_iff empty_set f1 f2(2) last_in_set more_M'_edges nat_neq_iff subsetD symm_diff_mutex vs_def)
        done
      subgoal by(simp add: edges_of_path_rev[symmetric] comp_edges_contained)
      done
    then show ?thesis
      using hd_rev
      by (metis comp_edges_contained edges_of_path.simps(1) empty_set inf_bot_right more_M'_edges not_less_iff_gr_or_eq vs_def)
  qed
  moreover have "2 \<le> length (component_path' (M \<oplus> M') C)"
    using component_path'_works(2,3)[OF finite_bla con_comp deg_le_2 doubleton_edges(1)]
    using distinct_card comp_ge_2 by fastforce
  ultimately show ?thesis
    unfolding augmenting_path_def vs_def
    using component_path'_works(1)[OF finite_bla con_comp deg_le_2 doubleton_edges(1)]
    by auto
qed

lemma augmenting_path_exists_1:
  assumes matchings: "matching M" "matching M'" and
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))" and
    doubleton_neq_edges: "\<forall>e\<in>(M \<oplus> M').\<exists>u v. e = {u,v} \<and> u \<noteq> v" "\<forall>e\<in>M. \<exists>u v. e = {u, v} \<and> u \<noteq> v" and
    finite_comp: "finite C" and
    finite_symm_diff: "finite (M \<oplus> M')"
  shows "augpath (M \<oplus> M') M (component_path' (M \<oplus> M') C)" (is "?g1 \<and> ?g2 \<and> ?g3")
proof(intro conjI)
  have deg_le_2: "\<forall>v\<in>Vs (M \<oplus> M'). degree (M \<oplus> M') v \<le> 2"
    using matchings
    by (simp add: degree_symm_diff)
  note finite_bla = finite_symm_diff
  have doubleton_edges: "\<forall>e\<in>(M \<oplus> M').\<exists>u v. e = {u, v} \<and> u \<noteq> v"
    using doubleton_neq_edges
    by fastforce
  {
    assume ass: "card C = 1"
    then obtain v where v: "C = {v}"
      using card_1_singletonE by blast
    moreover have C_nempty: "C \<noteq> {}" 
      by (simp add: v)
    ultimately have lv: "(component_path' (M \<oplus> M') C) = [v]"
      using component_path'_works(2,3)[OF finite_bla con_comp deg_le_2 doubleton_edges]
      apply simp
      by (metis C_nempty distinct.simps(2) hd_in_set last.simps last_in_set list.exhaust_sel set_empty singletonD)
    obtain e where e: "e \<in> (M \<oplus> M')" "v \<in> e"
      using con_comp v
      apply (simp add: alt_list_empty connected_components_def connected_component_def Vs_def)
      by force
    then obtain u where u: "e = {u, v}" "u \<noteq> v"
      using doubleton_neq_edges(1) e by fastforce
    moreover have "u \<in> connected_component (M \<oplus> M') v"
      using u
      by (smt connected_components_closed' e(1) edge_in_unique_component insertI1 insert_commute subset_eq)
    moreover have "C = connected_component (M \<oplus> M') v"
      using v
      by (metis con_comp connected_components_closed' insertI1)
    ultimately have False using v by auto
  }note C_nsingleton = this

  {
    assume "C = {}"
    then have False ?g1
      unfolding augmenting_path_def
      using  con_comp
      by (auto simp add: alt_list_empty connected_components_def connected_component_def)
  } note C_nempty = this
  have comp_ge_2: "card C \<ge> 2"
    using C_nsingleton C_nempty
    by (metis One_nat_def Suc_1 Suc_leI card_gt_0_iff finite_comp le_less)
  then show ?g3
    by (intro augmenting_path_exists_1_1 all_edges_covered_long_proof_eq[symmetric] assms)
  show ?g1 ?g2
    using matchings
    by (auto intro!: component_path'_works assms simp add: degree_symm_diff)
qed

lemma finite_con_comps:
  assumes "finite (Vs E)"
  shows "finite (connected_components E)"
  unfolding connected_components_def
  using assms
  by auto

lemma Berge_1:
  assumes finite: "finite M" "finite M'" and
    matchings: "matching M" "matching M'" and
    lt_matching: "card M < card M'" and
    doubleton_neq_edges: "\<forall>e\<in>(M \<oplus> M').\<exists>u v. e = {u,v} \<and> u \<noteq> v" "\<forall>e\<in>M. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "\<exists>p. augmenting_path M p \<and> path (M \<oplus> M') p \<and> distinct p"
proof-
  have finite_symm_diff: "finite (M \<oplus> M')"
    using finite
    by (simp add: finite_symm_diff)
  then have finiteVs: "finite (Vs (M \<oplus> M'))"
    by (metis Vs_def doubleton_neq_edges(1) finite.simps finite_Union)
  have "\<forall>e\<in>M \<oplus> M'. \<exists>u v. e = {u, v}"
    using doubleton_neq_edges by fastforce
  then obtain C where 
    con_comp: "C \<in> connected_components (M \<oplus> M')" and
    more_M'_edges: "card (M' \<inter> (component_edges (M \<oplus> M') C)) > card (M \<inter> (component_edges (M \<oplus> M') C))"
    using one_unbalanced_comp_edges[OF finite(1) lt_matching finite_con_comps[OF finiteVs]]
    unfolding components_edges_def
    by (auto simp add: inf_commute)
  moreover have finite_comp: "finite C"
    using finiteVs
    by (meson con_comp connected_component_subs_Vs rev_finite_subset)
  moreover note finite_symm_diff
  ultimately have "augpath (M \<oplus> M') M (component_path' (M \<oplus> M') C)"
    by(intro augmenting_path_exists_1 assms; auto)+
  then show ?thesis
    by metis
qed

subsection\<open>Direction 2 of Berge\<close>

text\<open>An augmenting path can be used to construct a larger matching.\<close>

lemma matching_delete:
  assumes "matching M"
  shows "matching (M - N)"
  using assms
  unfolding matching_def by blast

lemma matching_insert:
  assumes "e \<inter> (Vs M) = {}" "matching M"
  shows "matching (insert e M)"
  using assms
  unfolding Vs_def matching_def by blast

lemma symmetric_difference_assoc: "A \<oplus> (B \<oplus> C) = (A \<oplus> B) \<oplus> C"
  unfolding symmetric_diff_def by blast

lemma symm_diff_is_matching:
  assumes 
    "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
    "matching M"
    "hd p \<notin> Vs M"
    "length p \<ge> 2 \<and> even (length p) \<Longrightarrow> last p \<notin> Vs M"
    "distinct p"
  shows "matching (M \<oplus> set (edges_of_path p))"
  using assms
proof(induction p arbitrary: M rule: induct_list0123)
  case nil
  then show ?case by (simp add: symmetric_diff_def)
next
  case list1
  then show ?case by (simp add: symmetric_diff_def)
next
  case (list2 x y)
  have "\<nexists>e. e \<in> M \<and> x \<in> e" using Vs_def list2.prems(3) by fastforce
  moreover have "\<nexists>e. e \<in> M \<and> y \<in> e" using Vs_def list2.prems(4) by fastforce
  moreover have "z = x \<or> z = y \<or> z \<in> Vs M" if "z \<in> Vs (insert {x, y} M)" for z
    by (metis Sup_insert UnE Vs_def empty_iff insert_iff that)
  ultimately have "matching (insert {x, y} M)" using list2.prems(2) unfolding matching_def by simp
  moreover have "{x, y} \<notin> M" using \<open>\<nexists>e. e \<in> M \<and> x \<in> e\<close> by blast
  ultimately show ?case unfolding symmetric_diff_def by simp
next
  case (list3 x y z ps)
  from list3.prems(1)
  have "{x, y} \<notin> M" "{y, z} \<in> M" by (simp_all add: alt_list_step)

  define M' where "M' \<equiv> insert {x, y} (M - {{y, z}})"
  have M'symmdiff: "M' = M \<oplus> {{x, y}, {y, z}}" unfolding symmetric_diff_def M'_def
    using \<open>{x, y} \<notin> M\<close> \<open>{y, z} \<in> M\<close> by fastforce
  have xysymmdiff: "set (edges_of_path (x#y#z#ps)) = {{x, y}, {y, z}} \<oplus> set (edges_of_path (z # ps))"
    unfolding symmetric_diff_def
    using list3.prems(5) v_in_edge_in_path by fastforce

  have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path (z # ps))"
    using list3.prems(1) by (simp add: alt_list_step)
  hence altlistM': "alt_list (\<lambda>e. e \<notin> M') (\<lambda>e. e \<in> M') (edges_of_path (z # ps))"
    apply (rule alt_list_cong)
    using list3.prems(5) v_in_edge_in_path M'_def by force+

  have "x \<notin> Vs (M - {{y, z}})" using \<open>{y, z} \<in> M\<close> list3.prems(3) unfolding Vs_def by simp
  moreover have "y \<notin> Vs (M - {{y, z}})"
    using \<open>{y, z} \<in> M\<close> list3.prems(2) unfolding Vs_def matching_def by force
  ultimately have "matching M'" unfolding M'_def
    by (simp add: matching_delete matching_insert list3.prems(2))

  {
    assume "z \<in> Vs M'"
    hence "z \<in> Vs (M - {{y, z}})" unfolding M'_def Vs_def using list3.prems(5) by fastforce
    then obtain e where "z \<in> e" "e \<in> M" "e \<noteq> {y, z}" unfolding Vs_def by blast
    hence False using \<open>{y, z} \<in> M\<close> list3.prems(2) matching_def by force
  }
  moreover
  {
    assume "last (z # ps) \<in> Vs M'"
    hence "last (z # ps) \<in> Vs M \<or> last (z # ps) \<in> {x, y}" unfolding M'_def Vs_def by blast
    moreover assume "2 \<le> length (z # ps)" "even (length (z # ps))"
    ultimately have "last (z # ps) \<in> {x, y}" using list3.prems(4) by force
    hence False using list3.prems(5) last_in_set
      by (metis distinct.simps(2) distinct_length_2_or_more insert_iff list.distinct(1) singletonD)
  }
  moreover note \<open>matching M'\<close> altlistM' list3.prems(5)
  ultimately have "matching (M' \<oplus> set (edges_of_path (z # ps)))"
    using list3.IH(2) by fastforce
  then show ?case
    unfolding M'symmdiff xysymmdiff by (simp add: symmetric_difference_assoc)
qed

lemma condition_for_greatness:
  assumes "card (s \<inter> t) < card (s - t)" "finite t"
  shows "card t < card (t \<oplus> s)"
proof-
  have tsstinter: "(t - s) \<inter> (s - t) = {}" by blast

  have "card t = card ((t - s) \<union> (t \<inter> s))" by (simp add: Un_Diff_Int)
  also have "... = card (t - s) + card (t \<inter> s)"
    by (metis Diff_Diff_Int Diff_disjoint assms(2) card_Un_disjoint finite_Diff)
  also have "... < card (t - s) + card (s - t)"
    by (simp add: assms(1) inf.commute)
  also have "... = card ((t - s) \<union> (s - t))"
    by (metis assms card_Un_disjoint card.infinite finite_Diff not_less_zero tsstinter)
  also have "... = card (t \<oplus> s)" unfolding symmetric_diff_def by simp
  finally show ?thesis .
qed

lemma last_edge_in_last_vert_in:
  assumes "length p \<ge> 2" "last (edges_of_path p) \<in> E"
  shows "last p \<in> Vs E"
  using Vs_def assms last_v_in_last_e by fastforce

lemma hd_edge_in_hd_vert_in:
  assumes "length p \<ge> 2" "hd (edges_of_path p) \<in> E"
  shows "hd p \<in> Vs E"
  using Vs_def assms hd_v_in_hd_e by fastforce

lemma distinct_length_filter_neg: "distinct xs \<Longrightarrow> card (set xs - M) = length (filter (\<lambda>e. e \<notin> M) xs)"
proof (induction xs)
  case (Cons a as)
  thus ?case
  proof(cases "a \<in> M")
    case False thus ?thesis using Cons
      by (metis (full_types) distinct_card distinct_filter set_diff_eq set_filter)
  qed simp
qed simp

lemma new_matching_bigger:
  assumes "augmenting_path M p"
  assumes "distinct p"
  assumes "finite M"
  shows "card M < card (M \<oplus> set (edges_of_path p))"
proof-
  have dist: "distinct (edges_of_path p)"
    using assms(2)
    by (simp add: distinct_edges_of_vpath)
  have "length (filter (\<lambda>e. e \<notin> M) (edges_of_path p)) = length (filter (\<lambda>e. e \<in> M) (edges_of_path p)) + 1"
    using alternating_eq_iff_odd assms(1) augmenting_path_feats(2) augmenting_path_odd_length
    by blast
  then have "card (set (edges_of_path p) - M) = card (set (edges_of_path p) \<inter> M) + 1"
    using distinct_length_filter_neg[OF dist] distinct_length_filter[OF dist]
    by (simp add: inf_commute)
  then show ?thesis
    using condition_for_greatness[OF _ assms(3)] by simp
qed

lemma Berge_2:         
  assumes aug_path: "augmenting_path M p" "M \<subseteq> E" "path E p" "distinct p" and
    finite: "finite M" and
    matchings: "matching M"
  shows "matching (M \<oplus> set (edges_of_path p))" (is ?g1)
        "card M < card (M \<oplus> set (edges_of_path p))" (is ?g2)
        "(M \<oplus> set (edges_of_path p)) \<subseteq> E" (is ?g3)
proof-
  show ?g1
    apply(intro symm_diff_is_matching assms)
    using aug_path[unfolded augmenting_path_def] by simp_all
  show ?g2
    by (intro new_matching_bigger assms)
  show ?g3
    using path_edges_subset sym_diff_subset aug_path(2,3)
    by (metis le_supI order.trans)
qed

theorem Berge:
  assumes matching: "finite M" "matching M" "M \<subseteq> E" and
    graph: "(\<forall>e\<in>E. \<exists>u v. e = {u,v} \<and> u \<noteq> v)"
    "finite (Vs E)"
  shows "(\<exists>p. augmenting_path M p \<and> path E p \<and> distinct p) =
            (\<exists>M' \<subseteq> E. matching M' \<and> card M < card M')"
proof
  assume "\<exists>p. augmenting_path M p \<and> path E p \<and> distinct p"
  then obtain p where "augmenting_path M p" "path E p" "distinct p"
    by blast
  then obtain M' where "M' \<subseteq> E" "matching M'" "card M < card M'"
    using Berge_2 matching by metis
  then show "\<exists>M'\<subseteq>E. matching M' \<and> card M < card M'"
    by blast
next
  assume "\<exists>M'\<subseteq>E. matching M' \<and> card M < card M'"
  then obtain M' where M': "M' \<subseteq> E" "matching M'" "card M < card M'"
    by blast
  then have finiteM': "finite M'"
    using card.infinite by force
  have MM'_subset: "M \<oplus> M' \<subseteq> E"
    using sym_diff_subset matching(3) M'(1) by fast
  have "\<forall>e \<in> M \<oplus> M'. \<exists>u v. e = {u,v} \<and> u \<noteq> v"
    using MM'_subset graph(1) by blast
  moreover have "\<forall>e \<in> M. \<exists>u v. e = {u,v} \<and> u \<noteq> v"
    using matching(3) graph(1) by blast
  ultimately obtain p where "augmenting_path M p" "path (M \<oplus> M') p" "distinct p"
    using Berge_1[OF matching(1) finiteM' matching(2) M'(2, 3)]
    by blast
  moreover then have "path E p"
    using path_subset MM'_subset
    by blast
  ultimately show "\<exists>p. augmenting_path M p \<and> path E p \<and> distinct p"
    by metis
qed

abbreviation "graph_matching E M \<equiv> matching M \<and> M \<subseteq> E"

lemma laterally_transfer_aug_path':
  assumes "card M = card M'"
  assumes matching: "graph_matching E M'" "finite M'"
  assumes matching': "graph_matching E M" "finite M" 
  assumes graph: "(\<forall>e\<in>E. \<exists>u v. e = {u,v} \<and> u \<noteq> v)" "finite (Vs E)"
  assumes augpath: "augpath E M p"
  obtains q where "augpath E M' q"
proof-
  from augpath
  obtain N where N_def: "N \<subseteq> E" "matching N" "card M < card N" using Berge matching' graph by metis
  hence "card M' < card N" using assms(1) by linarith
  then obtain q where "augpath E M' q" using Berge matching graph N_def(1, 2) by metis
  then show ?thesis using that by simp
qed

lemma laterally_transfer_aug_path:
  assumes "card M = card M'"
  assumes matching: "graph_matching E M'" "finite M'"
  assumes matching': "graph_matching E M" "finite M" 
  assumes graph: "(\<forall>e\<in>E. \<exists>u v. e = {u,v} \<and> u \<noteq> v)" "finite (Vs E)"
  shows "(\<exists>p. augpath E M p) \<longleftrightarrow> (\<exists>p. augpath E M' p)"
proof-
  from assms(1) have card': "card M' = card M" by simp
  show ?thesis
    using laterally_transfer_aug_path'[OF assms(1) matching matching' graph]
          laterally_transfer_aug_path'[OF card' matching' matching graph]
    by metis
qed

locale graph_matching_defs =
  graph_defs +
  fixes M :: "'a set set"

abbreviation "alt_path M p \<equiv> alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
abbreviation "rev_alt_path M p \<equiv> alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p)"

end
