theory Undirected_Set_Graphs
  imports "Directed_Set_Graphs.enat_misc" "HOL-Eisbach.Eisbach_Tools" "HOL-Library.FuncSet" 
(*needed for proofs on number + cardinality of comps*)
begin

subsection \<open>Misc\<close>

text\<open>Since one of the matchings is bigger, there must be one edge equivalence class
  that has more edges from the bigger matching.\<close>

lemma lt_sum:
  "(\<Sum>x\<in>s. g x) < (\<Sum>x\<in>s. f x) \<Longrightarrow> \<exists>(x::'a ) \<in> s. ((g::'a \<Rightarrow> nat) x < f x)"
  by (auto simp add: not_le[symmetric] intro: sum_mono)

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
      using ass disj
      by(fastforce intro!: card_UN_disjoint finite)
  }note * = this
  show ?thesis
    using card_lt *[OF finite(2)] *[OF finite(3)]
    by (auto intro: lt_sum)
qed

definition card' :: "'a set \<Rightarrow> enat" where
  "card' A = (if infinite A then \<infinity> else card A)"

lemma card'_finite: "finite A \<Longrightarrow> card' A = card A"
  unfolding card'_def by simp

lemma card'_mono: "A \<subseteq> B \<Longrightarrow> card' A \<le> card' B"
  using finite_subset
  by (auto simp add: card'_def intro: card_mono)

lemma card'_empty[iff]: "(card' A = 0) \<longleftrightarrow> A = {}"
  unfolding card'_def using enat_0_iff(2) by auto

lemma card'_finite_nat[iff]: "(card' A = numeral m) \<longleftrightarrow> (finite A \<and> card A = numeral m)"
  unfolding card'_def
  by (simp add: numeral_eq_enat)

(*TODO: remove the enat notions*)

lemma card'_finite_enat[iff]: "(card' A = enat m) \<longleftrightarrow> (finite A \<and> card A = m)"
  unfolding card'_def by simp

(*TODO: FIX METIS*)

lemma card'_1_singletonE:
  assumes "card' A = 1"
  obtains x where "A = {x}"
  using assms
  unfolding card'_def
  by (fastforce elim!: card_1_singletonE dest: iffD1[OF enat_1_iff(1)] split: if_splits)

lemma card'_insert[simp]: "card' (insert a A) = (if a \<in> A then id else eSuc) (card' A)"
  using card_insert_if finite_insert
  by (simp add: card_insert_if card'_def)

lemma card'_empty_2[simp]: "card' {} = enat 0"
  by (simp add: card'_def)

section\<open>Undirected Graphs\<close>

definition Vs where "Vs G = \<Union> G"

lemma Vs_subset:
  "G \<subseteq> G' \<Longrightarrow> Vs G \<subseteq> Vs G'"
  by (auto simp: Vs_def)

lemma vs_member[iff?]: "v \<in> Vs G \<longleftrightarrow> (\<exists>e \<in> G. v \<in> e)"
  unfolding Vs_def by simp

lemma vs_member_elim[elim?]:
  assumes "v \<in> Vs G"
  obtains e where "v \<in> e" "e \<in> G"
  using assms
  by(auto simp: vs_member)

lemma vs_member_intro[intro]:
  "\<lbrakk>v \<in> e; e \<in> G\<rbrakk> \<Longrightarrow> v \<in> Vs G"
  using vs_member
  by force

lemma vs_transport:
  "\<lbrakk>u \<in> Vs G; \<And>e. \<lbrakk>u \<in> e; e \<in> G\<rbrakk> \<Longrightarrow> \<exists>g \<in> F. u \<in> g\<rbrakk> \<Longrightarrow>u \<in> Vs F"
  by (auto simp: vs_member)

lemma edges_are_Vs:
  assumes "{v, v'} \<in> G"
  shows "v \<in> Vs G"
  using assms by blast

lemma edges_are_Vs_2:
  assumes "{v', v} \<in> G"
  shows "v \<in> Vs G"
  using assms by blast

lemma finite_Vs_then_finite:
  assumes "finite (Vs G)"
  shows "finite G"
  using assms
  by (metis Vs_def finite_UnionD)

definition degree where
  "degree G v = card' ({e. v \<in> e} \<inter> G)"

lemma degree_def2: "degree G v \<equiv> card' {e \<in> G. v \<in> e}"
  unfolding degree_def
  by (simp add: Collect_conj_eq Int_commute)

lemma degree_Vs: "degree G v \<ge> 1" if "v \<in> Vs G"
proof-
  obtain e where "e \<in> G" "v \<in> e"
    using \<open>v \<in> Vs G\<close>
    by (auto simp: Vs_def)
  hence "{e} \<subseteq> {e \<in> G. v \<in> e}" by simp
  moreover have "card' {e} = 1" by (simp add: one_enat_def)
  ultimately show ?thesis
    by(fastforce dest!: card'_mono simp: degree_def2)
qed

lemma degree_not_Vs: "v \<notin> Vs G \<Longrightarrow> degree G v = 0"
  by (fastforce simp only: Vs_def degree_def)

lemma degree_insert: "\<lbrakk>v \<in> a; a \<notin> G\<rbrakk> \<Longrightarrow> degree (insert a G) v = eSuc (degree G v)"
  by (simp add: degree_def)

lemma degree_empty[simp]: "degree {} a = 0"
  unfolding degree_def by (simp add: zero_enat_def)

lemma degree_card_all:
  assumes "card G \<ge> numeral m"
  assumes "\<forall>e \<in> G. a \<in> e"
  assumes "finite G"
  shows "degree G a \<ge> numeral m"
  using assms unfolding degree_def
  by (simp add: card'_finite inf.absorb2 subsetI)

lemma subset_edges_less_degree:
  "G' \<subseteq> G \<Longrightarrow> degree G' v \<le> degree G v"
  by (auto intro: card'_mono simp: degree_def)

lemma less_edges_less_degree:
  shows "degree (G - G') v \<le> degree G v"
  by (intro subset_edges_less_degree)
     (simp add: subset_edges_less_degree)

definition "neighbourhood G v = {u. {u,v} \<in> G}"

lemma in_neighD[dest]: "v \<in> neighbourhood G u \<Longrightarrow> {u, v} \<in> G"
"v \<in> neighbourhood G u \<Longrightarrow> {v, u} \<in> G"
  by (auto simp: neighbourhood_def insert_commute)

locale graph_defs =
  fixes G :: "'a set set"

definition "dblton_graph G = (\<forall>e\<in>G. \<exists>u v. e = {u, v} \<and> u \<noteq> v)"

lemma dblton_graphE[elim]:
  assumes "dblton_graph G" "e \<in> G"
  obtains u v where "e = {u,v}" "u \<noteq> v"
  using assms
  by (auto simp: dblton_graph_def)

lemma dblton_graphI:
 assumes "\<And>e. e \<in> G \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "dblton_graph G"
  using assms
  by (auto simp: dblton_graph_def)

lemma dblton_graph_finite_Vs:
 assumes "dblton_graph G"
  shows "finite G \<longleftrightarrow> finite (Vs G)"
  using assms
  by (auto simp: dblton_graph_def Vs_def dest: finite_UnionD)

lemma dblton_graph_subset[intro]:
  "\<lbrakk>dblton_graph G1; G2 \<subseteq> G1\<rbrakk> \<Longrightarrow> dblton_graph G2"
  by (auto elim!: dblton_graphE intro!: dblton_graphI) 

abbreviation "graph_invar G \<equiv> dblton_graph G \<and> finite (Vs G)"

lemma graph_invar_finite_Vs:
 assumes "graph_invar G"
  shows "finite (Vs G)"
  using assms dblton_graph_finite_Vs
  by auto

lemma graph_invar_dblton:
 assumes "graph_invar G"
  shows "dblton_graph G"
  using assms dblton_graph_finite_Vs
  by auto

lemma graph_invar_finite:
 assumes "graph_invar G"
  shows "finite G"
  using assms dblton_graph_finite_Vs
  by auto
   
lemma graph_invar_subset[intro]:
  "\<lbrakk>graph_invar G1; G2 \<subseteq> G1\<rbrakk> \<Longrightarrow> graph_invar G2"
  using dblton_graph_subset
  by (metis dblton_graph_finite_Vs finite_subset)

locale graph_abs =
  graph_defs +
  assumes graph: "graph_invar G"
begin                  

lemma finite_E: "finite G"
  using finite_UnionD graph
  unfolding Vs_def
  by blast

lemma dblton_E: "dblton_graph G"
  using finite_UnionD graph
  unfolding Vs_def
  by blast

lemma dblton_graphE[elim]:
  assumes "e \<in> G"
  obtains u v where "e = {u,v}" "u \<noteq> v"
  using dblton_graphE[OF dblton_E assms] .

lemma finite_Vs: "finite (Vs G)"
  by (simp add: graph)

lemma finite_G_Vsb: "finite (Vs G) = finite G"
  using graph
  using finite_E by auto

end


lemma graph_abs_mono: "graph_abs G \<Longrightarrow> F \<subseteq> G \<Longrightarrow> graph_abs F"
  unfolding graph_abs_def
  by (auto simp: Vs_subset rev_finite_subset)
                                              
lemma graph_invar_insert[simp]: "u \<noteq> v \<Longrightarrow> graph_invar G \<Longrightarrow> graph_invar (insert {u,v} G)"
  unfolding graph_abs_def
  by (fastforce simp: Vs_def  intro!: dblton_graphI)

subsection\<open>Paths, connected components, and symmetric differences\<close>

text\<open>Some basic definitions about the above concepts. One interesting point is the use of the
     concepts of connected components, which partition the set of vertices, and the analogous
     partition of edges. Juggling around between the two partitions, we get a much shorter proof for
     the first direction of Berge's lemma, which is the harder one.\<close>


context fixes X :: "'a set set" begin
inductive path where
  path0: "path []" |
  path1: "v \<in> Vs X \<Longrightarrow> path [v]" |
  path2: "{v,v'} \<in> X \<Longrightarrow> path (v'#vs) \<Longrightarrow> path (v#v'#vs)"
end

declare path0

inductive_simps path_1: "path X [v]"

inductive_simps path_2: "path X (v # v' # vs)"

lemmas path_simps[simp] = path0 path_1 path_2


text\<open>
  If a set of edges cannot be partitioned in paths, then it has a junction of 3 or more edges.
  In particular, an edge from one of the two matchings belongs to the path
  equivalent to one connected component. Otherwise, there will be a vertex whose degree is
  more than 2.
\<close>


text\<open>
  Gvery edge lies completely in a connected component.
\<close>

fun edges_of_path where
"edges_of_path [] = []" |
"edges_of_path [v] = []" |
"edges_of_path (v#v'#l) = {v,v'} # (edges_of_path (v'#l))"

lemma path_ball_edges: "path G p \<Longrightarrow> b \<in> set (edges_of_path p) \<Longrightarrow> b \<in> G"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_index:
  "Suc i < length p \<Longrightarrow> edges_of_path p ! i = {p ! i, p ! Suc i}"
proof(induction i arbitrary: p)
  case 0
  then obtain u v ps where "p = u#v#ps" 
    by (auto simp: less_eq_Suc_le Suc_le_length_iff)
  thus ?case by simp
next
  case (Suc i)
  then obtain u v ps where "p = u#v#ps"
    by (auto simp: less_eq_Suc_le Suc_le_length_iff)
  hence "edges_of_path (v#ps) ! i = {(v#ps) ! i, (v#ps) ! Suc i}"
    using Suc.IH Suc.prems
    by simp
  thus ?case using \<open>p = u#v#ps\<close>
    by simp
qed

lemma edges_of_path_length: "length (edges_of_path p) = length p - 1"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_length': "p \<noteq> [] \<Longrightarrow> length p = length (edges_of_path p) + 1"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_for_inner:
  assumes "v = p ! i" "Suc i < length p"
  obtains u w where "{u, v} = edges_of_path p ! (i - 1)" "{v, w} = edges_of_path p ! i"
proof(cases "i = 0")
  case True thus ?thesis 
    using assms(1) edges_of_path_index[OF assms(2)] that
    by auto
next
  case False thus ?thesis
    by (auto simp add: Suc_lessD assms edges_of_path_index that)
qed

lemma path_vertex_has_edge:
  assumes "length p \<ge> 2" "v \<in> set p"
  obtains e where "e \<in> set (edges_of_path p)" "v \<in> e"
proof-
  have "\<exists>e \<in> set (edges_of_path p). v \<in> e"
    using assms Suc_le_eq 
    by (induction p rule: edges_of_path.induct) fastforce+
  thus ?thesis
    using that
    by rule
qed

lemma v_in_edge_in_path:
  assumes "{u, v} \<in> set (edges_of_path p)"
  shows "u \<in> set p"
  using assms
  by (induction p rule: edges_of_path.induct) auto

lemma v_in_edge_in_path_inj:
  assumes "e \<in> set (edges_of_path p)"
  obtains u v where "e = {u, v}"
  using assms
  by (induction p rule: edges_of_path.induct) auto

lemma v_in_edge_in_path_gen:
  assumes "e \<in> set (edges_of_path p)" "u \<in> e"
  shows "u \<in> set p"
proof-
  obtain u v where "e = {u, v}"
    using assms(1) v_in_edge_in_path_inj
    by blast
  thus ?thesis
    using assms
    by (force simp add: insert_commute intro: v_in_edge_in_path)
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
  have "edges_of_path (p @ p') = edges_of_path (butlast p @ last p # p')"
    by (subst append_butlast_last_id[symmetric, OF assms], subst append.assoc, simp)
  also have "... = edges_of_path (butlast p @ [last p]) @ edges_of_path (last p # p')"
    using edges_of_path_append_2
    by fastforce
  also have "... = edges_of_path p @ edges_of_path (last p # p')"
    by (simp add: assms)
  finally show ?thesis .
qed

lemma edges_of_path_rev:
  shows "rev (edges_of_path p) = edges_of_path (rev p)"
proof(induction p rule: edges_of_path.induct)
  case (3 v v' l)
  moreover have "edges_of_path (rev l @ [v', v]) = 
                   edges_of_path (rev l @ [v']) @ edges_of_path [v', v]"
    apply(subst edges_of_path_append_2)
    by auto
  ultimately show ?case
    by auto
qed auto

lemma edges_of_path_append: "\<exists>ep. edges_of_path (p @ p') = ep @ edges_of_path p'"
proof(cases p')
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis using edges_of_path_append_2 by blast
qed

lemma last_v_in_last_e: 
  "length p \<ge> 2 \<Longrightarrow> last p \<in> last (edges_of_path p)"
  by (induction "p" rule: induct_list012) (auto elim: edges_of_path.elims simp add: Suc_leI)

lemma hd_v_in_hd_e: 
  "length p \<ge> 2 \<Longrightarrow> hd p \<in> hd (edges_of_path p)"
  by (auto simp: Suc_le_length_iff numeral_2_eq_2)

lemma last_in_edge:
  assumes "p \<noteq> []"
  shows "\<exists>u. {u, last p} \<in> set (edges_of_path (v # p)) \<and> u \<in> set (v # p)"
  using assms
proof(induction "length p" arbitrary: v p)
  case (Suc x)
  thus ?case
  proof(cases p)
    case p: (Cons _ p')
    thus ?thesis
    proof(cases "p' = []")
      case False
      then show ?thesis
        using Suc
        by(auto simp add: p)
    qed auto
  qed auto
qed simp

find_theorems edges_of_path "(@)"

lemma edges_of_path_append_subset:
  "set (edges_of_path p') \<subseteq> set (edges_of_path (p @ p'))"
proof(cases p')
  case (Cons a list)
  then show ?thesis
    apply(subst edges_of_path_append_2)
    by auto
qed auto

lemma edges_of_path_append_subset_2:
  "set (edges_of_path p) \<subseteq> set (edges_of_path (p @ p'))"
proof(cases p)
  case (Cons a list)
  then show ?thesis 
   by(metis edges_of_path_append_subset edges_of_path_rev rev_append set_rev)
qed auto

lemma path_edges_subset:
  assumes "path G p"
  shows "set (edges_of_path p) \<subseteq> G"
  using assms
  by (induction, simp_all)

lemma edges_of_path_symmetric_split:"edges_of_path (xs@[x,y]@ys) = edges_of_path (xs@[x]) @[{x,y}] @ edges_of_path (y#ys)"
  by (metis append_is_Nil_conv edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append_2 
edges_of_path_append_3 hd_append2 last_ConsL last_ConsR list.discI list.sel(1))

lemma induct_list012[case_names nil single sucsuc]:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. \<lbrakk> P zs; P (y # zs) \<rbrakk> \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_list0123[consumes 0, case_names nil list1 list2 list3]:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x, y]; 
    \<And>x y z zs. \<lbrakk> P zs; P (z # zs); P (y # z # zs) \<rbrakk> \<Longrightarrow> P (x # y # z # zs)\<rbrakk>
    \<Longrightarrow> P xs"
by induction_schema (pat_completeness, lexicographic_order)

lemma tl_path_is_path: "path G p \<Longrightarrow> path G (tl p)"
  by (induction p rule: path.induct) (simp_all)

lemma path_concat:
  "\<lbrakk>path G p; path G q; q \<noteq> []; p \<noteq> [] \<Longrightarrow> last p = hd q\<rbrakk> \<Longrightarrow> path G (p @ tl q)"
  by (induction rule: path.induct) (simp_all add: tl_path_is_path)

lemma path_append:
  "\<lbrakk>path G p1; path G p2; \<lbrakk>p1 \<noteq> []; p2 \<noteq> []\<rbrakk> \<Longrightarrow> {last p1, hd p2} \<in> G\<rbrakk> \<Longrightarrow> path G (p1 @ p2)"
  by (induction rule: path.induct) (auto simp add: neq_Nil_conv elim: path.cases)

lemma mem_path_Vs: 
  "\<lbrakk>path G p; a\<in>set p\<rbrakk> \<Longrightarrow> a \<in> Vs G"
  by (induction rule: path.induct) (simp; blast)+

lemma subset_path_Vs: 
  "\<lbrakk>path G p\<rbrakk> \<Longrightarrow> set p \<subseteq> Vs G"
  by (induction rule: path.induct) (simp; blast)+

lemma path_suff:
  assumes "path G (p1 @ p2)"
  shows "path G p2"
  using assms
proof(induction p1)
  case (Cons a p1)
  then show ?case using Cons tl_path_is_path by force
qed simp

lemma path_pref:
  assumes "path G (p1 @ p2)"
  shows "path G p1"
  using assms
proof(induction p1)
  case (Cons a p1)
  then show ?case using Cons by (cases p1; auto simp add: mem_path_Vs)
qed simp

lemma rev_path_is_path:
  assumes "path G p"
  shows "path G (rev p)"
  using assms
proof(induction)
  case (path2 v v' vs)
  moreover hence "{last (rev vs @ [v']), hd [v]} \<in> G"
    by (simp add: insert_commute)
  ultimately show ?case 
    using path_append edges_are_Vs
    by force
qed simp_all

lemma rev_path_is_path_iff:
  "path G (rev p) \<longleftrightarrow> path G p"
  using rev_path_is_path
  by force

lemma path_subset:
  assumes "path G p" "G \<subseteq> G'"
  shows "path G' p"
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
  by (auto elim: vs_member_elim intro: v_in_edge_in_path_gen)

subsection \<open>Walks, and Connected Components\<close>

definition "walk_betw G u p v = (p \<noteq> [] \<and> path G p \<and> hd p = u \<and> last p = v)"

lemma nonempty_path_walk_between:
  "\<lbrakk>path G p; p \<noteq> []; hd p = u; last p = v\<rbrakk> \<Longrightarrow> walk_betw G u p v"
  by (simp add: walk_betw_def)

lemma nonempty_path_walk_betweenE:
  assumes "path G p" "p \<noteq> []" "hd p = u" "last p = v"
  obtains p where "walk_betw G u p v"
  using assms
  by (simp add: walk_betw_def)

lemma walk_nonempty:
  assumes "walk_betw G u p v"
  shows [simp]: "p \<noteq> []"
  using assms walk_betw_def by fastforce

lemma walk_between_nonempty_pathD:
  assumes "walk_betw G u p v"
  shows "path G p" "p \<noteq> []" "hd p = u" "last p = v"
  using assms unfolding walk_betw_def by simp_all

lemma walk_reflexive:
  "w \<in> Vs G \<Longrightarrow> walk_betw G w [w] w"
  by (simp add: nonempty_path_walk_between)

lemma walk_symmetric:
  "walk_betw G u p v \<Longrightarrow> walk_betw G v (rev p) u"
  by (auto simp add: hd_rev last_rev walk_betw_def intro: rev_path_is_path)

lemma walk_transitive:
   "\<lbrakk>walk_betw G u p v; walk_betw G v q w\<rbrakk> \<Longrightarrow> walk_betw G u (p @ tl q) w"
  by (auto simp add: walk_betw_def intro: path_concat elim: path.cases)

lemma walk_transitive_2:
  "\<lbrakk>walk_betw G v q w; walk_betw G u p v\<rbrakk> \<Longrightarrow> walk_betw G u (p @ tl q) w"
  by (auto simp add: walk_betw_def intro: path_concat elim: path.cases)

lemma walk_in_Vs:
  "walk_betw G a p b \<Longrightarrow> set p \<subseteq> Vs G"
  by (simp add: subset_path_Vs walk_betw_def)

lemma walk_endpoints:
  assumes "walk_betw G u p v"
  shows [simp]: "u \<in> Vs G"
  and   [simp]: "v \<in> Vs G"
  using assms mem_path_Vs walk_betw_def
  by fastforce+

lemma walk_pref:
  "walk_betw G u (pr @ [x] @ su) v \<Longrightarrow> walk_betw G u (pr @ [x]) x"
proof(rule nonempty_path_walk_between, goal_cases)
  case 1
  hence "walk_betw G u ((pr @ [x]) @ su) v"
    by auto
  thus ?case
    by (fastforce dest!: walk_between_nonempty_pathD(1) path_pref)
next
  case 3
  then show ?case
    by(cases pr) (auto simp: walk_betw_def)
qed auto

lemma walk_suff:
   "walk_betw G u (pr @ [x] @ su) v \<Longrightarrow> walk_betw G x (x # su) v"
  by (fastforce simp: path_suff walk_betw_def)

lemma edges_are_walks:
  "{v, w} \<in> G \<Longrightarrow> walk_betw G v [v, w] w"
  using edges_are_Vs insert_commute
  by (auto 4 3 intro!: nonempty_path_walk_between)

lemma walk_subset:
  "\<lbrakk>walk_betw G u p v; G \<subseteq> G'\<rbrakk> \<Longrightarrow> walk_betw G' u p v"
  using path_subset
  by (auto simp: walk_betw_def)

lemma induct_walk_betw[case_names path1 path2, consumes 1, induct set: walk_betw]:
  assumes "walk_betw G a p b"
  assumes Path1: "\<And>v. v \<in> Vs G \<Longrightarrow> P v [v] v"
  assumes Path2: "\<And>v v' vs b. {v, v'} \<in> G \<Longrightarrow> walk_betw G v' (v' # vs) b \<Longrightarrow> P v' (v' # vs) b \<Longrightarrow> P v (v # v' # vs) b"
  shows "P a p b"
proof-
  have "path G p" "p \<noteq> []" "hd p = a" "last p = b"
    using assms(1)
    by (auto dest: walk_between_nonempty_pathD)
  thus ?thesis
    by (induction arbitrary: a b rule: path.induct) (auto simp: nonempty_path_walk_between assms(2,3))
qed

lemma walk_betw_length:"a \<noteq> b \<Longrightarrow> walk_betw E a p b \<Longrightarrow> length p \<ge> 2" for a b E p
    unfolding walk_betw_def 
    by(induction p rule: edges_of_path.induct) auto

lemma walk_betw_different_verts_to_ditinct: 
  assumes "walk_betw G u p v" "u \<noteq> v" "length p = l"
  shows " \<exists> q. walk_betw G u q v \<and> distinct q \<and> set q \<subseteq> set p"
  using assms
proof(induction l arbitrary: u p v rule: less_induct)
  case (less l)
  show ?case
  proof(cases "distinct p")
    case True
    then show ?thesis 
      using less(2) by auto
  next
    case False
    then obtain x p1 p2 p3 where p_split:"p = p1@[x]@p2@[x]@p3"
      using not_distinct_decomp by blast
    have new_walk:"walk_betw G u (p1@[x]@p3) v" 
    proof(cases p1)
      case Nil
      hence "u =x"
        using less.prems(1) p_split walk_between_nonempty_pathD(3) by fastforce
      then show ?thesis 
        using less.prems(1) local.Nil p_split path_suff walk_betw_def by fastforce
    next
      case (Cons a list)
      then show ?thesis 
        using  append.assoc less.prems(1) list.sel(3) walk_pref walk_suff[of G u "p1@[x]@p2" x p3 v]
          walk_transitive[of G u "p1@[x]" x]
        by(unfold p_split) fastforce
    qed
    have "length (p1 @ [x] @ p3) < l"
      using p_split less(4) by simp
    then obtain q where q_prop: " walk_betw G u q v" "distinct q" "set q \<subseteq> set (p1 @ [x] @ p3)"
      using less(1)[OF _ new_walk less(3) refl] by auto
    show ?thesis
      using q_prop by(auto intro!: exI[of _ q] simp add: p_split)
  qed
qed

definition reachable where
  "reachable G u v = (\<exists>p. walk_betw G u p v)"

lemma reachableE:
  "reachable G u v \<Longrightarrow> (\<And>p. p \<noteq> [] \<Longrightarrow> walk_betw G u p v \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: reachable_def)

lemma reachableD:
  "reachable G u v \<Longrightarrow> \<exists>p. walk_betw G u p v"
  by (auto simp: reachable_def)

lemma reachableI:
  "walk_betw G u p v \<Longrightarrow> reachable G u v"
  by (auto simp: reachable_def)

lemma reachable_trans:
  "\<lbrakk>reachable G u v; reachable G v w\<rbrakk> \<Longrightarrow> reachable G u w"
  apply(erule reachableE)+
  apply (drule walk_transitive)
   apply assumption
  by (rule reachableI)

lemma reachable_sym:
  "reachable G u v \<longleftrightarrow> reachable G v u"
  by(auto simp add: reachable_def dest: walk_symmetric)

lemma reachable_refl:
  "u \<in> Vs G \<Longrightarrow> reachable G u u"
  by(auto simp add: reachable_def dest: walk_reflexive)

lemma not_reachable_empt: "reachable {} u v \<Longrightarrow> False"
  using subset_path_Vs[of empty _, simplified Vs_def Union_empty] 
  by (auto simp add: reachable_def walk_betw_def)

definition connected_component where
  "connected_component G v = {v'. v' = v \<or> reachable G v v'}"

text \<open>This is an easier to reason about characterisation, especially with automation\<close>

lemma connected_component_rechability:
  "connected_component G v = {v'. v' = v \<or> (reachable G v v')}"
  by (auto simp add: reachable_def connected_component_def)

definition "comps X E = connected_component E ` X"

text \<open>The abbreviation is there to allow for the definition as a lemma.\<close>

definition "connected_components_aux G = comps (Vs G) G"
abbreviation "connected_components G \<equiv> connected_components_aux G"

lemma connected_components_def: "connected_components G = {vs. \<exists>v. vs = connected_component G v \<and> v \<in> (Vs G)}"
  by(auto simp add: connected_components_aux_def comps_def)

lemma in_own_connected_component: "v \<in> connected_component G v"
  unfolding connected_component_def by simp

lemma in_connected_componentE:
  "\<lbrakk>v \<in> connected_component G w; \<lbrakk>reachable G w v; w \<in> Vs G\<rbrakk> \<Longrightarrow> P; w = v \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: connected_component_def reachable_refl elim: reachableE dest: walk_endpoints(1))

lemma in_connected_component_has_walk:
  assumes "v \<in> connected_component G w" "w \<in> Vs G"
  obtains p where "walk_betw G w p v"
proof(cases "v = w")
  case True thus ?thesis
   using that assms(2)
   by (auto dest: walk_reflexive )
next
  case False
  hence "reachable G w v"
    using assms(1) unfolding connected_component_def by blast
  thus ?thesis
    by (auto dest: reachableD that)
qed

(* TODO: Call in_connected_componentI *)

lemma has_path_in_connected_component:
  "walk_betw G u p v \<Longrightarrow> v \<in> connected_component G u"
  by(auto simp: connected_component_def reachable_def)

lemma in_connected_componentI:
  "reachable G w v \<Longrightarrow> v \<in> connected_component G w"
  by (auto simp: connected_component_rechability)

lemma in_connected_componentI2:
  "w = v \<Longrightarrow> v \<in> connected_component G w"
  by (auto simp: connected_component_rechability)

lemma edges_reachable:
  "{v, w} \<in> G \<Longrightarrow> reachable G v w"
  by (auto intro: edges_are_walks reachableI)

(* TODO: Call in_connected_componentI2 *)

lemma has_path_in_connected_component2:
  "(\<exists>p. walk_betw G u p v) \<Longrightarrow> v \<in> connected_component G u"
  unfolding connected_component_def reachable_def
  by blast

lemma connected_components_notE_singletons:
  "x \<notin> Vs G \<Longrightarrow> connected_component G x = {x}"
  by (fastforce simp add: connected_component_def reachable_def)

lemma connected_components_member_sym:
  "v \<in> connected_component G w \<Longrightarrow> w \<in> connected_component G v"
  by (auto elim!: in_connected_componentE intro: in_connected_componentI in_connected_componentI2
           simp: reachable_sym)

lemma connected_components_member_trans:
  "\<lbrakk>x \<in> connected_component G y; y \<in> connected_component G z\<rbrakk> \<Longrightarrow> x \<in> connected_component G z"
  by (auto elim!: in_connected_componentE dest: reachable_trans intro: in_connected_componentI
           simp: reachable_refl)

method in_tc uses tc_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R x y" for  y \<Rightarrow>
       \<open>match premises in b: "R y z" \<Rightarrow>
          \<open>(insert tc_thm[OF a b])\<close>\<close>\<close>)

method in_tc_2 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R x y" for  y \<Rightarrow>
       \<open>match premises in b: "R z y" \<Rightarrow>
          \<open>(insert tc_thm[OF a refl_thm[OF b]])\<close>\<close>\<close>)

method in_tc_3 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in b: "R y z" for  y \<Rightarrow>
       \<open>match premises in a: "R y x" \<Rightarrow>
          \<open>(insert tc_thm[OF refl_thm[OF a] b])\<close>\<close>\<close>)

method in_tc_4 uses tc_thm refl_thm = 
  (match conclusion in "R x z" for R and x::'a and z::'a \<Rightarrow>
     \<open>match premises in a: "R y x" for  y \<Rightarrow>
       \<open>match premises in b: "R z y" \<Rightarrow>
          \<open>(insert tc_thm[OF refl_thm[OF a] refl_thm[OF b]])\<close>\<close>\<close>)

method in_rtc uses tc_thm refl_thm =
  (safe?; (in_tc tc_thm: tc_thm | in_tc_2 tc_thm: tc_thm refl_thm: refl_thm |
    in_tc_3 tc_thm: tc_thm refl_thm: refl_thm | in_tc_4 tc_thm: tc_thm refl_thm: refl_thm),
    assumption?)+

lemma connected_components_member_eq:
  "v \<in> connected_component G w \<Longrightarrow> connected_component G v = connected_component G w"
  by(in_rtc tc_thm: connected_components_member_trans refl_thm: connected_components_member_sym)

lemma connected_components_closed:
    "\<lbrakk>v1 \<in> connected_component G v4; v3 \<in> connected_component G v4\<rbrakk> \<Longrightarrow> v3 \<in> connected_component G v1"
  by(in_rtc tc_thm: connected_components_member_trans refl_thm: connected_components_member_sym)

lemma C_is_componentE:
  assumes "C \<in> connected_components G"
  obtains v where "C = connected_component G v" "v \<in> Vs G"
  using assms
  by (fastforce simp add: connected_components_def)

lemma connected_components_closed':
  "\<lbrakk>v \<in> C; C \<in> connected_components G\<rbrakk> \<Longrightarrow> C = connected_component G v"
  by (fastforce elim: C_is_componentE simp: connected_components_member_eq)

lemma connected_components_closed'':
  "\<lbrakk>C \<in> connected_components G; v \<in> C\<rbrakk> \<Longrightarrow> C = connected_component G v"
  by (simp add: connected_components_closed')

lemma connected_components_eq:
  "\<lbrakk>v \<in> C ; v \<in> C'; C \<in> connected_components G; C' \<in> connected_components G\<rbrakk> \<Longrightarrow> C = C'"
  using connected_components_closed'[where G = G]
  by auto

lemma connected_components_eq':
  "\<lbrakk>C \<in> connected_components G; C' \<in> connected_components G; v \<in> C ; v \<in> C'\<rbrakk> \<Longrightarrow> C = C'"
  using connected_components_eq .

lemma connected_components_disj:
  "\<lbrakk>C \<noteq> C'; C \<in> connected_components G; C' \<in> connected_components G\<rbrakk> \<Longrightarrow> C \<inter> C' = {}"
  using connected_components_eq[where G = G]
  by auto

lemma own_connected_component_unique:
  assumes "x \<in> Vs G"
  shows "\<exists>!C \<in> connected_components G. x \<in> C"
proof(standard, intro conjI)
  show "connected_component G x \<in> connected_components G"
    using assms connected_components_def
    by blast
  show "x \<in> connected_component G x"
    using in_own_connected_component
    by fastforce
  fix C assume "C \<in> connected_components G \<and> x \<in> C"
  thus "C = connected_component G x"
    by (simp add: connected_components_closed')
qed

lemma edge_in_component:
  assumes "{x,y} \<in> G"
  shows "\<exists>C. C \<in> connected_components G \<and> {x,y} \<subseteq> C"
proof-
  have "y \<in> connected_component G x"
  proof(rule has_path_in_connected_component)
    show "walk_betw G x [x, y] y" 
      apply(rule nonempty_path_walk_between)
      using assms
      by auto
  qed
  moreover have "x \<in> Vs G" using assms
    by (auto dest: edges_are_Vs)
  ultimately show ?thesis
    unfolding connected_components_def
    using in_own_connected_component
    by fastforce
qed

lemma edge_in_unique_component:
  "{x,y} \<in> G \<Longrightarrow> \<exists>!C. C \<in> connected_components G \<and> {x,y} \<subseteq> C"
  by(force dest: connected_components_closed' edge_in_component )

lemma connected_component_set:
  "\<lbrakk>u \<in> Vs G; \<And>x. x \<in> C \<Longrightarrow> reachable G u x; \<And>x. reachable G u x \<Longrightarrow> x \<in> C\<rbrakk> \<Longrightarrow> connected_component G u = C"
  by (auto elim: in_connected_componentE intro: in_connected_componentI dest: reachable_refl)

text\<open>
  Now we should be able to partition the set of edges into equivalence classes
  corresponding to the connected components.\<close>

definition component_edges where
"component_edges G C = {{x, y} | x y.  {x, y} \<subseteq> C \<and> {x, y} \<in> G}"

lemma component_edges_disj_edges:
  assumes "C \<in> connected_components G" "C' \<in> connected_components G" "C \<noteq> C'"
  assumes "v \<in> component_edges G C" "w \<in> component_edges G C'"
  shows "v \<inter> w = {}"
proof(intro equals0I)
  fix x assume "x \<in> v \<inter> w"
  hence "x \<in> C" "x \<in> C'" using assms(4, 5) unfolding component_edges_def by blast+
  thus False
    using assms(1-3)
    by(auto dest: connected_components_closed')
qed

lemma component_edges_disj:
  assumes "C \<in> connected_components G" "C' \<in> connected_components G" "C \<noteq> C'"
  shows "component_edges G C \<inter> component_edges G C' = {}"
proof(intro equals0I, goal_cases)
  case (1 y)
  hence "y = {}"
    apply(subst Int_absorb[symmetric])
    apply(intro component_edges_disj_edges)
    using assms  
    by auto

  thus False using 1 unfolding component_edges_def by blast
qed

lemma reachable_in_Vs:
  assumes "reachable G u v"
  shows "u \<in> Vs G" "v \<in> Vs G"
  using assms
  by(auto dest: reachableD)

lemma connected_component_subs_Vs:
  "C \<in> connected_components G \<Longrightarrow> C \<subseteq> Vs G"
  by (auto simp: dest: reachable_in_Vs(2) elim: in_connected_componentE C_is_componentE)

definition components_edges where
"components_edges G = {component_edges G C| C. C \<in> connected_components G}"

lemma connected_comp_nempty:
  "C \<in> connected_components G \<Longrightarrow> C \<noteq> {}"
  using in_own_connected_component
  by (fastforce simp: connected_components_def)

lemma connected_comp_verts_in_verts:
  "\<lbrakk>v \<in> C; C \<in> connected_components G\<rbrakk> \<Longrightarrow> v \<in> Vs G"
  using connected_component_subs_Vs
  by blast

(* TODO replace  everywhere with C_componentE*)

lemma connected_comp_has_vert:
  assumes "C \<in> connected_components G"
  obtains w where "w \<in> Vs G" "C = connected_component G w"
  using C_is_componentE[OF assms]
  .

lemma component_edges_partition:
  shows "\<Union> (components_edges G) = G \<inter> {{x,y}| x y. True}"
  unfolding components_edges_def
proof(safe)
  fix x y
  assume "{x, y} \<in> G"
  then obtain C where "{x, y} \<subseteq> C" "C \<in> connected_components G"
    by (auto elim!: exE[OF edge_in_component])
  moreover then have "{x, y} \<in> component_edges G C"
    using \<open>{x, y} \<in> G\<close> component_edges_def
    by fastforce
  ultimately show "{x, y} \<in> \<Union> {component_edges G C |C. C \<in> connected_components G}"
    by blast
qed (auto simp add: component_edges_def)

(*
  The edges in that bigger equivalence class can be ordered in a path, since the degree of any
  vertex cannot exceed 2. Also that path should start and end with edges from the bigger matching.
*)

subsection\<open>Every connected component can be linearised in a path.\<close>

lemma path_subset_conn_comp:
  assumes "path G p"
  shows "set p \<subseteq> connected_component G (hd p)"
  using assms
proof(induction)
  case path0
  then show ?case by simp
next
  case path1
  then show ?case using in_own_connected_component by simp
next
  case (path2 v v' vs)
  hence "walk_betw G v' [v',v] v"
    by (simp add: edges_are_walks insert_commute)
  hence "v \<in> connected_component G v'"
    by (auto dest:has_path_in_connected_component) 
  moreover hence "connected_component G v = connected_component G v'"
    by (simp add: connected_components_member_eq)
  ultimately show ?case using path2.IH by fastforce
qed

lemma walk_betw_subset_conn_comp:
  "walk_betw G u p v \<Longrightarrow> set p \<subseteq> connected_component G u"
  using path_subset_conn_comp
  by (auto simp: walk_betw_def)

lemma path_in_connected_component:
  "\<lbrakk>path G p; hd p \<in> connected_component G x\<rbrakk> \<Longrightarrow> set p \<subseteq> connected_component G x"
  by (fastforce dest: path_subset_conn_comp simp: connected_components_member_eq)

lemma component_has_path:
  assumes "finite C'" "C' \<subseteq> C" "C \<in> connected_components G"
  shows "\<exists>p. path G p \<and> C' \<subseteq> (set p) \<and> (set p) \<subseteq> C"
  using assms
proof(induction C')
  case empty thus ?case
    using path0 by fastforce
next
  case ass: (insert x F)
  then obtain p where p: "path G p" "F \<subseteq> set p" "set p \<subseteq> C"
    by auto
  have "x \<in> C" using ass.prems(1) by blast
  hence C_def: "C = connected_component G x"
    by (simp add: assms(3) connected_components_closed')

  show ?case
  proof(cases "p = []")
    case True
    have "path G [x]" using ass connected_comp_verts_in_verts by force
    then show ?thesis using True p ass.prems(1) by fastforce
  next
    case F1: False
    then obtain h t where "p = h # t" using list.exhaust_sel by blast
    hence walkhp: "walk_betw G h p (last p)" using p(1) walk_betw_def by fastforce

    have "h \<in> C" using \<open>p = h # t\<close> p(3) by fastforce
    moreover have "x \<in> Vs G"
      using \<open>x \<in> C\<close> assms(3) connected_component_subs_Vs
      by auto
    ultimately obtain q where walkxh: "walk_betw G x q h"
      by (auto simp: C_def elim: in_connected_component_has_walk)
    hence walkxp: "walk_betw G x (q @ tl p) (last p)"
      by (simp add: walk_transitive walkhp)
    moreover hence "set (q @ tl p) \<subseteq> C"
      by(auto simp: C_def dest!: walk_betw_subset_conn_comp)
    moreover from walkxp have "path G (q @ tl p)"
      by (fastforce dest: walk_between_nonempty_pathD)
    moreover {
      from walkxh have "last q = h" "hd q = x" by (fastforce dest: walk_between_nonempty_pathD)+
      then have "insert x F \<subseteq> set (q @ tl p)" using \<open>p = h # t\<close> walkxh p(2) by fastforce
    }
    ultimately show ?thesis by blast
  qed
qed

lemma component_has_path':
  "\<lbrakk>finite C; C \<in> connected_components G\<rbrakk> \<Longrightarrow> \<exists>p. path G p \<and> C = (set p)"
  using component_has_path
  by fastforce

subsection\<open>Every connected component can be linearised in a simple path\<close>

text\<open>An important part of this proof is setting up and induction on the graph, i.e. on a set of
     edges, and the different cases that could arise.\<close>

lemma in_edges_of_path':
  "\<lbrakk> v \<in> set p; length p \<ge> 2\<rbrakk> \<Longrightarrow> v \<in> Vs (set (edges_of_path p))"
  by(auto dest: path_vertex_has_edge simp: Vs_def)

lemma in_edges_of_path:
  assumes "v \<in> set p" "v \<noteq> hd p"
  shows "v \<in> Vs (set (edges_of_path p))"
proof-
  have "length p \<ge> 2" using assms 
    by(cases p, auto dest!: length_pos_if_in_set simp: neq_Nil_conv)
  thus ?thesis by (simp add: assms(1) in_edges_of_path')
qed

lemma degree_edges_of_path_hd:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (hd p) = 1"
proof-
  obtain h nxt rest where p_def: "p = h # nxt # rest" using assms(2)
    by (auto simp: Suc_le_length_iff eval_nat_numeral)
  have calc: "{e. hd (h # nxt # rest) \<in> e} \<inter> set (edges_of_path (h # nxt # rest)) = {{h, nxt}}"
  proof(standard; standard)
    fix e assume "e \<in> {e. hd (h # nxt # rest) \<in> e} \<inter> set (edges_of_path (h # nxt # rest))"
    hence "e = {h, nxt} \<or> e \<in> set (edges_of_path (nxt # rest))" "h \<in> e" by fastforce+
    hence "e = {h, nxt}" using assms(1) v_in_edge_in_path_gen unfolding p_def by fastforce
    then show "e \<in> {{h, nxt}}" by simp
  qed simp
  show ?thesis unfolding p_def degree_def calc by (simp add: one_enat_def)
qed

lemma degree_edges_of_path_last:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (last p) = 1"
proof-
  have "distinct (rev p)" using assms(1) by simp
  moreover have "length (rev p) \<ge> 2" using assms(2) by simp
  ultimately have "degree (set (edges_of_path (rev p))) (hd (rev p)) = 1"
    using degree_edges_of_path_hd by blast
  then show ?thesis
    by(simp add: edges_of_path_rev[symmetric] hd_rev)
qed

lemma degree_edges_of_path_ge_2:
  assumes "distinct p" "v\<in>set p" "v \<noteq> hd p" "v \<noteq> last p"
  shows "degree (set (edges_of_path p)) v = 2"
  using assms
proof(induction p arbitrary: v rule: induct_list012)
  case nil then show ?case by simp
next
  case single then show ?case by simp
next
  case Cons: (sucsuc a a' p v)
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
        unfolding degree_def p by (simp add: eval_enat_numeral one_enat_def)
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

lemma in_Vs_insertE:
  "v \<in> Vs (insert e G) \<Longrightarrow> (v \<in> e \<Longrightarrow> P) \<Longrightarrow> (v \<in> Vs G \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Vs_def)

lemma list_sing_conv:
  "([x] = ys @ [y]) \<longleftrightarrow> (ys = [] \<and> y = x)"
  "([x] = y#ys) \<longleftrightarrow> (ys = [] \<and> y = x)"
  by (induction ys) auto

lemma path_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>path (insert e G) p; 
     (p = [] \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> e \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs G \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path {e} [v1, v2]; path (insert e G) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path G [v1,v2]; path (insert e G) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P )\<rbrakk>
    \<Longrightarrow> P"
proof(induction rule: path.induct)
  case path0
  then show ?case 
    by auto
next
  case (path1 v)
  then show ?case
    by (auto elim!: in_Vs_insertE)
next
  case (path2 v v' vs)
  then show ?case
    apply (auto simp: vs_member)
    by blast
qed

text \<open>A lemma which allows for case splitting over paths when doing induction on graph edges.\<close>

lemma welk_betw_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>walk_betw (insert e G) v1 p v2; 
     (\<lbrakk>v1\<in>Vs (insert e G); v1 = v2; p = []\<rbrakk> \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> e \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs G \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw {e} v1 [v1,v3] v3; walk_betw (insert e G) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw G v1 [v1,v3] v3; walk_betw (insert e G) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding walk_betw_def
  apply safe
  apply(erule path_insertE)
  by (simp | force)+

lemma reachable_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>reachable (insert e G) v1 v2;
     (\<lbrakk>v1 \<in> e; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<lbrakk>v1 \<in> Vs G; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable {e} v1 v3; reachable (insert e G) v3 v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable G v1 v3; reachable (insert e G) v3 v2\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding reachable_def
  apply(erule exE)
  apply(erule welk_betw_insertE)
  by (force simp: Vs_def)+

lemma in_Vs_unionE:
  "v \<in> Vs (G1 \<union> G2) \<Longrightarrow> (v \<in> Vs G1 \<Longrightarrow> P) \<Longrightarrow> (v \<in> Vs G2 \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Vs_def)

lemma path_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>path (G1 \<union> G2) p; 
     (p = [] \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs G1 \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs G2 \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path G1 [v1, v2]; path (G1 \<union> G2) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path G2 [v1,v2]; path (G1 \<union> G2) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P )\<rbrakk>
    \<Longrightarrow> P"
proof(induction rule: path.induct)
  case path0
  then show ?case 
    by auto
next
  case (path1 v)
  then show ?case
    by (auto elim!: in_Vs_unionE)
next
  case (path2 v v' vs)
  then show ?case
    by (simp add: vs_member) blast+
qed

lemma welk_betw_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>walk_betw (G1 \<union> G2) v1 p v2; 
     (\<lbrakk>v1\<in>Vs (G1 \<union> G2); v1 = v2; p = []\<rbrakk> \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs G1 \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs G2 \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw G1 v1 [v1,v3] v3; walk_betw (G1 \<union> G2) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw G2 v1 [v1,v3] v3; walk_betw (G1 \<union> G2) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding walk_betw_def
  apply safe
  apply(erule path_unionE)
  by (simp | force)+

lemma reachable_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>reachable (G1 \<union> G2) v1 v2;
     (\<lbrakk>v1 \<in> Vs G2; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<lbrakk>v1 \<in> Vs G1; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable G1 v1 v3; reachable (G1 \<union> G2) v3 v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable G2 v1 v3; reachable (G1 \<union> G2) v3 v2\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding reachable_def
  apply(erule exE)
  apply(erule welk_betw_unionE)
  by (force simp: Vs_def)+

lemma singleton_subset: "path {e} p \<Longrightarrow> set p \<subseteq> e"
  by (induction rule: path.induct) (auto simp: Vs_def)

lemma path_singletonD: 
  "path {{v1::'a,v2}} p \<Longrightarrow> p \<noteq> [] \<Longrightarrow> (hd p = v1 \<or> hd p = v2) \<and> (last p = v1 \<or> last p = v2)"
  by (induction rule: path.induct) (auto simp: Vs_def)

lemma walk_betw_repl_edge:
  assumes "path (insert {w, x} G) p" "p \<noteq> []" "walk_betw G w puv x"
  shows "\<exists>p'. walk_betw G (hd p) p' (last p)"
  using assms
proof(induction rule: induct_list012)
  case nil
  then show ?case
    by auto
next
  case (single x)
  then show ?case
    using walk_reflexive
    by (fastforce elim!: in_Vs_insertE dest: walk_endpoints)+
next
  case (sucsuc x y zs)
  then show ?case
    apply -
  proof(erule path_insertE, goal_cases)
    case (4 p' v1 v2)
    then show ?case
      using walk_symmetric walk_transitive
      by(fastforce simp del: path_simps dest!: path_singletonD)
  next
    case (5 p' v1 v2)
    then show ?case
      using walk_transitive
      by (fastforce simp del: path_simps elim!: nonempty_path_walk_betweenE)
  qed auto
qed

lemma in_connected_componentI3:
  "\<lbrakk>C \<in> connected_components G; w \<in> C; x \<in> C\<rbrakk> \<Longrightarrow> x \<in> connected_component G w"
  using connected_components_closed'
  by fastforce

lemma same_con_comp_reachable:
  "\<lbrakk>C \<in> connected_components G; w \<in> C; x \<in> C\<rbrakk> \<Longrightarrow> reachable G w x"
  using in_connected_componentI3
  by(fastforce intro: reachable_refl connected_comp_verts_in_verts elim: in_connected_componentE)

lemma same_con_comp_walk:
  assumes "C \<in> connected_components G" "w \<in> C" "x \<in> C"
  obtains pwx where "walk_betw G w pwx x"
proof-
  have "x \<in> connected_component G w" 
    using assms
    by (rule in_connected_componentI3)
  thus ?thesis
    using connected_comp_verts_in_verts[OF \<open>w \<in> C\<close> \<open>C \<in> connected_components G\<close>]
    by (auto elim: that in_connected_component_has_walk)
qed                             

lemma in_connected_componentI4:
  assumes "walk_betw G u puv v" "u \<in> C" "C \<in> connected_components G"
  shows "v \<in> C"
  using assms connected_components_closed'
  by (fastforce intro: has_path_in_connected_component)

lemma walk_betw_singletonD:
  "walk_betw {{v1::'a,v2}} u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> (hd p = v1 \<or> hd p = v2) \<and> (last p = v1 \<or> last p = v2) \<and> hd p = u \<and> last p = v"
  by (fastforce simp: walk_betw_def dest: path_singletonD)

(*TODO rename: path_can_be_split \<rightarrow> walk_can_be_split *)

lemma vwalk_betw_can_be_split:
  assumes "walk_betw (insert {w, x} G) u p v" "w \<in> Vs G" "x \<in> Vs G"
  shows "(\<exists>p. walk_betw G u p v) \<or>
         (\<exists>p1 p2. walk_betw G u p1 w \<and> walk_betw G x p2 v) \<or>
         (\<exists>p1 p2. walk_betw G u p1 x \<and> walk_betw G w p2 v)"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule welk_betw_insertE, goal_cases)
    case (4 p' v3)
    (*TODO: Lukas*)
      then show ?case
      apply simp
      using walk_between_nonempty_pathD(4)[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
            walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (auto dest: walk_reflexive)
  next
    case (5 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw G u [u, v3] v3\<close>]
      by blast
  qed (insert walk_reflexive, fastforce)+
qed

lemma reachability_split:
  "\<lbrakk>reachable (insert {w, x} G) u v; w \<in> Vs G; x \<in> Vs G\<rbrakk> \<Longrightarrow>
        (reachable G u v) \<or>
         (reachable G u w \<and> reachable G x v) \<or>
         (reachable G u x \<and> reachable G w v)"
  by(auto simp: reachable_def dest: vwalk_betw_can_be_split)

lemma connected_component_in_components:
  "v \<in> Vs G \<Longrightarrow> connected_component G v \<in> connected_components G"
  by (fastforce simp: connected_components_def)

lemma reachable_subset:
  "\<lbrakk>reachable G u v; G \<subseteq> G'\<rbrakk> \<Longrightarrow> reachable G' u v"
  by (auto dest: walk_subset intro: reachableI elim!: reachableE)

lemma in_Vs_insert: "x \<in> Vs G \<Longrightarrow> x \<in> Vs (insert e G)"
  by (auto simp: Vs_def)
  
lemma vwalk_betw_can_be_split_2:
  assumes "walk_betw (insert {w, x} G) u p v" "w \<in> Vs G" "x \<notin> Vs G"
  shows "(\<exists>p'. walk_betw G u p' v) \<or>
         (\<exists>p'. walk_betw G u p' w \<and> v = x) \<or>
         (\<exists>p'. walk_betw G w p' v \<and> u = x) \<or>
         (u = x \<and> v = x)"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule welk_betw_insertE, goal_cases)
    case (4 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (auto dest: walk_endpoints(1) walk_reflexive)
  next
    case (5 p' v3)
    then show ?case
     (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw G u [u, v3] v3\<close>] walk_endpoints(2)
      by (metis list.sel(3))
  qed (auto dest: walk_reflexive)+
qed

lemma reachability_split_2:
  "\<lbrakk>reachable (insert {w, x} G) u v; w \<in> Vs G; x \<notin> Vs G\<rbrakk> \<Longrightarrow>
     (reachable G u v) \<or>
     (reachable G u w \<and> v = x) \<or>
     (reachable G w v \<and> u = x) \<or>
     (u = x \<and> v = x)"
  by(auto simp: reachable_def dest: vwalk_betw_can_be_split_2)

lemma walk_betw_cons:
  "walk_betw G v1 (v2 # v3 # p) v4 \<longleftrightarrow> 
    (walk_betw G v3 (v3 # p) v4 \<and> walk_betw G v1 [v2, v3] v3)"
  by(auto simp: walk_betw_def)

lemma vwalk_betw_can_be_split_3:
  assumes "walk_betw (insert {w, x} G) u p v" "w \<notin> Vs G" "x \<notin> Vs G"
  shows "walk_betw G u p v \<or> walk_betw {{w, x}} u p v"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule welk_betw_insertE, goal_cases)
    case (4 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (simp, metis walk_betw_cons walk_endpoints(1))
  next
    case (5 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw G u [u, v3] v3\<close>] walk_betw_singletonD
      by fastforce
  qed (auto simp add: Vs_def walk_reflexive)
qed

lemma walk_in_edges_of_path:"walk_betw A v p w \<Longrightarrow> 2 \<le> length p \<Longrightarrow>
 walk_betw (set (edges_of_path p)) v p w"
 proof(induction v p w rule: induct_walk_betw)
            case (path2 v v' vs b)
            show ?case
            proof(cases vs)
              case Nil
              hence b'_is_v:"b = v'" 
                using path2.hyps(2) walk_between_nonempty_pathD(4) by force
              show ?thesis
                by (simp add: b'_is_v edges_are_walks local.Nil)
            next
              case (Cons a list)
              hence elngth: "length ( v' # vs) \<ge> 2" by auto
              show ?thesis 
              by(subst walk_betw_cons)
                (auto intro: walk_subset[OF path2(3)[OF elngth]] walk_subset[of "{{v, v'}}"] 
                      simp add: edges_are_walks )
          qed
        qed auto

lemma walk_betw_strengthen:"walk_betw G u p v \<Longrightarrow> length p \<ge> 2 \<Longrightarrow> set (edges_of_path p) \<subseteq> G' \<Longrightarrow> walk_betw G' u p v"
proof(induction  u p v rule: induct_walk_betw)
  case (path1 v)
  then show ?case by auto
next
  case (path2 v v' vs b)
  hence helper: " vs = Nil \<Longrightarrow> v' = b"  
    by (metis last_ConsL walk_betw_def)
  show ?case 
  proof(cases vs)
    case Nil
    then show ?thesis
      using path2(5) by (auto intro!:  edges_are_walks simp add: helper)
  next
    case (Cons a list)
    have "walk_betw G' v' (v' # vs) b"
      using local.Cons path2.IH path2.prems(2) by auto
    moreover have "walk_betw G' v [v, v'] v'" 
      using edges_are_walks path2.prems(2) by force
    ultimately show ?thesis 
      by (meson walk_betw_cons)
  qed
qed

lemma reachability_split3:
  "\<lbrakk>reachable (insert {w, x} G) u v; w \<notin> Vs G; x \<notin> Vs G\<rbrakk> \<Longrightarrow> 
  reachable G u v \<or> reachable {{w, x}} u v"
  by(auto simp: reachable_def dest: vwalk_betw_can_be_split_3)

lemma unchanged_connected_component:
  assumes "u \<notin> C" "v \<notin> C" 
  shows "C \<in> connected_components G \<longleftrightarrow> C \<in> connected_components (insert {u, v} G)"
proof-

  text \<open>This is to cover two symmetric cases\<close>
  have unchanged_con_comp_2:
    "C \<in> connected_components G \<longleftrightarrow> C \<in> connected_components (insert {u, v} G)"
    if "u \<notin> C" "v \<notin> C" "u \<in> Vs G" "v \<notin> Vs G"
    for u v
  proof-
    note assms = that
    show ?thesis
    proof(rule iffI, goal_cases)
      case 1
      then obtain v' where *: "C = connected_component G v'" "v' \<in> Vs G"
        by (rule C_is_componentE)
      hence "v' \<in> Vs (insert {u, v} G)"
        by(simp add: Vs_def)
      moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} G) v' x"for x
        using *
        by (auto intro: in_Vs_insert reachable_refl dest: reachable_subset elim!: in_connected_componentE)
      moreover have "reachable (insert {u, v} G) v' x \<Longrightarrow> x \<in> C" for x
        using * assms
        by (auto dest: reachability_split_2 intro!: in_connected_componentI)
      ultimately have "connected_component (insert {u,v} G) v' = C"
        by (rule connected_component_set)
      then show ?case
        using \<open>v' \<in> Vs (insert {u, v} G)\<close> connected_component_in_components
        by auto
    next
      case 2
      then obtain v' where *: "C = connected_component (insert {u, v} G) v'" "v' \<in> Vs (insert {u, v} G)"
        by (rule C_is_componentE)
      hence "v' \<in> Vs G"
        using assms in_own_connected_component
        by (fastforce elim: in_Vs_insertE)
      moreover have "reachable (insert {u, v} G) v' x \<Longrightarrow> reachable G v' x" for x
        using *(1) assms \<open>v' \<in> Vs G\<close>
        by (auto dest: in_connected_componentI reachable_subset reachability_split_2) 
      hence "x \<in> C \<Longrightarrow> reachable G v' x" for x
        using *
        by (auto simp: reachable_refl elim: in_connected_componentE)
      moreover have "reachable G v' x \<Longrightarrow> x \<in> C" for x
        using *
        by (auto simp: reachable_refl dest: reachable_subset intro: in_connected_componentI)
      ultimately have "connected_component G v' = C"
        by (rule connected_component_set)
      then show ?case
        using \<open>v' \<in> Vs G\<close> connected_component_in_components
        by auto
    qed
  qed

  show ?thesis
  proof(cases \<open>u \<in> Vs G\<close>)
    assume "u \<in> Vs G"
    then show ?thesis
    proof(cases \<open>v \<in> Vs G\<close>)
      assume "v \<in> Vs G"
      note assms = assms \<open>u \<in> Vs G\<close> \<open>v \<in> Vs G\<close>
      show ?thesis
      proof(rule iffI, goal_cases)
        case 1
        then obtain v' where *: "C = connected_component G v'" "v' \<in> Vs G"
          by (rule C_is_componentE)
        hence "v' \<in> Vs (insert {u, v} G)"
          by(simp add: Vs_def)
        moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} G) v' x"for x
          using * 
          by (auto intro: in_Vs_insert reachable_refl dest: reachable_subset
              elim!: in_connected_componentE)
        moreover have "reachable (insert {u, v} G) v' x \<Longrightarrow> x \<in> C" for x
          using *(1) assms
          by (auto dest: reachability_split intro!: in_connected_componentI)
        ultimately have "connected_component (insert {u,v} G) v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs (insert {u, v} G)\<close> connected_component_in_components
          by auto
      next
        case 2
        then obtain v' where *: "C = connected_component (insert {u, v} G) v'"
                                "v' \<in> Vs (insert {u, v} G)"
          by (rule C_is_componentE)
        hence "v' \<in> Vs G"
          using assms
          by (auto elim: in_Vs_insertE)
        moreover have "x \<in> C \<Longrightarrow> reachable G v' x" for x    
          using assms \<open>v' \<in> Vs G\<close>
          by (auto simp: *(1) elim!: in_connected_componentE 
              dest!: reachability_split dest: in_connected_componentI reachable_subset
              intro: reachable_refl)
        moreover have "reachable G v' x \<Longrightarrow> x \<in> C" for x
          using *
          by (auto dest: reachable_subset in_connected_componentI)
        ultimately have "connected_component G v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs G\<close> connected_component_in_components
          by auto
      qed

    next
      assume "v \<notin> Vs G"
      show ?thesis
        using unchanged_con_comp_2[OF assms \<open>u \<in> Vs G\<close> \<open>v \<notin> Vs G\<close>]
        .
    qed
  next
    assume "u \<notin> Vs G"
    then show ?thesis
    proof(cases \<open>v \<in> Vs G\<close>)
      assume "v \<in> Vs G"
      show ?thesis
        using unchanged_con_comp_2[OF assms(2,1) \<open>v \<in> Vs G\<close> \<open>u \<notin> Vs G\<close>]
        by (subst insert_commute)
    next
      assume "v \<notin> Vs G"
      note assms = assms \<open>u \<notin> Vs G\<close> \<open>v \<notin> Vs G\<close>
      show ?thesis
      proof(rule iffI, goal_cases)
        case 1
        then obtain v' where *: "C = connected_component G v'" "v' \<in> Vs G"
          by (rule C_is_componentE)
        hence "v' \<in> Vs (insert {u, v} G)"
          by(simp add: Vs_def)
        moreover have "x \<in> C \<Longrightarrow> reachable (insert {u, v} G) v' x"for x
          using *
          by (auto intro: reachable_refl in_Vs_insert dest: reachable_subset elim!: in_connected_componentE)
        moreover have "x \<in> C" if "reachable (insert {u, v} G) v' x" for x
        proof-
          have "\<not> reachable {{u, v}} v' x"
            using * assms \<open>u \<notin> Vs G\<close> \<open>v \<notin> Vs G\<close>
            by (auto dest: reachable_in_Vs(1) elim: vs_member_elim)
          thus ?thesis                                     
            using * that assms
            by (fastforce dest!: reachability_split3 simp add: in_connected_componentI)
        qed
        ultimately have "connected_component (insert {u,v} G) v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs (insert {u, v} G)\<close> connected_component_in_components
          by auto
      next
        case 2
        then obtain v' where *: "C = connected_component (insert {u, v} G) v'" "v' \<in> Vs (insert {u, v} G)"
          by (rule C_is_componentE)
        hence "v' \<in> Vs G"
          using assms in_own_connected_component
          by (force elim!: in_Vs_insertE)
        moreover have "reachable G v' x" if "reachable (insert {u, v} G) v' x" for x
        proof-
          have "\<not> reachable {{u, v}} v' x"
            using \<open>v' \<in> Vs G\<close> assms
            by (auto dest: reachable_in_Vs(1) elim: vs_member_elim)
          thus ?thesis
            using * assms that
            by (auto dest: reachability_split3)
        qed
        hence "x \<in> C \<Longrightarrow> reachable G v' x" for x
          using *
          by (auto simp: *(1) reachable_refl elim!: in_connected_componentE)
        moreover have "reachable G v' x \<Longrightarrow> x \<in> C" for x
          using *
          by (auto dest: reachable_subset in_connected_componentI)
        ultimately have "connected_component G v' = C"
          by (rule connected_component_set)
        then show ?case
          using \<open>v' \<in> Vs G\<close> connected_component_in_components
          by auto
      qed
    qed
  qed
qed

(*TODO rename connected_components_insert *)

lemma connected_components_union:
  assumes "Cu \<in> connected_components G" "Cv \<in> connected_components G"
  assumes "u \<in> Cu" "v \<in> Cv"
  shows "Cu \<union> Cv \<in> connected_components (insert {u, v} G)"
proof-
  have "u \<in> Vs (insert {u, v} G)" using assms(1) by (simp add: Vs_def)
  have "v \<in> Vs (insert {u, v} G)" using assms(1) by (simp add: Vs_def)

  have "reachable (insert {u, v} G) v x" if x_mem: "x \<in> Cu \<union> Cv" for x
  proof-
    have "reachable G u x \<or> reachable G v x"
      using x_mem assms
      by (auto dest: same_con_comp_reachable)
    then have "reachable (insert {u, v} G) u x \<or> reachable (insert {u, v} G) v x"
      by (auto dest: reachable_subset)
    thus ?thesis
      using edges_reachable[where G = "insert {u,v} G"]
      by (auto dest: reachable_trans)
  qed

  moreover note * = connected_comp_verts_in_verts[OF \<open>u \<in> Cu\<close> \<open>Cu \<in> connected_components G\<close>]
          connected_comp_verts_in_verts[OF \<open>v \<in> Cv\<close> \<open>Cv \<in> connected_components G\<close>]
  hence "reachable (insert {u, v} G) v x \<Longrightarrow> x \<in> Cu \<union> Cv" for x
    by(auto dest: in_connected_componentI reachability_split
            simp: connected_components_closed'[OF \<open>u \<in> Cu\<close> \<open>Cu \<in> connected_components G\<close>]
                  connected_components_closed'[OF \<open>v \<in> Cv\<close> \<open>Cv \<in> connected_components G\<close>])

  ultimately have "Cu \<union> Cv = connected_component (insert {u, v} G) v"
    apply(intro connected_component_set[symmetric])
    by(auto intro: in_Vs_insert)
  thus ?thesis
    using \<open>v \<in> Vs (insert {u, v} G)\<close> 
    by(auto intro: connected_component_in_components)
qed

lemma connected_components_insert_2:
  assumes "Cu \<in> connected_components G" "Cv \<in> connected_components G"
  assumes "u \<in> Cu" "v \<in> Cv"
  shows "connected_components (insert {u, v} G) = 
           insert (Cu \<union> Cv) ((connected_components G) - {Cu, Cv})"
proof-
  have Cuvins: "Cu \<union> Cv \<in> connected_components (insert {u, v} G)"
    by (simp add: assms connected_components_union)
  have "C \<in> connected_components (insert {u, v} G)" 
    if in_comps: "C \<in> insert (Cu \<union> Cv) (connected_components G - {Cu, Cv})" for C
  proof-
    consider (Cuv) "C = (Cu \<union> Cv)" | (other) "C \<in> connected_components G" "C \<noteq> Cu" "C \<noteq> Cv"
      using in_comps
      by blast
    thus ?thesis
    proof cases
      case other
      then show ?thesis
        using assms
        apply(subst unchanged_connected_component[symmetric])
        by (auto dest: connected_components_closed'[where C = C]
            connected_components_closed'[where C = Cu]
            connected_components_closed'[where C = Cv])
    qed (simp add: Cuvins)
  qed
  moreover have "C \<in> insert (Cu \<union> Cv) ((connected_components G) - {Cu, Cv})"
    if in_comps: "C \<in> connected_components (insert {u, v} G)" for C
  proof-
    have "u \<in> C \<or> v \<in> C \<Longrightarrow> C = Cu \<union> Cv"
      using Cuvins in_comps connected_components_closed'[where C = C] \<open>u \<in> Cu\<close> \<open>v \<in> Cv\<close>
            connected_components_closed'[where C = "Cu \<union> Cv"]
      by blast
    moreover have "C \<in> connected_components G" if "u \<notin> C"
    proof(cases \<open>v \<in> C\<close>)
      case True
      then show ?thesis
        using in_comps \<open>u \<in> Cu\<close> calculation that
        by auto
    next
      case False
      then show ?thesis
        apply(subst unchanged_connected_component[where u = u and v = v])
        using that in_comps
        by auto
    qed
    ultimately show ?thesis
      using assms(3, 4) by blast
  qed
  ultimately show ?thesis
    by auto

qed

lemma connected_components_insert_1:
  assumes "C \<in> connected_components G" "u \<in> C" "v \<in> C"
  shows "connected_components (insert {u, v} G) = connected_components G"
  using assms connected_components_insert_2 by fastforce

lemma in_connected_component_in_edges: "v \<in> connected_component G u \<Longrightarrow> v \<in> Vs G \<or> u = v"
  by(auto simp: connected_component_def Vs_def dest: walk_endpoints(2) elim!: reachableE vs_member_elim)

lemma in_con_comp_has_walk: assumes "v \<in> connected_component G u" "v \<noteq> u"
  obtains p where "walk_betw G u p v"
  using assms
  by(auto simp: connected_component_def elim!: reachableE)

find_theorems "(\<subseteq>)" reachable

lemma con_comp_subset: "G1 \<subseteq> G2 \<Longrightarrow> connected_component G1 u \<subseteq> connected_component G2 u"
  by (auto dest: reachable_subset simp: connected_component_def)

lemma in_con_comp_insert: "v \<in> connected_component (insert {u, v} G) u"
  using edges_are_walks[OF insertI1]
  by (force simp add: connected_component_def reachable_def)

lemma connected_components_insert:
  assumes "C \<in> connected_components G" "u \<in> C" "v \<notin> Vs G"
  shows "insert v C \<in> connected_components (insert {u, v} G)"
proof-
  have "u \<in> Vs (insert {u, v} G)" by (simp add: Vs_def)
  moreover have "connected_component (insert {u, v} G) u = insert v C"
  proof(standard, goal_cases)
    case 1
    thus ?case
      using assms
      by (fastforce elim: in_con_comp_has_walk dest!: vwalk_betw_can_be_split_2
                    simp add: in_connected_componentI4 connected_comp_verts_in_verts)
  next
    case 2
    have "C = connected_component G u"
      by (simp add: assms connected_components_closed')
    then show ?case
      by(auto intro!: insert_subsetI con_comp_subset[simplified]
              simp add: in_con_comp_insert)
  qed
  ultimately show ?thesis 
    using connected_components_closed' 
    by (fastforce dest: own_connected_component_unique)
qed

lemma connected_components_insert_3:
  assumes "C \<in> connected_components G" "u \<in> C" "v \<notin> Vs G"
  shows "connected_components (insert {u, v} G) = insert (insert v C) (connected_components G - {C})"
proof-
  have un_con_comp: "insert v C \<in> connected_components (insert {u, v} G)"
    by (simp add: assms connected_components_insert)
  have "D \<in> connected_components (insert {u, v} G)" 
    if "D \<in> insert (insert v C) (connected_components G - {C})"
    for D
  proof-
    from that consider (ins) "D = insert v C" | (other) "D \<in> connected_components G" "D \<noteq> C"
      by blast
    thus ?thesis
    proof cases
      case other
      moreover hence "v \<notin> D"
        using assms
        by (auto intro: connected_comp_verts_in_verts) 
      moreover have "u \<notin> D"
        using other assms 
        by (auto dest: connected_components_closed') 
      ultimately show ?thesis
        by(auto dest: unchanged_connected_component)
    qed (simp add: un_con_comp)
  qed
  moreover have "D \<in> insert (insert v C) (connected_components G - {C})"
    if "D \<in> connected_components (insert {u, v} G)"
    for D
  proof-
    have "u \<in> D \<longleftrightarrow> D = insert v C"
      using that assms(2) un_con_comp
      by (fastforce dest: connected_components_closed'')
    moreover hence "u \<in> D \<longleftrightarrow> v \<in> D"
      using that un_con_comp
      by (auto dest: connected_components_eq')
    ultimately show ?thesis 
        using that assms(2)
        by (auto simp: unchanged_connected_component[symmetric])
    qed
  ultimately show ?thesis by blast
qed

lemma connected_components_insert_1':
  "\<lbrakk>u \<in> Vs G; v \<in> Vs G\<rbrakk> \<Longrightarrow> 
     connected_components (insert {u, v} G)
       = insert (connected_component G u \<union> connected_component G v)
                     ((connected_components G) - {connected_component G u, connected_component G v})"
  by (auto simp add: connected_components_insert_2 in_own_connected_component
           dest!: connected_component_in_components)

lemma connected_components_insert_2':
  "\<lbrakk>u \<in> Vs G; v \<notin> Vs G\<rbrakk> 
   \<Longrightarrow> connected_components (insert {u, v} G)
         = insert (insert v (connected_component G u)) (connected_components G - {connected_component G u})"
  by (fastforce simp add: connected_components_insert_3 in_own_connected_component
                dest!: connected_component_in_components)

(*TODO: replace with connected_components_insert_4 everywhere*)

lemma connected_components_insert_4:
  assumes "u \<notin> Vs G" "v \<notin> Vs G"
  shows "connected_components (insert {u, v} G) = insert {u, v} (connected_components G)"
proof-
  have connected_components_small:
    "{u, v} \<in> connected_components (insert {u, v} G)"
  proof-
    have "u \<in> Vs (insert {u, v} G)"
      by (simp add: Vs_def)
    moreover have "connected_component (insert {u, v} G) u = {u, v}"
    proof(intro connected_component_set, goal_cases)
      case 1
      then show ?case
        by (simp add: Vs_def)
    next
      case (2 x)
      then show ?case
        by (auto simp add: \<open>u \<in> Vs (insert {u, v} G)\<close> reachable_refl edges_reachable)
    next
      case (3 x)
      then show ?case
        using reachable_in_Vs(1)
        by (fastforce simp add: assms dest: reachability_split3 walk_betw_singletonD elim: reachableE)
    qed
    ultimately show ?thesis
      by (fastforce dest: connected_component_in_components)
  qed

  have "{u, v} \<in> connected_components (insert {u, v} G)"
    by (simp add: assms connected_components_small)
  hence "C \<in> insert {u, v} (connected_components G)"
    if "C \<in> connected_components (insert {u, v} G)"
    for C
  proof(cases "C = {u, v}")
    case False
    hence "u \<notin> C" "v \<notin> C"
      using \<open>{u, v} \<in> connected_components (insert {u, v} G)\<close> that
      by (auto dest: connected_components_eq')
    hence "C \<in> connected_components G"
      using that
      by (auto dest: unchanged_connected_component)
    thus ?thesis
      by simp
  qed simp
  moreover have "C \<in> connected_components (insert {u, v} G)"
    if "C \<in> insert {u, v} (connected_components G)"
    for C
  proof(cases "C = {u, v}")
    case True
    thus ?thesis
      by (simp add: \<open>{u, v} \<in> connected_components (insert {u, v} G)\<close>)
  next
    case False
    hence "u \<notin> C" "v \<notin> C"
      using \<open>{u, v} \<in> connected_components (insert {u, v} G)\<close> that assms
      by (force simp add: insert_commute connected_comp_verts_in_verts)+
    thus ?thesis
      using that 
      by (auto dest: unchanged_connected_component)
  qed 
  ultimately show ?thesis
    by auto
qed

lemma connected_components_insert_3':
  "\<lbrakk>u \<notin> Vs G; v \<notin> Vs G\<rbrakk>
   \<Longrightarrow> connected_components (insert {u, v} G) = insert {u, v} (connected_components G)"
  using connected_components_insert_4
  .

text \<open>Elimination rule for proving lemmas about connected components by induction on graph edges.\<close>

lemma in_insert_connected_componentE[case_names both_nin one_in two_in]:
  assumes "C \<in> connected_components (insert {u,v} G)"
    "\<lbrakk>u \<notin> Vs G; v \<notin> Vs G;
     C \<in> insert {u,v} (connected_components G)\<rbrakk>
     \<Longrightarrow> P"
    "\<And>u' v'.
     \<lbrakk>u' \<in> {u,v}; v' \<in> {u, v}; u' \<in> Vs G; v' \<notin> Vs G;
     C \<in> insert (insert v' (connected_component G u')) (connected_components G - {connected_component G u'})\<rbrakk>
     \<Longrightarrow> P"
    "\<lbrakk>u \<in> Vs G; v \<in> Vs G; connected_component G u \<noteq> connected_component G v;
     C \<in> insert (connected_component G u \<union> connected_component G v)
                     ((connected_components G) - {connected_component G u, connected_component G v})\<rbrakk>
     \<Longrightarrow> P"
    "C \<in> (connected_components G) \<Longrightarrow> P"
  shows "P"
proof(cases \<open>u \<in> Vs G\<close>)
  assume \<open>u \<in> Vs G\<close>
  show ?thesis
  proof(cases \<open>v \<in> Vs G\<close>)
    assume \<open>v \<in> Vs G\<close>
    show ?thesis
    proof(cases "connected_component G u = connected_component G v")
      assume \<open>connected_component G u = connected_component G v\<close>
      hence "connected_components (insert {u,v} G) = connected_components G"        
        using \<open>u \<in> Vs G\<close>
        by (subst connected_components_insert_1[OF connected_component_in_components])
           (auto intro!: in_own_connected_component)
      thus ?thesis
        apply -
        apply(rule assms(5))
        using assms(1)
        by simp
    next
      assume \<open>connected_component G u \<noteq> connected_component G v\<close>
      then show ?thesis
      apply(rule assms(4)[OF \<open>u \<in> Vs G\<close> \<open>v \<in> Vs G\<close>])
      using assms(1)
      apply(subst connected_components_insert_1'[OF \<open>u \<in> Vs G\<close> \<open>v \<in> Vs G\<close>, symmetric])
      .
    qed
  next
    assume \<open>v \<notin> Vs G\<close>
    show ?thesis
      apply(rule assms(3)[where u' = u and v' = v])
      using assms(1) \<open>u \<in> Vs G\<close> \<open>v \<notin> Vs G\<close>
      by (auto simp: connected_components_insert_2'[symmetric])
  qed
next
  assume \<open>u \<notin> Vs G\<close>
  show ?thesis
  proof(cases \<open>v \<in> Vs G\<close>)
    assume \<open>v \<in> Vs G\<close>
    show ?thesis
      apply(rule assms(3)[where u' = v and v' = u])
      using assms(1) \<open>u \<notin> Vs G\<close> \<open>v \<in> Vs G\<close>
      by (auto simp: connected_components_insert_2'[symmetric] insert_commute)
  next
    assume \<open>v \<notin> Vs G\<close>
    show ?thesis
      apply(rule assms(2)[OF \<open>u \<notin> Vs G\<close> \<open>v \<notin> Vs G\<close>])
      using assms(1)
      apply(subst connected_components_insert_3'[OF \<open>u \<notin> Vs G\<close> \<open>v \<notin> Vs G\<close>, symmetric])
      .
  qed
qed

lemma exists_Unique_iff: "(\<exists>!x. P x) \<longleftrightarrow> (\<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> y = x))"
  by auto

lemma degree_one_unique:
  assumes "degree G v = 1"
  shows "\<exists>!e \<in> G. v \<in> e"
  using assms
proof-
  from assms obtain e where "{e} = {e. v \<in> e} \<inter> G"
    by (fastforce simp only: degree_def elim!: card'_1_singletonE)
  thus ?thesis
    by (auto simp: exists_Unique_iff)
qed

lemma complete_path_degree_one_head_or_tail:
  assumes "path G p" "distinct p" "v \<in> set p" "degree G v = 1"
  shows "v = hd p \<or> v = last p"
proof(rule ccontr)
  assume "\<not> (v = hd p \<or> v = last p)"
  hence "v \<noteq> hd p" "v \<noteq> last p" by simp_all
  hence "degree (set (edges_of_path p)) v = 2"
    by (simp add: degree_edges_of_path_ge_2 assms(2) assms(3))
  hence "2 \<le> degree G v"
    using subset_edges_less_degree[OF path_edges_subset[OF assms(1)], where v = v]
    by presburger
  then show False
    using assms(4) not_eSuc_ilei0
    by simp
qed

(*
  The proof of the following theorem should be improved by devising an induction principle for
  edges and connected components.
*)

lemma gr_zeroI: "(x::enat) \<noteq> 0 \<Longrightarrow> 0 < x"
  by auto

lemma degree_neq_zeroI: "\<lbrakk>e \<in> G; v \<in> e\<rbrakk> \<Longrightarrow> degree G v \<noteq> 0"
  by (auto simp add: degree_def)

lemma exists_conj_elim_2_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x\<rbrakk> \<Longrightarrow> V x; \<lbrakk>\<And>x. P x \<and> Q x \<Longrightarrow> V x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x; V x\<rbrakk> \<Longrightarrow> W x; \<lbrakk>\<And>x. P x \<and> Q x \<and> V x \<Longrightarrow> W x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_1: "\<lbrakk>\<And>x. \<lbrakk>P x; Q x; V x; W x\<rbrakk> \<Longrightarrow> X x; \<lbrakk>\<And>x. P x \<and> Q x \<and> V x \<and> W x \<Longrightarrow> X x\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_2_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y\<rbrakk> \<Longrightarrow> V x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<Longrightarrow> V x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y; V x y\<rbrakk> \<Longrightarrow> W x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<and> V x y \<Longrightarrow> W x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_2: "\<lbrakk>\<And>x y. \<lbrakk>P x y; Q x y; V x y; W x y\<rbrakk> \<Longrightarrow> X x y; \<lbrakk>\<And>x y. P x y \<and> Q x y \<and> V x y \<and> W x y \<Longrightarrow> X x y\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_2_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z\<rbrakk> \<Longrightarrow> V x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<Longrightarrow> V x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_3_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z\<rbrakk> \<Longrightarrow> W x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<Longrightarrow> W x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_4_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z\<rbrakk> \<Longrightarrow> X x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<Longrightarrow> X x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_5_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z\<rbrakk> \<Longrightarrow> Y x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<Longrightarrow> Y x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_5_3': "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z\<rbrakk> \<Longrightarrow> Y x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<Longrightarrow> Y x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

lemma exists_conj_elim_6_3: "\<lbrakk>\<And>x y z. \<lbrakk>P x y z; Q x y z; V x y z; W x y z; X x y z; Y x y z\<rbrakk> \<Longrightarrow> Z x y z; \<lbrakk>\<And>x y z. P x y z \<and> Q x y z \<and> V x y z \<and> W x y z \<and> X x y z \<and> Y x y z \<Longrightarrow> Z x y z\<rbrakk> \<Longrightarrow> S\<rbrakk> \<Longrightarrow> S"
  by auto

method instsantiate_obtains =
  (match conclusion in "P" for P
     \<Rightarrow> \<open>(match premises in ass[thin]: "\<And>x. _ x \<Longrightarrow> P" \<Rightarrow> \<open>rule ass\<close>) |
         (match premises in ass[thin]: "\<And>x y. _ x y \<Longrightarrow> P" \<Rightarrow> \<open>rule ass\<close>)\<close>)

lemmas exists_conj_elims = exists_conj_elim_2_1 exists_conj_elim_3_1 exists_conj_elim_4_1
                           exists_conj_elim_2_2 exists_conj_elim_3_2 exists_conj_elim_4_2

lemma edge_mid_path:
  "path G (p1 @ [v1,v2] @ p2) \<Longrightarrow> {v1,v2} \<in> G"
  using path_suff
  by fastforce

lemma snoc_eq_iff_butlast':
  "ys = xs @ [x] \<longleftrightarrow> (ys \<noteq> [] \<and> butlast ys = xs \<and> last ys = x)"
  by fastforce

lemma neq_Nil_conv_snoc: "xs \<noteq> [] \<longleftrightarrow> (\<exists>x ys. xs = ys @ [x])"
  by (auto simp add: snoc_eq_iff_butlast')

lemma degree_2: "\<lbrakk>{u,v} \<in> G; {v,w} \<in> G; distinct [u,v]; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow>2 \<le> degree G v"
  using degree_insert[where a = "{u,v}" and G = "G - {{u,v}}"]
  using degree_insert[where a = "{v,w}" and G = "(G - {{u,v}}) - {{v,w}}"]
  by (auto simp: degree_def doubleton_eq_iff eval_enat_numeral one_eSuc split: if_splits)

lemma degree_3:
 "\<lbrakk>{u,v} \<in> G; {v,w} \<in> G; {v, x} \<in> G; distinct [u,v,w]; u \<noteq> x; v \<noteq> x; w \<noteq> x\<rbrakk> \<Longrightarrow> 3 \<le> degree G v"
  using degree_insert[where a = "{u,v}" and G = "G - {{u,v}}"]
  using degree_insert[where a = "{v,w}" and G = "(G - {{u,v}}) - {{v,w}}"]
  using degree_insert[where a = "{v,x}" and G = "((G - {{u,v}}) - {{v,w}}) - {{v, x}}"]
  by (auto simp: degree_def doubleton_eq_iff eval_enat_numeral one_eSuc split: if_splits)

lemma Hilbert_choice_singleton: "(SOME x. x \<in> {y}) = y"
  by force

lemma Hilbert_set_minus: "s - {y} \<noteq>{} \<Longrightarrow> y \<noteq> (SOME x. x \<in> s - {y})"
  by(force dest!: iffD2[OF some_in_eq])

lemma connected_components_empty: "connected_components {} = {}"
  by (auto simp: connected_components_def Vs_def)

theorem component_has_path_distinct:
  assumes "finite G" and "dblton_graph G" and
    "C \<in> connected_components G" and
    "\<And>v. v \<in> Vs G \<Longrightarrow> degree G v \<le> 2"
  shows "\<exists>p. path G p \<and> C = (set p) \<and> distinct p"
  using assms
proof(induction "G" arbitrary: C)    
  case (insert e G')
  then obtain u v where uv[simp]: "e = {u,v}" "u \<noteq> v"
    by (force elim!: exists_conj_elims simp: dblton_graph_def)
  hence "u \<in> Vs (insert e G')" "v \<in> Vs (insert e G')"
    using insert
    by (auto simp: Vs_def)
  moreover have "degree (insert e G') u \<noteq> 0" "degree (insert e G') v \<noteq> 0"
    by(fastforce simp: degree_neq_zeroI[where e = e])+
  moreover have "\<lbrakk>x \<noteq>0; x \<noteq> 1; x \<noteq> 2\<rbrakk> \<Longrightarrow> 2 < x" for x::enat
    by (fastforce simp: eval_enat_numeral one_eSuc dest!: ileI1[simplified order_le_less] dest: gr_zeroI)  
  ultimately have degree_uv:
    "degree (insert e G') u \<le> 2" "degree (insert e G') v \<le> 2"
    by (auto simp: linorder_not_le[symmetric] simp del: \<open>e = {u,v}\<close>
        dest!: \<open>\<And>v'. v' \<in> Vs (insert e G') \<Longrightarrow> degree (insert e G') v' \<le> 2\<close>)

  have "v \<in> Vs G' \<Longrightarrow> degree G' v \<le> 2" for v
    using subset_edges_less_degree[where G' = G' and G = "insert e G'"]
    by (fastforce intro: dual_order.trans dest!: insert.prems(3) dest: in_Vs_insert[where e = e])
  then have IH: "C \<in> connected_components G' \<Longrightarrow> \<exists>p. path G' p \<and> C = set p \<and> distinct p"    
    for C
    using insert.IH insert.prems(1)
    by fastforce

  have deg_3: False
    if "p1 \<noteq> []" "p2 \<noteq> []" "path G (p1 @ u' # p2)" "{u, v} \<in> G" "v' \<notin> set (p1 @ u' # p2)"
      "distinct (p1 @ u' # p2)" "u' \<in> {u,v}" "u \<noteq> v" "v' \<in> {u, v}"
      "degree G u' \<le> 2"
    for G p1 u' v' p2
  proof-
    obtain v1 p1' where [simp]: "p1 = p1' @ [v1]"
      using \<open>p1 \<noteq> []\<close>
      by (auto simp: neq_Nil_conv_snoc)
    moreover obtain v2 p2' where [simp]: "p2 = v2 # p2'"
      using \<open>p2 \<noteq> []\<close>
      by (auto simp: neq_Nil_conv)
    ultimately have "v1 \<noteq> v2"
      using \<open>distinct (p1 @ u' # p2)\<close> \<open>path G (p1 @ u' # p2)\<close> path_2 path_suff
      by fastforce+
    moreover have "{v1,u'} \<in> G" "{u',v2} \<in> G"
      using \<open>path G (p1 @ u' # p2)\<close> path_2 path_suff
      by fastforce+
    moreover have "v1 \<noteq> v" "v1 \<noteq> u" "v2 \<noteq> v" "v2 \<noteq> u"
      using \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u, v}\<close> \<open>distinct (p1 @ u' # p2)\<close> \<open>v' \<notin> set (p1 @ u' # p2)\<close>
        mem_path_Vs[OF \<open>path G (p1 @ u' # p2)\<close>] \<open>u \<noteq> v\<close>
      by fastforce+
    moreover have "{u', SOME x. x \<in> {u, v} - {u'}} = {u,v}"
    proof-
      have "{u,v} - {v} = {u}"
        using \<open>u \<noteq> v\<close>
        by auto
      thus ?thesis
        using \<open>u' \<in> {u, v}\<close> \<open>u \<noteq> v\<close>
        by (fastforce simp add: Hilbert_choice_singleton)
    qed
    moreover have "u' \<noteq> (SOME x. x \<in> {u, v} - {u'})"
      using \<open>u' \<in> {u,v}\<close> \<open>u \<noteq> v\<close>
      by (fastforce intro!: Hilbert_set_minus)
    ultimately have "3 \<le> degree G u'"
      using \<open>{u, v} \<in> G\<close> \<open>v' \<notin> set (p1 @ u' # p2)\<close> \<open>distinct (p1 @ u' # p2)\<close>
      by (intro degree_3[where u = v1 and w = v2 and x = "SOME x. x \<in> ({u,v} - {u'})"]) auto
    thus False
      using degree_uv \<open>u' \<in> {u,v}\<close> \<open>degree G u' \<le> 2\<close>
      by(auto simp add: eval_enat_numeral one_eSuc dest: order_trans[where z = "eSuc 1"])
  qed

  from \<open>C \<in> connected_components (insert e G')\<close>[simplified \<open>e = {u, v}\<close>]
  show ?case
  proof(elim in_insert_connected_componentE, goal_cases)
    case 1
    then show ?case
    proof(safe, goal_cases)
      case 1
      then show ?case
        using \<open>u \<noteq> v\<close> \<open>v \<in> Vs (insert e G')\<close> \<open>e = {u,v}\<close>
        by (fastforce intro!: exI[where x = "[u, v]"])
    qed (fastforce dest: IH intro: path_subset)
  next
    case (2 u' v')
    moreover obtain p where "path G' p" "(connected_component G' u') = set p" "distinct p"
      using \<open>u' \<in> Vs G'\<close>
      by (force elim!: exists_conj_elims intro: IH simp add: connected_component_in_components)
    moreover then obtain p1 p2 where [simp]: "p = p1 @ u' # p2" "u' \<notin> set p1"
      using in_own_connected_component iffD1[OF in_set_conv_decomp_first]
      by (force elim!: exists_conj_elims)
    moreover hence "u' \<notin> set p2"
      using \<open>distinct p\<close>
      by auto
    moreover have "v' \<notin> set (p1 @ u' # p2)"
      using \<open>v' \<notin> Vs G'\<close> mem_path_Vs[OF \<open>path G' p\<close> ]
      by auto
    ultimately have False
      if "p1 \<noteq> []" "p2 \<noteq> []"
      by (fastforce intro!: deg_3[OF that, where G = "insert e G'" and v' = v' and u' = u']
          intro!: insert in_Vs_insert dest: path_subset[where G' = "insert e G'"])
    hence "p1 = [] \<or> p2 = []"
      by auto

    from "2"(5) show ?case
    proof(elim insertE[where a = C], goal_cases)
      case 1
      moreover from 2 have "path (insert e G') (v' # u' # p2)"
        using \<open>path G' p\<close>[simplified]
        by (fastforce intro: path_subset dest: path_suff)
      moreover from 2 have "path (insert e G') (p1 @ [u', v'])" if "p2 = []"
        using \<open>path G' p\<close>[simplified ] that 
        by (subst rev_path_is_path_iff[symmetric], subst (asm) rev_path_is_path_iff[symmetric]) (auto intro: path_subset)

      ultimately show ?case
        using \<open>p1 = [] \<or> p2 = []\<close> \<open>distinct p\<close> \<open>u' \<notin> set p2\<close> mem_path_Vs \<open>path G' p\<close> "2"(1-4)
        by (force intro!: exI[where x = "if p1 = [] then  v' # u' # p2 else p1 @ [u', v']"]
            simp add: \<open>connected_component G' u' = set p\<close>)
    qed (fastforce dest: IH intro: path_subset)
  next
    case 3

    from \<open>connected_component G' u \<noteq> connected_component G' v\<close>
    have "v \<notin> connected_component G' u" "u \<notin> connected_component G' v"
      using connected_components_member_eq
      by (fastforce simp only:)+
    from \<open>connected_component G' u \<noteq> connected_component G' v\<close>
    have "connected_component G' u \<inter> connected_component G' v = {}"
      using connected_components_disj
      by(auto intro!: connected_component_in_components 3)

    {
      fix u'
      assume "u' \<in> {u,v}"
      then obtain v' where \<open>v' \<in> {u,v}\<close> \<open>u' \<noteq> v'\<close>
        using uv(2)
        by blast
      obtain p where i: "path G' p" "(connected_component G' u') = set p" "distinct p"
        using \<open>u \<in> Vs G'\<close> \<open>v \<in> Vs G'\<close> \<open>u' \<in> {u,v}\<close>
        by (force elim!: exists_conj_elims intro: IH simp add: connected_component_in_components)
      moreover then obtain p1 p2 where [simp]: "p = p1 @ u' # p2" "u' \<notin> set p1"
        using in_own_connected_component iffD1[OF in_set_conv_decomp_first]
        by (force elim!: exists_conj_elims)
      moreover hence "u' \<notin> set p2"
        using \<open>distinct p\<close>
        by auto
      moreover have "v' \<notin> set (p1 @ u' # p2)"
        using \<open>v \<notin> connected_component G' u\<close> \<open>u \<notin> connected_component G' v\<close>
          \<open>connected_component G' u' = set p\<close> \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u,v}\<close> \<open>u' \<noteq> v'\<close>
        by auto
      ultimately have False
        if "p1 \<noteq> []" "p2 \<noteq> []"
        using \<open>u' \<in> {u,v}\<close> \<open>v' \<in> {u,v}\<close> degree_uv
        by (intro deg_3[OF that, where G = "insert e G'" and v' = v' and u' = u']) 
          (force intro!: degree_uv(1) in_Vs_insert dest: path_subset[where G' = "insert e G'"])+
      hence "p1 = [] \<or> p2 = []"
        by auto
      hence "\<exists>p p1 p2. path G' p \<and> (connected_component G' u') = set p \<and> distinct p \<and>
                       p = p1 @ u' # p2 \<and> (p1 = [] \<or> p2 = [])"
        by (fastforce intro!: i intro: exI[where x = p])
    } note * = this

    obtain p p1 p2 where
      "path G' p" "(connected_component G' u) = set p" "distinct p" "(p1 = [] \<or> p2 = [])" and
      [simp]: "p = p1 @ u # p2"
      apply (elim exists_conj_elim_5_3)
      using *
      by blast

    obtain p' p1' p2' where
      "path G' p'" "(connected_component G' v) = set p'" "distinct p'" "(p1' = [] \<or> p2' = [])" and
      [simp]: "p' = p1' @ v # p2'"
      apply (elim exists_conj_elim_5_3)
      using *
      by blast
    from "3"(4) show ?case
    proof(elim insertE[where a = C], goal_cases)
      case 1
      define witness_p where
        "witness_p = 
               (if p1 = [] \<and> p1' = [] then
                  (rev p2 @ [u, v] @ p2')
                else if p1 = [] \<and> p2' = [] then
                  (rev p2 @ [u, v] @ rev p1')
                else if p2 = [] \<and> p1' = [] then
                  (p1 @ [u, v] @ p2')
                else if p2 = [] \<and> p2' = [] then
                  (p1 @ [u, v] @ rev p1')
                else
                  undefined)"

      from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "path (insert e G') witness_p"
        using \<open>path G' p\<close> \<open>path G' p'\<close>
        by (auto intro!: path_subset[where G' = "(insert {u, v} G')"]
            path_concat[where p = "p1 @ [u]" and q = "u # v # rev p1'", simplified]
            path_concat[where p = "rev p2 @ [u]" and q = "u # v # p2'", simplified]
            path_concat[where p = "rev p2 @ [u]" and q = "u # v # rev p1'", simplified]
            path_concat[where p = "p1 @ [u]" and q = "u # v # []", simplified]
            path_concat[where p = "p1 @ [u]" and q = "u # v # p2'", simplified]
            simp: rev_path_is_path_iff[symmetric, where p = "(rev p2 @ [u])"]
            rev_path_is_path_iff[symmetric, where p = "(rev p2 @ [u, v])"]
            rev_path_is_path_iff[symmetric, where p = "(v # rev p1')"]
            witness_p_def
            split: if_splits)
      moreover from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "distinct witness_p"
        using \<open>distinct p\<close> \<open>distinct p'\<close>
          \<open>(connected_component G' u) = set p\<close>
          \<open>v \<notin> connected_component G' u\<close>
          \<open>(connected_component G' v) = set p'\<close>
          \<open>u \<notin> connected_component G' v\<close>
          \<open>connected_component G' u \<inter> connected_component G' v = {}\<close>
        by (fastforce simp: witness_p_def  split: if_splits)
      moreover from \<open>p1 = [] \<or> p2 = []\<close> \<open>p1' = [] \<or> p2' = []\<close> have "C = set witness_p"
        using \<open>(connected_component G' u) = set p\<close> \<open>(connected_component G' v) = set p'\<close>
          \<open> C = connected_component G' u \<union> connected_component G' v\<close>
        by (fastforce simp: witness_p_def  split: if_splits)
      ultimately show ?case
        by auto
    qed (fastforce dest: IH intro: path_subset)
  qed (fastforce dest: IH intro: path_subset)
qed (auto simp: connected_components_empty intro!: exI[where x = "[]"])

corollary (in graph_abs) component_has_path_distinct:
  assumes
    "C \<in> connected_components G" and
    "\<And>v. v \<in> Vs G \<Longrightarrow> degree G v \<le> 2"
  shows "\<exists>p. path G p \<and> C = (set p) \<and> distinct p"
  using component_has_path_distinct[OF _ _ assms] graph
        finite_E
  by fastforce
  
lemma finite_dbl_finite_verts: "finite G \<Longrightarrow> dblton_graph G \<Longrightarrow> finite (Vs G)"
  by (auto simp: Vs_def dblton_graph_def)

definition connected_at where
  "connected_at v e e' = (v \<in> (e \<inter> e'))"

lemma nempty_tl_hd_tl:
  "(tl l) \<noteq>[] \<Longrightarrow> l = (hd l) # (tl l)"
  by (induct "l"; simp)

lemma card3_subset:
  assumes "card s \<ge> 3"
  shows "\<exists>x y z. {x, y, z} \<subseteq> s \<and> x \<noteq> y  \<and> x \<noteq> z  \<and> y \<noteq> z"  
  using assms by(auto simp: numeral_3_eq_3 card_le_Suc_iff)

lemma mid_path_deg_ge_2:
  assumes "path G p"
    "v \<in> set p"
    "v \<noteq> hd p"
    "v \<noteq> last p"
    "distinct p"
    "finite G"
  shows "degree G v \<ge> 2"
  using assms
  by (metis degree_edges_of_path_ge_2 path_edges_subset subset_edges_less_degree)


lemma path_repl_edge:
  assumes "path G' p" "p \<noteq> []" "G' = (insert {w,x} G)" "path G puv" "hd puv = w" "last puv = x" "puv \<noteq> []"
  shows "\<exists>p'. p' \<noteq> [] \<and> path G p' \<and> hd p' = hd p \<and> last p' = last p"
  using assms
  by (metis walk_betw_repl_edge walk_betw_def)

lemma path_can_be_split:
  assumes "path G' p" "G' = insert {w,x} G" "{w,x} \<subseteq> Vs G" "p \<noteq> []"
  shows "(\<exists>p'. p' \<noteq> [] \<and> path G p' \<and> hd p' = hd p \<and> last p' = last p) \<or>
         (\<exists>p1 p2. p1 \<noteq> [] \<and> p2 \<noteq> [] \<and> path G p1 \<and> path G p2 \<and>
                             ((last p1 = w \<and> hd p2 = x) \<or> (last p1 = x \<and> hd p2 = w)) \<and>
                             hd p1 = hd p \<and> last p2 = last p)"
  using assms
  using vwalk_betw_can_be_split[OF _ , simplified walk_betw_def, where p = p and u = "hd p" and v = "last p"]
  apply simp
  by (smt (verit, ccfv_SIG))

lemma path_can_be_split_2:
  assumes "path (insert {w,x} G) p" "w \<in> Vs G" "x \<notin> Vs G" "p \<noteq> []"
  shows "(\<exists>p'. p' \<noteq> [] \<and> path G p' \<and> hd p' = hd p \<and> last p' = last p) \<or>
         (\<exists>p'. path G p' \<and> (p' \<noteq> [] \<longrightarrow> hd p' = w) \<and> ((hd p = last (x # p') \<and> last p = x) \<or> (hd p = x \<and> last p = last (x # p'))))"
  using vwalk_betw_can_be_split_2[OF _ \<open>w \<in> Vs G\<close> \<open>x \<notin> Vs G\<close>, simplified walk_betw_def, where p = p and u = "hd p" and v = "last p"]
  using assms
  apply simp
  by (smt (verit, del_insts) hd_rev last.simps last_rev path_simps(1) rev_is_Nil_conv rev_path_is_path_iff) 

lemma path_can_be_split_3:
  assumes "path G' p" "G' = insert {w,x} G" "w \<notin> Vs G" "x \<notin> Vs G" "p \<noteq> []"
  shows "path G p \<or> path {{w, x}} p"
  using assms
proof(induction)
  case (path2 v v' vs)
  show ?case
  proof(cases "path G (v' #  vs)")
    case True
    then have "path G (v # v' # vs)"
      using path2
      by (force simp: doubleton_eq_iff mem_path_Vs)
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
      using path path2
      by (auto simp: edges_are_Vs)
    then show ?thesis
      by auto
  qed
qed (auto simp add: Vs_def)

lemma v_in_apath_in_Vs_append:
  "path G (p1 @ v # p2) \<Longrightarrow> v \<in> Vs G"
  by (simp add: mem_path_Vs)

lemma edge_between_pref_suff:
  "\<lbrakk>p1 \<noteq> []; p2 \<noteq> []; path G (p1 @ p2)\<rbrakk>
    \<Longrightarrow> {last p1, hd p2} \<in> G"
  by(induction p1) (auto simp: neq_Nil_conv)+

lemma construct_path:
 "\<lbrakk>path G p1; path G p2; {hd p1, hd p2} \<in> G\<rbrakk>
   \<Longrightarrow> path G ((rev p1) @ p2)"
  by (simp add: last_rev path_append rev_path_is_path)

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
   by (fastforce dest: *)
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
      by (auto simp: insert_absorb)
  next
    case False
    then have *: "card (set l) \<ge> 2"
      by simp
    show ?thesis
      using Cons(1)[OF *]
      using "*" by force
  qed
qed

lemma edges_of_path_nempty:
  "edges_of_path xs \<noteq> [] \<longleftrightarrow> length xs \<ge> 2"
  by(induction xs rule: edges_of_path.induct) auto

lemma degree_edges_of_path_ge_2':
  "\<lbrakk>distinct p; v\<in>set p; v \<noteq> hd p; v \<noteq> last p\<rbrakk>
    \<Longrightarrow> degree (set (edges_of_path p)) v \<ge> 2"
  using degree_edges_of_path_ge_2
  by force

lemma last_edge_in_last_vert_in:
  assumes "length p \<ge> 2" "last (edges_of_path p) \<in> G"
  shows "last p \<in> Vs G"
  using assms
proof(induction p rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case
  using last_in_edge[where p="v'#l"]
  by( auto split: if_splits simp: neq_Nil_conv)
qed auto
 
lemma hd_edge_in_hd_vert_in:
  assumes "length p \<ge> 2" "hd (edges_of_path p) \<in> G"
  shows "hd p \<in> Vs G"
  using assms
proof(induction p rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case
  using last_in_edge[where p="v'#l"]
  by( auto split: if_splits simp: neq_Nil_conv)
qed auto

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
  assumes "finite G1" "e \<notin> G1" "v \<in> e"
  shows "degree (insert e G1) v = degree G1 v + 1"
  using assms
  by (simp add: degree_insert eSuc_plus_1)


lemma edges_of_path_snoc:
  assumes "p \<noteq> []"
  shows "(edges_of_path p) @ [{last p, a}] = edges_of_path (p @ [a])"
  using assms
  by (simp add: edges_of_path_append_3)

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

lemma xy_in_edges_of_path_split: 
  "{x, y} \<in> set (edges_of_path p) \<Longrightarrow> \<exists> p1 p2. p =p1@[x,y]@p2 \<or> p =p1@[y, x]@p2"
  by(force intro: exE[OF in_edges_of_path_split[of "{x, y}" p]] simp add: doubleton_eq_iff)

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
  by (simp add: edges_of_path_length)

lemma mem_eq_last_edge:
  "\<lbrakk>distinct p; e \<in> set (edges_of_path p); last p \<in> e\<rbrakk>
           \<Longrightarrow> e = last (edges_of_path p)"
  using edges_of_path_nempty last_vert_in_last_edge
  by fastforce

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
  "e \<in> set (edges_of_path p) \<Longrightarrow> e \<noteq> {}"
  using in_edges_of_path_split
  by auto

lemma edges_of_path_snoc_2:
  "edges_of_path (p @ [v1, v2]) = edges_of_path (p @ [v1]) @ [{v1 ,v2}]"
  apply(subst edges_of_path_append_2)
  by auto

lemma edges_of_path_snoc_3: "p \<noteq> [] \<Longrightarrow> edges_of_path (p @ [v1, v2]) = edges_of_path p @ [{last p, v1}, {v1 ,v2}]"
  apply(subst edges_of_path_append_3)
  by auto

lemma same_con_comp_path:
  "\<lbrakk>C \<in> connected_components G; w \<in> C; x \<in> C\<rbrakk> 
    \<Longrightarrow>\<exists>pwx. pwx \<noteq> [] \<and> path G pwx \<and> hd pwx = w \<and> last pwx = x"
  by(auto elim!: same_con_comp_walk[where x = x] simp: walk_betw_def)

lemma in_con_compI:
  assumes connected: "puv \<noteq> []" "path G puv" "hd puv = u" "last puv = v" and
    u_mv: "u\<in>Vs G" and
    uC: "u \<in> C" and
    C_in_comp: "C \<in> connected_components G"
  shows "v \<in> C"
proof(cases "u = v")
  case True
  then show ?thesis using assms by simp
next
  obtain w where w: "w \<in> Vs G" "C = connected_component G w"
    using C_in_comp
    by (smt connected_components_def mem_Collect_eq)
  then obtain pwu where pwu: "pwu \<noteq> []" "path G pwu" "hd pwu = w" "last pwu = u"
    using uC C_in_comp
    unfolding connected_components_def connected_component_def
    apply simp
    by (metis (no_types, lifting) C_in_comp in_own_connected_component same_con_comp_path uC w(2))
  moreover case False
  ultimately have "path G (pwu @ (tl puv))" "hd (pwu @ (tl puv)) = w" "last (pwu @ (tl puv)) = v"
    apply(intro path_append connected pwu tl_path_is_path; simp)
    using connected pwu path.simps
    by fastforce+
  then show ?thesis
    using w
    by (metis Nil_is_append_conv contra_subsetD last_in_set path_subset_conn_comp pwu(1))
qed

lemma component_has_path_no_cycle:
  assumes "finite C" "C \<in> connected_components G" "card C \<ge> 2"
  shows "\<exists>p. path G p \<and> C = (set p) \<and> hd p \<noteq> last p"
proof-
  obtain p where p: "path G p" "C = (set p)"
    using assms component_has_path'
    by auto
  then show ?thesis
    using remove_cycle_pfx_works_card_ge_2
    by (metis assms(3) path_suff remove_cycle_pfx_works)
qed

definition component_path where
"component_path G C = (SOME p. path G p \<and> C = set p \<and> hd p \<noteq> last p)"

lemma component_path_works:
  assumes "finite C" "C \<in> connected_components G" "card C \<ge> 2"
  shows "path G (component_path G C) \<and> C = set (component_path G C) \<and> hd (component_path G C) \<noteq> last (component_path G C)"
  unfolding component_path_def
  apply(rule someI_ex)
  using component_has_path_no_cycle[OF assms] .

lemma component_edges_subset:
  shows "component_edges G C \<subseteq> G"
  unfolding component_edges_def
  by auto

lemma edges_path_subset_edges:
  "\<lbrakk>path G p; set p \<subseteq> C\<rbrakk> \<Longrightarrow>
    set (edges_of_path p) \<subseteq> component_edges G C"
  by (induction rule: path.induct) (auto simp add:  component_edges_def)

lemma Vs_component_edges:
  "dblton_graph G \<Longrightarrow> C \<in> connected_components G \<Longrightarrow> Vs (component_edges G C) = C"
  unfolding component_edges_def Vs_def connected_components_def
proof (standard, goal_cases)
  case 1
  then show ?case by auto
next
  case 2
  then have "\<exists>v. v \<in> \<Union> G \<and> C = connected_component G v" by blast
  then obtain v where "v \<in> \<Union> G" "C = connected_component G v" by blast
  with in_connected_component_in_edges
    have "\<forall>x \<in> C. x \<in> \<Union> G" using Vs_def by fastforce

  have "\<forall>x \<in> C. \<exists>y \<in> C. {x, y} \<in> G"
  proof
    fix x
    assume "x \<in> C"
    with in_connected_component_in_edges \<open>v \<in> \<Union> G\<close> \<open>C = connected_component G v\<close>
      have "x \<in> \<Union> G" using Vs_def by fastforce
    then have "\<exists>e. e \<in> G \<and> x \<in> e" by blast
    with dblton_graphE[OF \<open>dblton_graph G\<close>] have "\<exists>y. x \<noteq> y \<and> {x, y} \<in> G"
      using insert_absorb
      by (smt (verit, ccfv_SIG) empty_iff insert_commute insert_iff)
    then obtain y where "x \<noteq> y" "{x, y} \<in> G" by blast
    then have "walk_betw G x [x, y] y" 
      unfolding walk_betw_def by auto
    from has_path_in_connected_component[OF this] connected_components_member_eq
      \<open>x \<in> C\<close> \<open>C = connected_component G v\<close>
      have "y \<in> connected_component G v" by fast
    with \<open>{x, y} \<in> G\<close> \<open>C = connected_component G v\<close>
    show "\<exists>y \<in> C. {x, y} \<in> G" by blast
  qed

  then have "\<forall>x \<in> C. \<exists>y. {x, y} \<subseteq> C \<and> {x, y} \<in> G \<and> x \<in> {x, y}"
     by auto 
  then show ?case
    using Complete_Lattices.Union_iff[where ?C = "{{x, y} |x y. {x, y} \<subseteq> C \<and> {x, y} \<in> G}"]
    by (smt (verit) mem_Collect_eq subsetI)
qed 

lemma components_edges_image_Vs:
  "dblton_graph G \<Longrightarrow> Vs ` (components_edges G) = connected_components G"
  unfolding components_edges_def Vs_def
proof-
  assume "dblton_graph G"
  have "\<Union> ` {component_edges G C |C. C \<in> connected_components G} = 
    {\<Union> (component_edges G C) |C. C \<in> connected_components G}" by blast
  also have "... = 
    {C |C. C \<in> connected_components G}"
    using Vs_component_edges[OF \<open>dblton_graph G\<close>] by (metis Vs_def)
  finally show "\<Union> ` {component_edges G C |C. C \<in> connected_components G} = connected_components G"
    by auto
qed 

lemma Union_connected_components:
  "dblton_graph G \<Longrightarrow> Union (connected_components G) = (Vs G)"
proof-
  assume "dblton_graph G"
  from \<open>dblton_graph G\<close> have "G = G \<inter> {{x, y} |x y. True}" by fast
  with component_edges_partition have "\<Union> (components_edges G) = G" by fastforce
  then have "Vs G = Vs (\<Union> (components_edges G))" by auto
  also have "... = \<Union> (Vs ` (components_edges G))" unfolding Vs_def by auto
  also have "... = \<Union> (connected_components G)"
    using components_edges_image_Vs[OF \<open>dblton_graph G\<close>] by auto
  finally show ?thesis by simp
qed

lemma component_edges_nonempty:
  assumes "dblton_graph G"
  shows "C \<in> connected_components G \<Longrightarrow> component_edges G C \<noteq> {}"
  using Vs_component_edges assms connected_comp_nempty vs_member by fastforce


lemma finite_con_comps:
  "finite (Vs G) \<Longrightarrow> finite (connected_components G)"
  by (auto simp: connected_components_def)

lemma connected_component_finite:
  "finite G \<Longrightarrow> dblton_graph G \<Longrightarrow> C \<in> connected_components G \<Longrightarrow> finite C"
  by (meson connected_component_subs_Vs finite_dbl_finite_verts finite_subset)

lemma component_edges_finite:
  "finite G \<Longrightarrow> C \<in> connected_components G \<Longrightarrow> finite (component_edges G C)"
  by (meson component_edges_subset rev_finite_subset)


subsection \<open>Alternative definition of connected components\<close>

text \<open>In some cases, an alternative definition of the @{term connected_components} of a graph is necessary,
for example if we want to consider only a subset of the edges of a graph, but still consider all the vertices
of the vertices. Then we can use the following definition, which gives the connected components of the
graph (V, X), which includes the singleton connected components (the vertices in V which are not covered
by the edge set X).\<close> 

text \<open>The abbreviation is there to allow for the definition as a lemma.\<close>
definition "connected_components'_aux V X = comps (V \<union> (Vs X)) X"

abbreviation "connected_components' V X \<equiv> connected_components'_aux V X"

lemma connected_components'_def:
  "connected_components' V X = connected_components X \<union> ((\<lambda>v. {v}) ` (V - (Vs X)))"
  using connected_components_notE_singletons image_iff 
  by (fastforce simp add: connected_components'_aux_def connected_components_def comps_def)

lemma connected_components'_disj:
  "\<lbrakk>C \<noteq> C'; C \<in> connected_components' V X; C' \<in> connected_components' V X\<rbrakk> \<Longrightarrow> C \<inter> C' = {}"
proof-
  assume "C \<noteq> C'" "C \<in> connected_components' V X" "C' \<in> connected_components' V X"
  
  then consider (1) "C \<in> connected_components X \<and> C' \<in> connected_components X" |
                (2) "C \<in> {{v} | v. v \<in> V - (Vs X)} \<and> C' \<in> connected_components X" |
                (3) "C \<in> connected_components X \<and> C' \<in> {{v} | v. v \<in> V - (Vs X)}" |
                (4) "C \<in> {{v} | v. v \<in> V - (Vs X)} \<and> C' \<in> {{v} | v. v \<in> V - (Vs X)}"
    unfolding connected_components'_def by auto
  then show "C \<inter> C' = {}"
  proof (cases)
    case 1
    with connected_components_disj[OF \<open>C \<noteq> C'\<close>] show ?thesis by auto
  next
    case 2
    then have "C \<subseteq> V - Vs X" by blast
    moreover have "C' \<subseteq> Vs X" using 2
      by (simp add: connected_component_subs_Vs)
    ultimately show ?thesis by auto
  next
    case 3
    then have "C' \<subseteq> V - Vs X" by blast
    moreover have "C \<subseteq> Vs X" using 3
      by (simp add: connected_component_subs_Vs)
    ultimately show ?thesis by auto
  next
    case 4
    with \<open>C \<noteq> C'\<close> show ?thesis by blast
  qed
qed

lemma union_connected_components':
  "dblton_graph X \<Longrightarrow> Vs X \<subseteq> V \<Longrightarrow> \<Union> (connected_components' V X) = V"
  unfolding connected_components'_def
proof-
  assume "dblton_graph X" "Vs X \<subseteq> V"
  have "\<Union> (connected_components X \<union> ((\<lambda>v. {v}) ` (V - (Vs X)))) = 
    \<Union> (connected_components X) \<union> \<Union> ((\<lambda>v. {v}) ` (V - (Vs X)))" by simp  
  also have "... = Vs X \<union> \<Union> ((\<lambda>v. {v}) ` (V - (Vs X)))"
    using Union_connected_components[OF \<open>dblton_graph X\<close>] by metis
  also have "... = Vs X \<union> (V - Vs X)"
    by auto
  also have "... = V"
    using \<open>Vs X \<subseteq> V\<close> by auto
  finally show "\<Union> (connected_components X \<union> ((\<lambda>v. {v}) ` (V - (Vs X)))) = V" .
qed

lemma connected_component'_nonempty:
  "C' \<in> connected_components' V X \<Longrightarrow> C' \<noteq> {}"
  unfolding connected_components'_def using connected_comp_nempty by blast


subsection \<open>Cycles\<close>

fun epath :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "epath G u [] v = (u = v)"
| "epath G u (x#xs) v \<longleftrightarrow> (\<exists>w. u \<noteq> w \<and> {u, w} = x \<and> epath G w xs v) \<and> x \<in> G"

lemma epath_empty:
  assumes "epath {} u p v"
  shows "u = v" and "p = []"
  using assms
  by (auto elim: epath.elims)

lemma epath_last:
  "p \<noteq> [] \<Longrightarrow> epath G u p v \<Longrightarrow> v \<in> last p"
  apply (induction p arbitrary: u v)
  by auto

lemma epath_edges_subset:
  "epath G v p w \<Longrightarrow> set p \<subseteq> G"
  apply (induction p arbitrary: v w)
  apply simp
  by auto

lemma epath_subset:
  "epath G v p w \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> epath G' v p w"
  apply (induction p arbitrary: v w)
  apply simp
  by auto

lemma epath_subset_other_set:
  "epath G u p v \<Longrightarrow> set p \<subseteq> G' \<Longrightarrow> epath G' u p v"
  apply (induction p arbitrary: u v)
  apply simp
  by auto

lemma epath_single: "e \<in> G \<Longrightarrow> e= {x, y} \<Longrightarrow> x \<noteq> y \<Longrightarrow> epath G x [e] y"
  by auto

lemma epath_non_empty: "epath G u p v \<Longrightarrow> u \<noteq> v \<Longrightarrow> length p \<ge> 1"
  by (cases p) auto

lemma epath_find_splitter:"epath X u (P@[e,d]@Q) v \<Longrightarrow> \<exists> x. epath X u (P@[e]) x \<and> epath X x ([d]@Q) v \<and> x \<in> e \<inter> d"
proof(induction P arbitrary: u)
  case Nil
  then show ?case by auto
next
  case (Cons ee P)
  obtain w where w_prop:"u \<noteq> w" "{u, w} = ee" "epath X w (P @ [e, d]@Q) v" " ee \<in> X" 
    using Cons(2) by auto
  obtain x where "epath X w (P @ [e]) x" "epath X x ([d] @ Q) v \<and> x \<in> e \<inter> d" 
    using Cons(1)[OF w_prop(3)] by auto
  hence "epath X u ((ee#P) @ [e]) x" "epath X x ([d] @ Q) v \<and> x \<in> e \<inter> d"
    using w_prop by auto
  then show ?case by blast
qed

lemma epath_find_splitter_advanced:
"epath X u (P@[e1, e2, e3]@Q) v \<Longrightarrow> \<exists> x y.  e2 = {x, y} \<and> x \<noteq> y \<and> epath X u (P@[e1]) x \<and>
                                      epath X y ([e3]@Q) v \<and> x \<in> e1 \<inter> e2 \<and> y \<in> e2 \<inter> e3"
proof(induction P arbitrary: u)
  case Nil
  then show ?case by auto
next
  case (Cons ee P)
  obtain w where w_prop:"u \<noteq> w" "{u, w} = ee" "epath X w (P @ [e1 ,e2 ,e3 ]@ Q) v" "ee \<in> X"
    using Cons(2) by auto
  obtain x y where xy_prop:"e2 = {x, y}"
          "x \<noteq> y" "epath X w (P @ [e1]) x" "epath X y ([e3] @ Q) v" "x \<in> e1 \<inter> e2" "y \<in> e2 \<inter> e3"
    using Cons(1)[OF w_prop(3)] by blast
  hence "epath X u ((ee # P) @ [e1]) x"
    using w_prop by auto
  then show ?case 
    using xy_prop by blast
qed

lemma epath_distinct_epath:"epath G u p v \<Longrightarrow>
l = length p \<Longrightarrow> \<exists> q. epath G u q v \<and> set q \<subseteq> set p \<and> distinct q" 
proof(induction l arbitrary: u p v rule: less_induct)
  case (less l)
  show ?case
  proof(cases l)
    case 0
    then show ?thesis 
      using less.prems by force
  next
    case (Suc nat)
    note Suc = less Suc
  then obtain e p' where ep':"p = e#p'" by(cases p) auto
  show ?thesis
  proof(cases "e \<in> set p'")
    case True
    then obtain p1 p2 where p1p2:"p' = p1 @[e]@p2"
      by (metis append_Cons append_self_conv2 in_set_conv_decomp_first)
    have bulast_p1_subst:"butlast (e # p1) @ [last (e # p1)] = e#p1"
      by simp
    have epath_verbose:"epath G u (butlast (e # p1) @ [last (e # p1), e] @ p2) v"
      by (metis append.assoc append_Cons append_Nil bulast_p1_subst ep' less.prems(1) p1p2)
    obtain x where x_prop:"epath G u (e#p1) x" 
         "epath G x ([e] @ p2) v" "x \<in> last (e # p1) \<inter> e"
      using epath_find_splitter[OF epath_verbose] by (subst (asm) bulast_p1_subst[symmetric])auto
    show ?thesis 
    proof(cases p1)
      case Nil
      hence epath_p2:"epath G u p2 v"
        using x_prop(2) Suc(2) p1p2 ep' by auto
      have  "\<exists>q. epath G u q v \<and> set q \<subseteq> set p2 \<and> distinct q"
        using p1p2 ep' Suc(3)  by(intro Suc(1)[OF _ epath_p2 refl]) simp
      then obtain q where "epath G u q v" "set q \<subseteq> set p2"  "distinct q"
        by auto
      then show ?thesis
        using ep' p1p2 by auto
    next
      case (Cons a list)
      obtain a where e_endpoints:" e = {a, u}" "a \<noteq> u" 
        using x_prop(1) by auto
      hence x_is:"x = u \<or> x = a"
        using x_prop(3) by blast
      show ?thesis 
      proof(cases rule: disjE[OF x_is])
        case 1
        hence  u_v_path:"epath G u ([e] @ p2) v" 
          using x_prop(2) by force
        obtain q where "epath G u q v" "set q \<subseteq> set ([e] @ p2)" "distinct q" 
          using Suc(1)[OF _ u_v_path refl] Suc(3) ep' p1p2  by auto
        then show ?thesis
          using ep' p1p2 by auto
      next
        case 2
        hence  u_v_path:"epath G u ([e, e] @ p2) v" 
          using e_endpoints x_prop(2) by fastforce
        obtain q where "epath G u q v" "set q \<subseteq> set ([e,e] @ p2)" "distinct q" 
          using Suc(1)[OF _ u_v_path refl] Suc(3) ep' p1p2 Cons  by auto         
        then show ?thesis
          using ep' p1p2 by auto
      qed
    qed
  next
    case False
    then obtain w where w_prop:"u \<noteq> w" "{u, w} = e" "epath G w p' v" "e \<in> G"
      using ep' less.prems(1) by auto
    obtain q where "epath G w q v" "set q \<subseteq> set p'" "distinct q"
      using  Suc(1)[OF _ w_prop(3) refl] ep' Suc(3) by auto
    moreover hence "epath G u (e#q) v"
      using w_prop(1,2,4) by auto
    ultimately show ?thesis 
      using False ep' by(intro exI[of _ "e#q"]) auto
  qed
qed
qed

lemma epath_append:"epath X x P y \<Longrightarrow> epath X y Q z \<Longrightarrow> epath X x (P@Q) z"
  by(induction X x P y rule: epath.induct) auto

lemma epath_one_split: " epath G u p v \<Longrightarrow> {x, y} \<in> set p \<Longrightarrow> x \<noteq> y \<Longrightarrow>
                        \<exists> p1 p2. p = p1@[{x,y}]@p2 \<and> ((epath G u p1 x \<and> epath G y p2 v) \<or>
                                                       (epath G u p1 y \<and> epath G x p2 v))"
proof(induction p arbitrary: u )
  case Nil
  then show ?case by simp
next
  case (Cons e p)
  show ?case 
  proof(cases "{x,y} = e")
    case True
    show ?thesis 
      apply(rule exI[of _ Nil])
      apply(rule exI[of _ p])
      using Cons True by fastforce
  next
    case False
    obtain w where w_prop: "u \<noteq> w" "{u, w} = e" "epath G w p v" "e \<in> G"
      using  Cons(2)[simplified] by auto
    hence xy_in_p:"{x, y} \<in> set p"
      using Cons.prems(2) False by auto
    obtain p1 p2 where p1p2:"p = p1 @ [{x, y}] @ p2" 
      "epath G w p1 x \<and> epath G y p2 v \<or> epath G w p1 y \<and> epath G x p2 v"
      using Cons(1)[OF w_prop(3) xy_in_p Cons(4)] by auto
    show ?thesis
      apply(rule exI[of _ "{u, w}#p1"])
      using p1p2(1) p1p2(2) w_prop(1) w_prop(2) w_prop(4) by (auto intro!: exI[of _ p2])
  qed
qed

lemma epath_rev: "epath G u p v \<Longrightarrow> epath G v (rev p) u"
proof(induction G u p v rule: epath.induct)
  case (2  G u x p v)
  thus ?case
    using epath_append[of G v "rev p" _  "[x]" u] epath_single[of x G]  
    by(auto simp add: doubleton_eq_iff )
qed simp

definition depath :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "depath G u p v = ( epath G u p v \<and> distinct p)"

definition decycle :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> bool" where
  "decycle G u p = (epath G u p u \<and> length p > 2 \<and> distinct p)"

lemma decycle_subset:
  "decycle G u p \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> decycle G' u p"
  unfolding decycle_def using epath_subset by metis

lemma decycle_not_subset:
  "\<exists>u. decycle G u p \<Longrightarrow> \<nexists>u. decycle G' u p \<Longrightarrow> \<not>set p \<subseteq> G'"
proof (rule ccontr, goal_cases)
  case 1
  then have "set p \<subseteq> G'" by blast
  from \<open>\<exists>u. decycle G u p\<close> decycle_def
    have "(\<exists>u. epath G u p u \<and> length p > 2 \<and> distinct p)"
    by metis
  then obtain u where "epath G u p u" "length p > 2" "distinct p"
    by blast

  with epath_subset_other_set[OF \<open>epath G u p u\<close> \<open>set p \<subseteq> G'\<close>] decycle_def
    have "decycle G' u p" by metis
  with \<open>\<nexists>u. decycle G' u p\<close> show ?case by blast
qed

lemma new_edge_in_decycle: "\<not> decycle T u C \<Longrightarrow> decycle (insert e T) u C \<Longrightarrow> e \<in> set C" 
  using   epath_edges_subset epath_subset_other_set subset_insert
  by(fastforce simp add: decycle_def)

subsection \<open>More on Components\<close>

lemma connected_component_non_empt: "connected_component A x \<noteq> {}"
  by(auto simp add: connected_component_def)

thm connected_components'_def[where X = E for E, where V = X for X]

lemma number_comps_below_vertex_card:
  assumes "finite E" "finite X"
  shows "card (comps X E) \<le> card X"
  using assms(2) card_image_le 
  by(auto simp add: comps_def connected_component_def)

lemma new_edge_disjoint_components: 
  assumes "u = u"  "v = v" "E = E"
  defines "E_new \<equiv> insert {u,v} E"
  shows "connected_component E_new u = connected_component E_new v"
  using connected_components_member_eq in_con_comp_insert
  by (fastforce simp add: E_new_def)

lemma unite_disjoint_components_by_new_edge:
  assumes "u \<notin>connected_component E x" "v \<notin>connected_component E x"
  defines "E_new \<equiv> insert {u,v} E"
  shows "connected_component E x =connected_component E_new x "
  using  assms(1,2) connected_component_in_components[of x ]
         unchanged_connected_component[of u "connected_component E x" v ] 
         connected_components_notE_singletons[of x ] in_Vs_insertE
  by (cases "x \<in> Vs E") 
     (auto intro: in_Vs_insertE[of x "{u, v}" E]
        simp add: connected_components_closed'' in_own_connected_component E_new_def)

lemma insert_edge_endpoints_same_component:
  assumes E_new_def: "E_new \<equiv> insert {u,v} E"
  shows "connected_component E u \<union> connected_component E v = connected_component E_new u "
    using assms  new_edge_disjoint_components[of u v E] con_comp_subset[of E "insert {u, v} E"] 
          unite_disjoint_components_by_new_edge[of u E _ v] connected_components_member_sym 
    by(fastforce simp add: E_new_def)

text \<open>If an edge is added between two different components, how do the components change?\<close>

lemma new_component_insert_edge: 
  assumes "connected_component E u \<noteq> connected_component E v" "u \<in> X" "v \<in> X"
  defines "E_new \<equiv> insert {u,v} E"
    shows "comps X E_new = comps X E - {connected_component E u,  connected_component E v} \<union> 
                             {connected_component E u \<union> connected_component E v}"
proof
  show "comps X E_new
    \<subseteq> comps X E - {connected_component E u, connected_component E v} \<union>
       {connected_component E u \<union> connected_component E v}"
  proof
    fix x
    assume xasms:" x \<in> comps X E_new"
    thus "x \<in> comps X E - {connected_component E u, connected_component E v} \<union>
              {connected_component E u \<union> connected_component E v}"
    proof(cases "x = (connected_component E u \<union> connected_component E v)")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain w where w: "w \<in> X " "x = connected_component E_new w" 
        using xasms unfolding comps_def E_new_def by blast
      have "connected_component E_new w = connected_component E w"
      proof(rule ccontr)
        assume "connected_component E_new w \<noteq> connected_component E w"
        hence 11:"connected_component E w \<subset> connected_component E_new w"
          by (simp add: E_new_def con_comp_subset psubsetI subset_insertI)
        hence 12:"u \<in> connected_component E w \<or> v \<in> connected_component E w" unfolding E_new_def 
          using unite_disjoint_components_by_new_edge[of u E w v] by auto
        have " x = connected_component E u \<union> connected_component E v"
        proof(subst w(2), rule)
          show "connected_component E_new w \<subseteq> connected_component E u \<union> connected_component E v"
            using 12 insert_edge_endpoints_same_component[of E_new u v E]  E_new_def connected_components_member_eq[of u E_new w] 
                     connected_components_member_sym[of u E ]  11 insert_edge_endpoints_same_component[of E_new u v E]
                     connected_components_member_eq[of v E_new w]
                     connected_components_member_sym[of v E ]  insert_edge_endpoints_same_component[of E_new v u E]
              by fastforce
            show " connected_component E u \<union> connected_component E v \<subseteq> connected_component E_new w"
                using 12 E_new_def 11 new_edge_disjoint_components[of u v E]
                    con_comp_subset[of E E_new] connected_components_member_eq[of u _ w] 
                connected_components_member_eq[of v _ w]
                by blast           
        qed
        thus False using False by simp
      qed 
      moreover hence "x \<noteq> connected_component E u" "x \<noteq> connected_component E v"
        using E_new_def assms(1) connected_components_member_eq[of u E_new w]
              in_con_comp_insert[of v u E]  connected_components_member_eq[of v E u]
              in_connected_componentI2[of u u E] w(2) connected_components_member_eq[of v E_new w]
              in_con_comp_insert[of u v E, simplified]  connected_components_member_eq[of u E v]
              in_connected_componentI2[of v v E] doubleton_eq_iff[of u v v u, simplified] 
        by auto
      ultimately have "x \<in> comps X E - {connected_component E u, connected_component E v}" 
        by (simp add: comps_def w(1) w(2))
      thus "x \<in> comps X E - {connected_component E u, connected_component E v} \<union>
         {connected_component E u \<union> connected_component E v}" by simp
    qed
  qed
  show "comps X E - {connected_component E u, connected_component E v} \<union>
       {connected_component E u \<union> connected_component E v}
        \<subseteq> comps X E_new"
  proof
    fix x
    assume xasms: "x \<in> comps X E - {connected_component E u, connected_component E v} \<union>
             {connected_component E u \<union> connected_component E v} "
    thus "x \<in> comps X E_new "
    proof(cases "x \<noteq> connected_component E u \<union> connected_component E v")
      case True
        then obtain w where w: "w \<in> X " "x = connected_component E w" "w \<noteq> u" "w\<noteq>v"
        using xasms True by (auto simp add: comps_def E_new_def)
      then show ?thesis 
        using unite_disjoint_components_by_new_edge[of u E w v]  True  connected_components_member_eq[of u E w] 
              connected_components_member_eq[of v E w] xasms
        by (auto simp add: E_new_def comps_def)
    next
      case False
      hence False: "x = connected_component E u \<union> connected_component E v" by simp
      then show ?thesis using insert_edge_endpoints_same_component[of E_new u v E, OF E_new_def] assms(2)
        by(simp add: comps_def)
    qed
  qed
qed

lemma unequal_components_disjoint: 
"connected_component E u \<noteq> connected_component E v \<Longrightarrow> u \<in> X \<Longrightarrow>
 v \<in> X \<Longrightarrow> connected_component E u \<inter> connected_component E v = {}"
  by (metis Int_emptyI connected_components_member_eq)

lemma finite_verts_finite_no_comps: "finite E \<Longrightarrow> finite X \<Longrightarrow> finite (comps X E)" 
  by (simp add: comps_def)

lemma same_component_after_insert: 
  assumes "u \<in> X" "v \<in> X" "E=E"
  defines "E_new \<equiv> insert {u,v} E"
    shows "connected_component E_new u = connected_component E_new v"
  using connected_components_member_eq[of v E_new u] in_con_comp_insert[of v u E] 
  by (simp add: E_new_def)

text \<open>By adding an edge between two different components, the number of components decreases.\<close>

theorem card_decrease_component_join:
  assumes "connected_component E u \<noteq> connected_component E v" "u \<in> X" "v \<in> X" "finite X" "finite E"
  defines "E_new \<equiv> insert {u,v} E"
  shows   "card (comps X E_new) + 1 = card (comps X E)"
proof-
  have comps:"comps X E_new = comps X E - {connected_component E u,  connected_component E v} \<union> 
                             {connected_component E u \<union> connected_component E v}"
    using new_component_insert_edge assms by simp
  have aa:"connected_component E u \<union> connected_component E v
         \<in> comps X E - {connected_component E u, connected_component E v} \<Longrightarrow>
         connected_component E u \<union> connected_component E v = connected_component E x \<Longrightarrow>
         x \<in> X \<Longrightarrow> False" for x
    using connected_components_member_eq[of u E] in_own_connected_component[of u E]
    by blast
  have bb: "connected_component E u \<union> connected_component E v
    \<in> comps X E - {connected_component E u, connected_component E v} \<Longrightarrow>
    connected_component E u \<union> connected_component E v \<in> connected_component E ` X"
    using  comps_def[of X E] connected_components_member_eq[of v E_new u]  
     in_con_comp_insert[of v u E] E_new_def
    by simp
  have "card (comps X E_new) = card (comps X E - {connected_component E u,  connected_component E v}) + 1"
    using finite_verts_finite_no_comps assms  aa bb comps
    by (fastforce intro: card_insert_disjoint elim: imageE[of "connected_component E u \<union> connected_component E v"
                                       "connected_component E" X])+
  moreover have "card (comps X E - {connected_component E u,  connected_component E v}) = 
                card (comps X E - {connected_component E u}) -1"
    by (simp add: assms(1) assms(2) assms(3) comps_def)
  moreover have "card (comps X E - {connected_component E u}) > 0"
    using assms(1) assms(3) assms(4) assms(5)  
          card_0_eq[of "comps X E - {connected_component E u}"] comps_def[of X E] finite_verts_finite_no_comps[of E X] 
    by fastforce
  moreover have " card (comps X E - {connected_component E u}) = 
                  card (comps X E) -1"
    by (simp add: assms(1) assms(2) assms(3) comps_def)
  moreover have "card (comps X E) > 0" 
    using calculation(3) calculation(4) by linarith
  ultimately show ?thesis by simp
qed

lemma same_component_set_mono: 
"A \<subseteq> B \<Longrightarrow> connected_component A x = connected_component A y \<Longrightarrow>
     connected_component B x = connected_component B y"
  using in_own_connected_component[of x A]
  by (cases "x=y") (auto intro!: connected_components_member_eq in_connected_componentI reachable_subset[of A _ _ B] in_connected_componentE[of x A y])

lemma same_connected_component_SOME:"x \<in> X \<Longrightarrow> connected_component A
 (SOME xa. xa \<in> connected_component A x \<and> xa \<in> X)
 = connected_component A x" 
  using in_own_connected_component some_eq_ex[of "\<lambda> xa. xa \<in> connected_component A x \<and> xa \<in> X"]
  by (force intro!: connected_components_member_eq)

lemma number_of_comps_anti_mono_strict:
  fixes A B
  assumes "B \<subseteq> A" "finite A" "x \<in> X" "connected_component B x \<subset> connected_component A x" "Vs A \<subseteq> X"
          "finite X"
  shows "card (comps X B) > card (comps X A)" 
proof-
  define f where "f = (\<lambda> C. let v = (SOME v. C = connected_component A v \<and> v \<in> X) in connected_component B v)"
  have some_value:"C \<in> (comps X A) \<Longrightarrow> C= connected_component A (SOME v. C = connected_component A v \<and> v \<in> X) \<and> 
                            (SOME v. C = connected_component A v \<and> v \<in> X) \<in> X"
    for C 
    using some_eq_ex[of "\<lambda> v. C = connected_component A v \<and> v \<in> X"]
    by(force simp add: comps_def) 
  have uneq_comps_disj:"C \<in> (comps X A) \<Longrightarrow> D \<in> (comps X A) \<Longrightarrow> C \<noteq> D \<Longrightarrow> f C \<inter> f D = {}" for C D
    unfolding  f_def  Let_def 
    apply(rule unequal_components_disjoint[of _ _ _ UNIV, simplified])
    using some_value[of C] some_value[of D]
          same_component_set_mono[OF assms(1)]
    by blast
  have never_same:"C \<in> (comps X A) \<Longrightarrow> D \<in> (comps X A) \<Longrightarrow> C \<noteq> D \<Longrightarrow> f C \<noteq> f D" for C D
    using uneq_comps_disj[of C D]  connected_component_non_empt by (fastforce simp add:  f_def)
  have img_subs:"f ` (comps X A) \<subseteq>  (comps X B)"
    by (simp add: f_def comps_def image_subsetI some_value)
  obtain v where v_prop:"v \<in> X" "v \<in> connected_component A x" "v \<notin> connected_component B x"
    using assms in_connected_component_in_edges[of _ A x] by force 
  have x_not_in_comp_v: "x \<notin> connected_component B v"
    using connected_components_member_sym v_prop(3) by fastforce
  have "connected_component B x \<in>  f ` (comps X A) \<Longrightarrow>
        connected_component B v \<in>  f ` (comps X A) \<Longrightarrow> False"
    using  connected_components_member_eq[OF v_prop(2)] 
     in_own_connected_component[of v B] same_component_set_mono[OF assms(1)]
      some_value  v_prop(3) f_def  
    by (metis (no_types, lifting) imageE)
  hence not_all_b_comp_chosen:"f ` (comps X A) \<subset> (comps X B)"
    using v_prop(1) assms(3) img_subs by(auto simp add: comps_def)
  have "card (comps X A) = card ( f ` (comps X A))"
    using never_same by (force intro!: sym[OF card_image] simp add: inj_on_def)
  also have "... < card (comps X B)"
    using psubset_card_mono[OF _ not_all_b_comp_chosen] assms
    by(simp add: comps_def)
  finally show ?thesis by simp
qed

lemma number_of_comps_anti_mono:"B \<subseteq> A  \<Longrightarrow> finite B \<Longrightarrow> finite X \<Longrightarrow> card (comps X B) \<ge> card (comps X A)"
  unfolding comps_def
  apply(rule card_inj[where f = "\<lambda> C. (let x = (SOME x. x \<in> C \<and> x \<in> X) in connected_component B x)"])
  subgoal
    using  some_eq_ex[of "\<lambda> x. (x = _ \<or> reachable A _ x) \<and> x \<in> X"] 
    by(fastforce intro!: imageI simp add:  Pi_def connected_component_def Let_def Vs_def)
  subgoal
    unfolding inj_on_def Let_def
    apply simp
    apply (rule, rule)
    subgoal for x y
      apply(subst (2) sym[OF same_connected_component_SOME[of x X A]], simp)
      apply(subst (2) sym[OF   same_connected_component_SOME[of y X A]], simp)
      by (metis (no_types, lifting) con_comp_subset connected_components_member_eq 
          in_connected_componentI2 in_mono)
    done 
  by simp

subsection \<open>Connected Graphs\<close>

definition "Uconnected G = (\<forall> u\<in> Vs G. \<forall> v \<in> Vs G. reachable G u v)"

lemma UconnectedI: "(\<And> u v. u \<in> Vs G \<Longrightarrow> v \<in> Vs G \<Longrightarrow> reachable G u v) \<Longrightarrow>Uconnected G"
  by(auto simp add: Uconnected_def)

lemma UconnectedE: "Uconnected G \<Longrightarrow> 
           ((\<And> u v. u \<in> Vs G \<Longrightarrow> v \<in> Vs G \<Longrightarrow> reachable G u v) \<Longrightarrow>P) \<Longrightarrow> P"
  by(auto simp add: Uconnected_def)

lemma same_comp_Uconnected: 
  "(\<And> u v. u \<in> Vs G \<Longrightarrow> v \<in> Vs G \<Longrightarrow> connected_component G u = connected_component G v)
                            \<Longrightarrow> Uconnected G"
  apply(rule UconnectedI) 
  subgoal for u v
    apply(rule in_connected_componentE[of v G u])
      apply((insert in_own_connected_component[of v G])[1], blast) 
    by (auto intro: Undirected_Set_Graphs.reachable_refl[of v G])
  done  

lemma Uconnected_same_comp: "Uconnected G \<Longrightarrow> u \<in> Vs G 
        \<Longrightarrow> v \<in> Vs G \<Longrightarrow> connected_component G u = connected_component G v"
  using connected_components_member_eq in_connected_componentI
  by(unfold Uconnected_def) fast

lemma connected_component_one_edge:
  assumes "r \<in> e"  "\<exists> u v. {u,v} = e \<and> u \<noteq> v" 
  shows   "Vs {e} = connected_component {e} r"
proof-
  obtain u v where e_split: "e = {u,v}" "u \<noteq> v"
    using assms(2) by auto
  hence "Vs {e} = {u,v}" 
    by (simp add: Vs_def)
  moreover have "connected_component {e} r = {u,v}"
    using assms(1) e_split(2)  calculation e_split(1) in_connected_component_in_edges
    by (fastforce simp add: e_split(1) in_own_connected_component in_con_comp_insert 
        connected_components_member_sym)
  ultimately show ?thesis by auto
qed

lemma Uconnected_def_via_components:
"Uconnected G = ((\<forall> v \<in> Vs G. connected_component G v = Vs G))" 
proof(cases "G = {}")
  case True
  then show ?thesis 
    by (auto intro: UconnectedI vs_member_elim)
next
  case False
  note false = this
  show ?thesis
  proof(cases "G = {{}}")
    case True
    hence "Uconnected G"
      by(auto intro:  UconnectedI simp add: Vs_def )
    moreover have "Vs G = {}"
      using True by(auto simp add: Vs_def)
    ultimately show ?thesis by auto
  next
    case False 
    then obtain e where "e \<in> G" "e \<noteq> {}"
      using false by blast
    then obtain v where "v \<in> Vs G" 
      by blast
    show ?thesis 
    proof(rule, goal_cases)
      case 1
      then show ?case using  in_connected_component_in_edges  
        by(fastforce elim!: UconnectedE intro: in_connected_componentI)
    next
      case 2
      then show ?case 
        using UconnectedE[OF same_comp_Uconnected, of G] 
        by(auto intro!: UconnectedI)
    qed
  qed
qed
end