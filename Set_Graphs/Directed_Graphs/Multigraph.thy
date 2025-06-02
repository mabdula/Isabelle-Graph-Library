theory Multigraph
  imports Directed_Set_Graphs.Awalk 
begin

locale multigraph_spec =
  fixes \<E>::"'edge_type set"
and fst::"'edge_type \<Rightarrow> 'a"
and snd::"'edge_type \<Rightarrow> 'a"
and make_pair::"'edge_type \<Rightarrow> 'a \<times> 'a"
and create_edge:: "'a \<Rightarrow> 'a \<Rightarrow> 'edge_type"
begin

abbreviation "\<V> \<equiv> dVs (make_pair ` \<E>)"
subsection \<open>Basic Definitions\<close>

definition E_sym::"('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" ("_\<^sup>\<leftrightarrow>") where
  "E_sym E = E \<union> {(u,v) | v u. (v,u) \<in> E}"

text \<open>We define operators for denoting incoming and outgoing arcs of a vertex.\<close>

definition delta_plus::"'a \<Rightarrow> 'edge_type set" ("\<delta>\<^sup>+") where
    "\<delta>\<^sup>+ v = {e. e \<in> \<E> \<and> fst e = v}"
                                   
definition delta_minus::"'a \<Rightarrow> 'edge_type set" ("\<delta>\<^sup>-") where
    "\<delta>\<^sup>- v =  {e. e \<in> \<E> \<and> snd e = v}"

text \<open>Same for sets of vertices.\<close>

definition Delta_plus::"'a set \<Rightarrow>  'edge_type set" ("\<Delta>\<^sup>+") where
    "\<Delta>\<^sup>+ X = {e. e \<in> \<E> \<and> fst e \<in> X \<and> snd e \<notin> X}"

definition Delta_minus::"'a set \<Rightarrow>  'edge_type set" ("\<Delta>\<^sup>-") where
    "\<Delta>\<^sup>- X = {e. e \<in> \<E> \<and> snd e \<in> X \<and> fst e \<notin> X}"

definition In_edges::"'a set \<Rightarrow> 'edge_type set" where
  "In_edges X = {e. e \<in> \<E> \<and> fst e \<in> X \<and> snd e \<in> X}"

definition "multigraph_path  (es::('edge_type list)) \<longleftrightarrow> (es = [] \<or> (es \<noteq> [] \<and>
                      awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es))))"

lemma multigraph_pathI: "es = [] \<Longrightarrow> multigraph_path  es"
                "awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es)) 
                           \<Longrightarrow> es \<noteq> [] \<Longrightarrow> multigraph_path  es"
  unfolding multigraph_path_def by auto

lemma multigraph_pathE: "multigraph_path es \<Longrightarrow> (es = [] \<Longrightarrow> P) \<Longrightarrow>
                                  (es \<noteq> [] \<Longrightarrow>
                      awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es)) \<Longrightarrow> P) \<Longrightarrow>P"
  unfolding multigraph_path_def by auto

lemma multigraph_pathE': "multigraph_path es \<Longrightarrow> (es = [] \<Longrightarrow> P) \<Longrightarrow>
                                  (\<And> d ds. es = d#ds \<Longrightarrow>
                      awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es)) 
                          \<Longrightarrow> P) \<Longrightarrow>P"
  unfolding multigraph_path_def by (cases es) auto

end

locale multigraph = multigraph_spec where \<E> = "\<E>::'edge_type set" for \<E> +
assumes make_pair:"\<And> e x y. fst e = x \<Longrightarrow> snd e = y \<Longrightarrow> make_pair e = (x,y)"
assumes create_edge: "\<And> x y. make_pair (create_edge x y) = (x, y)"
assumes finite_E: "finite \<E>" 
assumes E_not_empty: "\<E> \<noteq> {}"
begin

lemmas make_pair' = make_pair[OF refl refl]

lemma create_edge': "fst (create_edge u v) = u"  "snd (create_edge u v) = v" 
  using create_edge make_pair by force+

lemma make_pair'': "prod.fst (make_pair e) = fst e"  "prod.snd (make_pair e) = snd e" 
                   "prod.fst o make_pair = fst"  "prod.snd o make_pair = snd" 
  using create_edge make_pair by force+

text \<open>As mentioned, vertices $\mathcal{V}$ are defined by the elements involved in the ordered pairs.\<close>

lemma V_non_empt: "\<V> \<noteq> {}" 
  by (simp add: E_not_empty)

lemma fst_E_V:"e \<in> \<E> \<Longrightarrow> fst e \<in> \<V>" 
  by (auto simp add: make_pair')
lemma snd_E_V:"e \<in> \<E> \<Longrightarrow> snd e \<in> \<V>" 
  by (auto simp add: make_pair')


lemma \<V>_finite: "finite \<V>"
  by (simp add: finite_E finite_vertices_iff)

lemma finite_deltas: "finite (delta_plus x)" "finite (delta_minus x)"
 by (auto simp add: delta_plus_def delta_minus_def  finite_E)

lemma Delta_plus_univ_empty: "\<Delta>\<^sup>+ \<V> = {}" 
  by(auto simp add:Delta_plus_def make_pair')

lemma Delta_minus_univ_empty: "\<Delta>\<^sup>- \<V> = {}" 
  by(auto simp add: Delta_minus_def make_pair')

lemma x_not_y_out_es_not_same: 
   "x \<noteq> y \<Longrightarrow> \<delta>\<^sup>+ x \<inter> \<delta>\<^sup>+ y = {}" 
  using  delta_plus_def by auto

lemma x_not_y_in_es_not_same: 
   "x \<noteq> y \<Longrightarrow> \<delta>\<^sup>- x \<inter> \<delta>\<^sup>- y = {}" 
  using  delta_minus_def by auto

lemma delta_plus_finite: "finite (\<delta>\<^sup>+ x)"
  by (simp add: delta_plus_def finite_E)

lemma delta_minus_finite: "finite (\<delta>\<^sup>- x)"
  by (simp add: delta_minus_def finite_E)

lemma multigraph_path_intros:
  "multigraph_path  []"
  "multigraph_path  [e]"
  "snd e = fst (hd es) \<Longrightarrow> multigraph_path  es \<Longrightarrow> multigraph_path (e # es)"
  subgoal
    unfolding multigraph_path_def by simp
  subgoal 2
    by (simp add: arc_implies_awalk make_pair multigraph_path_def )
  subgoal
    using 2 
    by (auto simp add: arc_implies_awalk make_pair awalk_Cons_iff multigraph_path_def )
  done

lemma multigraph_path_induct: 
assumes "multigraph_path x2"
        "(\<And>g. P  [])"
        "(\<And>g e.  P  [e])"
        "(\<And>g e es. snd e = fst (hd es) \<Longrightarrow> multigraph_path  es \<Longrightarrow> P  es \<Longrightarrow> P  (e # es))"
      shows   "P  x2"
proof(rule multigraph_pathE[OF assms(1)], goal_cases)
  case 2
  then show ?case 
  proof(induction x2)
  next
    case (Cons a x2) 
    note cons = this
    then show ?case 
    proof(cases x2)
      case (Cons aa list)
      then show ?thesis 
      using  assms(3) assms(4)[of a x2]  multigraph_pathI(2)[of x2 ]
             awalk_Cons_iff[of _ "(fst (hd (_ # _)))" "make_pair a"]
             awalk_Cons_iff[of _ "prod.snd (make_pair a)"] assms(4)[of a x2] cons
      by(auto intro: assms(4)[of  a x2])(simp add: make_pair)
    qed (auto simp add: assms multigraph_pathI(2))
  qed simp 
qed (simp add: assms(2))

lemma multigraph_path_simps:
"multigraph_path  a2 =
(( a2 = []) \<or>
 (\<exists> e.  a2 = [e] ) \<or>
 (\<exists>e es.  a2 = e # es \<and>  snd e = fst (hd es) \<and> multigraph_path  es))"
  by(rule, rule multigraph_path_induct[of a2], 
          auto intro: multigraph_pathI(1) multigraph_path_intros(2) multigraph_path_intros(3))
 
lemma flowpath_cases: 
"multigraph_path  a2 \<Longrightarrow>
( a2 = [] \<Longrightarrow> P) \<Longrightarrow>
(\<And>e. a2 = [e]\<Longrightarrow> P) \<Longrightarrow>
(\<And> e es. a2 = e # es  \<Longrightarrow> snd e = fst (hd es) \<Longrightarrow> multigraph_path es \<Longrightarrow> P) \<Longrightarrow>
P"
  using multigraph_path_simps by metis

end
end