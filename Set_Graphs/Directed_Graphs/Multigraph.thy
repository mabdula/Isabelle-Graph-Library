(*
  Author: Thomas Ammer
*)

theory Multigraph
  imports Directed_Set_Graphs.Awalk 
begin

provenance human

locale multigraph_spec =
  fixes \<E>::"'edge set"
and fst::"'edge \<Rightarrow> 'a"
and snd::"'edge \<Rightarrow> 'a"
and create_edge:: "'a \<Rightarrow> 'a \<Rightarrow> 'edge"
begin

definition "make_pair e = (fst e, snd e)"

lemmas [code] = make_pair_def

lemma make_pair:"\<And> e x y. \<lbrakk>fst e = x; snd e = y\<rbrakk> \<Longrightarrow> make_pair e = (x,y)"
  by(auto simp add: make_pair_def)

lemma make_pair_function:
"make_pair = (\<lambda> e. (fst e, snd e))"
  by(auto simp add: make_pair_def)

abbreviation "\<V> \<equiv> dVs (make_pair ` \<E>)"
subsection \<open>Basic Definitions\<close>

definition E_sym::"('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" ("_\<^sup>\<leftrightarrow>") where
  "E_sym E = E \<union> {(u,v) | v u. (v,u) \<in> E}"

text \<open>We define operators for denoting incoming and outgoing arcs of a vertex.\<close>

definition delta_plus::"'a \<Rightarrow> 'edge set" ("\<delta>\<^sup>+") where
    "\<delta>\<^sup>+ v = {e. e \<in> \<E> \<and> fst e = v}"
                                   
definition delta_minus::"'a \<Rightarrow> 'edge set" ("\<delta>\<^sup>-") where
    "\<delta>\<^sup>- v =  {e. e \<in> \<E> \<and> snd e = v}"

text \<open>Same for sets of vertices.\<close>

definition Delta_plus::"'a set \<Rightarrow>  'edge set" ("\<Delta>\<^sup>+") where
    "\<Delta>\<^sup>+ X = {e. e \<in> \<E> \<and> fst e \<in> X \<and> snd e \<notin> X}"

definition Delta_minus::"'a set \<Rightarrow>  'edge set" ("\<Delta>\<^sup>-") where
    "\<Delta>\<^sup>- X = {e. e \<in> \<E> \<and> snd e \<in> X \<and> fst e \<notin> X}"

definition In_edges::"'a set \<Rightarrow> 'edge set" where
  "In_edges X = {e. e \<in> \<E> \<and> fst e \<in> X \<and> snd e \<in> X}"

definition "multigraph_path  (es::('edge list)) \<longleftrightarrow> (es = [] \<or> (es \<noteq> [] \<and>
                      awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es))))"

lemma multigraph_pathI: "es = [] \<Longrightarrow> multigraph_path  es"
                "\<lbrakk>awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es)); es \<noteq> []\<rbrakk>
                  \<Longrightarrow> multigraph_path es"
  unfolding multigraph_path_def by auto

lemma multigraph_pathE: "\<lbrakk>multigraph_path es; es = [] \<Longrightarrow> P;
    \<lbrakk>es \<noteq> []; awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es))\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  unfolding multigraph_path_def by auto

lemma multigraph_pathE': "\<lbrakk>multigraph_path es; es = [] \<Longrightarrow> P;
    \<And>d ds. \<lbrakk>es = d#ds; awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es))\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  unfolding multigraph_path_def by (cases es) auto

lemma deltas_in_E: "delta_plus x \<subseteq> \<E>" "delta_minus x \<subseteq> \<E>"
  by(auto simp add: delta_plus_def delta_minus_def)

text \<open>We define operators for denoting the neighbours.\<close>

definition gamma_plus::"'a \<Rightarrow> 'a set" ("\<gamma>\<^sup>+") where
    "\<gamma>\<^sup>+ u = {v | v e.  e \<in> \<E> \<and> fst e = u \<and> snd e = v}"
                                   
definition gamma_minus::"'a \<Rightarrow> 'a set" ("\<gamma>\<^sup>-") where
    "\<gamma>\<^sup>- u = {v | v e.  e \<in> \<E> \<and> fst e = v \<and> snd e = u}"

definition Gamma_plus::"'a set \<Rightarrow> 'a set" ("\<Gamma>\<^sup>+") where
    "\<Gamma>\<^sup>+ X = {v | v e.  e \<in> \<E> \<and> fst e \<in> X \<and> snd e = v \<and> v \<notin> X}"
                                   
definition Gamma_minus::"'a set \<Rightarrow> 'a set" ("\<Gamma>\<^sup>-") where
    "\<Gamma>\<^sup>- X = {v | v e.  e \<in> \<E> \<and> fst e = v \<and> snd e \<in> X \<and> v \<notin> X}"

end

lemma delta_plus_mono:
 "E \<subseteq> F \<Longrightarrow> multigraph_spec.delta_plus E fst x \<subseteq> multigraph_spec.delta_plus F fst x" for fst
  by(auto simp add: multigraph_spec.delta_plus_def)

lemma delta_minus_mono:
 "E \<subseteq> F \<Longrightarrow> multigraph_spec.delta_minus E fst x \<subseteq> multigraph_spec.delta_minus F fst x" for fst
  by(auto simp add: multigraph_spec.delta_minus_def)

lemma in_delta_plusI: 
"\<lbrakk>e \<in> E; fst e = x\<rbrakk> \<Longrightarrow> e \<in> multigraph_spec.delta_plus E fst x" for fst
  by(auto simp add: multigraph_spec.delta_plus_def)

lemma in_delta_plusD: 
"e \<in> multigraph_spec.delta_plus E fst x \<Longrightarrow> e \<in> E"
"e \<in> multigraph_spec.delta_plus E fst x \<Longrightarrow> fst e = x"for fst
  by(auto simp add: multigraph_spec.delta_plus_def)

lemma in_delta_minusI: 
"\<lbrakk>e \<in> E; fst e = x\<rbrakk> \<Longrightarrow> e \<in> multigraph_spec.delta_minus E fst x" for fst
  by(auto simp add: multigraph_spec.delta_minus_def)

lemma in_delta_minusD: 
"e \<in> multigraph_spec.delta_minus E fst x \<Longrightarrow> e \<in> E"
"e \<in> multigraph_spec.delta_minus E fst x \<Longrightarrow> fst e = x"for fst
  by(auto simp add: multigraph_spec.delta_minus_def)

lemma finite_gamma_minus:
  "finite G \<Longrightarrow> finite (multigraph_spec.gamma_minus G fst snd x)" for fst snd
  by(auto simp add: multigraph_spec.gamma_minus_def)

lemma finite_gamma_plus:
  "finite G \<Longrightarrow> finite (multigraph_spec.gamma_plus G fst snd x)" for fst snd
  by(auto simp add: multigraph_spec.gamma_plus_def)

locale multigraph = multigraph_spec where \<E> = "\<E>::'edge set" for \<E> +
assumes fst_create_edge:"\<And> x y. fst (create_edge x y) = x"
assumes snd_create_edge:"\<And> x y. snd (create_edge x y) = y"
assumes finite_E: "finite \<E>" 
assumes E_not_empty: "\<E> \<noteq> {}"
begin

lemma  create_edge: "\<And> x y. make_pair (create_edge x y) = (x, y)"
  by(auto simp add: make_pair_def fst_create_edge snd_create_edge)

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
  "\<lbrakk>snd e = fst (hd es); multigraph_path es\<rbrakk> \<Longrightarrow> multigraph_path (e # es)"
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
        "\<And>g e es. \<lbrakk>snd e = fst (hd es); multigraph_path es; P es\<rbrakk> \<Longrightarrow> P (e # es)"
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
"\<lbrakk>multigraph_path a2; a2 = [] \<Longrightarrow> P; \<And>e. a2 = [e] \<Longrightarrow> P;
  \<And>e es. \<lbrakk>a2 = e # es; snd e = fst (hd es); multigraph_path es\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
P"
  using multigraph_path_simps by metis

end
end