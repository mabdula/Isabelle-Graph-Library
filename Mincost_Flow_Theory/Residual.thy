section \<open>Residual Graphs\<close>

text \<open>In this file we build a theory related to residual graphs and some of their properties.\<close>

theory Residual
  imports Preliminaries
begin

text \<open>When conducting pen-and-paper proofs on graphs, almost no attention is paid to a 
     suitable formal foundation.
     Usually, a graph is then defined as a set of vertices $V$ connected by edges $E \subseteq V \times V$.
     The important characteristic of this definition is that graph arcs emerge from the vertices. 
     For our aims - formalizing a flow problem by a proof assistant -  this definition turns out to be inapt.
     It is much more useful to first fix a set of pairs denoting directed edges and after that,
     vertices are simply defined as the elements of all pairs.
     Luckily, there is a preexisting theory on those \textit{pair graphs} which is imported above.
     We remark the inability of this formalization to handle vertices without any edge.
     Since the theorems and algorithms we want to prove mostly affect arcs,
     this drawback may be neglected.
     Furthermore, there is already some work done on \textit{arc walks}.
     All algorithms presented in our formalization are based on the notion of an \textit{augmenting path}.
     In an informal setting, vertices are usually considered as the foundation of walks and paths. 
     But regarding flow augmentation on paths, reasoning on walks defined by edges is required.
    \<close>

text \<open>We fix a finite and non-empty set of directed edges.
      Those arcs get assigned some real-valued costs $c$ and non-negative capacities $u$.\<close>

locale flow_network_spec =
multigraph_spec where \<E> = "\<E>::'edge_type set" for \<E> +
fixes \<u>::"'edge_type \<Rightarrow> ereal"

locale flow_network =
 multigraph where \<E> = "\<E>::'edge_type set" +
 flow_network_spec where \<E> = "\<E>::'edge_type set" for \<E> +
 assumes u_non_neg: "\<And> e. \<u> e \<ge> 0"

locale cost_flow_spec = flow_network_spec where \<E> = "\<E>::'edge_type set" for \<E>  + 
  fixes \<c>::"'edge_type \<Rightarrow> real"

context flow_network_spec
begin

definition delta_plus_infty::"'a \<Rightarrow> 'edge_type set" ("\<delta>\<^sup>+\<^sub>\<infinity>") where
    "\<delta>\<^sup>+\<^sub>\<infinity> v = {e. e \<in> \<E> \<and> fst e = v \<and> \<u> e = PInfty}"
                                   
definition delta_minus_infty::"'a \<Rightarrow> 'edge_type set" ("\<delta>\<^sup>-\<^sub>\<infinity>") where
    "\<delta>\<^sup>-\<^sub>\<infinity> v =  {e. e \<in> \<E> \<and> snd e = v \<and> \<u> e = PInfty}"

definition infty_edges ("\<E>\<^sub>\<infinity>") where
 "infty_edges = {e. e \<in> \<E> \<and> \<u> e = PInfty}"
end
context flow_network
begin

lemma finite_infty_edges:"finite (infty_edges)" 
  by(auto intro: finite_E finite_subset[OF _ finite_E] simp add:  infty_edges_def)

lemma infty_edges_in_E: "infty_edges \<subseteq> \<E>"
  using infty_edges_def by force

lemma infty_edges_del: 
 "delta_plus x - delta_plus_infty x = delta_plus x - infty_edges"
 "delta_minus x - delta_minus_infty x = delta_minus x - infty_edges"
 "delta_minus_infty x \<subseteq> infty_edges"
 "delta_plus_infty x \<subseteq> infty_edges"
 "delta_minus_infty x \<subseteq> delta_minus x"
 "delta_plus_infty x \<subseteq> delta_plus x"
  unfolding infty_edges_def delta_plus_def delta_plus_infty_def 
            delta_minus_def delta_minus_infty_def
  by auto

lemma finite_infinite_deltas: "finite (delta_plus_infty x)" "finite (delta_minus_infty x)"
 by (auto simp add:  delta_minus_infty_def  delta_plus_infty_def finite_E)
end
context flow_network_spec
begin

definition flow_non_neg::"('edge_type \<Rightarrow> real) \<Rightarrow> bool" ("_ \<ge>\<^sub>F 0") where
"g \<ge>\<^sub>F 0 \<longleftrightarrow> (\<forall> e \<in> \<E>. g e \<ge> 0)"

text \<open>Outgoing flow for a node.\<close>

definition flow_out::"('edge_type \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
           "flow_out g v =  (\<Sum> e \<in> \<delta>\<^sup>+ v. g e) "

text \<open>Ingoing flow for a node.\<close>

definition flow_in::"('edge_type \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
           "flow_in g v =  (\<Sum> e \<in> \<delta>\<^sup>- v. g e) "

text \<open>Absolute value of a flow.\<close>

definition "Abs g = (\<Sum> e \<in> \<E>. g e)"

text \<open>If a circulation is non-trivial, 
      then there has to be a vertex with strictly positive excess.\<close>
end
context flow_network
begin
lemma Abs_pos_some_node_pos: "Abs g > 0 \<Longrightarrow> g \<ge>\<^sub>F 0 \<Longrightarrow>\<exists> v. flow_out g v > 0 \<and> v \<in> \<V>"
proof(rule ccontr)
  assume c: " 0 < Abs g"  " g \<ge>\<^sub>F 0"
         "\<nexists>v. 0 < flow_out g v \<and> v \<in> \<V>"
  hence  b:"\<forall> e \<in> \<E>. g e \<ge> 0" 
    using flow_non_neg_def by blast
  then obtain e where e_Def:"g e > 0 \<and> e \<in> \<E>" using c(1) unfolding Abs_def 
    by (meson less_le_not_le sum_nonpos)
  hence "flow_out g (fst e) > 0" 
     using b 
    by(auto intro!: ordered_comm_monoid_add_class.sum_pos2 simp add: finite_E flow_out_def delta_plus_def)
  moreover have "(fst e) \<in> \<V>" using e_Def 
    using dVsI(1) dVsI(2) mem_Collect_eq 
     fst_E_V snd_E_V by fastforce
  ultimately show False 
    using c(3) by blast
qed
end
context flow_network_spec
begin
text \<open>The support is the set of all edges with non-zero flow.\<close>

definition "support g = {(e::'edge_type)| e. g e > (0::real) \<and> e \<in> \<E>}"

text \<open>Basically, a flow is a function assigning non-negative reals to edges.
     Then, a vertex's excess is the difference between incoming and outgoing flow.\<close>

definition ex::"('edge_type \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" ("ex\<^bsub>_\<^esub> _")where
"ex\<^bsub>f\<^esub> v = (\<Sum> e \<in> \<delta>\<^sup>- v. f e) - (\<Sum> e \<in> \<delta>\<^sup>+ v. f e)"

text \<open>A circulation is a flow with zero excess everywhere.\<close>

definition is_circ::"('edge_type \<Rightarrow> real) \<Rightarrow> bool" where
"is_circ g = (\<forall> v \<in> \<V>. ex g v = 0)"

lemma is_circI: "(\<And> v. v \<in> \<V> \<Longrightarrow> ex g v = 0) \<Longrightarrow> is_circ g"
  by (auto simp add: is_circ_def)

text \<open>$f$ is a valid $u$-flow iff all flow values assigned by $f$ are below edge capacities $u$.\<close>

definition  isuflow::"('edge_type \<Rightarrow> real) \<Rightarrow> bool" where
"isuflow f \<longleftrightarrow> (\<forall> e \<in> \<E>. f e \<le> \<u> e \<and> f e \<ge> 0)"

lemma isuflowI: "(\<And> e. e \<in> \<E> \<Longrightarrow> f e \<le> \<u> e) \<Longrightarrow>(\<And> e. e \<in> \<E> \<Longrightarrow> f e \<ge> 0) \<Longrightarrow> isuflow f"
  by(auto simp add:isuflow_def)

lemma isuflowE: "isuflow f\<Longrightarrow> ((\<And> e. e \<in> \<E> \<Longrightarrow> f e \<le> \<u> e) \<Longrightarrow>(\<And> e. e \<in> \<E> \<Longrightarrow> f e \<ge> 0) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add:isuflow_def)

text \<open>Of course, we can also impose some constraints on the excesses. 
     A function $b$ returning the desired excess flow for any node is a \textit{balance}.
     Positive balances indicate some kind of supply, whereas negative values display a demand.\<close>

text \<open> Now, we call $f$ a $b$-flow for some balance $b$ iff
\begin{itemize}
\item the constraints on edge capacities are respected, i.e. the flow can indeed be realized in the graph, and
\item the balances (or more concretely) demands and supplies are obeyed to.
\end{itemize}
\<close>

definition isbflow::"('edge_type \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)  \<Rightarrow> bool"  ("_ is _ flow")where
"f is b flow \<longleftrightarrow> (isuflow f \<and> (\<forall> v \<in> \<V> . (- ex f v) = b v))"

text \<open>Unsurprisingly, a balance has somehow to be balanced. 
      This means, that the overall sum of demands and supplies is zero.
      In fact, for invalid balances with non-zero sum no proper flow assignment to edges exists.\<close>

definition "is_balance b = ((\<Sum> v \<in> \<V>. b v) = 0)" 

definition zero_balance::"('a \<Rightarrow> real) \<Rightarrow> bool" where
"zero_balance b = (\<forall> v \<in> \<V>. b v = 0)"

text \<open>We need to talk about paths in the graph alongside which a flow is
 non-negative.\<close>

definition "flowpath (g::'edge_type \<Rightarrow> real) (es::('edge_type list)) \<longleftrightarrow> multigraph_path es \<and>
                          (\<forall> e \<in> set es. g e > 0)"

text \<open>Similarly to other settings we have seen so far, we prove some technical lemmas.\<close>

lemma flowpathI: "es = [] \<Longrightarrow> flowpath g es"
                "awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es)) \<Longrightarrow>
                          (\<forall> e \<in> set es. g e > 0) \<Longrightarrow> es \<noteq> [] \<Longrightarrow> flowpath g es"
  unfolding flowpath_def multigraph_path_def by auto

lemma flowpathE: "flowpath g es \<Longrightarrow> (es = [] \<Longrightarrow> P) \<Longrightarrow>
                                  (es \<noteq> [] \<Longrightarrow>
                      awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es)) \<Longrightarrow>
                          (\<forall> e \<in> set es. g e > 0) \<Longrightarrow> P) \<Longrightarrow>P"
  unfolding flowpath_def multigraph_path_def by auto

lemma flowpathE': "flowpath g es \<Longrightarrow> (es = [] \<Longrightarrow> P) \<Longrightarrow>
                                  (\<And> d ds. es = d#ds \<Longrightarrow>
                      awalk UNIV (fst (hd es)) (map make_pair es) (snd (last es)) \<Longrightarrow>
                          (\<forall> e \<in> set es. g e > 0) \<Longrightarrow> P) \<Longrightarrow>P"
  unfolding flowpath_def multigraph_path_def by (cases es) auto
end
context flow_network
begin
lemma flowpath_intros:
  "flowpath g []"
  "0 < g e \<Longrightarrow> flowpath g [e]"
  "0 < g e \<Longrightarrow> snd e = fst (hd es) \<Longrightarrow> flowpath g es \<Longrightarrow> flowpath g (e # es)"
  subgoal
    unfolding flowpath_def multigraph_path_def by simp
  subgoal 2
    by (simp add: arc_implies_awalk make_pair flowpath_def multigraph_path_def)
  subgoal
    using 2 
    by (auto simp add: arc_implies_awalk make_pair awalk_Cons_iff flowpath_def multigraph_path_def)
  done

lemma flowpath_induct: 
assumes "flowpath x1 x2"
        "(\<And>g. P g [])"
        "(\<And>g e. 0 < g e \<Longrightarrow> P g [e])"
        "(\<And>g e es.0 < g e \<Longrightarrow> snd e = fst (hd es) \<Longrightarrow> flowpath g es \<Longrightarrow> P g es \<Longrightarrow> P g (e # es))"
      shows   "P x1 x2"
proof(rule flowpathE[OF assms(1)], goal_cases)
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
      using  assms(3) assms(4)[of x1 a x2]  flowpathI(2)[of x2 x1]
             awalk_Cons_iff[of _ "(fst (hd (_ # _)))" "make_pair a"]
             awalk_Cons_iff[of _ "prod.snd (make_pair a)"] assms(4)[of x1 a x2] cons
      by(auto intro: assms(4)[of x1 a x2])(simp add: make_pair)
    qed (auto simp add: assms flowpathI(2))
  qed simp 
qed (simp add: assms(2))

lemma flowpath_simps:
"flowpath a1 a2 =
((\<exists>g. a1 = g \<and> a2 = []) \<or>
 (\<exists>g e. a1 = g \<and> a2 = [e] \<and> 0 < g e) \<or>
 (\<exists>g e es. a1 = g \<and> a2 = e # es \<and> 0 < g e \<and> snd e = fst (hd es) \<and> flowpath g es))"
  by(rule, rule flowpath_induct[of a1 a2], auto intro: flowpathI(1) flowpath_intros(2) flowpath_intros(3))
 
lemma flowpath_cases: 
"flowpath a1 a2 \<Longrightarrow>
(\<And>g. a1 = g \<Longrightarrow> a2 = [] \<Longrightarrow> P) \<Longrightarrow>
(\<And>g e. a1 = g \<Longrightarrow> a2 = [e] \<Longrightarrow> 0 < g e \<Longrightarrow> P) \<Longrightarrow>
(\<And>g e es. a1 = g \<Longrightarrow> a2 = e # es \<Longrightarrow> 0 < g e \<Longrightarrow> snd e = fst (hd es) \<Longrightarrow> flowpath g es \<Longrightarrow> P) \<Longrightarrow>
P"
  using flowpath_simps by metis

text \<open>Let us now take a look at the properties of flowpaths.
We observe a relationship to augmenting paths and some topological statements on connectivity.
\<close>

lemma flow_path_split_left:
  assumes "flowpath g (es@fs)" 
  shows   "flowpath g es"
proof(induction "es@fs" arbitrary: es fs rule: flowpath_induct, goal_cases)
  case (3 g e es fs)
  then show ?case by(cases es) (auto intro: flowpath_intros)
next
  case (4 g e es esa fs)
  then show ?case 
    by (smt (verit, ccfv_SIG) Cons_eq_append_conv hd_append2 flowpath_simps)
qed (auto simp add: assms flowpath_intros)

lemma flow_path_split_right: "flowpath g (es@fs) \<Longrightarrow> flowpath g fs"
proof(induction es)
  case (Cons e es)
  hence a: "flowpath g (e # (es @ fs))" by simp
  from this have  "flowpath g (es @ fs)"
    by (metis list.distinct(1) list.sel(3) flowpath_simps)
  then show ?case using Cons by simp
qed simp

lemma flow_path_append:
  assumes "flowpath g es" 
  shows   "es \<noteq>[] \<Longrightarrow>flowpath g fs \<Longrightarrow> snd(last es) = fst (hd fs) \<Longrightarrow>flowpath g (es@fs)"
proof(induction es rule: flowpath_induct, goal_cases)
  case (4 g e es)
  then show ?case 
    using  flowpath_intros(3)
    by(cases es) auto
qed (auto simp add: flowpath_intros assms)
end

context flow_network_spec
begin


subsection \<open>Residual Arcs\<close>

text \<open>An intuitive ad-hoc approach for finding a flow meeting certain constraints is to search for paths 
     and then assigning some flow to the edges involved.
     This naive approach is flawed due to the absence of some kind of error correction:
     If we pushed flow from $u$ to $v$  then we can also push 
     some ``virtual'' units of flow from $v$ to $u$
     by undoing the flow in the opposite direction. 
     For making this precise, we introduce the notion of residual arcs.
\<close>

text \<open>For any original edge we have two residual edges: 
      The \textit{forward} edge from $u$ to $v$ just wraps the pair $(u, v)$, 
      whereas a \textit{backward} edge points from $v$ to $u$.
     The Isabelle constructors $F$ and $B$ indicate this difference.\<close>

datatype 'type Redge = is_forward: F 'type | is_backward: B 'type

lemma F_and_B_inj_on: "inj_on F X"  "inj_on B X" 
  by(auto intro: inj_onI)

text \<open>Between vertices $u$ and $v$ there might be up to four residual arcs.
     In fact, this makes the residual graph a multigraph. 
     Note the difference between $(u,v)$ (original edge), $F (u,v)$ 
     (forward-pointing residual edge from $u$ to $v$) and $B (u, v)$ (a backward residual arc).
In common literature the residual graph w.r.t. to some flow $f$ is usually denoted by $G_f.$
\<close>

text \<open>We can obtain heads and tails of arcs.\<close>

fun fstv::"'edge_type Redge \<Rightarrow> 'a" where 
    "fstv (F e) = fst e"|
    "fstv (B e) = snd e"

fun sndv::"'edge_type Redge \<Rightarrow> 'a" where 
    "sndv (F e) = snd e"|
    "sndv (B e) = fst e"

text \<open>Similarly, we introduce the notion of residual capacities. 
     The capacity of a residual edge w.r.t. some current flow $f$ 
     is exactly the remaining flow that could be pushed through $e$ in addition to $f$.
     For backward arcs this is the amount of flow that can be cancelled by
     abrogating the assignment due to $f$.\<close>

fun rcap::"('edge_type \<Rightarrow> real) \<Rightarrow> 'edge_type Redge \<Rightarrow> ereal" ("\<uu>\<^bsub>_\<^esub>_") where 
"\<uu>\<^bsub>f\<^esub> (F e) = \<u> e - f e"|
"\<uu>\<^bsub>f\<^esub> (B e) = f e"

text \<open>Two cases regarding residual edges.\<close>

lemma redge_pair_cases: "(\<And> ee. e = F ee \<Longrightarrow> P e) \<Longrightarrow>
                        (\<And> ee. e = B ee  \<Longrightarrow> P e)
                         \<Longrightarrow> P e" 
  by(cases e, auto)

text \<open>We can refer to the original edge where the residual arc emerges from.\<close>

fun oedge::"'edge_type Redge \<Rightarrow> 'edge_type" where
 "oedge (F e) = e"|
 "oedge (B e) = e"

lemma oedge_simps'[simp]: "oedge (F e) = e" "oedge (B e) =  e"
  by auto

lemma oedge_both_redges_image: "oedge ` {F e, B e} = {e}"
  by  auto

text \<open>We can also generate regular arcs just by omitting the constructors.
     Those are not necessarily contained in $\mathcal{E}$.\<close>

fun to_vertex_pair::"'edge_type Redge \<Rightarrow> 'a \<times> 'a" where
 "to_vertex_pair (F e) = make_pair e"|     
 "to_vertex_pair (B e) = prod.swap (make_pair e)"
end

context flow_network
begin

lemma to_vertex_pair_fst_snd: "to_vertex_pair e = (fstv e, sndv e)"
  by(cases e) (auto simp add: make_pair')

lemma to_vertex_pair_same_vertex:"{prod.fst (to_vertex_pair e), prod.snd (to_vertex_pair e)} = {fstv e, sndv e}"
  using fst_conv fstv.simps snd_conv sndv.simps to_vertex_pair.elims 
  by (cases e) (auto simp add: make_pair')

lemma fstv_in_verts: "e \<in>  E \<Longrightarrow> fstv e \<in> dVs (to_vertex_pair ` E)"
  unfolding dVs_def
  apply(rule UnionI[of "{prod.fst (to_vertex_pair e), prod.snd (to_vertex_pair e)}"])
  by fastforce (simp add: to_vertex_pair_same_vertex)

lemma sndv_in_verts: "e \<in>  E \<Longrightarrow> sndv e \<in> dVs (to_vertex_pair ` E)"
  unfolding dVs_def
  apply(rule UnionI[of "{prod.fst (to_vertex_pair e), prod.snd (to_vertex_pair e)}"])
  by fastforce (simp add: to_vertex_pair_same_vertex)
end
context flow_network_spec
begin

text \<open>For any residual edge, there is a counterpart in the opposite direction.
      A residual arc and its reverse both emerge from the same original edge.\<close>

fun erev::"'edge_type Redge \<Rightarrow> 'edge_type Redge" where
"erev (F e) = (B e)"|
"erev (B e) = (F e)"

lemma erve_erve_id: "erev (erev e) = e"
  by (metis erev.elims erev.simps(1) erev.simps(2))

lemma oedge_and_reversed: "oedge (erev e) = oedge e"
  by (metis erev.elims oedge.simps(1) oedge.simps(2))

lemma redge_erve_cases: "d = erev e \<Longrightarrow> (\<And> a. e = F a \<Longrightarrow> d = B a \<Longrightarrow>P) \<Longrightarrow>
                             (\<And> a. e = B a \<Longrightarrow> d = F a \<Longrightarrow>P) \<Longrightarrow> P" for e d P
  by(cases e, auto)

lemma redge_erve_cases_with_e: "d = erev e \<Longrightarrow> (\<And> a. e = F a \<Longrightarrow> d = B a \<Longrightarrow>P e d) \<Longrightarrow>
                             (\<And> a. e = B a \<Longrightarrow> d = F a \<Longrightarrow>P e d) \<Longrightarrow> P e d" for e d P
  by(cases e, auto)

lemma inj_erev: "inj_on erev A" for A 
     using  erve_erve_id inj_on_def by metis 

lemma redge_case_flip: "f (case e of F a \<Rightarrow> x a  |
                                     B a \<Rightarrow> y a) =
                        (case e of F a \<Rightarrow> f (x a) |
                                   B a \<Rightarrow> f (y a)) " 
  by (simp add: Redge.case_eq_if split_beta)
end
context flow_network
begin
lemma to_vertex_pair_erev_swap:"to_vertex_pair \<circ> erev = prod.swap  \<circ> to_vertex_pair"
  by(auto intro!: ext intro: redge_erve_cases_with_e[OF refl ] simp del: make_pair')

lemma to_vertex_pair_erev_swap_arg:"to_vertex_pair (erev e)= prod.swap  (to_vertex_pair e)"
  by( auto intro!: ext intro: erev.induct simp del: make_pair') 

lemma rev_erev_swap:"(map prod.swap (rev (map to_vertex_pair pp)))
       = (map to_vertex_pair (rev (map erev pp)))"
  by(simp add: rev_map to_vertex_pair_erev_swap)

lemma rev_prepath_fst_to_lst:"pp \<noteq> [] \<Longrightarrow> fstv (hd (map erev (rev pp))) = sndv (last pp)"
  by(auto intro: erev.induct[of  _ "(last pp)"]simp add: sym[OF rev_map] hd_rev last_map)

lemma rev_prepath_lst_to_fst:"pp \<noteq> [] \<Longrightarrow> sndv (last (map erev (rev pp))) = fstv (hd pp)"
  by(auto intro: erev.induct[of  _ "(hd pp)"] simp add:  sym[OF rev_map] last_rev hd_map)
end
context flow_network_spec
begin
text \<open>The set of residual arcs for the fixed set of edges $\mathcal{E}$.\<close>

definition "\<EE> = {e. \<exists> d. e = F d \<and> d \<in> \<E>} \<union>
                {e. \<exists> d. e = B d \<and> d \<in> \<E>}"

lemma Residuals_project_erev_sym:"e \<in> {e |e. e \<in> \<EE> \<and> P( oedge e )}
      \<longleftrightarrow> erev e \<in> {e |e. e \<in> \<EE> \<and> P( oedge e )}"
  by(induction e rule: erev.induct) (auto simp add: \<EE>_def)

lemma oedge_on_\<EE>: "oedge ` \<EE> = \<E>"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 e)
  then obtain d where "e = oedge d" "d \<in> \<EE>" by auto
  moreover then obtain a where "d = F a \<and> a \<in> \<E> \<or>
        d = B a \<and> a \<in> \<E>"
        unfolding \<EE>_def  by auto
 ultimately show ?case by auto
next
  case (2 e)
  moreover then obtain a where "e = a" by force
  moreover hence "F a \<in> \<EE>"and "B a \<in> \<EE>"
    using 2 \<EE>_def by blast+
  moreover hence  "oedge (F a) \<in> oedge ` \<EE>"and "oedge (B a) \<in> oedge `\<EE>"
    by blast+
  ultimately show ?case by simp
qed
end 
context flow_network
begin
lemma finite_\<EE>: "finite \<EE>" 
  unfolding \<EE>_def 
  using finite_img[of \<E> "\<lambda> x. F x"] finite_E  finite_img[of \<E> "\<lambda> x. B ((snd x), (fst x))"] finite_E 
  by auto


text \<open>For valid flows, residual capacities cannot be negative.\<close>

lemma is_flow_rcap_non_neg: 
  assumes "isuflow f"
          "e \<in> \<EE>" 
    shows "rcap f e \<ge> 0"
  using assms  rcap.simps ereal_diff_positive
  unfolding isuflow_def \<EE>_def 
  by (cases e)  auto

lemma o_edge_res: "oedge e \<in> \<E> \<longleftrightarrow> e \<in> \<EE>"
  by(auto intro: redge_pair_cases  oedge.elims[OF refl, of e] simp add: \<EE>_def )
end
context flow_network_spec
begin
text \<open>We define the residual capacity of a path, i.e. formally a list of residual edges.\<close>

definition "Rcap f es = Min (insert PInfty {rc. (\<exists> e.  rc = (rcap f e) \<and> e \<in> es)})"
definition "Rcap_old f es = Min  {rc. (\<exists> e.  rc = (rcap f e) \<and> e \<in> es)}"

lemma Rcap_same: "es \<noteq> {} \<Longrightarrow> finite es \<Longrightarrow> Rcap f es = Rcap_old f es"
  unfolding Rcap_def Rcap_old_def by simp

lemma RcapI: "finite ES \<Longrightarrow> ES \<noteq> {} \<Longrightarrow>
                (\<And> e. e \<in> ES \<Longrightarrow> rcap f e \<ge> th) \<Longrightarrow> Rcap f ES \<ge> th"
    for ES f th unfolding Rcap_def 
    using Min_gr_iff by auto

lemma  Rcap_strictI: "finite ES \<Longrightarrow> ES \<noteq> {} \<Longrightarrow>
                (\<And> e. e \<in> ES \<Longrightarrow> rcap f e > th) \<Longrightarrow> Rcap f ES > th"
    for ES f th unfolding Rcap_def 
  using Min_gr_iff by auto

lemma  Rcap_strictI': "finite ES \<Longrightarrow>
                (\<And> e. e \<in> ES \<Longrightarrow> rcap f e > th) \<Longrightarrow> th < PInfty \<Longrightarrow> Rcap f ES > th"
  for ES f th unfolding Rcap_def 
  by(auto simp add: Min_gr_iff)

lemma Rcap_union: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow>
                             Rcap f A > x \<Longrightarrow> Rcap f B > x \<Longrightarrow> Rcap f (A \<union> B) > x" for f A B x
  apply(subst Rcap_same, simp, simp)
  apply(subst (asm) Rcap_same, simp, simp)+
  unfolding Rcap_old_def 
  by(subst function_union, subst linorder_class.Min_Un, auto)

lemma Rcap_subset: "finite B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow>
                                Rcap f B > x \<Longrightarrow> Rcap f A > x" for f A B x
  apply(subst Rcap_same, simp, simp add: finite_subset)
  apply(subst (asm) Rcap_same, force, simp add: finite_subset) 
  unfolding Rcap_old_def 
  by(rule order.strict_trans2)(auto intro!: Min.subset_imp)
           
text \<open>Set lemmas for working with this definition.\<close>

lemma rcap_extr_head: " \<gamma> \<le> Rcap f (set (e # es))  \<Longrightarrow> \<gamma> \<le> rcap f e"
  apply(subst (asm) Rcap_same, force, simp add: finite_subset) 
  apply(subst  miny(2)[of \<gamma> "rcap f e"], 
        subst Min.in_idem[of "{\<uu>\<^bsub>f\<^esub>ea |ea. ea \<in> set (e # es)}" "rcap f e"])
  using finite_img[of "set (e#es)" "\<lambda> e. rcap f e"]
  unfolding Rcap_old_def by auto

lemma rcap_extr: "e \<in> set es \<Longrightarrow>  \<gamma> \<le> Rcap f (set es)  \<Longrightarrow> \<gamma> \<le> rcap f e"
  by(induction es, simp)
    (metis order_antisym_conv rcap_extr_head set_ConsD set_subset_Cons subsetI)

lemma rcap_extr_non_zero: "e \<in> set es \<Longrightarrow>  set es = ES \<Longrightarrow> 0 < Rcap f ES \<Longrightarrow> 0 < rcap f e"
  by (metis dual_order.refl leD order_less_le rcap_extr)

lemma rcap_exract_single: "es \<noteq>[] \<Longrightarrow> Rcap f (set (e#es)) = min (rcap f e) (Rcap f (set es))"
  apply(subst  Rcap_same, force, simp add: finite_subset)+
  apply(rule trans[of _ " min (Min {\<uu>\<^bsub>f\<^esub>e}) (Rcap_old f (set es))"])
  unfolding Rcap_old_def
  subgoal
    apply(subst sym[OF Lattices_Big.linorder_class.Min_Un[of "{rcap f e}" 
                       "{\<uu>\<^bsub>f\<^esub>ea |ea. ea \<in> set (es)}"]]) 
    by (fastforce intro!: cong[of Min Min])+
  by simp
   
lemma rcap_single: "Rcap f {e} = rcap f e" unfolding Rcap_def by simp

lemma rcap_extr_tail: 
assumes "es \<noteq> []"  "\<gamma> \<le> Rcap f (set (e # es))" 
shows   "\<gamma> \<le> Rcap f (set es)"
proof- 
  have 0: "finite {\<uu>\<^bsub>f\<^esub>e |e. e \<in> set es}" 
    using finite_imageI[of "set es" "rcap f"] by simp
  have 1:"{\<uu>\<^bsub>f\<^esub>e |e. e \<in> set es} \<noteq> {}"
    by (simp add: assms(1))
  hence " Rcap f (set (e#es)) = min (Min {\<uu>\<^bsub>f\<^esub>e |e. e \<in> set es}) (Min {\<uu>\<^bsub>f\<^esub>e})"
    using assms apply(subst  Rcap_same, force, simp add: finite_subset)+ 
    using assms apply(subst  (asm) Rcap_same, force, simp add: finite_subset)
    using Min_Un[of "{\<uu>\<^bsub>f\<^esub>e |e. e \<in> set es}" "{\<uu>\<^bsub>f\<^esub>e}"] 0 1
    unfolding Rcap_old_def 
    using set_img_extract[of es "rcap f" e]
    by (smt (verit, del_insts) Collect_cong empty_iff finite.emptyI finite_insert singletonI)
  hence " Rcap f (set (e#es)) = min (Min {\<uu>\<^bsub>f\<^esub>e |e. e \<in> set es}) \<uu>\<^bsub>f\<^esub>e" by auto
  then show ?thesis 
    using assms apply(subst  Rcap_same, force, simp add: finite_subset)+ 
    using Rcap_old_def assms(2) by force
qed

lemma erev_\<EE>: "e \<in> \<EE> \<Longrightarrow> erev e \<in> \<EE>" for e
  unfolding \<EE>_def by auto

lemma vs_erev: "sndv (erev a) = fstv a" "fstv (erev a) = sndv a" for a
  by(cases rule: erev.cases[of a], simp+)+

lemma inj_erev_general: "inj erev"
  unfolding inj_def
  apply(rule)+
  subgoal for x y
    by(cases rule: erev.cases[of x]) 
                    (cases rule: erev.cases[of y], simp, simp) +
  done


subsection \<open>Residual Reachability\<close>

text \<open>We define the notion of \textit{residual reachability}. 
This means that there is some non-empty list of edges with positive capacity contained in the residual graph.
Edge connectivity is enforced by using the $awalk$ predicate from the theories on pair graphs.
For this we need naked pairs without wrapping constructors.
\<close>

definition resreach::"('edge_type \<Rightarrow> real)   \<Rightarrow>'a \<Rightarrow> 'a \<Rightarrow> bool" where
       "resreach f u v = (\<exists> p. awalk (to_vertex_pair ` \<EE>) u (map to_vertex_pair p) v 
                            \<and> Rcap f (set p) > 0 \<and> p \<noteq> [] \<and> set p \<subseteq> \<EE>)"
end
context flow_network
begin
text \<open>We will use this similarly to an inductive predicate which 
      raises the need for some introduction rules.\<close>

lemma intros_helper: 
"0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> sndv e = u \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> resreach f u v \<Longrightarrow> resreach f (fstv e) v"
 proof-
    assume assm: "0 < \<uu>\<^bsub>f\<^esub>e" "sndv e = u" "e \<in> \<EE>" "resreach f  u v"
    then obtain p where p_prop:"awalk (to_vertex_pair ` \<EE>) u (map to_vertex_pair p) v" 
                        "Rcap f (set p) > 0" "p \<noteq> []" "set p \<subseteq> \<EE>"
      unfolding resreach_def by auto
    have "awalk (to_vertex_pair ` \<EE>) (fstv e) (map to_vertex_pair (e#p)) v" 
      using  arg_cong[of "to_vertex_pair e " "(fstv e, sndv e)" "\<lambda> d. cas (fstv e) (d # map to_vertex_pair p) v"]
             to_vertex_pair_fst_snd  assm cas.simps(2) p_prop fstv_in_verts 
      by (auto simp add: to_vertex_pair_fst_snd awalk_def)
    moreover  have "Rcap f (set (e#p)) > 0"
     using p_prop assm 
     by(cases p)(simp add: Rcap_def, subst rcap_exract_single, auto)
  ultimately show ?thesis     
    using assm p_prop unfolding resreach_def
    by (metis insert_subset list.distinct(1) list.simps(15))
qed

lemma resreach_intros:
  "0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> e \<in> \<EE> \<Longrightarrow>  resreach f  (fstv e) (sndv e)" 
  "0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> sndv e = u \<Longrightarrow>  e \<in> \<EE> \<Longrightarrow> resreach f u v \<Longrightarrow> resreach f (fstv e) v" 
  using intros_helper 
  unfolding resreach_def  awalk_def
  using fstv_in_verts 
  by (intro exI[of _ "[e]"], auto simp add: to_vertex_pair_fst_snd  rcap_single)

lemma vs_to_vertex_pair_pres: "fstv (e) = prod.fst (to_vertex_pair e)"
                       "sndv  e  = prod.snd (to_vertex_pair e)" 
  by (simp add: to_vertex_pair_fst_snd)+

text \<open>An induction rule.\<close>

lemma resreach_induct:
assumes "resreach f  u v"
        "(\<And>f e . 0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> P f  (fstv e) (sndv e))"
        "(\<And>f e u v.  0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow>
                       sndv e = u \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> resreach f  u v \<Longrightarrow> P f  u v \<Longrightarrow> P f  (fstv e) v)"
  shows "P f  u v"
proof-
  obtain p where p_props: "awalk (to_vertex_pair ` \<EE>) u (map to_vertex_pair p) v "
                           "Rcap f (set p) > 0"  "p \<noteq> []" "set p \<subseteq> \<EE>"
    using assms unfolding resreach_def by auto
  from this assms(2)  assms(3) show ?thesis
  proof(induction p arbitrary: u v)
    case Nil
    then show ?case using p_props by simp
  next
    case (Cons e p1)
    note IH = this
    hence  "e \<in> \<EE>" by auto     
    then show ?case 
    proof(cases p1)
      case Nil
      have "P f (fstv e) (sndv e)"
        using IH(3) local.Nil rcap_single  \<open>e \<in> \<EE>\<close> 
        by (auto intro: IH(6))
      moreover have "fstv e = u" using IH(2) unfolding awalk_def using Nil
        by (simp add: to_vertex_pair_fst_snd)
      moreover have "sndv e = v" using IH(2) unfolding awalk_def using Nil 
         by (simp add: to_vertex_pair_fst_snd)
      ultimately show ?thesis by simp
    next
      case (Cons a list)
      have fstve_is_u: "fstv e = u" 
        using IH(2) unfolding awalk_def using cas.simps(2)
        by (metis list.simps(9) prod.exhaust_sel vs_to_vertex_pair_pres(1))
      have 001:"fstv a = sndv e" 
        using IH(2)[simplified list.simps(9)] awalk_Cons_iff[of "(to_vertex_pair ` \<EE>)" u "to_vertex_pair e" "map to_vertex_pair p1" v]  local.Cons
              vs_to_vertex_pair_pres(1)[of a] vs_to_vertex_pair_pres(2)[of e]
              awalk_Cons_iff[of "(to_vertex_pair ` \<EE>)" "sndv e" "to_vertex_pair a" "map to_vertex_pair list" v]
        by force
      have bb: "resreach f (sndv e) v"
          unfolding resreach_def
          using IH(4)  awalk_Cons_iff[ of "(to_vertex_pair ` \<EE>)" "fstv e"  "to_vertex_pair e" "map to_vertex_pair p1" v]
                vs_to_vertex_pair_pres(2)[of e] IH(2)[simplified list.simps(9)] fstve_is_u 
                IH(3) local.Cons  rcap_exract_single[of p1 f e] Cons IH(5) 
          by (force intro!: exI[of _ p1])     
      have 002: "awalk (to_vertex_pair ` \<EE>) (sndv e) (map to_vertex_pair p1) v"
          by (metis IH(2) awalk_Cons_iff list.simps(9) vs_to_vertex_pair_pres(2))
      have aa: "P f (sndv e) v"
          using 002 rcap_exract_single[of list f a] rcap_exract_single[of p1 f e] Cons IH(3)
            IH(5) assms(2) IH(7)  Cons.IH by fastforce
      show ?thesis
        using  fstve_is_u IH rcap_extr_non_zero[of e "e#p1" "set (e#p1)" f] \<open>e \<in> \<EE>\<close> bb  aa 
        by (auto intro: IH(7)[of f e "sndv e"   v])
    qed
    qed
  qed

text\<open>Simplification.\<close>

lemma resreach_simps: "resreach a1 a2 a3 =
((\<exists>f e. a1 = f \<and> a2 = fstv e \<and> a3 = sndv e \<and> 0 < \<uu>\<^bsub>f\<^esub>e \<and> e \<in> \<EE>) \<or>
 (\<exists>f e u v.
     a1 = f \<and>
     a2 = fstv e \<and> a3 = v \<and> 0 < \<uu>\<^bsub>f\<^esub>e \<and> sndv e = u \<and> e \<in> \<EE> \<and> resreach f u v))"
  apply rule
  subgoal
   apply(rule resreach_induct[of a1 a2 a3]) 
    by blast+
  subgoal
    using resreach_intros by auto
  done

lemma 
resreach_cases: "resreach a1 a2 a3 \<Longrightarrow>
(\<And>f e. a1 = f \<Longrightarrow> a2 = fstv e \<Longrightarrow> a3 = sndv e \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> P) \<Longrightarrow>
(\<And>f e u v.
    a1 = f \<Longrightarrow>
    a2 = fstv e \<Longrightarrow>
    a3 = v \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> sndv e = u \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> resreach f u v \<Longrightarrow> P) \<Longrightarrow>
P"
  using  resreach_induct[of a1 a2 a3 ]
  by (metis resreach_simps)

lemma resreach_app_single': 
  assumes "resreach f u v"
  shows   "rcap f e > 0 \<Longrightarrow> v = fstv e \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> resreach  f u (sndv e)"
  by(induction rule: resreach_induct[OF assms])
    (auto simp add: resreach_intros(1) resreach_intros(2))
end
context flow_network_spec
begin
subsection \<open>Cuts\<close>

text \<open>In general a \textit{cut} $(A, \mathcal{V} \setminus A)$ is a partition of $\mathcal{V}$.\<close>

text \<open>The \textit{residual cut} w.r.t. $f$ and $v$ is anything that is reachable from $v$
           in the residual graph defined by $f$\<close>

definition "Rescut f v = insert v {u. resreach f v u}"
end
context flow_network
begin
text \<open>After that, let's look a some properties of the rescut.\<close>

lemma Rescut_around_in_V:
  assumes "v \<in> \<V>"
  shows " Rescut f v \<subseteq> \<V>"
proof
  fix x
  assume asm:"x \<in> Rescut f v " 
  show " x \<in> \<V>"
  proof(cases "x \<noteq> v")
    case True
    have aa:"resreach f v x" using asm True unfolding Rescut_def by simp
    hence "x \<in> \<V>"
      apply(induction rule: resreach_induct[OF aa])
      unfolding \<EE>_def dVs_def 
     by(cases rule: redge_pair_cases) (auto simp add: make_pair')
    then show ?thesis by simp
  next
    case False
    show ?thesis
      using False assms by blast
  qed 
qed
end
context flow_network_spec
begin
text \<open>The capacity of a cut $(X, \mathcal{E} \setminus X)$ is the accumulated capacity of all leaving edges.\<close>

definition "Cap X = (\<Sum> e \<in> \<Delta>\<^sup>+ X. \<u> e)"
end
context flow_network
begin
text \<open>A variant of the flow value lemma:
     The sum of balances within a set of vertices equals the difference of outgoing and incoming flow.
We prove this by expanding the definition of excess flow and subsequent rearranging of summations.
Any flow $f \; e$ relating to an inner edge of $X$ gets cancelled and just the crossing edges survive.
\<close>

theorem flow_value:
  assumes "f is b flow" 
          "X \<subseteq> \<V>" 
  shows   "(\<Sum> v \<in> X. b v) = (\<Sum> e \<in> \<Delta>\<^sup>+ X. f e) - (\<Sum> e \<in> \<Delta>\<^sup>- X. f e)"
proof-
  have b_is_ex: "\<forall> v \<in> X. b v = -ex f v" 
    using assms unfolding isbflow_def by auto
  hence 1:"(\<Sum> v \<in> X. b v) = (\<Sum> v \<in> X. -ex f v)" by simp
  also have  2:"... =  (\<Sum> v \<in> X.  (\<Sum> e \<in> \<delta>\<^sup>+ v. f e) -  (\<Sum> e \<in> \<delta>\<^sup>- v. f e))" 
    unfolding ex_def by force
  also have  3:"... = (\<Sum> v \<in> X.  (\<Sum> e \<in> \<delta>\<^sup>+ v. f e)) - (\<Sum> v \<in> X.  (\<Sum> e \<in> \<delta>\<^sup>- v. f e))" 
    by (simp add: sum_subtractf)
  have 4:"finite X" 
    using \<V>_finite assms(2) infinite_super by blast
  hence 5:"(\<Sum> v \<in> X.  (\<Sum> e \<in> \<delta>\<^sup>+ v. f e)) = (\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>+ v). f e)"
    using disjoint_multiple_sum[of X  "\<delta>\<^sup>+" f] x_not_y_out_es_not_same 
          delta_plus_finite assms(2) by force
  have 6:"\<Union> (\<delta>\<^sup>+ ` X) = 
           (\<Union> (\<delta>\<^sup>+ ` X) \<inter> In_edges X) \<union> (\<Union> (\<delta>\<^sup>+ ` X) - In_edges X)" by blast
  moreover have 7:"finite ((\<Union> (\<delta>\<^sup>+ ` X) \<inter> In_edges X))"
    using \<open>finite X\<close> assms(2) delta_plus_finite by blast
  moreover have 8:"finite ((\<Union> (\<delta>\<^sup>+ ` X) - In_edges X))"
    using \<open>finite X\<close> assms(2) delta_plus_finite by blast
  ultimately have  9:"(\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>+ v). f e) = 
        (\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>+ v) \<inter> In_edges X. f e) +
        (\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>+ v) - In_edges X. f e)"
    using sum.union_disjoint[of "(\<Union> (\<delta>\<^sup>+ ` X) \<inter> In_edges X)" "(\<Union> (\<delta>\<^sup>+ ` X) - In_edges X)"]
    by force
  have 09: "In_edges X \<subseteq> \<Union> (\<delta>\<^sup>+ ` X) \<inter> In_edges X"
   proof
    fix e 
    assume assm: "e \<in> In_edges X"
    hence "\<exists> x. x \<in> X \<and> e \<in> \<delta>\<^sup>+ x" 
      unfolding In_edges_def delta_plus_def 
     by fastforce
   hence "e \<in> \<Union> (\<delta>\<^sup>+ ` X)" by blast
   thus "e \<in> \<Union> (\<delta>\<^sup>+ ` X) \<inter> In_edges X" using assm by simp
   qed
  hence 10:" (\<Union> v \<in> X. \<delta>\<^sup>+ v) \<inter> In_edges X = In_edges X" 
    by auto
  have 11: " (\<Union> v \<in> X. \<delta>\<^sup>+ v) - In_edges X = \<Delta>\<^sup>+ X"
    unfolding In_edges_def Delta_plus_def delta_plus_def by auto
  have 12: "(\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>+ v). f e) = (\<Sum> e \<in> \<Delta>\<^sup>+ X. f e) +  (\<Sum> e \<in> In_edges X. f e)" 
    by (simp add: "10" "11" "9")
  have 15:"(\<Sum> v \<in> X.  (\<Sum> e \<in> \<delta>\<^sup>- v. f e)) = (\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>- v). f e)"
    using disjoint_multiple_sum[of X  "\<delta>\<^sup>-" f] x_not_y_in_es_not_same 
          delta_minus_finite assms(2)  "4" by blast
  have 16:"\<Union> (\<delta>\<^sup>- ` X) = 
           (\<Union> (\<delta>\<^sup>- ` X) \<inter> In_edges X) \<union> (\<Union> (\<delta>\<^sup>- ` X) - In_edges X)" by blast
  moreover have 17:"finite ((\<Union> (\<delta>\<^sup>- ` X) \<inter> In_edges X))"
    using \<open>finite X\<close> assms(2) delta_minus_finite by blast
  moreover have 18:"finite ((\<Union> (\<delta>\<^sup>- ` X) - In_edges X))"
    using \<open>finite X\<close> assms(2) delta_minus_finite by blast
  ultimately have  19:"(\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>- v). f e) = 
        (\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>- v) \<inter> In_edges X. f e) +
        (\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>- v) - In_edges X. f e)"
    using sum.union_disjoint[of "(\<Union> (\<delta>\<^sup>- ` X) \<inter> In_edges X)" "(\<Union> (\<delta>\<^sup>- ` X) - In_edges X)"]
    by force
  have 20: "In_edges X \<subseteq> \<Union> (\<delta>\<^sup>- ` X) \<inter> In_edges X"
  proof
    fix e 
    assume assm: "e \<in> In_edges X"
    hence "\<exists> x. x \<in> X \<and> e \<in> \<delta>\<^sup>- x" unfolding In_edges_def delta_minus_def 
     by fastforce
   hence "e \<in> \<Union> (\<delta>\<^sup>- ` X)" by blast
   thus "e \<in> \<Union> (\<delta>\<^sup>- ` X) \<inter> In_edges X" using assm by simp
 qed
  hence 110:" (\<Union> v \<in> X. \<delta>\<^sup>- v) \<inter> In_edges X = In_edges X" by auto
  have 111: " (\<Union> v \<in> X. \<delta>\<^sup>- v) - In_edges X = \<Delta>\<^sup>- X"
    unfolding In_edges_def Delta_minus_def delta_minus_def by auto
  have 112: "(\<Sum> e \<in> (\<Union> v \<in> X. \<delta>\<^sup>- v). f e) = (\<Sum> e \<in> \<Delta>\<^sup>- X. f e) +  (\<Sum> e \<in> In_edges X. f e)" 
    by (simp add: "110" "111" "19")
  have "(\<Sum> v \<in> X.  (\<Sum> e \<in> \<delta>\<^sup>+ v. f e)) - (\<Sum> v \<in> X.  (\<Sum> e \<in> \<delta>\<^sup>- v. f e)) =
         ((\<Sum> e \<in> \<Delta>\<^sup>+ X. f e) +  (\<Sum> e \<in> In_edges X. f e)) - 
         ((\<Sum> e \<in> \<Delta>\<^sup>- X. f e) +  (\<Sum> e \<in> In_edges X. f e))"
    using "15" "5" 12 112 by presburger
  also have "... = (\<Sum> e \<in> \<Delta>\<^sup>+ X. f e) -  (\<Sum> e \<in> \<Delta>\<^sup>- X. f e) " 
    by fastforce
  thus ?thesis 
    using "1" "2" "3" calculation by presburger
qed

corollary uflow_zero_total_excess:
  assumes "isuflow f"
  shows "(\<Sum> v \<in> \<V>. ex f v) = 0"
  using flow_value[of f "\<lambda> v. - ex f v" \<V>, simplified  isbflow_def assms sum_negf, simplified ]
        Delta_minus_univ_empty Delta_plus_univ_empty by simp

text \<open>From this we know that the sum of balances within $X$ is bounded by the cut capacity
     of $(X, \mathcal{E} \setminus X)$.\<close>

lemma flow_cross_cut_less_cap:"isuflow f \<Longrightarrow>  sum f (\<Delta>\<^sup>+ X) \<le> Cap X"
  unfolding Delta_plus_def Cap_def isuflow_def 
  by (metis (no_types, lifting) CollectD case_prodE sum_mono)

lemma sum_crossing_out_pos: "isuflow f \<Longrightarrow> sum f (\<Delta>\<^sup>+ X) \<ge> 0 "
  unfolding Delta_plus_def isuflow_def 
  by (metis (no_types, lifting) case_prodE mem_Collect_eq sum_nonneg)

lemma sum_crossing_in_pos: "isuflow f \<Longrightarrow> sum f (\<Delta>\<^sup>- X) \<ge> 0 "
  unfolding Delta_minus_def isuflow_def 
  by (metis (no_types, lifting) case_prodE mem_Collect_eq sum_nonneg)

corollary flow_less_cut: "f is b flow \<Longrightarrow> X \<subseteq> \<V> \<Longrightarrow> sum b X \<le> Cap X"
  using  isbflow_def[of f b] flow_cross_cut_less_cap [of f X]
         flow_value[of f  b X] sum_crossing_in_pos[of f X] 
  by (smt (verit, best) dual_order.trans le_ereal_le sum.cong sum_ereal verit_comp_simplify1(2))

text \<open>Furthermore, we observe that for the residual cut around a vertex, no incoming edge can carry any flow.
     Otherwise, the was an activated residual edge in the opposite direction 
     which contradicts assuming an ingoing edge.\<close>

theorem rescut_ingoing_zero:
  assumes "f is b flow"
  shows   "sum f (\<Delta>\<^sup>- (Rescut f v)) = 0"
  proof(rule ccontr)
    assume assm: "sum f (\<Delta>\<^sup>- (Rescut f v)) \<noteq> 0"
    have "sum f (\<Delta>\<^sup>- (Rescut f v)) > 0" 
      using sum_crossing_in_pos[of f "Rescut f v"]
      using assm assms isbflow_def by auto
    then obtain e where "e \<in> \<Delta>\<^sup>- (Rescut f v)\<and> f e > 0"
      by (meson linorder_not_less sum_nonpos)
    hence "fst e \<notin> (Rescut f v) \<and> snd e \<in> (Rescut f v) \<and> f e > 0" 
      using Delta_minus_def by force
    hence a:"rcap f (B e) > 0" and "e \<in> \<E>"
      using Delta_minus_def \<open>e \<in> \<Delta>\<^sup>- (Rescut f v) \<and> 0 < f e\<close> by auto
    have "resreach f v (snd e)" 
      using \<open>e \<in> \<E>\<close> \<open>fst e \<notin> Rescut f v \<and> snd e \<in> Rescut f v \<and> 0 < f e\<close> a
          fstv.simps(2)[of e]  Rescut_def[of f v]
          o_edge_res[of "(B e)"] oedge.simps(2)[of e] 
          resreach_intros(1)[of f "(B e)"] sndv.simps(2)[of e] 
      by auto
    hence "resreach f v (fst e)" using a 
     using \<open>e \<in> \<E>\<close> fstv.simps(2)[of e] o_edge_res[of "(B e)"]
          oedge.simps(2)[of e] 
          resreach_app_single'[of f v "snd e" ] sndv.simps(2)[of e] by force
    hence "fst e \<in> Rescut f v" 
      by (simp add: Rescut_def)
    thus False 
      by (simp add: \<open>fst e \<notin> Rescut f v \<and> snd e \<in> Rescut f v \<and> 0 < f e\<close>)
  qed

corollary rescut_all_edges_sat:
  assumes "f is b flow"
          "  Rescut f v \<subseteq> \<V>"
  shows "sum b (Rescut f v) = sum f (\<Delta>\<^sup>+ (Rescut f v))"
    using flow_value[of f b "(Rescut f v)"]  assms
    by (simp add: rescut_ingoing_zero)

text \<open> We also obtain that the sum of outgoing flow equals the capacity for any rescut.\<close>

theorem rescut_outgoing_cap:
  assumes "f is b flow"
          "(Rescut f v) \<subseteq> \<V>"
  shows   "sum f (\<Delta>\<^sup>+ (Rescut f v)) = Cap (Rescut f v)"
proof(rule ccontr)
    assume "(\<Sum>x\<in>\<Delta>\<^sup>+ (Rescut f v). ereal (f x)) \<noteq> Cap (Rescut f v) "
    hence "sum f (\<Delta>\<^sup>+ (Rescut f v)) < Cap (Rescut f v)"
      using assms(1) assms(2) flow_less_cut[of f b "Rescut f v"]  less_eq_ereal_def 
            rescut_all_edges_sat[of f b v] sum_ereal[of f "(\<Delta>\<^sup>+ (Rescut f v))"] by simp
    then obtain e where "e \<in> \<Delta>\<^sup>+ (Rescut f v)\<and> f e < \<u> e"
      by (metis Cap_def linorder_not_less sum_ereal sum_mono)
    hence "fst e \<in> (Rescut f v) \<and> snd e \<notin> (Rescut f v) \<and> f e < \<u> e" 
      using Delta_plus_def by force
    hence a:"rcap f (F e) > 0" "e \<in> \<E>"
      using Delta_plus_def \<open>e \<in> \<Delta>\<^sup>+ (Rescut f v) \<and> f e < \<u> e\<close> 
      by (auto simp add: ereal_diff_gr0) 
    have 000: "(fst e) \<in> Rescut f v"
      using \<open>fst e \<in> Rescut f v \<and> snd e \<notin> Rescut f v \<and> f e < \<u> e\<close> a(1) a(2)  Rescut_def[of f v] 
      by simp
    moreover have fsstev:"fst e \<noteq> v" 
      using  \<open>fst e \<in> Rescut f v \<and> snd e \<notin> Rescut f v \<and> f e < \<u> e\<close> a(1) a(2)
             o_edge_res prod.exhaust_sel  Rescut_def[of f v] fstv.simps(1)[of e]
             oedge.simps(1)[of e] sndv.simps(1)[of e]
             resreach_intros(1)[of f "F e"]
      by fastforce
    hence "resreach f v (fst e)" using  Rescut_def[of f v]
      using 000 by simp
    hence "resreach f v (snd e)"
      using a(1) a(2) fstv.simps(1)[of e] sndv.simps(1)[of e]
            o_edge_res[of "(F e)"] oedge.simps(1)[of e]
            resreach_app_single'[of f  v "fst e" "F e"] 
      by fastforce
     hence "resreach f v (snd e)" using a 
      using Rescut_def \<open>fst e \<in> Rescut f v \<and> snd e \<notin> Rescut f v \<and> f e < \<u> e\<close> by blast
    hence "snd e \<in> Rescut f v" 
      by (simp add: Rescut_def)
    thus False 
      by (simp add: \<open>fst e \<in> Rescut f v \<and> snd e \<notin> Rescut f v \<and> f e < \<u> e\<close>)
  qed

  text \<open>Our analysis finally implies that for any valid flow
        the sum of balances amounts exactly to the rescut capacity.\<close>

theorem flow_saturates_res_cut:
  assumes "f is b flow"
          "(Rescut f v) \<subseteq> \<V>"
  shows   "sum b (Rescut f v)= Cap (Rescut f v)"
  using assms(1) assms(2) rescut_all_edges_sat rescut_outgoing_cap by auto
end
context flow_network_spec
begin
text \<open>Similarly, we define the Anti-Rescut which is formed out of the residually reaching vertices.\<close>

definition "ARescut f v = insert v {u. resreach f u v}"
end
context flow_network
begin
text \<open>After that, let's look a some properties of the rescut.\<close>

lemma ARescut_around_in_V:
  assumes "v \<in> \<V>"
  shows " ARescut f v \<subseteq> \<V>"
proof
  fix x
  assume asm:"x \<in> ARescut f v " 
  show " x \<in> \<V>"
  proof(cases "x \<noteq> v")
    case True
    have aa:"resreach f x v" using asm True unfolding ARescut_def by simp
    hence "x \<in> \<V>"
      apply(induction  rule: resreach_induct[OF aa])     
      unfolding \<EE>_def dVs_def
      subgoal for f e 
        apply(cases rule: redge_pair_cases[of e]) 
         apply(rule sufficientE[of  "e \<in> {F e |e. e \<in> \<E>}"], simp)
         apply(rule membershipE[of e F "\<lambda> xy. xy \<in> \<E>"], simp) 
        by (auto simp add: make_pair')
      subgoal for f e u v
         apply(cases rule: redge_pair_cases[of e])
         apply(rule sufficientE[of  "e \<in> {F e |e. e \<in> \<E>}"], simp)
         apply(rule membershipE[of e F "\<lambda> xy. xy \<in> \<E>"], simp) 
        by (auto simp add: make_pair')
      done
    then show ?thesis by simp
  next
    case False
    thus ?thesis using assms by blast
  qed 
qed

lemma finite_Rescut: "x \<in> \<V> \<Longrightarrow> finite (Rescut f x)"
  by (meson Rescut_around_in_V \<V>_finite rev_finite_subset)

lemma finite_ARescut: "x \<in> \<V> \<Longrightarrow> finite (ARescut f x)"
  by (meson ARescut_around_in_V \<V>_finite rev_finite_subset)

lemma cardV_0:"card \<V> > 0" 
  by (simp add: E_not_empty \<V>_finite card_gt_0_iff)
end
context flow_network_spec
begin
definition "ACap X = (\<Sum> e \<in> \<Delta>\<^sup>- X. \<u> e)"
end
context flow_network
begin

lemma flow_cross_acut_less_acap:"isuflow f \<Longrightarrow>  sum f (\<Delta>\<^sup>- X) \<le> ACap X"
  unfolding Delta_minus_def ACap_def isuflow_def 
  by (metis (no_types, lifting) CollectD case_prodE sum_mono)

corollary flow_less_acut: 
  assumes "f is b flow" shows "X \<subseteq> \<V> \<Longrightarrow> sum b X \<ge> - ACap X"
  using  assms flow_cross_acut_less_acap [of f X]
         flow_value[of f  b X] sum_crossing_out_pos[of f X] 
  by (simp add: dual_order.trans minus_leq_flip isbflow_def)

text \<open>Furthermore, we observe that for the residual cut around a vertex, no incoming edge can carry any flow.
     Otherwise, the was an activated residual edge in the opposite direction 
     which contradicts assuming an ingoing edge.\<close>

theorem arescut_outgoing_zero:
  assumes "f is b flow"
  shows   "sum f (\<Delta>\<^sup>+ (ARescut f v)) = 0"
  proof(rule ccontr)
    assume assm: "sum f (\<Delta>\<^sup>+ (ARescut f v)) \<noteq> 0"
    have "sum f (\<Delta>\<^sup>+ (ARescut f v)) > 0" 
      using sum_crossing_out_pos[of f "ARescut f v"]
      using assm assms isbflow_def by auto
    then obtain e where "e \<in> \<Delta>\<^sup>+ (ARescut f v)\<and> f e > 0"
      by (meson linorder_not_less sum_nonpos)
    hence "snd e \<notin> (ARescut f v) \<and> fst e \<in> (ARescut f v) \<and> f e > 0" 
      unfolding Delta_plus_def by auto
    hence a:"rcap f (B e) > 0" and "e \<in> \<E>"
      using Delta_plus_def \<open>e \<in> \<Delta>\<^sup>+ (ARescut f v) \<and> 0 < f e\<close> 
      by auto
    have "resreach f (snd e) v" 
      apply(rule resreach_intros(2)[of f "(B e)" "fst e" v, simplified])
      using \<open>e \<in> \<E>\<close> \<open>snd e \<notin> ARescut f v \<and> fst e \<in> ARescut f v \<and> 0 < f e\<close> a 
          fstv.simps(2) [of e]  ARescut_def[of f v]
          o_edge_res[of "(B e)"] oedge.simps(2)[of e] 
          resreach_intros(2)[of f "(B e)" "fst e" v] resreach_intros(1)[of f "(B e)"]
           sndv.simps(2)[of e]
      by(simp, simp, cases "fst e = v", auto)
    hence "snd e \<in> ARescut f v" 
      by (simp add: ARescut_def)
    thus False 
      by (simp add: \<open>snd e \<notin> ARescut f v \<and> fst e \<in> ARescut f v \<and> 0 < f e\<close>)
  qed

corollary arescut_all_edges_sat:
  assumes "f is b flow"
          "ARescut f v \<subseteq> \<V>"
  shows "sum b (ARescut f v) = - sum f (\<Delta>\<^sup>- (ARescut f v))"
    using flow_value[of f b "(ARescut f v)"]  assms
    by (simp add: arescut_outgoing_zero)

text \<open> We also obtain that the sum of outgoing flow equals the capacity for any rescut.\<close>

theorem arescut_ingoing_cap:
  assumes "f is b flow"
          "(ARescut f v) \<subseteq> \<V>"
  shows   "sum f (\<Delta>\<^sup>- (ARescut f v)) =  ACap (ARescut f v)"
proof(rule ccontr)
    assume asm:"(\<Sum>x\<in>\<Delta>\<^sup>- (ARescut f v). ereal (f x)) \<noteq>  ACap (ARescut f v) "
    have "sum f (\<Delta>\<^sup>- (ARescut f v)) < ACap (ARescut f v)"
      using assms flow_less_acut[of f b "ARescut f v"] asm
            arescut_all_edges_sat[of f b v, OF assms] sum_ereal[of b "((ARescut f v))"] 
             ereal_uminus_le_reorder
      by force     
    then obtain e where "e \<in> \<Delta>\<^sup>- (ARescut f v)\<and> f e < \<u> e"
      unfolding ACap_def 
      by (metis linorder_not_le sum_ereal sum_mono)
    hence a0:"fst e \<notin> (ARescut f v) \<and> snd e \<in> (ARescut f v) \<and> f e < \<u> e" 
      using Delta_minus_def by force
    hence a:"rcap f (F e) > 0" "e \<in> \<E>"
      using Delta_minus_def \<open>e \<in> \<Delta>\<^sup>- (ARescut f v) \<and> f e < \<u> e\<close> 
      by(auto simp add: ereal_diff_gr0)
    hence "snd e \<noteq> v \<Longrightarrow> resreach f (fst e) v "
      using resreach_intros(2)[of f "F e" "snd e" v] a0 unfolding ARescut_def \<EE>_def 
      by (metis (no_types, lifting) CollectD \<open>\<lbrakk>0 < \<uu>\<^bsub>f\<^esub>F e; sndv (F e) = snd e; F e \<in> \<EE>; 
            resreach f (snd e) v\<rbrakk> \<Longrightarrow> resreach f (fstv (F e)) v\<close> fstv.simps(1) insertE o_edge_res 
               oedge.simps(1) prod.collapse sndv.simps(1))
    hence "fst e \<in> ARescut f v" 
      using resreach_intros(1)[of f "F e"] a 
      unfolding ARescut_def \<EE>_def
      by (metis (mono_tags, lifting) \<open>\<lbrakk>0 < \<uu>\<^bsub>f\<^esub>F e; F e \<in> \<EE>\<rbrakk> \<Longrightarrow> resreach f (fstv (F e)) 
                 (sndv (F e))\<close> fstv.simps(1) insertCI mem_Collect_eq o_edge_res oedge.simps(1)
                   prod.collapse sndv.simps(1))
    thus False 
      using a0 by blast
  qed

  text \<open>Our analysis finally implies that for any valid flow
        the sum of balances amounts exactly to the rescut capacity.\<close>

theorem flow_saturates_ares_cut:
  assumes "f is b flow"
          "(ARescut f v) \<subseteq> \<V>"
  shows   " - sum b (ARescut f v)= ACap (ARescut f v)"
  using assms arescut_all_edges_sat arescut_ingoing_cap by auto

end

context cost_flow_spec
begin
text \<open>Recall that we introduced costs for the edges by the locale assumptions, 
     and we will now lift this notion to costs of flows.
     For any unit of flow going through an arc,
     our global account is charged by the respective costs assigned to that edge.
     This means that $c$ denotes the per-unit costs of an arc.
     The costs of a flow are obtained by summing over all edges.\<close>

definition "\<C> f = (\<Sum> e \<in> \<E>. (f e) * (\<c> e))"


text \<open>Since graph arcs from $\mathcal{E}$ get some costs assigned, we lift that to residual edges.
     The costs of a residual arc should precisely mirror the effect of using that arc:
     In the \textit{forward} case we push flow through the original edge, so we incur the costs given by $c$.
     On the contrary, using a \textit{backward} edge means cancelling some flow 
     and thus, the costs are reduced according to $c$.
\<close>

fun \<cc>::"'edge_type Redge \<Rightarrow> real" where
"\<cc> (F e) = \<c> e"|
"\<cc> (B e) = - \<c> e"

lemma erev_costs: " \<cc> (erev e) = - \<cc> e" for e
  by(cases rule: erev.cases[of e], auto)
end

locale cost_flow_network= 
flow_network where \<E> = "\<E>::'edge_type set" +
cost_flow_spec where \<E> = "\<E>::'edge_type set" for \<E>
end