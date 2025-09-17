section \<open>Eliminating Capacities\<close>
theory Hitchcock_Reduction
  imports Cost_Optimality
begin

section \<open>Reduction: Eliminating Capacities from a Flow Network\<close>

subsection \<open>Mixed-Capacity Graphs\<close>

datatype ('a, 'edge_type) hitchcock_wrapper = edge 'edge_type | vertex 'a

fun edge_of where
  "edge_of (edge e) = e"

fun vertex_of where
  "vertex_of (vertex x) = x"

datatype ('a, 'edge_type) hitchcock_edge = outedge 'edge_type | inedge 'edge_type | vtovedge 'edge_type |
  dummy "('a, 'edge_type) hitchcock_wrapper" "('a, 'edge_type) hitchcock_wrapper"

fun get_edge where
  "get_edge (outedge e) = e"|
  "get_edge (inedge e) = e"|
  "get_edge (vtovedge e) = e"

lemma get_vertex_inv: "vertex_of (vertex x) = x" 
  by simp

lemma get_vertex_inv_image:"vertex_of ` (vertex ` X) = X" by force

definition "new_fstv_gen fstv = (\<lambda> e. (case e of inedge e \<Rightarrow> edge e |
                                     outedge e \<Rightarrow> edge e|
                                    vtovedge e \<Rightarrow> vertex (fstv e)|
                                   ( dummy u v) \<Rightarrow> u))"
definition  "new_sndv_gen fstv sndv = (\<lambda> e. (case e of inedge e \<Rightarrow> vertex(fstv e) |
                                     outedge e \<Rightarrow> vertex (sndv e) |
                                    vtovedge e \<Rightarrow> vertex (sndv e)|
                                    (dummy u v) \<Rightarrow> v))"

definition "new_create_edge_gen = (\<lambda> u v. dummy u v)"

definition "new_\<E>1_gen \<E> \<u> = {inedge e| e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}"
definition "new_\<E>2_gen \<E> \<u> = {outedge e| e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u> }"
definition "new_\<E>3_gen \<E> \<u> = {vtovedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u> }"

definition "new_\<c>_gen D fstv \<E> \<u> \<c> = (\<lambda> e'. if e' \<in> new_\<E>1_gen  \<E> \<u>  then 0
                       else if  e' \<in> new_\<E>2_gen \<E> \<u> then \<c> (edge_of (new_fstv_gen fstv e')) 
                       else if e' \<in> new_\<E>3_gen \<E> \<u> then \<c> (get_edge e')
                       else (case e' of dummy _ _  \<Rightarrow> 0 |
                                        inedge _ \<Rightarrow> 0 |
                                        e' \<Rightarrow> if get_edge e' \<in> D then \<c> (get_edge e') else 0))"

definition "new_\<b>_gen fstv \<E> \<u> \<b> = (\<lambda> x'. (case x' of edge e \<Rightarrow> real_of_ereal (\<u> e)
                       | vertex x \<Rightarrow> \<b> x - sum (real_of_ereal o \<u>) 
                        ((multigraph_spec.delta_plus \<E> fstv x) - (flow_network_spec.delta_plus_infty fstv \<E> \<u> x))))"

definition "new_f_gen fstv \<E> \<u>  f = (\<lambda> e'. (let e = edge_of (new_fstv_gen fstv e') in
                               (if e' \<in> new_\<E>1_gen \<E> \<u> then real_of_ereal (\<u> e) - f e
                                else if e' \<in> new_\<E>2_gen \<E> \<u>  then f e else
                                if e' \<in> new_\<E>3_gen \<E> \<u>  then f (get_edge e')
                                else undefined)))"

definition "old_f_gen \<E> \<u> f' = (\<lambda> e. if e \<in> flow_network_spec.infty_edges \<E> \<u> then f' (vtovedge e)
                    else  f' (outedge e))"

theorem reduction_of_mincost_flow_to_hitchcock_general:
  fixes \<c> \<b> D
  assumes "flow_network fstv sndv create_edge (\<u>::'edge_type \<Rightarrow> ereal) \<E>"
  defines "make_pair \<equiv> multigraph_spec.make_pair fstv sndv"
  defines "fstv' \<equiv> new_fstv_gen fstv"
  defines "sndv' \<equiv> new_sndv_gen fstv sndv"
  defines "make_pair' \<equiv> multigraph_spec.make_pair fstv' sndv'"
  defines "create_edge' \<equiv> new_create_edge_gen"
  defines "\<E>1 \<equiv> new_\<E>1_gen \<E> \<u>"
  defines "\<E>2 \<equiv> new_\<E>2_gen \<E> \<u>"
  defines "\<E>3 \<equiv> new_\<E>3_gen \<E> \<u>"
  defines "\<E>' \<equiv> \<E>1 \<union> \<E>2 \<union> \<E>3"
  defines "\<u>' \<equiv> (\<lambda> e. PInfty)"
  defines "\<c>' \<equiv> new_\<c>_gen D fstv \<E> \<u> \<c>"
  defines "\<b>' \<equiv> new_\<b>_gen fstv \<E> \<u> \<b>"
  shows 
    "flow_network fstv' sndv' create_edge' \<u>' \<E>'" (is ?case1) and
    "\<And> f f' . \<lbrakk>flow_network_spec.isbflow fstv sndv  \<E> \<u> f \<b>; f' = new_f_gen fstv \<E> \<u>  f\<rbrakk>
       \<Longrightarrow>flow_network_spec.isbflow fstv' sndv'  \<E>' \<u>' f' \<b>' \<and> (cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f')" 
    (is "\<And> f f' . ?a f f' \<Longrightarrow> ?b f f'  \<Longrightarrow> ?c f f'") and
    "\<And> f f'. \<lbrakk>flow_network_spec.isbflow fstv' sndv' \<E>' \<u>' f' \<b>';
          f = old_f_gen \<E> \<u>  f' \<rbrakk> \<Longrightarrow>
          flow_network_spec.isbflow fstv sndv \<E> \<u> f \<b> 
        \<and> (cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f')"
    (is "\<And> f f'. ?x f f' \<Longrightarrow> ?y f f' \<Longrightarrow> ?z f f'") and
    "has_neg_cycle make_pair' \<E>' \<c>' \<longleftrightarrow> has_neg_infty_cycle make_pair \<E> \<c> \<u>" and
    "\<And> f f' . \<lbrakk> f = old_f_gen \<E> \<u> f'; cost_flow_spec.is_Opt fstv' sndv' \<u>' \<E>' \<c>' \<b>' f'\<rbrakk>
          \<Longrightarrow> cost_flow_spec.is_Opt fstv sndv \<u> \<E> \<c> \<b> f" 
    (is "\<And> f f'.  ?b1 f f'\<Longrightarrow> ?c1 f' \<Longrightarrow> ?d1 f ") and
    "\<And> f f' . \<lbrakk> f' = new_f_gen fstv \<E> \<u> f; cost_flow_spec.is_Opt fstv sndv  \<u> \<E> \<c> \<b> f\<rbrakk>
\<Longrightarrow>  cost_flow_spec.is_Opt fstv' sndv'  \<u>' \<E>' \<c>' \<b>' f'" 
    (is "\<And> f f'.  ?b2 f f'\<Longrightarrow> ?c2 f \<Longrightarrow> ?d3 f' ")
proof-
  note fstv'_def_old = fstv'_def
  note  \<E>1_def_old =  \<E>1_def
  note  \<E>2_def_old =  \<E>2_def
  note  \<E>3_def_old =  \<E>3_def
  have fstv'_def: "fstv' = (\<lambda> e. (case e of inedge e \<Rightarrow> edge e |
                                     outedge e \<Rightarrow> edge e|
                                    vtovedge e \<Rightarrow> vertex (fstv e)|
                                   ( dummy u v) \<Rightarrow> u))"
    by (simp add: fstv'_def new_fstv_gen_def)
  have sndv'_def: "sndv' = (\<lambda> e. (case e of inedge e \<Rightarrow> vertex(fstv e) |
                                     outedge e \<Rightarrow> vertex (sndv e) |
                                    vtovedge e \<Rightarrow> vertex (sndv e)|
                                    (dummy u v) \<Rightarrow> v))" 
    by (simp add: new_sndv_gen_def sndv'_def)
  have make_pair'_def: "make_pair' = (\<lambda> e. (fstv' e, sndv' e))"
    by(auto simp add: assms(2) assms(3) make_pair'_def multigraph_spec.make_pair_def)
  have create_edge'_def: "create_edge' = (\<lambda> u v. dummy u v)"
    by (simp add: create_edge'_def new_create_edge_gen_def)
  have \<E>1_def: "\<E>1 = {inedge e| e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}"
    by (simp add: \<E>1_def new_\<E>1_gen_def)
  have \<E>2_def: "\<E>2 = {outedge e| e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}"
    by (simp add: \<E>2_def new_\<E>2_gen_def)
  have \<E>3_def: "\<E>3 = {vtovedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u>}"
    by (simp add: \<E>3_def new_\<E>3_gen_def)
  have \<c>'_def: "\<c>' = (\<lambda> e'. if e' \<in> \<E>1 then 0
                       else if  e' \<in> \<E>2 then \<c> (edge_of (fstv' e')) 
                       else if e' \<in> \<E>3 then \<c> (get_edge e')
                       else (case e' of dummy _ _  \<Rightarrow> 0 |
                                         inedge _ \<Rightarrow> 0 |
                                        e' \<Rightarrow> if get_edge e' \<in> D then \<c> (get_edge e') else 0))"
    by(unfold \<c>'_def new_\<c>_gen_def new_\<E>1_gen_def new_\<E>2_gen_def new_\<E>3_gen_def
        \<E>1_def \<E>2_def \<E>3_def new_fstv_gen_def fstv'_def) simp
  have \<b>'_def: "\<b>' = (\<lambda> x'. (case x' of edge e \<Rightarrow> real_of_ereal (\<u> e)
                       | vertex x \<Rightarrow> \<b> x - sum (real_of_ereal o \<u>) 
                        ((multigraph_spec.delta_plus \<E> fstv x) 
                    - (flow_network_spec.delta_plus_infty fstv \<E> \<u> x))))"
    unfolding \<b>'_def new_\<b>_gen_def by blast                 
  have u_pos: "\<And> e. \<u> e \<ge> 0" 
    using assms(1) by(auto simp add: flow_network_def flow_network_axioms_def)
  have finites: "finite {inedge e |e .e \<in> \<E>}"
    "finite {outedge e |e. e \<in> \<E>}"
    "finite {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}"
    "finite {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}"
    "finite {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}"
    using assms(1) finite_img[of \<E> inedge]  finite_img[of \<E> outedge] 
      finite_img[of _ vtovedge, OF
        flow_network.finite_infty_edges[OF assms(1)]] 
      finite_subset[of "{inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}"
        "{inedge e|e. e \<in> \<E>}"]
      finite_subset[of "{outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}"
        "{outedge e |e. e \<in> \<E>}"]
      multigraph.finite_E flow_network_def by blast+
  hence finiteE':"finite \<E>'"
    by(auto simp add: \<E>'_def \<E>1_def \<E>2_def \<E>3_def) 
  moreover have nonemptyE': "\<E>' \<noteq> {}"
    using assms(1) 
    by(auto simp add: \<E>'_def \<E>1_def \<E>2_def \<E>3_def flow_network_def multigraph_def
        flow_network_axioms_def flow_network_spec.infty_edges_def)    
  moreover have mgraph':"multigraph fstv' sndv'  create_edge'  \<E>'"
    using assms(1) finiteE' nonemptyE'
    by(auto simp add: flow_network_def multigraph_def fstv'_def sndv'_def make_pair'_def create_edge'_def)   
  ultimately show residual':"flow_network fstv' sndv'  create_edge' \<u>' \<E>'"
    using assms(1) 
    by(auto simp add: flow_network_def \<u>'_def flow_network_axioms_def)
  have cost_flow: "cost_flow_network fstv sndv  create_edge \<u> \<E>"
    by (simp add: assms(1) cost_flow_network.intro)
  have mgraph: "multigraph fstv sndv  create_edge \<E>"
    using assms(1) flow_network_def by blast
  have flow_network: "flow_network fstv sndv  create_edge \<u> \<E>" 
    by (simp add: assms(1))
  have cost_flow': "cost_flow_network fstv' sndv' create_edge' \<u>' \<E>'"
    by (simp add: residual' cost_flow_network.intro)
  have Es_non_inter: "\<E>1 \<inter> \<E>2 = {}"  "\<E>1 \<inter> \<E>3 = {}"  "\<E>2 \<inter> \<E>3 = {}"
    using \<E>1_def \<E>2_def \<E>3_def assms(2) by fastforce+
  show claim1:"\<And> f f' . ?a f f' \<Longrightarrow> ?b f f'  \<Longrightarrow> ?c f f'"
    unfolding new_f_gen_def old_f_gen_def
    unfolding symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
      symmetric[OF fstv'_def_old] 
  proof(goal_cases)
    case (1 f f')
    note case1=this[simplified]
    have ex_b:"\<And> v. v\<in>dVs (make_pair ` \<E>) \<Longrightarrow> - flow_network_spec.ex fstv sndv \<E> f v = \<b> v"
      using case1 by(auto simp add: flow_network_spec.isbflow_def make_pair_def)
    have "e \<in> \<E>' \<Longrightarrow> ereal (f' e) \<le> \<u>' e" for e
      by(simp add: \<E>'_def case1(2) \<u>'_def)
    moreover have "e \<in> \<E>' \<Longrightarrow> 0 \<le> f' e" for e
      using case1(1) fstv'_def ereal_le_real_iff u_pos
      by(auto split: prod.split 
          simp add: \<E>1_def \<E>2_def \<E>'_def case1(2) \<u>'_def flow_network_spec.isbflow_def
          flow_network_spec.isuflow_def Let_def \<E>3_def 
          flow_network_spec.infty_edges_def  u_pos)
    ultimately have isuflow': "flow_network_spec.isuflow \<E>' \<u>' f'"
      unfolding flow_network_spec.isuflow_def by auto
    have a1: "{e. ((\<exists> d. e = inedge d \<and> d \<in> \<E>) \<or>
                (\<exists> d. e = outedge d \<and> d \<in> \<E>)) \<and>
               fstv' e = edge ee} = 
             (if ee \<in> \<E> then { inedge ee , outedge ee} else {})" for ee
      by (auto simp add: fstv'_def)
    have a2: "{e. ((\<exists>ee. e = inedge ee \<and> ee \<in> \<E>) \<or>
                (\<exists>ee. e = outedge ee \<and> ee \<in> \<E>)) \<and>
               sndv' e = edge ee} = 
             {}" for ee
      by (auto simp add: sndv'_def)
    have b'_met:"v\<in>dVs (make_pair' ` \<E>') \<Longrightarrow> - flow_network_spec.ex fstv' sndv' \<E>' f' v = \<b>' v" for v
    proof(goal_cases)
      case 1
      show ?case
      proof(cases v)
        case (edge x1)
        hence empty_simper:" {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}. sndv' e = v}  = {}" 
          by (auto simp add: sndv'_def)
        have x1_in_E:"x1 \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>" 
          using 1 edge by(auto simp add:dVs_def \<E>'_def \<E>1_def \<E>2_def \<E>3_def  make_pair'_def sndv'_def fstv'_def)
        have set_spliter: "{e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
                  {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
                  {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}. fstv' e = v} 
            = {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}. fstv' e = v} \<union>
             {e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}. fstv' e = v} \<union>
             {e \<in> {vtovedge e | e. e \<in>  flow_network_spec.infty_edges \<E> \<u>}. fstv' e = v}" 
          by auto
        have da: "sum g {e. (\<exists>ea. e = inedge ea \<and> ea \<in> \<E> \<and> (ea \<in> \<E> \<longrightarrow> \<u> ea \<noteq> \<infinity>)) \<and> fstv' e = edge x1} +
               sum g {e. (\<exists>ea. e = outedge ea \<and> ea \<in> \<E> \<and> (ea \<in> \<E> \<longrightarrow> \<u> ea \<noteq> \<infinity>)) \<and> fstv' e = edge x1} +
                sum g {e. (\<exists>ea. e = vtovedge ea \<and> ea \<in> \<E> \<and> \<u> ea = \<infinity>) \<and> fstv' e = edge x1} =
                g (inedge x1) + g (outedge x1) " 
          if "\<u> x1 \<noteq> \<infinity>" for g 
        proof-
          have h1:"{e. (\<exists>ea. e = inedge ea \<and> ea \<in> \<E> \<and> (ea \<in> \<E> \<longrightarrow> \<u> ea \<noteq> \<infinity>)) \<and> fstv' e = edge x1} =
                 {inedge x1}"
            using x1_in_E that by (auto simp add: fstv'_def)
          have h2:"sum g
                 {e. (\<exists>ea. e = outedge ea \<and> ea \<in> \<E> \<and> (ea \<in> \<E> \<longrightarrow> \<u> ea \<noteq> \<infinity>)) \<and> fstv' e = edge x1} =
                         g (outedge x1)"
            apply(rule forw_subst[of _ "sum _ {outedge x1}", OF _ ])
            using x1_in_E that
            by (force intro!: cong[of "sum g" _ _ "{_}", OF refl] simp add: fstv'_def)+
          show ?thesis
            apply(rule forw_subst[of "sum _ _" 0])
            using h1 h2 
            by(auto intro: forw_subst[of _ "{}"] simp add: fstv'_def)
        qed  
        have d01: "finite {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
                                 fstv' e = v}"
          "finite {e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
                                 fstv' e = v}"
          "{e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}. fstv' e = v} \<inter>
                    {e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}. fstv' e = v} =
                    {}"
          using finites assms(2) edge
          by(auto intro: da forw_subst[of "sum _ _" 0] forw_subst[of _ "{}"] 
              simp add: flow_network_spec.infty_edges_def)
        have d1:"sum g
          {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {vtovedge e | e . e \<in> flow_network_spec.infty_edges \<E> \<u>}. fstv' e = v} = 
              (if \<u> x1 < PInfty then g (inedge x1) + g (outedge x1)
               else 0)" for g 
          apply(subst set_spliter)
          apply(subst comm_monoid_add_class.sum.union_disjoint)
          using finites  x1_in_E edge comm_monoid_add_class.sum.union_disjoint[OF d01, of g]
          by(auto intro: da simp add: flow_network_spec.infty_edges_def)
        show ?thesis 
          unfolding flow_network_spec.ex_def  multigraph_spec.delta_minus_def
            multigraph_spec.delta_plus_def
          unfolding \<E>'_def \<E>1_def \<E>2_def \<b>'_def \<E>3_def
          apply(simp only: empty_simper)
          using edge x1_in_E  d1[of f'] fstv'_def
          by(auto simp add: fstv'_def case1(2) Let_def \<E>1_def \<E>2_def \<E>3_def)  
      next
        case (vertex x1)
        hence almost_empty_simper:" {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {vtovedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.
             fstv' e = v}
                = {vtovedge e | e. e \<in> flow_network_spec.delta_plus_infty fstv \<E> \<u> x1}" 
          by(auto simp add: vertex flow_network_spec.delta_plus_infty_def
              flow_network_spec.infty_edges_def fstv'_def)
        have x_in_V: "x1 \<in> dVs (make_pair ` \<E>)"
        proof-
          have "vertex x1 \<in> dVs (make_pair' ` \<E>')"
            using "1" vertex by blast
          then obtain a b d where "d \<in> \<E>'" "make_pair' d = (a, b)" "a = vertex x1 \<or> b = vertex x1"
            by(auto simp add: dVs_def) metis+
          thus ?thesis
            using flow_network.infty_edges_in_E[OF assms(1)] 
            by(cases d)
              (auto  intro: multigraph.snd_E_V[OF mgraph]  multigraph.fst_E_V[OF mgraph]
                simp add: \<E>'_def make_pair'_def sndv'_def fstv'_def \<E>1_def \<E>2_def \<E>3_def make_pair_def)
        qed

        have i1: "(get_edge `
            {vtovedge e |e. e \<in> \<E> \<and> fstv e = x1 \<and> \<u> e = \<infinity> }) =
              {e \<in> \<E>. fstv e = x1 \<and> \<u> e = \<infinity>}"
          by (auto simp add: image_def)
        have h0: "(\<Sum>x\<in>{vtovedge e |e. e \<in> \<E> \<and> fstv e = x1 \<and> \<u> e = \<infinity>}. f (get_edge x)) =
                     sum f {e \<in> \<E>. fstv e = x1 \<and> \<u> e = \<infinity>} "
        proof(subst sum_inj_on[of get_edge _ f, simplified, symmetric], goal_cases)
          case 1
          show ?case
          proof(rule inj_onI, goal_cases)
            case (1 x y)
            thus ?case
              by(cases x, all \<open>cases y\<close>) auto
          qed
        qed (simp add: i1)
        have "(\<Sum>x\<in>{vtovedge e |e. e \<in> \<E> \<and> fstv e = x1 \<and> \<u> e = \<infinity>}.
                 if \<exists>e. x = inedge e \<and> e \<in> \<E> \<and> (e \<in> \<E> \<longrightarrow> \<u> e \<noteq> \<infinity>)
                  then real_of_ereal (\<u> (edge_of (fstv' x))) - f (edge_of (fstv' x))
                   else if x \<in> \<E>2 then f (edge_of (fstv' x)) else if x \<in> \<E>3 then f (get_edge x) else undefined) =
               sum f {e \<in> \<E>. fstv e = x1 \<and> \<u> e = \<infinity>}"
          apply(subst sum_if_not_P, force simp add: \<E>2_def \<E>3_def, subst sum_if_not_P)
          by(force simp add: \<E>2_def \<E>3_def sum_if_P flow_network_spec.infty_edges_def
              intro: h0 | subst sum_if_P )+
        hence h1: "sum f' {vtovedge e |e. e \<in> flow_network_spec.delta_plus_infty fstv \<E> \<u> x1} =
              sum f (flow_network_spec.delta_plus_infty fstv \<E> \<u> x1)"
          by(auto simp add:  flow_network_spec.delta_plus_infty_def
              flow_network_spec.infty_edges_def case1(2) \<E>1_def \<E>2_def \<E>3_def Let_def)
        have h2: "sum f' {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u> } \<union>
              {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {vtovedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.  sndv' e = v} = 
            sum f' {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.sndv' e = v} +
           (sum f' {e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}. sndv' e = v} +
            sum f' {e \<in> {vtovedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u>}. sndv' e = v})"
          using finiteE'[simplified \<E>'_def \<E>1_def \<E>2_def \<E>3_def]  assms(2) 
          by(simp add: conj_disj_distribR Collect_disj_eq)
            (subst union_disjoint_triple[simplified Un_assoc]| 
              force simp add: intro: cong[of "sum f'", OF refl])+
        have i4: "(\<lambda>x. edge_of (fstv' x)) ` {outedge e |e. e \<in> \<E> \<and> sndv e = x1} = {e \<in> \<E>. sndv e = x1}"
          by(auto simp add: image_def fstv'_def)
        have i5: "(\<lambda>x. edge_of (fstv' x)) ` {outedge e |e. e \<in> {e \<in> \<E>. \<u> e = PInfty} \<and> sndv e = x1} = 
                    {e \<in> \<E>. sndv e = x1 \<and> \<u> e = PInfty}"
          by(auto simp add: image_def fstv'_def)
        have h3: "(\<Sum>x\<in>{e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
              sndv' e = vertex x1}.
          f (edge_of (fstv' x))) =
          sum f (multigraph_spec.delta_minus \<E> sndv x1 
                 - flow_network_spec.delta_minus_infty sndv \<E> \<u> x1)"
        proof(subst sum_inj_on[of "\<lambda> x. (edge_of (fstv' x))" _ f, simplified, symmetric], goal_cases)
          case 1
          thus ?case
          proof(rule inj_onI, goal_cases)
            case (1 x y)
            thus?case
              by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
          qed
        next
          case 2
          thus ?case
          proof(rule forw_subst[of _ 
                "{outedge e |e. e \<in> \<E> \<and> sndv e = x1} - 
                {outedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u> \<and> sndv e = x1}"], goal_cases)
            case 2
            thus ?case
            proof(subst flow_network_spec.infty_edges_def, 
                subst inj_on_image_set_diff[OF _ Diff_subset], goal_cases)
              case 1
              then show ?case 
              proof(rule  inj_onI, goal_cases)
                case (1 x y)
                thus ?case
                  by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
              qed
            qed  (insert i4 i5, auto simp add: flow_network_spec.delta_minus_infty_def multigraph_spec.delta_minus_def)
          qed (force simp add: sndv'_def)
        qed
        have i6: "(\<lambda>x. edge_of (fstv' x)) ` {inedge e |e. e \<in> \<E> \<and> fstv e = x1} =
                    {e \<in> \<E>. fstv e = x1}" 
          by(auto simp add: image_def fstv'_def)
        have i7: "(\<lambda>x. edge_of (fstv' x)) ` {inedge e |e. e \<in> {e \<in> \<E>. \<u> e = PInfty} \<and> fstv e = x1} 
            = {e \<in> \<E>. fstv e = x1 \<and> \<u> e = PInfty}" 
          by(auto simp add: image_def fstv'_def)
        have h4: "(\<Sum>x\<in>{e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
              sndv' e = vertex x1}.
          (real_of_ereal (\<u> (edge_of (fstv' x))) - f (edge_of (fstv' x)))) =
          sum (\<lambda> e. real_of_ereal (\<u> e) - f e) (multigraph_spec.delta_plus \<E> fstv x1 - flow_network_spec.delta_plus_infty fstv \<E> \<u> x1)"
        proof(subst sum_inj_on[of "\<lambda> x. (edge_of (fstv' x))" _ _, simplified, symmetric], goal_cases)
          case 1
          then show ?case 
          proof(rule  inj_onI, goal_cases)
            case (1 x y)
            thus ?case
              by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
          qed
        next
          case 2
          thus ?case
          proof(rule forw_subst[of _ 
                "{inedge e |e. e \<in> \<E> \<and> fstv e = x1} - 
                {inedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u> \<and> fstv e = x1}"], goal_cases)
            case 2
            thus ?case
            proof(subst flow_network_spec.infty_edges_def,
                subst inj_on_image_set_diff[OF _ Diff_subset], goal_cases)
              case 1
              thus ?case
              proof(rule inj_onI, goal_cases)
                case (1 x y)
                thus ?case
                  by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
              qed
            qed (insert i6 i7, auto simp add: multigraph_spec.delta_plus_def flow_network_spec.delta_plus_infty_def)
          qed (force simp add: sndv'_def)
        qed
        have h5: "(\<Sum>x\<in>{e \<in> {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.
               sndv' e = vertex x1}.  f (get_edge x)) = 
                 sum f (flow_network_spec.delta_minus_infty sndv \<E> \<u> x1)"
          apply(subst sum_inj_on[of get_edge _ _, simplified, symmetric],
              force simp add: inj_on_def, rule cong[of "sum _", OF refl])
          by(fastforce simp add: image_def inj_on_def multigraph_spec.delta_minus_def 
              flow_network_spec.delta_minus_infty_def flow_network_spec.infty_edges_def sndv'_def)+
        have excess_at_x1: " sum f (multigraph_spec.delta_plus \<E> fstv x1) - sum f (multigraph_spec.delta_minus \<E> sndv x1) = \<b> x1"
          using case1(1) x_in_V 
          by(auto simp add: flow_network_spec.isbflow_def flow_network_spec.ex_def make_pair_def)
        have h6: "sum f (flow_network_spec.delta_plus_infty fstv \<E> \<u> x1) +
                    sum f (multigraph_spec.delta_plus \<E> fstv x1 - flow_network_spec.delta_plus_infty fstv \<E> \<u> x1) =
                     \<b> x1 +
                      (sum f (flow_network_spec.delta_minus_infty sndv \<E> \<u> x1) +
                       sum f (multigraph_spec.delta_minus \<E> sndv x1 - flow_network_spec.delta_minus_infty sndv \<E> \<u> x1)) "
          apply(subst comm_monoid_add_class.sum.union_disjoint[symmetric])
          using multigraph.delta_plus_finite[OF mgraph, of x1] 
            flow_network.infty_edges_del(6)[OF assms(1), of x1] 
            Un_absorb1[OF flow_network.infty_edges_del(6)[OF flow_network, of x1]] 
            multigraph.delta_minus_finite[OF mgraph, of x1] 
            flow_network.infty_edges_del(5)[OF assms(1), of x1] 
            Un_absorb1[OF flow_network.infty_edges_del(5)[OF assms(1), of x1]] 
            excess_at_x1 
          by (auto intro: forw_subst[OF comm_monoid_add_class.sum.union_disjoint[symmetric]] 
              simp add: finite_subset)
        have h7: "sum f' {e \<in> {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}. sndv' e = vertex x1} = 
                 sum f (flow_network_spec.delta_minus_infty sndv \<E> \<u> x1)"
          using h3 h4 h5
          by(subst case1(2), subst Let_def, subst sum_if_not_P_not_Q_but_R)
            (auto simp add: algebra_simps sum_subtractf \<E>3_def assms(3) \<E>1_def \<E>2_def)
        have h8: "sum f' {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}. 
                                   sndv' e = vertex x1} = 
              (\<Sum>x\<in>{e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}. 
                                   sndv' e = vertex x1}.
                  real_of_ereal (\<u> (edge_of (fstv' x))) - f (edge_of (fstv' x)))"
          using h3 h4 h5
          by(auto simp add: case1(2) algebra_simps Let_def \<E>1_def)
        have h9: "sum f' {e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
                       sndv' e = vertex x1} =
            (\<Sum>x\<in>{e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
               sndv' e = vertex x1}.
            f (edge_of (fstv' x)))" 
          using assms(2) 
          by(subst case1(2), subst Let_def, subst  sum_if_not_P)
            (auto simp add: \<E>2_def \<E>1_def)
        have "- (sum f' {e \<in> \<E>'. sndv' e = v} - sum f' {e \<in> \<E>'. fstv' e = v}) = \<b>' v"
          apply(simp only: \<E>'_def \<E>1_def \<E>2_def \<E>3_def almost_empty_simper h1 h2)
          unfolding h8 h9 h3 h4 h5 h7 vertex
          by(auto simp add: algebra_simps h6 \<b>'_def sum_subtractf \<E>3_def assms(3) \<E>1_def \<E>2_def)
        thus ?thesis
          by(auto simp add: flow_network_spec.ex_def  multigraph_spec.delta_minus_def
              multigraph_spec.delta_plus_def)
      qed
    qed
    show ?case
    proof(rule conjI, goal_cases)
      case 1
      then show ?case 
        by(auto simp add: b'_met flow_network_spec.isbflow_def isuflow' make_pair'_def make_pair_def
            multigraph_spec.make_pair_def)
    next
      case 2
      have is_E: "(\<lambda>x. edge_of (fstv' x)) `
          {outedge e |e. e \<in> \<E> \<and> e \<notin> flow_network_spec.infty_edges \<E> \<u>} \<union>
           get_edge `
          {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>} = \<E>"
        by(fastforce simp add: image_def flow_network_spec.infty_edges_def fstv'_def split: hitchcock_edge.split
            elim!: get_edge.cases)
      have costs_are: "(\<Sum>e\<in>\<E>. f e * \<c> e) =
         (\<Sum>x\<in>{inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
           (real_of_ereal (\<u> (edge_of (fstv' x))) - f (edge_of (fstv' x))) * 0) +
         (\<Sum>x\<in>{outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
             f (edge_of (fstv' x)) * \<c> (edge_of (fstv' x))) +
         (\<Sum>x\<in>{vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.
             f (get_edge x) * \<c> (get_edge x))"
      proof(subst sum_inj_on[of "\<lambda>x. edge_of (fstv' x)" _ "\<lambda> e. f e * \<c> e",simplified, symmetric], goal_cases)
        case 1
        show ?case
        proof(rule inj_onI, goal_cases)
          case (1 x y)
          thus  ?case 
            by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
        qed
      next
        case 2
        show ?case
        proof(subst sum_inj_on[of get_edge _ "\<lambda> e. f e * \<c> e",
              simplified, symmetric], goal_cases)
          case 1
          show ?case
          proof(rule  inj_onI, goal_cases)
            case (1 x y)
            thus ?case
              by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
          qed    
        next
          case 2
          show ?case
            using finites is_E cong[OF refl is_E, of "sum ( \<lambda> e. f e * \<c> e)", symmetric] 
            by(auto intro:  forw_subst[OF sym[OF comm_monoid_add_class.sum.union_disjoint]] simp add: fstv'_def )
        qed
      qed
      have sum_flow_costs_split:"(\<Sum>e\<in>\<E>'. f' e * \<c>' e) = 
           (\<Sum>e\<in>\<E>1. f' e * \<c>' e) + (\<Sum>e\<in>\<E>2. f' e * \<c>' e) + (\<Sum>e\<in>\<E>3. f' e * \<c>' e)"
        apply(subst \<E>'_def union_disjoint_triple)+
        using finites 
        by(auto simp add: \<E>1_def \<E>2_def \<E>3_def)
      have costs_E1_0:"(\<Sum>e\<in>\<E>1. f' e * \<c>' e) =  0" 
        using assms(2)
        by (force simp add:  \<E>1_def \<c>'_def )
      have costs_E3_are: "(\<Sum>e\<in>\<E>3. f' e * \<c>' e) = 
        (\<Sum>x\<in>{(vtovedge e)::('a, 'edge_type) hitchcock_edge |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.
         f (get_edge x) * \<c> (get_edge x))"
        unfolding \<E>1_def \<E>2_def \<c>'_def case1(2) \<E>3_def Let_def f_of_double_if_cond_same 
        apply(subst (1) sum_if_not_P_not_Q_but_R)
        by auto
      have costs_E2_are: "(\<Sum>e\<in>\<E>2. f' e * \<c>' e) = 
         (\<Sum>x\<in>{outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
            f (edge_of (fstv' x)) * \<c> (edge_of (fstv' x)))"
        unfolding \<E>1_def \<E>2_def \<c>'_def case1(2) \<E>3_def Let_def f_of_double_if_cond_same 
        apply(subst (1) sum_if_not_P)
        by auto
      show ?case 
        using costs_E3_are costs_E2_are costs_E1_0 costs_are
        by (auto simp add: cost_flow_spec.\<C>_def sum_flow_costs_split)
    qed
  qed

  show claim2:"\<And> f f'. ?x f f' \<Longrightarrow> ?y f f' \<Longrightarrow> ?z f f'"
    unfolding new_f_gen_def old_f_gen_def
    unfolding symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
      symmetric[OF fstv'_def_old] 
  proof(goal_cases)
    case (1 f f')
    note case1=this
    show ?case 
    proof(rule conjI, goal_cases)
      case 1
      have flow_distr_two_edges:"(inedge e) \<in> \<E>1 \<Longrightarrow> f'  (inedge e) 
                                                 = real_of_ereal (\<u> e) - f' (outedge e)" for e
      proof(goal_cases)
        case 1
        have  "edge e  \<in> dVs (make_pair' ` \<E>') \<and> vertex (sndv e) \<in> dVs (make_pair' ` \<E>') \<and> \<u> e \<noteq> PInfty \<and>e \<in> \<E>"
        proof-
          have e_where:"e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>"
            using 1[simplified \<E>1_def] by simp
          hence "e \<in> \<E>" "\<u> e \<noteq> PInfty"
            by(auto simp add: flow_network_spec.infty_edges_def)
          moreover have "edge e  \<in> dVs (make_pair' ` \<E>')"
          proof-
            have "\<exists>x. (\<exists>v1 v2. x = {v1, v2} \<and> (v1, v2) \<in> make_pair' ` \<E>') \<and> edge e \<in> x"
              apply(rule exI[of _ "{edge e, vertex (fstv e)}"], auto)
              apply(rule exI[of _ "edge e"])
              using 1 by (auto intro!: bexI[of _ "inedge e"] exI[of _ "vertex (fstv e)"] 
                  simp add: fstv'_def \<E>'_def  make_pair'_def image_def sndv'_def)
            thus ?thesis
              by (auto simp add:   dVs_def)
          qed
          moreover have "vertex (sndv e) \<in> dVs (make_pair' ` \<E>')"
          proof-
            have "\<exists>x. (\<exists>v1 v2. x = {v1, v2} \<and> (v1, v2) \<in> make_pair' ` \<E>') \<and> vertex (sndv e) \<in> x"
              apply(rule exI[of _ "{edge e, vertex (sndv e)}"], auto)
              apply(rule exI[of _ "edge e"])
              using 1  \<E>2_def e_where 
              by (auto intro!: bexI[of _ "outedge e"] exI[of _ "vertex (sndv e)"]  
                  simp add: make_pair'_def \<E>'_def fstv'_def sndv'_def image_def)
            thus ?thesis by(auto simp add:  dVs_def)
          qed
          ultimately show ?thesis by simp
        qed
        hence dVs': "edge e  \<in> dVs (make_pair' ` \<E>')" "vertex (sndv e) \<in> dVs (make_pair' ` \<E>')" "\<u> e \<noteq> PInfty"
          "e \<in> \<E>" by simp+    
        hence "(\<u> e) = - flow_network_spec.ex fstv' sndv' \<E>' f' (edge e)"
          using case1(1) 1 not_MInfty_nonneg[OF u_pos, of e] 
          by(auto intro: real_of_ereal.elims[of "\<u> e", OF refl]
              simp add: flow_network_spec.isbflow_def  \<b>'_def \<E>1_def make_pair_def
              make_pair'_def multigraph_spec.make_pair_def)
        moreover have "multigraph_spec.delta_plus \<E>' fstv' (edge e) = {inedge e, outedge e}"
          unfolding multigraph_spec.delta_plus_def
          using 1
          by (auto simp add: \<E>'_def \<E>1_def \<E>2_def \<E>3_def fstv'_def)
        moreover have "multigraph_spec.delta_minus \<E>' sndv' (edge e) = {}"
          by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def \<E>3_def sndv'_def  multigraph_spec.delta_minus_def)
        ultimately have "\<u> e = f' (inedge e) + f' (outedge e)"
          by ( simp add: flow_network_spec.ex_def)
        then show ?case by simp
      qed
      have "flow_network_spec.isuflow \<E> \<u> f"
        unfolding flow_network_spec.isuflow_def
      proof(rule ballI,  goal_cases)
        case (1 e)
        show ?case
        proof(cases "\<u> e")
          case (real r)
          hence edges_in:"outedge e  \<in> \<E>2" "inedge e \<in> \<E>1"
            using 1  PInfty_neq_ereal(1)[of r] 
            by(auto simp add: \<E>2_def \<E>1_def flow_network_spec.infty_edges_def)
          hence dVs': "edge e  \<in> dVs (make_pair' ` \<E>')" "vertex (sndv e) \<in> dVs (make_pair' ` \<E>')" 
            using  1
            by(auto intro!: exI[of _ "{edge e, vertex (sndv e)}"] exI[of "\<lambda> v1. \<exists> v2.  {edge e, vertex (sndv e)} = {v1, v2} \<and> _ v1 v2" "edge e"]
                exI[of "\<lambda> v2.  {edge e, vertex (sndv e)} = {_ , v2} \<and> _ _ v2" "vertex (sndv e)"]
                simp add: dVs_def \<E>'_def make_pair'_def fstv'_def sndv'_def image_def split: hitchcock_edge.split)
          hence "\<u> e = - ereal ( flow_network_spec.ex fstv'  sndv' \<E>' f' (edge e))"
            using case1(1) real
            by (auto simp add: flow_network_spec.isbflow_def  \<b>'_def multigraph_spec.make_pair_def make_pair_def make_pair'_def)
          moreover have "multigraph_spec.delta_plus \<E>' fstv' (edge e) = {inedge e, outedge e}"
            unfolding multigraph_spec.delta_plus_def
            using 1 real 
            by (auto simp add: \<E>'_def \<E>1_def \<E>2_def \<E>3_def flow_network_spec.infty_edges_def fstv'_def)
          moreover have "multigraph_spec.delta_minus \<E>' sndv' (edge e) = {}"
            unfolding multigraph_spec.delta_minus_def 
            by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def \<E>3_def flow_network_spec.infty_edges_def sndv'_def)
          ultimately have "\<u> e = f' (inedge e) + f' (outedge e)"
            by (auto simp add: flow_network_spec.ex_def )
          moreover have "f' (inedge e) \<ge> 0" "f' (outedge e) \<ge> 0"
            using case1(1) edges_in
            by(auto simp add: \<E>'_def flow_network_spec.isbflow_def flow_network_spec.isuflow_def)
          ultimately show ?thesis
            using edges_in(1)
            by(auto simp add: case1(2) \<E>2_def)
        next
          case PInf
          moreover hence edges_in:"vtovedge e  \<in> \<E>'"
            using 1
            by(auto simp add: \<E>3_def \<E>'_def flow_network_spec.infty_edges_def)
          moreover have "e \<in> flow_network_spec.infty_edges \<E> \<u>"
            using PInf 1
            by(auto simp add: flow_network_spec.infty_edges_def)
          ultimately show ?thesis
            using case1(1,2)
            by(auto simp add: \<E>'_def flow_network_spec.isuflow_def flow_network_spec.isbflow_def)
        next
          case MInf
          thus ?thesis 
            by (simp add: u_pos)
        qed
      qed
      moreover have "\<forall>v\<in>dVs (make_pair ` \<E>). - flow_network_spec.ex fstv sndv \<E> f v = \<b> v"
      proof(rule ballI, goal_cases)
        case (1 v)
        then obtain e where "e \<in> \<E>" "v = fstv e \<or> v = sndv e"
          using assms(1)
          by(auto simp add: dVs_def flow_network_def multigraph_def
              multigraph_spec.make_pair_def make_pair'_def make_pair_def) 
        moreover hence "vtovedge e \<in> \<E>' \<or>( 
              (outedge e) \<in> \<E>' \<and> (inedge e) \<in> \<E>')"
          unfolding \<E>'_def \<E>1_def \<E>3_def \<E>2_def by fastforce
        ultimately have "vertex v \<in> dVs (make_pair' ` \<E>')"
          by (auto simp add: dVs_def make_pair'_def fstv'_def sndv'_def split: hitchcock_edge.split)
            (force intro!: exI[of _ "{vertex (fstv e), vertex (sndv e)}"]| 
              force intro!: exI[of _ "{vertex (sndv e), edge e}"]|
              force intro!: exI[of _ "{vertex (fstv e), edge e}"] )+
        hence "  \<b> v  = 
          - sum f' (multigraph_spec.delta_minus \<E>' sndv' (vertex v)) + sum f' (multigraph_spec.delta_plus \<E>' fstv' (vertex v))
               + (sum (real_of_ereal o \<u>) (multigraph_spec.delta_plus \<E> fstv v -flow_network_spec.delta_plus_infty fstv \<E> \<u> v ))"
          using case1(1) 
          by(auto simp add: flow_network_spec.isbflow_def \<b>'_def flow_network_spec.ex_def
              multigraph_spec.make_pair_def make_pair'_def make_pair_def)
        moreover have "multigraph_spec.delta_plus \<E>' fstv' (vertex v) = 
                     {vtovedge d | d. d \<in> flow_network_spec.delta_plus_infty fstv \<E> \<u> v}"
          unfolding multigraph_spec.delta_plus_def
          unfolding  \<E>'_def \<E>1_def \<E>2_def \<E>3_def
          by(auto simp add: flow_network_spec.infty_edges_def flow_network_spec.delta_plus_infty_def
              fstv'_def)
        moreover have "sum f' (multigraph_spec.delta_minus \<E>' sndv' (vertex v)) = 
                     sum f' ( multigraph_spec.delta_minus \<E>' sndv' (vertex v) \<inter> \<E>1) +
                     sum f' (multigraph_spec.delta_minus \<E>' sndv' (vertex v) \<inter> \<E>2) +
                     sum f' (multigraph_spec.delta_minus \<E>' sndv' (vertex v) \<inter> \<E>3)"
          unfolding  multigraph_spec.delta_minus_def
          unfolding \<E>'_def
          apply(subst sym[OF comm_monoid_add_class.sum.union_disjoint])
          using \<E>'_def finiteE'  Es_non_inter 
          by(auto intro: forw_subst[OF  sym[OF comm_monoid_add_class.sum.union_disjoint]]
              cong[of "sum f'", OF refl]) 
        moreover have "sum f' (multigraph_spec.delta_minus \<E>' sndv' (vertex v) \<inter> \<E>2) = 
                      sum (\<lambda> e. f' (outedge e)) 
                           (multigraph_spec.delta_minus \<E> sndv v - flow_network_spec.delta_minus_infty sndv \<E> \<u> v)"
        proof(subst sum_inj_on[of outedge _ f', simplified, symmetric], goal_cases)
          case 2
          show ?case
            apply(rule cong[of "sum f'", OF refl])
            unfolding multigraph_spec.delta_minus_def 
            by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def  multigraph_spec.delta_minus_def flow_network_spec.delta_minus_infty_def
                flow_network_spec.infty_edges_def sndv'_def)
        qed (auto simp add: inj_on_def)
        moreover have "sum f' ( multigraph_spec.delta_minus \<E>' sndv' (vertex v) \<inter> \<E>1) = 
                     sum (\<lambda> e. real_of_ereal (\<u> e) - f' (outedge e)) 
                          (multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v)"
        proof(subst sum_cong[OF sym[OF flow_distr_two_edges]], goal_cases)
          case (1 x)
          then show ?case 
            by(fastforce simp add: multigraph_spec.delta_plus_def flow_network_spec.delta_plus_infty_def
                \<E>1_def flow_network_spec.infty_edges_def) 
        next
          case 2
          then show ?case  
          proof(subst sum_inj_on[of inedge _ "f'",  symmetric, simplified o_def], goal_cases)
            case 2
            show ?case
              by(auto intro!: cong[of "sum f'", OF refl]
                  simp add:  \<E>'_def \<E>1_def \<E>2_def \<E>3_def flow_network_spec.delta_plus_infty_def
                  flow_network_spec.infty_edges_def sndv'_def
                  multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def)
          qed (simp add: inj_on_def)
        qed
        moreover have "sum (\<lambda> e. real_of_ereal (\<u> e) - f' (outedge e)) 
                          (multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v)
                      = sum (real_of_ereal \<circ> \<u>) (multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v)
                         - sum (\<lambda> e. f' (outedge e)) 
                             (multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v)"
          by(auto simp add: sum_subtractf[of _ _ "multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v"])
        moreover have "sum f' (multigraph_spec.delta_minus \<E>' sndv' (vertex v) \<inter> \<E>3) 
                       =  sum (\<lambda> e. f' (vtovedge e))
                          (flow_network_spec.delta_minus_infty sndv \<E> \<u> v)" 
        proof(subst sum_inj_on[of vtovedge _ "f'", symmetric, simplified o_def], goal_cases)
          case 2
          show ?case
            by(auto intro!: cong[of "sum f'", OF refl] 
                simp add: \<E>'_def \<E>1_def \<E>2_def \<E>3_def image_def flow_network_spec.infty_edges_def
                multigraph_spec.delta_minus_def flow_network_spec.delta_minus_infty_def 
                sndv'_def)
        qed (simp add: inj_on_def)
        moreover have "
          (\<Sum>e\<in>multigraph_spec.delta_minus \<E> sndv v - flow_network_spec.delta_minus_infty sndv \<E> \<u> v.
                  f' (outedge e)) +      
          (\<Sum>e\<in>flow_network_spec.delta_minus_infty sndv \<E> \<u> v. f' (vtovedge e)) = 
          sum f (multigraph_spec.delta_minus \<E> sndv v)"
        proof-
          have helper:"sum f' (outedge ` (multigraph_spec.delta_minus \<E> sndv v -
                                          flow_network_spec.delta_minus_infty sndv \<E> \<u> v) \<union>
                               vtovedge ` flow_network_spec.delta_minus_infty sndv \<E> \<u> v) =
                      sum f (multigraph_spec.delta_minus \<E> sndv v)"
          proof-
            have a1:"inj_on (\<lambda>e. if e \<in> flow_network_spec.infty_edges \<E> \<u> then vtovedge e else outedge e)
                  (multigraph_spec.delta_minus \<E> sndv v)"
              by (fastforce simp add: inj_on_def)+
            show ?thesis
              using sum_inj_on[of "\<lambda> e. if _ e then _ e else _ e" _ f', simplified, symmetric, OF a1]
              by (fastforce intro!: cong[of "sum f'", OF refl] 
                  simp add: image_def multigraph_spec.delta_minus_def
                  flow_network_spec.delta_minus_infty_def
                  flow_network_spec.infty_edges_def if_distrib[of f', symmetric] case1(2))
          qed
          have inj_helpers: "inj_on outedge (multigraph_spec.delta_minus \<E> sndv v -
                          flow_network_spec.delta_minus_infty sndv \<E> \<u> v)"
            "inj_on vtovedge (flow_network_spec.delta_minus_infty sndv \<E> \<u> v)"
            by(force simp add: inj_on_def)+
          show ?thesis
            unfolding sum_inj_on[of outedge _ f', simplified, symmetric, OF inj_helpers(1)]
              sum_inj_on[of vtovedge _ f', simplified, symmetric, OF inj_helpers(2)]
            using flow_network.finite_infinite_deltas[OF flow_network] 
              multigraph.finite_deltas[OF mgraph] 
            by (subst comm_monoid_add_class.sum.union_disjoint[symmetric])(auto simp add: helper)
        qed
        moreover have "
          (\<Sum>e\<in>multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v.
                  f' (outedge e)) +      
          (\<Sum>e\<in>flow_network_spec.delta_plus_infty fstv \<E> \<u> v. f' (vtovedge e)) = 
          sum f (multigraph_spec.delta_plus \<E> fstv v)"
        proof-
          have helper: "sum f' (outedge ` (multigraph_spec.delta_plus \<E> fstv v -
                                           flow_network_spec.delta_plus_infty fstv \<E> \<u> v) \<union>
                          vtovedge ` flow_network_spec.delta_plus_infty fstv \<E> \<u> v) =
                        sum f (multigraph_spec.delta_plus \<E> fstv v)"
            unfolding case1(2)
          proof(subst if_distrib[of f', symmetric], 
              subst sum_inj_on[of "\<lambda> e. if _ e then _ e else _ e" _ f',
                simplified, symmetric], goal_cases)
            case 2
            then show ?case 
              by (force intro: cong[of "sum f'", OF refl] 
                  simp add: image_def multigraph_spec.delta_plus_def
                  flow_network_spec.delta_plus_infty_def
                  flow_network_spec.infty_edges_def )
          qed (auto simp add: inj_on_def)
          have inj_helpers: "inj_on outedge (multigraph_spec.delta_plus \<E> fstv v -
                            flow_network_spec.delta_plus_infty fstv \<E> \<u> v)"
            "inj_on vtovedge (flow_network_spec.delta_plus_infty fstv \<E> \<u> v)"
            by(force simp add: inj_on_def)+
          show ?thesis
            unfolding sum_inj_on[of outedge _ f', simplified, symmetric, OF inj_helpers(1)]
              sum_inj_on[of vtovedge _ f',simplified, symmetric, OF inj_helpers(2)]
            using flow_network.finite_infinite_deltas[OF flow_network] 
              multigraph.finite_deltas[OF mgraph] 
            by (subst comm_monoid_add_class.sum.union_disjoint[symmetric])(auto simp add: helper)
        qed
        moreover have "sum f' {vtovedge e | e. e \<in> flow_network_spec.delta_plus_infty fstv \<E> \<u> v}
             = (\<Sum>e\<in>flow_network_spec.delta_plus_infty fstv \<E> \<u> v. f' (vtovedge e))" 
          by(subst sum_inj_on[of vtovedge _ f', simplified, symmetric])
            (force intro: cong[of "sum f'", OF refl] simp add: image_def inj_on_def)+    
        ultimately show ?case 
          by(auto simp add: flow_network_spec.ex_def)
      qed
      ultimately show ?case 
        by(auto simp add: flow_network_spec.isbflow_def multigraph_spec.make_pair_def make_pair'_def make_pair_def)
    next
      case 2
      have helper1:"(\<Sum>e\<in>\<E>. f e * \<c> e) = 
        (\<Sum>e \<in> flow_network_spec.infty_edges \<E> \<u>.  f' (vtovedge e) * \<c> e) +
        (\<Sum>e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>. f' (outedge e) * \<c> e)"
        unfolding 1(2)
        apply(subst (2) Un_Diff_cancel2[of \<E> "flow_network_spec.infty_edges \<E> \<u>", simplified
              flow_network.infty_edges_in_E[OF assms(1), simplified subset_Un_eq Un_commute],
              symmetric])
        using multigraph.finite_E[OF mgraph]  flow_network.finite_infty_edges[OF flow_network]
          sum_if_not_P[of "\<E> - flow_network_spec.infty_edges \<E> \<u>"]
          sum_if_P[of "flow_network_spec.infty_edges \<E> \<u>"]
        by (subst comm_monoid_add_class.sum.union_disjoint)auto
      have helper2: "(\<Sum>e\<in>\<E> - flow_network_spec.infty_edges \<E> \<u>. f' (outedge e) * \<c> e) =
                    (\<Sum>x\<in>\<E>2. f' x * \<c> (edge_of (fstv' x)))"
        unfolding \<E>2_def Setcompr_eq_image
        by(auto intro: forw_subst[OF  sum_inj_on] simp add: inj_on_def fstv'_def)
      have helper3: "(\<Sum>e\<in>flow_network_spec.infty_edges \<E> \<u>. f' (vtovedge e) * \<c> e) =
                    (\<Sum>x\<in>\<E>3. f' x * \<c> (get_edge x))"
        unfolding \<E>3_def  Setcompr_eq_image[of vtovedge,
            simplified]
        by(fastforce intro: forw_subst[OF  sum_inj_on] simp add: inj_on_def)
      have auxes: "finite (\<E>1 \<union> \<E>2)" "finite \<E>3" "(\<E>1 \<union> \<E>2) \<inter> \<E>3 = {}" "finite \<E>1" "finite \<E>2"
        using \<E>'_def finiteE' Es_non_inter  by auto
      have overall_costs_split: "(\<Sum>e\<in>\<E>'. f' e * \<c>' e) = 
                  (\<Sum>e\<in>\<E>1. f' e * \<c>' e) + (\<Sum>e\<in>\<E>2. f' e * \<c>' e) + (\<Sum>e\<in>\<E>3. f' e * \<c>' e)"
        by(simp add: \<E>'_def
            comm_monoid_add_class.sum.union_disjoint[OF auxes(1,2,3)]
            comm_monoid_add_class.sum.union_disjoint[OF auxes(4,5) Es_non_inter(1)])
      have costs_E1_0: "(\<Sum>e\<in>\<E>1. f' e * \<c>' e) = 0"
        by(simp add: \<c>'_def) 
      have costs_E2_are: "(\<Sum>e\<in>\<E>2. f' e * \<c>' e) = (\<Sum>x\<in>\<E>2. f' x * \<c> (edge_of (fstv' x)))"
        unfolding \<c>'_def 
        apply(subst  sum_if_not_P[of \<E>2 _ ])
        using Es_non_inter 
        by auto
      have costs_E3_are: "(\<Sum>e\<in>\<E>3. f' e * \<c>' e) = (\<Sum>x\<in>\<E>3. f' x * \<c> (get_edge x))"
        using Es_non_inter
        by (auto intro!: sum_if_not_P_not_Q_but_R simp add: \<c>'_def )
      show ?case 
        using Es_non_inter sum_if_P[of \<E>3 ] helper1 helper2 helper3
        by (auto simp add:  cost_flow_spec.\<C>_def overall_costs_split costs_E1_0 costs_E2_are costs_E3_are)
    qed
  qed
  show claim3:  "has_neg_cycle make_pair' \<E>' \<c>' = has_neg_infty_cycle make_pair \<E> \<c> \<u>"
  proof(rule iffI, goal_cases)
    case 1
    then obtain C where C_prop:"closed_w (make_pair' ` \<E>') (map make_pair' C)"
      "foldr (\<lambda>e. (+) (\<c>' e)) C 0 < 0" "set C \<subseteq> \<E>'"
      by (auto elim!: has_neg_cycleE)
    hence C_inE: "set C \<subseteq> \<E>'" "C \<noteq> []"
      by(auto simp add:awalk_def closed_w_def)
    have C_in_E3: "set C \<subseteq> \<E>3"
    proof-
      have "e \<in> set C \<Longrightarrow> e \<notin> \<E>3 \<Longrightarrow> False" for e
      proof(goal_cases)
        case 1
        hence ab_where:"e \<in> \<E>1 \<union> \<E>2" 
          using C_inE \<E>'_def by blast
        obtain C1 C2 where C_split: "C = C1@[e]@C2" 
          by (metis "1"(1) in_set_conv_decomp_first single_in_append)
        hence rotated:"closed_w (make_pair' ` \<E>') (map make_pair' ([e]@ C2@C1))" 
          "set (map make_pair' C) = set (map make_pair'([e]@C2@C1))"
          "closed_w (make_pair' ` \<E>') (map make_pair' (C2@C1@[e]))" 
          using closed_w_rotate C_prop(1) 
          by(force intro: closed_w_rotate)+
        hence snd_last:"snd (last (map make_pair' ([e]@C2@C1))) = fstv' e" 
          using  awalk_fst_last[of "map make_pair' ([e] @ C2 @ C1)"]
          by(force simp add: closed_w_def fstv'_def make_pair'_def sndv'_def) 
        have last_in_E:"last ([e]@C2@C1) \<in> \<E>' " 
          using  C_inE  C_split last_in_set[of "[e] @ C2 @ C1"] by auto
        show ?case
        proof(rule disjE[OF  ab_where[simplified Un_iff]], goal_cases)
          case 1
          then obtain d where "e = inedge d"
            "d \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>"
            by(auto simp add: \<E>1_def)
          moreover have  "sndv' (last ([e] @ C2 @ C1)) = fstv' e" 
            using  snd_last
            apply(subst (asm) last_map)
            by(auto simp add: make_pair'_def)       
          ultimately show ?case
            using last_in_E 
            by(cases "(last ([e] @ C2 @ C1))") 
              (auto simp add: \<E>'_def \<E>1_def \<E>2_def \<E>3_def sndv'_def fstv'_def)   
        next
          case 2
          then obtain d where "e = outedge d"
            "d \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>"
            by(auto simp add: \<E>2_def)
          moreover have  "sndv' (last ([e] @ C2 @ C1)) = fstv' e" 
            using  snd_last
            apply(subst (asm) last_map)
            by(auto simp add: make_pair'_def)   
          ultimately show ?case
            using last_in_E 
            by(cases "(last ([e] @ C2 @ C1))") 
              (auto simp add: \<E>'_def \<E>1_def \<E>2_def \<E>3_def sndv'_def fstv'_def) 
        qed
      qed
      thus ?thesis by auto
    qed
    hence closed_w_E3: "closed_w (make_pair' ` \<E>3) (map make_pair' C)"
      using C_inE(2) C_prop(1)   subset_mono_awalk'[of "(make_pair' ` \<E>')" _ "map make_pair' C" _ "make_pair' ` \<E>3"]
      by (auto intro!: image_mono simp add: closed_w_def)
    then obtain u where u_prop: "awalk (make_pair' ` \<E>3) u (map make_pair' C) u" " 0 < length C" 
      by(auto simp add: closed_w_def)
    define D where "D = map get_edge C"
    have map_C_is:"map (make_pair \<circ> get_edge) C =
         (map ((\<lambda>e. (vertex_of (fst e), vertex_of (snd e))) \<circ> make_pair') C)"
      using C_in_E3 assms(1)
      by(auto intro: map_cong[OF refl] 
          simp add: make_pair'_def fstv'_def sndv'_def \<E>3_def flow_network_def 
          multigraph_def multigraph_spec.make_pair_def  make_pair_def
          split: hitchcock_edge.split)
    have "closed_w (make_pair ` \<E>) (map make_pair D)"
    proof-
      have "\<lbrakk>C \<noteq> []; flow_network fstv sndv  create_edge \<u> \<E>\<rbrakk> \<Longrightarrow>
        awalk (make_pair ` \<E>) (vertex_of u) (map ((\<lambda>e. (vertex_of (fst e), vertex_of (snd e))) \<circ> make_pair') C)
        (vertex_of u)"
        by(fastforce intro!: subset_mono_awalk[OF awalk_map[OF _ u_prop(1)], simplified, OF _ refl, of vertex_of] 
            simp add: make_pair'_def fstv'_def sndv'_def \<E>3_def flow_network_def multigraph_def
            flow_network_spec.infty_edges_def map_C_is multigraph_spec.make_pair_def  make_pair_def)
      thus ?thesis
        using u_prop(2) assms(1) 
        by(auto intro: exI[of _ "vertex_of u"] simp add: map_C_is closed_w_def  D_def) 
    qed
    moreover have "foldr (\<lambda>e. (+) (\<c> e)) D start = foldr (\<lambda>e. (+) (\<c>' e)) C start" for start  
      using Es_non_inter C_in_E3
      unfolding D_def fold_map comp_def \<c>'_def
      by(induction C arbitrary: start) auto
    moreover have "\<forall>e\<in>set D. \<u> e = PInfty"
      using C_in_E3
      by(auto simp add: D_def \<E>3_def flow_network_spec.infty_edges_def)
    moreover have "set D \<subseteq> \<E>" 
      using C_in_E3
      by (auto simp add: flow_network_spec.infty_edges_def D_def \<E>3_def )
    ultimately show ?case
      using C_prop(2) by (auto intro!: has_neg_infty_cycleI)
  next
    case 2
    then obtain D where D_prop: "closed_w (make_pair ` \<E>) (map make_pair D)" "foldr (\<lambda>e. (+) (\<c> e)) D 0 < 0" 
      "(\<forall>e\<in>set D. \<u> e = PInfty)" "set D \<subseteq> \<E>"
      by (auto elim!: has_neg_infty_cycleE)
    then obtain u where u_prop: "awalk (make_pair ` \<E>)  u (map make_pair D) u" "0 < length D"
      by(auto simp add: closed_w_def)
    have D_infty_edges:"set D \<subseteq> flow_network_spec.infty_edges \<E> \<u>"
      using D_prop(3,4) 
      by(fastforce simp add:flow_network_spec.infty_edges_def)
    have map_make_pair': "(map make_pair' (map vtovedge D)) =  map (\<lambda>e. (vertex (fst e), vertex (snd e))) (map make_pair D)"
      using assms(1)
      by (auto simp add: make_pair'_def fstv'_def sndv'_def flow_network_def multigraph_def multigraph_spec.make_pair_def make_pair_def)
    have awalk_E3:"awalk (make_pair' ` \<E>3) (vertex u) (map make_pair' (map vtovedge D)) (vertex u)"
      using u_prop(2) D_infty_edges
      apply(subst map_make_pair')
      using assms(1) 
      by (fastforce intro!: subset_mono_awalk'[OF awalk_map[OF _ u_prop(1)], OF _ refl, of vertex] 
          simp add: make_pair'_def fstv'_def sndv'_def \<E>3_def image_def flow_network_def multigraph_def 
          multigraph_spec.make_pair_def make_pair_def
          split: hitchcock_edge.split)
    hence C_in_E3:"set (map vtovedge D) \<subseteq> \<E>3" 
      using D_prop(3,4)
      by(auto simp add: \<E>3_def flow_network_spec.infty_edges_def)
    hence "awalk (make_pair' ` \<E>') (vertex u) (map make_pair' (map vtovedge D)) (vertex u)"
      using awalk_E3 by(auto intro: subset_mono_awalk simp add: \<E>'_def )
    hence "closed_w (make_pair' ` \<E>') (map make_pair' (map vtovedge D))"
      using closed_w_def u_prop(2) by blast
    moreover have "foldr (\<lambda>e. (+) (\<c>' e)) (map vtovedge D) start
                    = foldr (\<lambda>e. (+) (\<c> e)) D start" for start
      using Es_non_inter C_in_E3
      unfolding  fold_map comp_def \<c>'_def
      by(induction D arbitrary: start) auto
    moreover have "set (map vtovedge D) \<subseteq> \<E>'" 
      using C_in_E3 \<E>'_def by blast
    ultimately show ?case 
      using  D_prop(2) by (fastforce intro!: has_neg_cycleI)
  qed
  note claim1=claim1[simplified new_f_gen_def old_f_gen_def, simplified
      symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
      symmetric[OF fstv'_def_old]]
  note claim2=claim2[simplified new_f_gen_def old_f_gen_def, simplified
      symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
      symmetric[OF fstv'_def_old]]
  show claim4: "\<And> f f'.  ?b1 f f'\<Longrightarrow> ?c1 f' \<Longrightarrow> ?d1 f "
    unfolding new_f_gen_def old_f_gen_def
    unfolding symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
      symmetric[OF fstv'_def_old] 
  proof(goal_cases)
    case (1 f f')
    note case1=this
    note optf=1
    hence opt_unfold: "flow_network_spec.isbflow fstv' sndv' \<E>' \<u>' f' \<b>'"
      "(\<And> f''. flow_network_spec.isbflow fstv' sndv' \<E>' \<u>' f'' \<b>' 
            \<Longrightarrow> cost_flow_spec.\<C> \<E>' \<c>' f' \<le> cost_flow_spec.\<C> \<E>' \<c>' f'')"
      by(auto simp add: cost_flow_spec.is_Opt_def)
    have claim2_result:"cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f'" "flow_network_spec.isbflow fstv sndv \<E> \<u> f \<b>"
      using claim2[OF opt_unfold(1)] case1 by simp+
    show ?case
    proof(rule ccontr, goal_cases)
      case 1
      then obtain d where d_prop:"flow_network_spec.isbflow fstv sndv  \<E> \<u> d \<b>" 
        "cost_flow_spec.\<C> \<E> \<c> d < cost_flow_spec.\<C> \<E> \<c> f"
        using claim2_result(2) by(auto simp add: cost_flow_spec.is_Opt_def)
      define d' where "d' =
    (\<lambda>e'. let e = edge_of (fstv' e')
           in if e' \<in> \<E>1 then real_of_ereal (\<u> e) - d e
              else if e' \<in> \<E>2 then d e
                   else if e' \<in> \<E>3 then d (get_edge e')
                        else undefined)"
      have d'_flow: "flow_network_spec.isbflow fstv' sndv'  \<E>' \<u>' d' \<b>'" 
        "cost_flow_spec.\<C> \<E> \<c> d = cost_flow_spec.\<C> \<E>' \<c>' d'"
        using  claim1[of d d'] d_prop(1) d'_def by auto 
      moreover hence "cost_flow_spec.\<C> \<E>' \<c>' d' < cost_flow_spec.\<C> \<E>' \<c>' f'"
        using claim2_result(1) d_prop(2) by auto
      ultimately show False
        using opt_unfold(2)[of d'] by simp
    qed
  qed
  show "\<And> f f'.  ?b2 f f'\<Longrightarrow> ?c2 f \<Longrightarrow> ?d3 f'"
    unfolding new_f_gen_def old_f_gen_def
    unfolding symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
      symmetric[OF fstv'_def_old] 
  proof(goal_cases)
    case (1 f f')
    note optf=this
    note case1 = this
    hence opt_unfold: "flow_network_spec.isbflow fstv sndv \<E> \<u> f \<b>"
      "(\<And> f'. flow_network_spec.isbflow fstv sndv \<E> \<u> f' \<b> \<Longrightarrow> cost_flow_spec.\<C> \<E> \<c> f \<le> cost_flow_spec.\<C> \<E> \<c> f')"
      by(auto simp add: cost_flow_spec.is_Opt_def)
    have claim1_result: "flow_network_spec.isbflow fstv' sndv'  \<E>' \<u>' f' \<b>' \<and>
                           cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f'" 
      using  case1 by(auto intro!: claim1[OF opt_unfold(1)]) 
    hence claim1_result:"cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f'" 
      "flow_network_spec.isbflow fstv' sndv'  \<E>' \<u>' f' \<b>'"
      by auto
    show ?case
    proof(rule ccontr, goal_cases)
      case 1
      then obtain d' where d'_prop:"flow_network_spec.isbflow fstv' sndv'  \<E>' \<u>' d' \<b>'" 
        "cost_flow_spec.\<C> \<E>' \<c>' d' < cost_flow_spec.\<C> \<E>' \<c>' f'"
        using claim1_result 
        by(auto simp add: cost_flow_spec.is_Opt_def)
      define d where "d = (\<lambda>e. if e \<in> flow_network_spec.infty_edges \<E> \<u> then d' (vtovedge e)
          else d' (outedge e))"
      have d_flow: "flow_network_spec.isbflow fstv sndv  \<E> \<u> d \<b>" 
        "cost_flow_spec.\<C> \<E> \<c> d = cost_flow_spec.\<C> \<E>' \<c>' d'"
        using claim2[of d'] d'_prop(1) d_def  by auto
      moreover hence "cost_flow_spec.\<C> \<E> \<c> d < cost_flow_spec.\<C> \<E> \<c> f"
        by (simp add: claim1_result(1) d'_prop(2))
      ultimately show False
        using opt_unfold(2)[of d] by simp
    qed
  qed
qed

subsection \<open>Finite-Capacity Graphs\<close>

definition "new_\<E>1 \<E> \<u> = {(edge e, vertex (fst e))| e. e \<in> \<E>}"
definition "new_\<E>2 \<E> \<u> = {(edge e, vertex (snd e))| e. e \<in> \<E>}"

definition "new_\<c> \<E> \<u> \<c> = (\<lambda> e'. if e' \<in> new_\<E>2 \<E> \<u> 
                                 then \<c> (edge_of (fst e')) 
                                 else if e' \<in> new_\<E>1 \<E> \<u>
                                 then 0 else undefined)"

definition "new_\<b> \<E> \<u> \<b> = (\<lambda> x'. (case x' of edge e \<Rightarrow> \<u> e
                       | vertex x \<Rightarrow> \<b> x -( sum \<u> (multigraph_spec.delta_plus \<E> fst x))))"

definition "new_f \<E> \<u> f = (\<lambda> e'. (let e = edge_of (fst e') 
                                                  in
                                                 (if e' \<in> new_\<E>2 \<E> \<u> then f e else
                                                    if e' \<in> new_\<E>1 \<E> \<u> then \<u> e - f e
                                                    else undefined)))"

definition "old_f f' = (\<lambda> e. f' (edge e, vertex (snd e)))"

theorem reduction_of_mincost_flow_to_hitchcock:
  fixes \<c> \<b>
  assumes "flow_network fst snd Pair (ereal o \<u>) \<E>"
  assumes "\<nexists> x. (x,x) \<in> \<E>"
  defines "\<E>1 \<equiv> new_\<E>1 \<E> \<u>"
  defines "\<E>2 \<equiv> new_\<E>2 \<E> \<u>"
  defines "\<E>' \<equiv> \<E>1 \<union> \<E>2"
  defines "\<u>' \<equiv> (\<lambda> e. PInfty)"
  defines "\<c>' \<equiv> new_\<c> \<E> \<u> \<c>"
  defines "\<b>' \<equiv> new_\<b> \<E> \<u> \<b>"
  shows 
    "flow_network fst snd Pair \<u>' \<E>'" (is ?case1) and
    "\<And> f f'. \<lbrakk> flow_network_spec.isbflow fst snd \<E> (ereal o \<u>) f \<b>; f' = new_f \<E> \<u> f\<rbrakk>
       \<Longrightarrow>flow_network_spec.isbflow fst snd \<E>' \<u>' f' \<b>' \<and> (cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f')" 
    (is "\<And> f f'. ?a f \<Longrightarrow> ?b f f' \<Longrightarrow> ?c  f f'") and
    "\<And> f f'. \<lbrakk> flow_network_spec.isbflow fst snd  \<E>' \<u>' f' \<b>'; f = old_f f'\<rbrakk> \<Longrightarrow>
          flow_network_spec.isbflow fst snd  \<E> (ereal o \<u>) f \<b> \<and> (cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f')"
    (is "\<And> f f'. ?x f' \<Longrightarrow> ?y f f'\<Longrightarrow> ?z f f'") and
    "\<lbrakk> cost_flow_spec.is_Opt fst snd  (ereal o \<u>) \<E> \<c> \<b> f; f' = new_f \<E> \<u> f\<rbrakk> \<Longrightarrow>
 cost_flow_spec.is_Opt fst snd   \<u>' \<E>' \<c>' \<b>' f'"
    and
    "\<lbrakk> cost_flow_spec.is_Opt fst snd   \<u>' \<E>' \<c>' \<b>' f'; f = old_f f'\<rbrakk> \<Longrightarrow>
 cost_flow_spec.is_Opt fst snd  (ereal o \<u>) \<E> \<c> \<b> f " and
    "\<nexists> C. closed_w \<E>' C" 
proof-
  note  \<E>1_def_old =  \<E>1_def
  note  \<E>2_def_old =  \<E>2_def
  have \<E>1_def: "\<E>1 = {(edge e, vertex (fst e))| e. e \<in> \<E>}"
    by (simp add: \<E>1_def new_\<E>1_def)
  have \<E>2_def: "\<E>2 = {(edge e, vertex (snd e))| e. e \<in> \<E>}"
    by (simp add: \<E>2_def new_\<E>2_def)
  have \<c>'_def: "\<c>' = (\<lambda> e'. if e' \<in> \<E>2 then \<c> (edge_of (fst e')) else if e' \<in> \<E>1  
then 0 else undefined)"
    unfolding \<c>'_def new_\<c>_def new_\<E>1_def new_\<E>2_def
      \<E>1_def \<E>2_def by simp
  have \<b>'_def: "\<b>' = (\<lambda> x'. (case x' of edge e \<Rightarrow> \<u> e
                       | vertex x \<Rightarrow> \<b> x -( sum \<u> (multigraph_spec.delta_plus \<E> fst x))))"
    unfolding \<b>'_def new_\<b>_def by simp  
  have finites: "finite {(edge (a, b), vertex a) |a b. (a, b) \<in> \<E>}"
    "finite {(edge (a, b), vertex b) |a b. (a, b) \<in> \<E>}"
    using assms(1) finite_img[of \<E> "\<lambda> e. (edge e, vertex (fst e))"]
      finite_img[of \<E> "\<lambda> e. (edge e, vertex (snd e))"]
    by(auto simp add: flow_network_def multigraph_def flow_network_axioms_def)
  hence finiteE':"finite \<E>'"
    by(simp add: \<E>'_def \<E>1_def \<E>2_def)
  moreover have nonemptyE': "\<E>' \<noteq> {}"
    using assms(1) by(auto simp add: \<E>'_def \<E>1_def \<E>2_def flow_network_def multigraph_def flow_network_axioms_def)
  ultimately show residual':"flow_network fst snd  Pair \<u>' \<E>'"
    using assms(1) 
    by(auto simp add: flow_network_def \<u>'_def multigraph_def flow_network_axioms_def)
  have cost_flow: "cost_flow_network fst snd  Pair \<u> \<E>" 
    using assms(1)
    by (auto simp add: comp_def cost_flow_network_def)
  have cost_flow': "cost_flow_network fst snd  Pair \<u>' \<E>'"
    using residual'
    by (auto simp add: comp_def cost_flow_network_def)
  have flow_network': "flow_network fst snd  Pair \<u>' \<E>'"
    using residual'
    by (auto simp add: comp_def cost_flow_network_def)
  have flow_network: "flow_network fst snd  Pair \<u> \<E>"
    using assms(1)
    by (auto simp add: comp_def cost_flow_network_def)
  have mgraph': "multigraph fst snd  Pair \<E>'"
    using flow_network_def residual' by blast
  have mgraph: "multigraph fst snd  Pair \<E>"
    using flow_network_def assms(1) by blast
  have Es_non_inter: "\<E>1 \<inter> \<E>2 = {}" 
    using \<E>1_def \<E>2_def assms(2) by fastforce
  show claim1:"\<And> f f'. ?a f \<Longrightarrow> ?b f f' \<Longrightarrow> ?c f f'"
    unfolding new_f_def old_f_def
    unfolding symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] 
  proof(goal_cases)
    case (1 f f')
    note case1=this[simplified]
    have ex_b:"\<And> v. v\<in>dVs \<E> \<Longrightarrow> - flow_network_spec.ex fst snd \<E> f v = \<b> v"
      using case1 by(auto simp add: flow_network_spec.isbflow_def multigraph_spec.make_pair_def)
    have "e \<in> \<E>' \<Longrightarrow> ereal (f' e) \<le> \<u>' e" for e
      by(simp add: \<E>'_def case1(2) \<u>'_def)
    moreover have "e \<in> \<E>' \<Longrightarrow> 0 \<le> f' e" for e
      using case1(1)
      by(auto split: prod.split 
          simp add: \<E>1_def \<E>2_def \<E>'_def case1(2) \<u>'_def flow_network_spec.isbflow_def
          flow_network_spec.isuflow_def Let_def
          intro!: ereal_diff_positive real_of_ereal_pos)
    ultimately have isuflow': "flow_network_spec.isuflow \<E>' \<u>' f'"
      unfolding flow_network_spec.isuflow_def by auto
    have a1: "{e. ((\<exists>a b. e = (edge (a, b), vertex a) \<and> (a, b) \<in> \<E>) \<or>
                (\<exists>a b. e = (edge (a, b), vertex b) \<and> (a, b) \<in> \<E>)) \<and>
               fst e = edge (a, b)} = 
             (if (a,b) \<in> \<E> then { (edge (a, b), vertex a) , (edge (a, b), vertex b)} else {})" for a b
      by auto
    have a2: "{e. ((\<exists>a b. e = (edge (a, b), vertex a) \<and> (a, b) \<in> \<E>) \<or>
                (\<exists>a b. e = (edge (a, b), vertex b) \<and> (a, b) \<in> \<E>)) \<and>
               snd e = edge (a, b)} = {}" for a b
      by auto 
    have a4: "{e. ((\<exists>a b. e = (edge (a, b), vertex a) \<and> (a, b) \<in> \<E>) \<or>
                     (\<exists>a b. e = (edge (a, b), vertex b) \<and> (a, b) \<in> \<E>)) \<and>
                    snd e = vertex x2} = 
               {(edge (a, b), vertex x2)| a b. (a, b) \<in> \<E> \<and> (x2 = a \<or> x2 = b)}" for x2 
      by auto
    have b'_met:"v\<in>dVs \<E>' \<Longrightarrow> - flow_network_spec.ex fst snd \<E>' f' v = \<b>' v" for v
    proof(goal_cases)
      case 1
      show ?case
      proof(cases v)
        case (edge x1)
        hence empty_simper:" {e \<in> {(edge e, vertex (fst e)) |e. e \<in> \<E>} \<union> {(edge e, vertex (snd e)) |e. e \<in> \<E>}. snd e = v}
                = {}" by auto
        have x1_in_E:"x1 \<in> \<E>" 
          using 1 edge unfolding dVs_def \<E>'_def \<E>1_def \<E>2_def by auto
        have d1:"(\<Sum>x\<in>{e. ((\<exists>a b. e = (edge (a, b), vertex a) \<and> (a, b) \<in> \<E>) \<or>
               (\<exists>a b. e = (edge (a, b), vertex b) \<and> (a, b) \<in> \<E>)) \<and>
              fst e = edge x1}. g x) = 
              g (edge x1, vertex (fst x1)) + g (edge x1, vertex (snd x1))" for g        
          using x1_in_E assms(2) 
          by(auto simp add: a1[of "fst x1" "snd x1", simplified prod.collapse] two_sum_remove, 
              cases x1, auto)
        have d2: "f' (edge x1, vertex (snd x1))  + f' (edge x1, vertex (fst x1)) = \<u> x1 "
          if "v = edge x1" "x1 \<in> \<E>"
        proof-
          show ?thesis
            using that assms(2)
            unfolding case1(2) Let_def \<E>1_def \<E>2_def  
          proof(subst if_P, goal_cases)
            case 2
            thus ?case
            proof(subst if_not_P, goal_cases)
              case 2
              thus ?case 
                by(cases x1) auto
            qed force
          qed force
        qed
        have "- (sum f' {e \<in> \<E>'. snd e = v} - sum f' {e \<in> \<E>'. fst e = v}) = \<b>' v"
          using edge x1_in_E 
          by (unfold empty_simper \<E>'_def \<E>1_def \<E>2_def)(auto  simp add: d1 \<b>'_def intro: d2)
        thus ?thesis 
          by(simp add: flow_network_spec.ex_def  multigraph_spec.delta_minus_def
              multigraph_spec.delta_plus_def)
      next
        case (vertex x1)
        hence empty_simper:" {e \<in> {(edge e, vertex (fst e)) |e. e \<in> \<E>} \<union> {(edge e, vertex (snd e)) |e. e \<in> \<E>}. fst e = v}
                = {}" by auto
        have set_sum_split:"{(edge (a, b), vertex x1) |a b. (a, b) \<in> \<E> \<and> (x1 = a \<or> x1 = b)}
               = {(edge (a, b), vertex x1) |a b. (a, b) \<in> \<E> \<and> x1 = a}
                 \<union> {(edge (a, b), vertex x1) |a b. (a, b) \<in> \<E> \<and> x1 = b}" by auto
        have summation_split: "(\<Sum>e'\<in>{(edge (a, b), vertex x1) |a b. (a, b) \<in> \<E> \<and> x1 = a} \<union>
             {(edge (a, b), vertex x1) |a b. (a, b) \<in> \<E> \<and> x1 = b}. g e') =
              (\<Sum>e'\<in>{(edge (a, b), vertex x1) |a b. (a, b) \<in> \<E> \<and> x1 = a} . g e') + 
             (\<Sum>e'\<in> {(edge (a, b), vertex x1) |a b. (a, b) \<in> \<E> \<and> x1 = b}. g e')" for g
          using assms(2) 
          by (auto intro: comm_monoid_add_class.sum.union_disjoint 
              finite_subset[OF _ finites(1)] finite_subset[OF _ finites(2)]) 
        have summation_u:"(\<Sum>e'\<in>{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}. 
                       (\<u> (edge_of (fst e')))) =
                       (sum \<u> {e \<in> \<E>. fst e = x1})"         
        proof(rule cong[OF refl, of _ _ ], 
            subst sum_inj_on[of "edge_of o fst" "{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}" \<u>, 
              simplified, symmetric ], goal_cases)
          case 1
          show ?case
            by(auto split: hitchcock_wrapper.split simp add: inj_on_def)
        next
          case 2
          show ?case
            by(force intro: cong[of "sum _", OF refl] split: hitchcock_wrapper.split simp add: image_Collect)
        qed
        have summation_snd: "(\<Sum>e'\<in>{(edge (a, x1), vertex x1) |a. (a, x1) \<in> \<E>}. f (edge_of (fst e'))) =
                               sum f {e \<in> \<E>. snd e = x1}"
        proof(subst sum_inj_on[of "edge_of o fst" "{(edge (a, x1), vertex x1) |a. (a, x1) \<in> \<E>}" f, 
              simplified, symmetric ], goal_cases)
          case 1
          thus ?case
            by(auto split: hitchcock_wrapper.split simp add: inj_on_def)
        next
          case 2
          thus ?case
            by(force intro: cong[of "sum _", OF refl] split: hitchcock_wrapper.split simp add:  image_Collect) 
        qed
        have summation_fst:
          "(\<Sum>e'\<in>{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}. f (edge_of (fst e'))) =
                    sum f {e \<in> \<E>. fst e = x1}"
        proof(subst sum_inj_on[of "edge_of o fst" "{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}" f, 
              simplified, symmetric ], goal_cases)
          case 1
          thus ?case
            by(auto split: hitchcock_wrapper.split simp add: inj_on_def)
        next
          case 2
          thus ?case
            by(force intro: cong[of "sum _", OF refl] split: hitchcock_wrapper.split simp add:  image_Collect) 
        qed
        have final_helper: "
                   - (\<Sum>x\<in>{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}. \<u> (edge_of (fst x)) - f (edge_of (fst x))) -
                (\<Sum>x\<in>{(edge (a, x1), vertex x1) |a. (a, x1) \<in> \<E>}. f (edge_of (fst x))) =
                \<b> x1 - sum \<u> (multigraph_spec.delta_plus \<E> fst x1)"
          if "v = vertex x1" "\<And> x. (x, x) \<notin> \<E>"
          using 1 that
          by(subst sym[OF ex_b])
            (auto simp add: flow_network_spec.ex_def  multigraph_spec.delta_minus_def
              multigraph_spec.delta_plus_def summation_u summation_fst summation_snd sum_subtractf
              \<E>'_def \<E>1_def \<E>2_def dVs_def )
        have second_final_helper: "
           - (\<Sum>e'\<in>{e. ((\<exists>a b. e = (edge (a, b), vertex a) \<and> (a, b) \<in> \<E>) \<or>
                  (\<exists>a b. e = (edge (a, b), vertex b) \<and> (a, b) \<in> \<E>)) \<and>
                 snd e = vertex x1}.
                 if \<exists>a b. e' = (edge (a, b), vertex b) \<and> (a, b) \<in> \<E> then f (edge_of (fst e'))
                 else if e' \<in> {(edge e, vertex (fst e)) |e. e \<in> \<E>} then \<u> (edge_of (fst e')) 
                                                                 - f (edge_of (fst e'))
                 else undefined) = \<b> x1 - sum \<u> (multigraph_spec.delta_plus \<E> fst x1)"
          if "v = vertex x1" "\<And> x. (x, x) \<notin> \<E>"
          using that
        proof((subst a4[of x1] set_sum_split summation_split)+, goal_cases)
          case 1
          thus ?case
          proof(subst sum_if_not_P[where i="\<lambda> y x. x", simplified], goal_cases)
            case 2
            thus ?case
              by(subst sum_if_P[where i="\<lambda> y x. x", simplified]| force intro!: final_helper)+
          qed force
        qed
        have "- (sum f' {e \<in> {(edge e, vertex (fst e)) |e. e \<in> \<E>} \<union>
                 {(edge e, vertex (snd e)) |e. e \<in> \<E>}. snd e = v} -  0) =
            (case v of edge e \<Rightarrow> \<u> e | vertex x \<Rightarrow> \<b> x - sum \<u> (multigraph_spec.delta_plus \<E> fst x))"
          using vertex assms(2)
          by (unfold case1(2) Let_def  \<E>1_def \<E>2_def)(auto intro: second_final_helper)
        thus ?thesis
          by(auto simp only: empty_simper sum.empty 
              simp add: flow_network_spec.ex_def  multigraph_spec.delta_minus_def
              multigraph_spec.delta_plus_def \<E>'_def \<E>1_def \<E>2_def \<b>'_def)
      qed
    qed
    show ?case
    proof(rule conjI, goal_cases)
      case 1
      then show ?case 
        by(auto simp add: b'_met flow_network_spec.isbflow_def isuflow' multigraph_spec.make_pair_def)
    next
      case 2
      have E'_costs_split: "(\<Sum>e\<in>\<E>'. f' e * \<c>' e) = 
              (\<Sum>e\<in>\<E>1. f' e * \<c>' e) + (\<Sum>e\<in>\<E>2. f' e * \<c>' e)" 
        apply(subst \<E>'_def comm_monoid_add_class.sum.union_disjoint)+
        using finites assms(2)
        by (auto simp add: \<E>1_def \<E>2_def)
      have E1_sum_0:"(\<Sum>e\<in>\<E>1. f' e * \<c>' e) = 0" 
        unfolding \<E>1_def \<E>2_def \<c>'_def case1(2)  setcompr_eq_image      
        apply(subst sum_inj_on, simp add: inj_on_def)+
        using assms(2)
        by(auto simp add: sum_if_P f_of_double_if_cond_same 
            intro: forw_subst[OF sum_if_not_P])
      have E2_sum_is: "(\<Sum>e\<in>\<E>2. f' e * \<c>' e)  = (\<Sum>x\<in>\<E>. f x * \<c> x)" 
        unfolding \<E>1_def \<E>2_def \<c>'_def case1(2)  setcompr_eq_image
        apply(subst sum_inj_on, simp add: inj_on_def)+
        by simp
      from 2 show ?case 
        by(simp add: cost_flow_spec.\<C>_def E'_costs_split E2_sum_is E1_sum_0)
    qed
  qed
  show claim2:"\<And> f f'. ?x f' \<Longrightarrow> ?y f f' \<Longrightarrow> ?z f f'"
    unfolding new_f_def old_f_def
  proof(goal_cases)
    case (1 f f')
    note case1=this
    show ?case 
    proof(rule conjI, goal_cases)
      case 1
      have flow_distr_two_edges:"(edge e, vertex (fst e)) \<in> \<E>1 \<Longrightarrow> f'  (edge e, vertex (fst e)) 
                                                 = \<u> e - f' (edge e, vertex (snd e))" for e
      proof(goal_cases)
        case 1
        hence dVs': "edge e  \<in> dVs \<E>'" "vertex (snd e) \<in> dVs \<E>'"
          unfolding dVs_def \<E>'_def \<E>1_def \<E>2_def
          by blast+
        hence "real_of_ereal (\<u> e) = - flow_network_spec.ex fst snd \<E>' f' (edge e)"
          using case1(1)
          by (auto simp add: flow_network_spec.isbflow_def  \<b>'_def multigraph_spec.make_pair_def)
        moreover have "multigraph_spec.delta_plus \<E>' fst (edge e)
                = {(edge e, vertex (fst e)), (edge e, vertex (snd e))}"
          unfolding multigraph_spec.delta_plus_def
          using 1
          by(cases e) (auto simp add:  \<E>'_def \<E>1_def \<E>2_def)
        moreover have "multigraph_spec.delta_minus \<E>' snd (edge e) = {}"
          by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def multigraph_spec.delta_minus_def)
        moreover have "(edge e, vertex (fst e))\<noteq> (edge e, vertex (snd e))"
          using 1 assms(2) by(cases e) (auto simp add: \<E>'_def \<E>1_def)
        ultimately have "\<u> e = f' (edge e, vertex (fst e)) + f' (edge e, vertex (snd e))"
          by (auto simp add: flow_network_spec.ex_def)
        then show ?case by simp
      qed
      have "flow_network_spec.isuflow \<E> (ereal o \<u>) f" 
        unfolding flow_network_spec.isuflow_def comp_def
      proof(rule ballI, goal_cases)
        case (1 e)
        hence dVs': "edge e  \<in> dVs \<E>'" "vertex (snd e) \<in> dVs \<E>'"
          unfolding dVs_def \<E>'_def \<E>1_def \<E>2_def
          by blast+
        hence "real_of_ereal (\<u> e) = - flow_network_spec.ex fst snd \<E>' f' (edge e)"
          using case1(1)
          by (auto simp add: flow_network_spec.isbflow_def  \<b>'_def multigraph_spec.make_pair_def)
        moreover have "multigraph_spec.delta_plus \<E>' fst (edge e) = {(edge e, vertex (fst e)), (edge e, vertex (snd e))}"
          unfolding multigraph_spec.delta_plus_def
          using 1
          by(cases e) (auto simp add:  \<E>'_def \<E>1_def \<E>2_def)
        moreover have "multigraph_spec.delta_minus \<E>' snd (edge e) = {}"
          by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def multigraph_spec.delta_minus_def)
        moreover have "(edge e, vertex (fst e))\<noteq> (edge e, vertex (snd e))"
          using 1 assms(2) by(cases e) auto
        ultimately have "\<u> e = f' (edge e, vertex (fst e)) + f' (edge e, vertex (snd e))"
          by (auto simp add: flow_network_spec.ex_def )
        moreover have "f' (edge e, vertex (fst e)) \<ge> 0" "f' (edge e, vertex (snd e)) \<ge> 0"
          using case1(1) 1
          unfolding flow_network_spec.isbflow_def
          unfolding flow_network_spec.isuflow_def 
          unfolding \<E>'_def \<E>1_def \<E>2_def
          by fast+
        ultimately show ?case
          by(simp add: case1(2))
      qed
      moreover have "\<forall>v\<in>dVs \<E>. - flow_network_spec.ex fst snd \<E> f v = \<b> v"
      proof(rule ballI, goal_cases)
        case (1 v)
        hence "vertex v \<in> dVs \<E>'"
          by(auto simp add: \<E>'_def \<E>1_def \<E>2_def dVs_def , blast, metis insertI1 insert_commute)
        hence "- (sum f' (multigraph_spec.delta_minus  \<E>' snd (vertex v)) 
                         - sum f' (multigraph_spec.delta_plus \<E>' fst (vertex v))) =
                    \<b> v - real_of_ereal (sum \<u> (multigraph_spec.delta_plus \<E> fst v))"
          using case1(1) 
          by(auto simp add: flow_network_spec.isbflow_def \<b>'_def flow_network_spec.ex_def multigraph_spec.make_pair_def)
        moreover have "multigraph_spec.delta_plus \<E>' fst (vertex v) = {}"
          by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def  multigraph_spec.delta_plus_def)
        moreover have "sum f' (multigraph_spec.delta_minus \<E>' snd (vertex v)) = 
                     sum f' ( multigraph_spec.delta_minus \<E>' snd (vertex v) \<inter> \<E>1) +
                     sum f' (multigraph_spec.delta_minus \<E>' snd (vertex v) \<inter> \<E>2)"
          unfolding  multigraph_spec.delta_minus_def \<E>'_def
          apply(subst sym[OF comm_monoid_add_class.sum.union_disjoint])
          using \<E>'_def finiteE'  Es_non_inter 
          by(auto intro: cong[of "sum f'", OF refl]) 
        moreover have "sum f' (multigraph_spec.delta_minus \<E>' snd (vertex v) \<inter> \<E>2) = 
                      sum (\<lambda> e. f' (edge e, vertex (snd e))) (multigraph_spec.delta_minus \<E> snd v)"
        proof(subst sum_inj_on[of "(\<lambda> e. (edge e, vertex (snd e)))" _ f', simplified, symmetric], goal_cases)
          case 2
          thus ?case
            by(auto intro: cong[of "sum f'", OF refl] 
                simp add: multigraph_spec.delta_minus_def \<E>'_def \<E>1_def \<E>2_def)
        qed(simp add: inj_on_def)
        moreover have "sum f' ( multigraph_spec.delta_minus \<E>' snd (vertex v) \<inter> \<E>1) = 
                     sum (\<lambda> e. \<u> e - f' (edge e, vertex (snd e))) (multigraph_spec.delta_plus \<E> fst v)"
        proof(subst  sum_cong[OF sym[OF flow_distr_two_edges]], goal_cases)
          case 2
          thus ?case
          proof(subst sum_inj_on[of "(\<lambda> e. (edge e, vertex (fst e)))" _ "ereal o f'", 
                simplified, symmetric], goal_cases)
            case 2
            thus ?case
              by(auto intro: cong[of "sum f'", OF refl] 
                  simp add:  multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def 
                  \<E>'_def \<E>1_def \<E>2_def)
          qed (simp add: inj_on_def)
        qed (fastforce simp add:  \<E>1_def  multigraph_spec.delta_plus_def)
        moreover have "sum (\<lambda> e. \<u> e - f' (edge e, vertex (snd e))) (multigraph_spec.delta_plus \<E> fst v)
                      = sum \<u> (multigraph_spec.delta_plus \<E> fst v)
                         - sum (\<lambda> e. f' (edge e, vertex (snd e))) (multigraph_spec.delta_plus \<E> fst v)"
          by(auto simp add: sum_subtractf[of _ _ "multigraph_spec.delta_plus \<E> fst v"])
        ultimately show ?case
          by(simp add: flow_network_spec.ex_def case1(2))
      qed
      ultimately show ?case
        by(simp add: flow_network_spec.isbflow_def multigraph_spec.make_pair_def)
    next
      case 2
      have costs_E'_split: "(\<Sum>e\<in>\<E>'. f' e * \<c>' e) = 
           (\<Sum>e\<in>\<E>1. f' e * \<c>' e) + (\<Sum>e\<in>\<E>2. f' e * \<c>' e)"
        using  finiteE' 
        by (auto simp add: comm_monoid_add_class.sum.union_disjoint \<E>'_def Es_non_inter)
      have costs_E1_0: " (\<Sum>e\<in>\<E>1. f' e * \<c>' e) = 0"
        unfolding \<c>'_def 
        using Es_non_inter  
        by(subst sum_if_not_P[of \<E>1 _ ])(auto simp add: inj_on_def case1(2) image_def) 
      have costs_E2_is: "(\<Sum>e\<in>\<E>2. f' e * \<c>' e) = (\<Sum>e\<in>\<E>. f e * \<c> e)"
        unfolding \<c>'_def 
      proof(subst sum_if_P[of \<E>2 _ ], goal_cases)
        case 2
        have inj_help: "inj_on (\<lambda>e. (edge e, vertex (snd e))) \<E>" 
          by(simp add: inj_on_def) 
        have sum_set_eq:"{(edge (a, b), vertex b) |a b. (a, b) \<in> \<E>} = (\<lambda>e. (edge e, vertex (snd e))) ` \<E>"
          by auto
        show ?case
          by(simp add: sum_inj_on[of "\<lambda> e. (edge e, vertex (snd e))" \<E> 
                "\<lambda> e. f' e *  \<c> (edge_of (fst e))", simplified, OF inj_help, symmetric] sum_set_eq
              case1(2) \<E>2_def)
      qed
      show ?case 
        by(auto simp add: cost_flow_spec.\<C>_def costs_E'_split costs_E1_0 costs_E2_is)
    qed
  qed
  show  "\<nexists> C. closed_w \<E>' C"
  proof(rule notI, goal_cases)
    case 1
    then obtain C where C_props: "closed_w \<E>' C" by auto
    then obtain u where u_props: "awalk \<E>' u C u" "0 < length C" by (auto simp add: closed_w_def)
    have C_in_E': "set C \<subseteq> \<E>'" 
      using u_props(1) by(auto simp add: awalk_def)
    have C_ends: "fst (hd C) = u" "snd (last C) = u"
      using awalk_fst_last u_props(1) u_props(2) by force+
    show ?case
    proof(cases C rule: list_cases3)
      case 1
      then show ?thesis 
        using u_props(2) by simp
    next
      case (2 e)
      then show ?thesis 
        using C_in_E' C_ends by(auto simp add: \<E>'_def \<E>1_def \<E>2_def) 
    next
      case (3 e d rest)
      obtain ee where ee:"e = (edge ee, vertex (fst ee)) \<or> e = (edge ee, vertex (snd ee))"
        using 3 C_in_E' \<E>'_def \<E>1_def \<E>2_def by force
      moreover obtain dd where dd: "d = (edge dd, vertex (fst dd)) \<or> d = (edge dd, vertex (snd dd))"
        using 3 C_in_E' \<E>'_def \<E>1_def \<E>2_def by force
      moreover have "snd e = fst d" 
        using 3
        by (metis awalk_Cons_iff u_props(1))
      ultimately show False by auto  
    qed
  qed
  show "cost_flow_spec.is_Opt fst snd  (ereal \<circ> \<u>) \<E> \<c> \<b> f \<Longrightarrow>
    f' = new_f \<E> \<u> f \<Longrightarrow> cost_flow_spec.is_Opt fst snd \<u>' \<E>' \<c>' \<b>' f'"
  proof(goal_cases)
    case 1
    hence bflow:"flow_network_spec.isbflow fst snd  \<E> (ereal o \<u>) f \<b>"
      using assms(1) cost_flow_network.intro cost_flow_spec.is_Opt_def by blast
    hence bflow':"flow_network_spec.isbflow fst snd  \<E>' \<u>' f' \<b>'"
      using "1"(2) claim1 by blast 
    moreover have "flow_network_spec.isbflow fst snd  \<E>' \<u>' g' \<b>' \<Longrightarrow>
           cost_flow_spec.\<C> \<E>' \<c>' f' \<le> cost_flow_spec.\<C> \<E>' \<c>' g'" for g'
    proof-
      assume asm: "flow_network_spec.isbflow fst snd  \<E>' \<u>' g' \<b>'"
      have "flow_network_spec.isbflow fst snd  \<E> (ereal o \<u>) (old_f g') \<b>"
        "cost_flow_spec.\<C> \<E> \<c> (old_f g') = cost_flow_spec.\<C> \<E>' \<c>' g'"
        using claim2[OF asm refl] by auto
      moreover have "cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f'"
        using claim1[OF bflow] 1(2) by simp
      ultimately show ?thesis 
        using 1(1) 
        by(auto simp add: cost_flow_spec.is_Opt_def)
    qed
    ultimately show ?case
      by(auto intro: cost_flow_spec.is_OptI)
  qed
  show "cost_flow_spec.is_Opt fst snd  \<u>' \<E>' \<c>' \<b>' f' \<Longrightarrow>
    f = old_f f' \<Longrightarrow> cost_flow_spec.is_Opt fst snd  (ereal \<circ> \<u>) \<E> \<c> \<b> f"
  proof(goal_cases)
    case 1
    hence bflow':"flow_network_spec.isbflow fst snd   \<E>' \<u>' f' \<b>'" 
      using cost_flow' cost_flow_spec.is_Opt_def by blast
    hence bflow:"flow_network_spec.isbflow fst snd  \<E> (ereal o \<u>) f \<b>"
      using "1"(2) claim2 by blast 
    moreover have "flow_network_spec.isbflow fst snd  \<E> (ereal o \<u>) g \<b> \<Longrightarrow>
           cost_flow_spec.\<C> \<E> \<c> f \<le> cost_flow_spec.\<C> \<E> \<c> g" for g
    proof-
      assume asm: "flow_network_spec.isbflow fst snd  \<E> (ereal o \<u>) g \<b>"
      have "flow_network_spec.isbflow fst snd   \<E>' \<u>' (new_f \<E> \<u> g) \<b>'"
        "cost_flow_spec.\<C> \<E>' \<c>' (new_f \<E> \<u> g) = cost_flow_spec.\<C> \<E> \<c> g"
        using claim1[OF asm refl] by auto
      moreover have "cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f'"
        using claim2[OF bflow'] 1(2) by simp
      ultimately show ?thesis 
        using 1(1) 
        by(auto simp add: cost_flow_spec.is_Opt_def)
    qed
    ultimately show ?case 
      by(auto intro: cost_flow_spec.is_OptI)
  qed
qed

end