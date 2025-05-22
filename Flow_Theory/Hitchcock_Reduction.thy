section \<open>Eliminating Capacities\<close>
theory Hitchcock_Reduction
  imports Cost_Optimality
begin

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

definition "new_make_pair_gen fstv sndv = (\<lambda> e. (new_fstv_gen fstv e, new_sndv_gen fstv sndv e))"

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

definition "new_f_gen fstv \<E> \<u> arbit f = (\<lambda> e'. (let e = edge_of (new_fstv_gen fstv e') in
                               (if e' \<in> new_\<E>1_gen \<E> \<u> then real_of_ereal (\<u> e) - f e
                                else if e' \<in> new_\<E>2_gen \<E> \<u>  then f e else
                                if e' \<in> new_\<E>3_gen \<E> \<u>  then f (get_edge e')
                                else arbit e')))"

definition "old_f_gen \<E> \<u> f' = (\<lambda> e. if e \<in> flow_network_spec.infty_edges \<E> \<u> then f' (vtovedge e)
                    else  f' (outedge e))"

theorem reduction_of_mincost_flow_to_hitchcock_general:
  fixes \<c> \<b> D
  assumes "flow_network fstv sndv make_pair create_edge (\<u>::'edge_type \<Rightarrow> ereal) \<E>"
  defines "fstv' \<equiv> new_fstv_gen fstv"
  defines "sndv' \<equiv> new_sndv_gen fstv sndv"
  defines "make_pair' \<equiv> new_make_pair_gen fstv sndv"
  defines "create_edge' \<equiv> new_create_edge_gen"

  defines "\<E>1 \<equiv> new_\<E>1_gen \<E> \<u>"
  defines "\<E>2 \<equiv> new_\<E>2_gen \<E> \<u>"
  defines "\<E>3 \<equiv> new_\<E>3_gen \<E> \<u>"
  defines "\<E>' \<equiv> \<E>1 \<union> \<E>2 \<union> \<E>3"
  defines "\<u>' \<equiv> (\<lambda> e. PInfty)"
  defines "\<c>' \<equiv> new_\<c>_gen D fstv \<E> \<u> \<c>"
  defines "\<b>' \<equiv> new_\<b>_gen fstv \<E> \<u> \<b>"
shows 
   "flow_network fstv' sndv' make_pair' create_edge' \<u>' \<E>'" (is ?case1) and
   "\<And> f f' arbit. flow_network_spec.isbflow fstv sndv make_pair \<E> \<u> f \<b> \<Longrightarrow> 
                   f' = new_f_gen fstv \<E> \<u> arbit f
       \<Longrightarrow>flow_network_spec.isbflow fstv' sndv' make_pair' \<E>' \<u>' f' \<b>' \<and> (cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f')" 
      (is "\<And> f f' arbit. ?a f f' \<Longrightarrow> ?b f f' arbit \<Longrightarrow> ?c f f'") and
   "\<And> f f'. flow_network_spec.isbflow fstv' sndv' make_pair' \<E>' \<u>' f' \<b>' \<Longrightarrow> 
          f = old_f_gen \<E> \<u>  f' \<Longrightarrow>
          flow_network_spec.isbflow fstv sndv make_pair \<E> \<u> f \<b> \<and> (cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f')"
      (is "\<And> f f'. ?x f f' \<Longrightarrow> ?y f f' \<Longrightarrow> ?z f f'") and
     "(\<exists> C. closed_w (make_pair' ` \<E>') (map make_pair' C) \<and> foldr (\<lambda> e acc. \<c>' e + acc) C 0 < 0 \<and> set C \<subseteq> \<E>') \<longleftrightarrow>
      (\<exists> D. closed_w (make_pair ` \<E>) (map make_pair D) \<and> foldr (\<lambda> e acc. \<c> e + acc) D 0 < 0 \<and> set D \<subseteq> \<E>
           \<and> (\<forall> e \<in> set D. \<u> e = PInfty))" and
"\<And> f f' arbit. f' = (\<lambda> e'. (let e = edge_of (fstv' e') in (if e' \<in> \<E>2 then f e else
                                          if e' \<in> \<E>1 then real_of_ereal (\<u> e) - f e
                                          else arbit e'))) \<Longrightarrow> arbit = (\<lambda> e'. f (edge_of (fstv' e'))) \<Longrightarrow>
f = (\<lambda>e. f' (outedge e))" (is "\<And> f f' arbit. ?x1 f f' arbit \<Longrightarrow> ?y1 f arbit \<Longrightarrow> ?z1 f f'")
   "\<And> f f' . f = old_f_gen \<E> \<u> f' \<Longrightarrow>
    cost_flow_spec.is_Opt fstv' sndv' make_pair' \<u>' \<E>' \<c>' \<b>' f'
\<Longrightarrow> cost_flow_spec.is_Opt fstv sndv make_pair \<u> \<E> \<c> \<b> f" 
(is "\<And> f f'.  ?b1 f f'\<Longrightarrow> ?c1 f' \<Longrightarrow> ?d1 f ") and
   "\<And> f f' . f' = new_f_gen fstv \<E> \<u> arbit f
\<Longrightarrow> cost_flow_spec.is_Opt fstv sndv make_pair \<u> \<E> \<c> \<b> f
\<Longrightarrow>  cost_flow_spec.is_Opt fstv' sndv' make_pair' \<u>' \<E>' \<c>' \<b>' f'" 
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
      by (simp add: assms(2) assms(3) make_pair'_def new_make_pair_gen_def)
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
     unfolding \<c>'_def new_\<c>_gen_def new_\<E>1_gen_def new_\<E>2_gen_def new_\<E>3_gen_def
          \<E>1_def \<E>2_def \<E>3_def new_fstv_gen_def fstv'_def by simp
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
  moreover have mgraph':"multigraph fstv' sndv' make_pair' create_edge'  \<E>'"
    using assms(1) finiteE' nonemptyE'
    by(auto simp add: flow_network_def multigraph_def fstv'_def sndv'_def make_pair'_def create_edge'_def)   
  ultimately show residual':"flow_network fstv' sndv' make_pair' create_edge' \<u>' \<E>'"
     using assms(1) 
     by(auto simp add: flow_network_def \<u>'_def flow_network_axioms_def)
  have cost_flow: "cost_flow_network fstv sndv make_pair create_edge \<u> \<E>"
    by (simp add: assms(1) cost_flow_network.intro)
  have mgraph: "multigraph fstv sndv make_pair create_edge \<E>"
    using assms(1) flow_network_def by blast
  have flow_network: "flow_network fstv sndv make_pair create_edge \<u> \<E>" 
    by (simp add: assms(1))
  have cost_flow': "cost_flow_network fstv' sndv' make_pair' create_edge' \<u>' \<E>'"
        by (simp add: residual' cost_flow_network.intro)
   have Es_non_inter: "\<E>1 \<inter> \<E>2 = {}"  "\<E>1 \<inter> \<E>3 = {}"  "\<E>2 \<inter> \<E>3 = {}"
     using \<E>1_def \<E>2_def \<E>3_def assms(2) by fastforce+
   show claim1:"\<And> f f' arbit. ?a f f' \<Longrightarrow> ?b f f' arbit \<Longrightarrow> ?c f f'"
     unfolding new_f_gen_def old_f_gen_def
     unfolding symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
            symmetric[OF fstv'_def_old] 
   proof(goal_cases)
     case (1 f f' arbit)
     note case1=this[simplified]
     have ex_b:"\<And> v. v\<in>dVs (make_pair ` \<E>) \<Longrightarrow> - flow_network_spec.ex fstv sndv \<E> f v = \<b> v"
       using case1 by(auto simp add: flow_network_spec.isbflow_def)
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
              {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.
         sndv' e = v}
                = {}" by (auto simp add: sndv'_def)
         have x1_in_E:"x1 \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>" 
           using 1 edge by(auto simp add:dVs_def \<E>'_def \<E>1_def \<E>2_def \<E>3_def  make_pair'_def sndv'_def fstv'_def)
         have set_spliter: "{e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
                  {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
                  {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.
             fstv' e = v} 
            = {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
             fstv' e = v} \<union>
             {e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.
             fstv' e = v} \<union>
             {e \<in> {vtovedge e | e. e \<in>  flow_network_spec.infty_edges \<E> \<u>}.
              fstv' e = v}" by auto
         have da:"\<u> x1 \<noteq> \<infinity> \<Longrightarrow>
                sum g {e. (\<exists>ea. e = inedge ea \<and> ea \<in> \<E> \<and> (ea \<in> \<E> \<longrightarrow> \<u> ea \<noteq> \<infinity>)) \<and> fstv' e = edge x1} +
               sum g {e. (\<exists>ea. e = outedge ea \<and> ea \<in> \<E> \<and> (ea \<in> \<E> \<longrightarrow> \<u> ea \<noteq> \<infinity>)) \<and> fstv' e = edge x1} +
                sum g {e. (\<exists>ea. e = vtovedge ea \<and> ea \<in> \<E> \<and> \<u> ea = \<infinity>) \<and> fstv' e = edge x1} =
                g (inedge x1) + g (outedge x1) " for g 
             apply(rule forw_subst[of "sum _ _" 0])
              apply(rule forw_subst[of _ "{}"])
               apply (force simp add: fstv'_def)
              apply force
             apply simp
             apply(rule sum_eq_split)
              apply(rule forw_subst[of _ "sum _ {inedge x1}", OF _ ])
               apply simp
              apply(rule cong[of "sum g"])
               apply simp
             using x1_in_E apply (auto simp add: fstv'_def)[1]
             apply(rule forw_subst[of _ "sum _ {outedge x1}", OF _ ])
             using x1_in_E 
             by (force intro!: cong[of "sum g" _ _ "{_}", OF refl] simp add: fstv'_def)+
         
         have d1:"sum g
        {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {vtovedge e | e . e \<in> flow_network_spec.infty_edges \<E> \<u>}.
         fstv' e = v} = 
              (if \<u> x1 < PInfty then g (inedge x1) + g (outedge x1)
               else 0)" for g 
           apply(subst set_spliter)
           apply(subst comm_monoid_add_class.sum.union_disjoint)
           using finites flow_network_spec.infty_edges_def apply auto[3]
           apply(subst comm_monoid_add_class.sum.union_disjoint)
           using finites flow_network_spec.infty_edges_def assms(2) apply auto[3]          
           using x1_in_E edge
           by(auto intro: da forw_subst[of "sum _ _" 0] forw_subst[of _ "{}"] 
                  simp add: flow_network_spec.infty_edges_def)

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
                                simp add: \<E>'_def make_pair'_def sndv'_def fstv'_def \<E>1_def \<E>2_def \<E>3_def)
         qed
           
         have i1: "(get_edge `
            {vtovedge e |e. e \<in> \<E> \<and> fstv e = x1 \<and> \<u> e = \<infinity> }) =
              {e \<in> \<E>. fstv e = x1 \<and> \<u> e = \<infinity>}"
           by (auto simp add: image_def)
         have h0: "(\<Sum>x\<in>{vtovedge e |e. e \<in> \<E> \<and> fstv e = x1 \<and> \<u> e = \<infinity>}. f (get_edge x)) =
                     sum f {e \<in> \<E>. fstv e = x1 \<and> \<u> e = \<infinity>} "
           apply(subst sum_inj_on[of get_edge _ f, simplified, symmetric])
           subgoal 
             apply(rule  inj_onI)
             subgoal for x y
               by(cases x, all \<open>cases y\<close>) auto
             done
           by(simp add: i1)
         have "(\<Sum>x\<in>{vtovedge e |e. e \<in> \<E> \<and> fstv e = x1 \<and> \<u> e = \<infinity>}.
                 if \<exists>e. x = inedge e \<and> e \<in> \<E> \<and> (e \<in> \<E> \<longrightarrow> \<u> e \<noteq> \<infinity>)
                  then real_of_ereal (\<u> (edge_of (fstv' x))) - f (edge_of (fstv' x))
                   else if x \<in> \<E>2 then f (edge_of (fstv' x)) else if x \<in> \<E>3 then f (get_edge x) else arbit x) =
               sum f {e \<in> \<E>. fstv e = x1 \<and> \<u> e = \<infinity>}"
           apply(subst sum_if_not_P)
           apply(auto simp add: \<E>2_def \<E>3_def)[1]
           apply(subst sum_if_not_P)
           apply(auto simp add: \<E>2_def \<E>3_def)[1]
           apply(subst sum_if_P)
            by(auto simp add: \<E>2_def \<E>3_def sum_if_P flow_network_spec.infty_edges_def
                       intro: h0)
          hence h1: "sum f' {vtovedge e |e. e \<in> flow_network_spec.delta_plus_infty fstv \<E> \<u> x1} =
              sum f (flow_network_spec.delta_plus_infty fstv \<E> \<u> x1)"
           by(auto simp add:  flow_network_spec.delta_plus_infty_def
                 flow_network_spec.infty_edges_def case1(2) \<E>1_def \<E>2_def \<E>3_def Let_def)
           have h2: "sum f'
        {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u> } \<union>
              {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>} \<union>
              {vtovedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.
         sndv' e = v} = 
         sum f'
           {e \<in> {inedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}.sndv' e = v} +
        (sum f'
        {e \<in> {outedge e |e. e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>}. sndv' e = v} +
         sum f'
        {e \<in> {vtovedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u>}. sndv' e = v})"
           apply(subst sym[OF comm_monoid_add_class.sum.union_disjoint])
           using  finiteE'[simplified \<E>'_def \<E>1_def \<E>2_def \<E>3_def] apply auto[3]
           apply(subst sym[OF comm_monoid_add_class.sum.union_disjoint])
           using finiteE'[simplified \<E>'_def \<E>1_def \<E>2_def \<E>3_def]  assms(2) 
           by(auto intro: cong[of "sum f'", OF refl]) 
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
           apply(subst sum_inj_on[of "\<lambda> x. (edge_of (fstv' x))" _ f, simplified, symmetric])
           subgoal 
             apply(rule  inj_onI)
             subgoal for x y
               by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
             done
           apply(rule forw_subst[of _ 
            "{outedge e |e. e \<in> \<E> \<and> sndv e = x1} - 
                {outedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u> \<and> sndv e = x1}"])
           apply(force simp add: sndv'_def)
           apply(subst flow_network_spec.infty_edges_def)
           using multigraph_spec.delta_minus_def flow_network_spec.delta_minus_infty_def
          apply(subst inj_on_image_set_diff[OF _ Diff_subset])
           subgoal 
             apply(rule  inj_onI)
             subgoal for x y
               by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
             done
           using i4 i5 
           by (auto simp add: flow_network_spec.delta_minus_infty_def multigraph_spec.delta_minus_def)
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
           apply(subst sum_inj_on[of "\<lambda> x. (edge_of (fstv' x))" _ _, simplified, symmetric])
           subgoal 
             apply(rule  inj_onI)
             subgoal for x y
               by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
             done
           apply(rule forw_subst[of _ 
            "{inedge e |e. e \<in> \<E> \<and> fstv e = x1} - 
                {inedge e | e. e \<in> flow_network_spec.infty_edges \<E> \<u> \<and> fstv e = x1}"])
            apply (force simp add: sndv'_def)
           apply(subst flow_network_spec.infty_edges_def)
          unfolding multigraph_spec.delta_plus_def flow_network_spec.delta_plus_infty_def
          apply(subst inj_on_image_set_diff[OF _ Diff_subset])
           subgoal 
             apply(rule  inj_onI)
             subgoal for x y
               by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
             done
           using i6 i7 by auto
        have h5: "(\<Sum>x\<in>{e \<in> {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>}.
               sndv' e = vertex x1}.
           f (get_edge x)) = 
                 sum f (flow_network_spec.delta_minus_infty sndv \<E> \<u> x1)"
           apply(subst sum_inj_on[of get_edge _ _, simplified, symmetric],
                   force simp add: inj_on_def, rule cong[of "sum _", OF refl])
          by(fastforce simp add: image_def inj_on_def multigraph_spec.delta_minus_def 
                flow_network_spec.delta_minus_infty_def flow_network_spec.infty_edges_def sndv'_def)+
        have excess_at_x1: " sum f (multigraph_spec.delta_plus \<E> fstv x1) - sum f (multigraph_spec.delta_minus \<E> sndv x1) = \<b> x1"
          using case1(1) x_in_V 
          by(auto simp add: flow_network_spec.isbflow_def flow_network_spec.ex_def)
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
          by (auto intro:  forw_subst[OF comm_monoid_add_class.sum.union_disjoint[symmetric]] simp add: finite_subset)
      
        show ?thesis
          unfolding flow_network_spec.ex_def  multigraph_spec.delta_minus_def
           multigraph_spec.delta_plus_def
          unfolding \<E>'_def \<E>1_def \<E>2_def \<b>'_def \<E>3_def
          apply(simp only: almost_empty_simper)
          apply(subst h1)
          apply(subst h2)
          apply(subst vertex)+
          apply(subst hitchcock_wrapper.simps(6))
          (*Unfolding the flow and simplification of the if*)
          apply(subst case1(2))
          apply(subst Let_def)
          apply(subst sum_if_P)
          using \<E>1_def apply simp
          apply(subst case1(2))
          apply(subst Let_def)
          apply(subst (2) sum_if_not_P)
          using \<E>1_def assms(2) apply force
          apply(subst (2) sum_if_P, simp add: \<E>2_def)
          apply(subst case1(2))
          apply(subst Let_def)
          apply(subst (3) sum_if_not_P, force simp add: \<E>1_def assms(3))
          apply(subst (3) sum_if_not_P, force simp add: \<E>2_def)
          apply(subst (3) sum_if_P, simp add: \<E>3_def)
          (*transforming to sums over sets of edges in the original graph*)
          apply(subst h3)
          apply(subst h4)
          apply(subst h5)
          by(fastforce simp add: algebra_simps h6 sum_subtractf)
       qed
    qed
    show ?case
    proof(rule, goal_cases)
      case 1
      then show ?case 
        by(auto simp add: b'_met flow_network_spec.isbflow_def isuflow')
    next
      case 2
      have is_E: "(\<lambda>x. edge_of (fstv' x)) `
          {outedge e |e. e \<in> \<E> \<and> e \<notin> flow_network_spec.infty_edges \<E> \<u>} \<union>
           get_edge `
          {vtovedge e |e. e \<in> flow_network_spec.infty_edges \<E> \<u>} = \<E>"
        by(fastforce simp add: image_def flow_network_spec.infty_edges_def fstv'_def split: hitchcock_edge.split
                  elim!: get_edge.cases)
      show ?case 
        text \<open>unfold the costs and edges\<close>
        unfolding cost_flow_spec.\<C>_def cost_flow_spec.\<C>_def
        unfolding \<E>'_def \<E>1_def \<E>2_def \<c>'_def case1(2) \<E>3_def
        text \<open>split the new costs\<close>
        apply(subst comm_monoid_add_class.sum.union_disjoint)
        using finites apply (simp, simp)
        using assms(3) apply force
        apply(subst comm_monoid_add_class.sum.union_disjoint)
        using finites apply (simp, simp)
        using assms(2) apply force
        text \<open>Deal with the new flow\<close>
        unfolding Let_def
        apply(subst (2) sum_if_P, simp)
        apply(subst (2) sum_if_P, simp)
        apply(subst (3) sum_if_not_P)
        using assms(2) apply force
        apply(subst (3) sum_if_P, simp)
        apply(subst (3) sum_if_not_P)
        using assms(2) apply force
        apply(subst (3) sum_if_P, simp)
        apply(subst (3) sum_if_not_P, force simp add: assms(3))
        apply(subst (4) sum_if_not_P, fast)
        apply(subst (4) sum_if_not_P, fast)
        apply(subst (4) sum_if_P, simp)
        apply(subst (4) sum_if_not_P, fast)
        apply(subst (4) sum_if_not_P, fast)
        apply(subst (4) sum_if_P, simp)
        text \<open>Re-assemble the sums\<close>
        apply(subst sum_inj_on[of "\<lambda>x. edge_of (fstv' x)" _ "\<lambda> e. f e * \<c> e",simplified, symmetric])
            subgoal 
             apply(rule  inj_onI)
             subgoal for x y
               by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
             done
          apply(subst sum_inj_on[of get_edge _ "\<lambda> e. f e * \<c> e",
                       simplified, symmetric])
             subgoal 
             apply(rule  inj_onI)
             subgoal for x y
               by(cases x, all \<open>cases y\<close>) (auto simp add: fstv'_def)
             done
           using finites is_E cong[OF refl is_E, of "sum ( \<lambda> e. f e * \<c> e)", symmetric] 
           by(auto intro:  forw_subst[OF sym[OF comm_monoid_add_class.sum.union_disjoint]] simp add: fstv'_def )
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
    proof(rule, goal_cases)
      case 1
      have flow_distr_two_edges:"(inedge e) \<in> \<E>1 \<Longrightarrow> f'  (inedge e) 
                                                 = real_of_ereal (\<u> e) - f' (outedge e)" for e
     proof(goal_cases)
       case 1
       thm 1[simplified \<E>1_def]
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
                   simp add: flow_network_spec.isbflow_def  \<b>'_def \<E>1_def )
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
      proof(rule,  goal_cases)
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
         by (auto simp add: flow_network_spec.isbflow_def  \<b>'_def)
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
         using case1(1)
         unfolding flow_network_spec.isbflow_def
         unfolding flow_network_spec.isuflow_def 
         using edges_in
         by(auto simp add: \<E>'_def)
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
         unfolding flow_network_spec.isbflow_def
         unfolding flow_network_spec.isuflow_def 
         by(auto simp add: \<E>'_def)
     next
       case MInf
       thus ?thesis 
         by (simp add: u_pos)
     qed
     qed
     moreover have "\<forall>v\<in>dVs (make_pair ` \<E>). - flow_network_spec.ex fstv sndv \<E> f v = \<b> v"
     proof(rule, goal_cases)
       case (1 v)
       then obtain e where "e \<in> \<E>" "v = fstv e \<or> v = sndv e"
         using assms(1)
         by(auto simp add: dVs_def flow_network_def multigraph_def) 
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
         by(auto simp add: flow_network_spec.isbflow_def \<b>'_def flow_network_spec.ex_def)
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
         apply(subst sum_inj_on[of outedge _ f', simplified, symmetric])
         subgoal
           unfolding inj_on_def by simp
         apply(rule cong[of "sum f'", OF refl])
         unfolding multigraph_spec.delta_minus_def 
         by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def  multigraph_spec.delta_minus_def flow_network_spec.delta_minus_infty_def
                           flow_network_spec.infty_edges_def sndv'_def)
        
       moreover have "sum f' ( multigraph_spec.delta_minus \<E>' sndv' (vertex v) \<inter> \<E>1) = 
                     sum (\<lambda> e. real_of_ereal (\<u> e) - f' (outedge e)) 
                          (multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v)"
         apply(subst (2) sum_cong flow_distr_two_edges)
          apply(rule sym[OF flow_distr_two_edges])
         subgoal
           unfolding \<E>1_def 
           by(fastforce simp add: multigraph_spec.delta_plus_def flow_network_spec.delta_plus_infty_def
                                   flow_network_spec.infty_edges_def)   
         apply(subst sum_inj_on[of inedge _ "f'", 
                 symmetric, simplified o_def])
         subgoal
           unfolding inj_on_def by simp
         apply(rule cong[of "sum f'", OF refl])
         unfolding multigraph_spec.delta_plus_def 
                   multigraph_spec.delta_minus_def
         by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def \<E>3_def  
                           flow_network_spec.delta_plus_infty_def
                           flow_network_spec.infty_edges_def sndv'_def)
       moreover have "sum (\<lambda> e. real_of_ereal (\<u> e) - f' (outedge e)) 
                          (multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v)
                      = sum (real_of_ereal \<circ> \<u>) (multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v)
                         - sum (\<lambda> e. f' (outedge e)) 
                             (multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v)"
         by(auto simp add: sum_subtractf[of _ _ "multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v"])
       moreover have "sum f' (multigraph_spec.delta_minus \<E>' sndv' (vertex v) \<inter> \<E>3) 
                       =  sum (\<lambda> e. f' (vtovedge e))
                          (flow_network_spec.delta_minus_infty sndv \<E> \<u> v)" 
         apply(subst sum_inj_on[of vtovedge _ "f'", symmetric, simplified o_def])
         subgoal
           unfolding inj_on_def by auto
         apply(rule cong[of "sum f'", OF refl])
         unfolding multigraph_spec.delta_minus_def
         by(auto simp add: \<E>'_def \<E>1_def \<E>2_def \<E>3_def image_def 
                           flow_network_spec.infty_edges_def  
                           flow_network_spec.delta_minus_infty_def sndv'_def)
       moreover have "
          (\<Sum>e\<in>multigraph_spec.delta_minus \<E> sndv v - flow_network_spec.delta_minus_infty sndv \<E> \<u> v.
                  f' (outedge e)) +      
          (\<Sum>e\<in>flow_network_spec.delta_minus_infty sndv \<E> \<u> v. f' (vtovedge e)) = 
          sum f (multigraph_spec.delta_minus \<E> sndv v)"
         apply(subst sum_inj_on[of outedge _ f', simplified, symmetric], simp add: inj_on_def)
         apply(subst sum_inj_on[of vtovedge _ f', simplified, symmetric], force simp add: inj_on_def)
         apply(subst comm_monoid_add_class.sum.union_disjoint[symmetric])
         using flow_network.finite_infinite_deltas[OF flow_network] 
               multigraph.finite_deltas[OF mgraph] apply (simp, simp, force)
         unfolding case1(2)
         apply(subst if_distrib[of f', symmetric])
         apply(subst sum_inj_on[of "\<lambda> e. if _ e then _ e else _ e" _ f',
                     simplified, symmetric])
         by (fastforce intro!: cong[of "sum f'", OF refl] 
                simp add: image_def multigraph_spec.delta_minus_def
                          flow_network_spec.delta_minus_infty_def
                          flow_network_spec.infty_edges_def inj_on_def)+
        moreover have "
          (\<Sum>e\<in>multigraph_spec.delta_plus \<E> fstv v - flow_network_spec.delta_plus_infty fstv \<E> \<u> v.
                  f' (outedge e)) +      
          (\<Sum>e\<in>flow_network_spec.delta_plus_infty fstv \<E> \<u> v. f' (vtovedge e)) = 
          sum f (multigraph_spec.delta_plus \<E> fstv v)"
         apply(subst sum_inj_on[of outedge _ f', simplified, symmetric], simp add: inj_on_def)
         apply(subst sum_inj_on[of vtovedge _ f',simplified, symmetric], force simp add: inj_on_def)
         apply(subst comm_monoid_add_class.sum.union_disjoint[symmetric])
         using flow_network.finite_infinite_deltas[OF flow_network] 
               multigraph.finite_deltas[OF mgraph] apply (simp, simp, force)
         unfolding case1(2)
         apply(subst if_distrib[of f', symmetric])
         apply(subst sum_inj_on[of "\<lambda> e. if _ e then _ e else _ e" _ f',
                     simplified, symmetric])
         by (force intro: cong[of "sum f'", OF refl] 
                simp add: image_def multigraph_spec.delta_plus_def
                          flow_network_spec.delta_plus_infty_def
                          flow_network_spec.infty_edges_def inj_on_def )+
      moreover have "sum f' {vtovedge e | e. e \<in> flow_network_spec.delta_plus_infty fstv \<E> \<u> v}
             = (\<Sum>e\<in>flow_network_spec.delta_plus_infty fstv \<E> \<u> v. f' (vtovedge e))" 
        by(subst sum_inj_on[of vtovedge _ f', simplified, symmetric])
          (force intro: cong[of "sum f'", OF refl] simp add: image_def inj_on_def)+    
       ultimately show ?case 
         by(auto simp add: flow_network_spec.ex_def)
     qed
     ultimately show ?case 
       by(auto simp add: flow_network_spec.isbflow_def)
   next
     case 2
     have helper1:"(\<Sum>e\<in>\<E>. f e * \<c> e) = 
        (\<Sum>e \<in> flow_network_spec.infty_edges \<E> \<u>.  f' (vtovedge e) * \<c> e) +
        (\<Sum>e \<in> \<E> - flow_network_spec.infty_edges \<E> \<u>. f' (outedge e) * \<c> e)"
       unfolding 1(2)
       apply(subst (2) Un_Diff_cancel2[of \<E> "flow_network_spec.infty_edges \<E> \<u>", simplified
              flow_network.infty_edges_in_E[OF assms(1), simplified subset_Un_eq Un_commute],
              symmetric])
       apply(subst comm_monoid_add_class.sum.union_disjoint)
       using multigraph.finite_E[OF mgraph]  flow_network.finite_infty_edges[OF flow_network]
        sum_if_not_P[of "\<E> - flow_network_spec.infty_edges \<E> \<u>"]
        sum_if_P[of "flow_network_spec.infty_edges \<E> \<u>"]
       by auto
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
     show ?case 
       unfolding cost_flow_spec.\<C>_def \<c>'_def 
       unfolding \<E>'_def
       apply(subst comm_monoid_add_class.sum.union_disjoint[OF auxes(1,2,3)])
       apply(subst comm_monoid_add_class.sum.union_disjoint[OF auxes(4,5) Es_non_inter(1)])

       apply(subst sum_if_P[of "\<E>1" _ ], simp)
       apply(subst  sum_if_not_P[of \<E>2 _ ])
       using Es_non_inter apply fast
       apply(subst sum_if_P[of \<E>2 _ ], simp)
       apply(subst sum_if_not_P[of \<E>3 _ ])
       using Es_non_inter sum_if_P[of \<E>3 ] helper1 helper2 helper3 
       by (auto intro: forw_subst[OF  sum_if_not_P[of \<E>3 _ ]])
   qed
 qed
  show claim3:  "(\<exists> C. closed_w (make_pair' ` \<E>') (map make_pair' C) \<and> foldr (\<lambda> e acc. \<c>' e + acc) C 0 < 0 \<and> set C \<subseteq> \<E>') \<longleftrightarrow>
      (\<exists> D. closed_w (make_pair ` \<E>) (map make_pair D) \<and> foldr (\<lambda> e acc. \<c> e + acc) D 0 < 0 \<and> set D \<subseteq> \<E>
           \<and> (\<forall> e \<in> set D. \<u> e = PInfty))"
  proof(rule, goal_cases)
    case 1
    then obtain C where C_prop:"closed_w (make_pair' ` \<E>') (map make_pair' C)"
                               "foldr (\<lambda>e. (+) (\<c>' e)) C 0 < 0" "set C \<subseteq> \<E>'"
      by auto
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
        by(auto intro: map_cong[OF refl] simp add: make_pair'_def fstv'_def sndv'_def \<E>3_def flow_network_def multigraph_def
                  split: hitchcock_edge.split)
      have "closed_w (make_pair ` \<E>) (map make_pair D)"
      proof-
        have "C \<noteq> [] \<Longrightarrow>
        flow_network fstv sndv make_pair create_edge \<u> \<E> \<Longrightarrow>
        awalk (make_pair ` \<E>) (vertex_of u) (map ((\<lambda>e. (vertex_of (fst e), vertex_of (snd e))) \<circ> make_pair') C)
        (vertex_of u)"
      by(fastforce intro!: subset_mono_awalk[OF awalk_map[OF _ u_prop(1)], simplified, OF _ refl, of vertex_of] 
                 simp add: make_pair'_def fstv'_def sndv'_def \<E>3_def flow_network_def multigraph_def
                           flow_network_spec.infty_edges_def map_C_is)
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
      using C_prop(2) by auto
  next
    case 2
    then obtain D where D_prop: "closed_w (make_pair ` \<E>) (map make_pair D)" "foldr (\<lambda>e. (+) (\<c> e)) D 0 < 0" 
                                "(\<forall>e\<in>set D. \<u> e = PInfty)" "set D \<subseteq> \<E>"by auto
    then obtain u where u_prop: "awalk (make_pair ` \<E>)  u (map make_pair D) u" "0 < length D"
      by(auto simp add: closed_w_def)
    have D_infty_edges:"set D \<subseteq> flow_network_spec.infty_edges \<E> \<u>"
      using D_prop(3,4) 
      by(fastforce simp add:flow_network_spec.infty_edges_def)
    have map_make_pair': "(map make_pair' (map vtovedge D)) =  map (\<lambda>e. (vertex (fst e), vertex (snd e))) (map make_pair D)"
      using assms(1) by (auto simp add: make_pair'_def fstv'_def sndv'_def flow_network_def multigraph_def)

    have awalk_E3:"awalk (make_pair' ` \<E>3) (vertex u) (map make_pair' (map vtovedge D)) (vertex u)"
      using u_prop(2) D_infty_edges
      apply(subst map_make_pair')
      using assms(1) 
      by (fastforce intro!: subset_mono_awalk'[OF awalk_map[OF _ u_prop(1)], OF _ refl, of vertex] 
                      simp add: make_pair'_def fstv'_def sndv'_def \<E>3_def image_def flow_network_def multigraph_def 
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
      using  D_prop(2) by fastforce
  qed
  note claim1=claim1[simplified new_f_gen_def old_f_gen_def, simplified
        symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
            symmetric[OF fstv'_def_old]]
  note claim2=claim2[simplified new_f_gen_def old_f_gen_def, simplified
        symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
            symmetric[OF fstv'_def_old]]
  show claim5: "\<And> f f' arbit. ?x1 f f' arbit \<Longrightarrow> ?y1 f arbit \<Longrightarrow> ?z1 f f'"
    by(auto simp add: Let_def \<E>1_def \<E>2_def fstv'_def) 
  show claim4: "\<And> f f'.  ?b1 f f'\<Longrightarrow> ?c1 f' \<Longrightarrow> ?d1 f "
     unfolding new_f_gen_def old_f_gen_def
     unfolding symmetric[OF \<E>1_def_old] symmetric[OF \<E>2_def_old] symmetric[OF \<E>3_def_old]
            symmetric[OF fstv'_def_old] 
  proof(goal_cases)
    case (1 f f')
    note case1=this
     note optf=1
      hence opt_unfold: "flow_network_spec.isbflow fstv' sndv' make_pair' \<E>' \<u>' f' \<b>'"
    "(\<And> f''. flow_network_spec.isbflow fstv' sndv' make_pair' \<E>' \<u>' f'' \<b>' 
            \<Longrightarrow> cost_flow_spec.\<C> \<E>' \<c>' f' \<le> cost_flow_spec.\<C> \<E>' \<c>' f'')"
        by(auto simp add: cost_flow_spec.is_Opt_def)
      have claim2_result:"cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f'" "flow_network_spec.isbflow fstv sndv make_pair \<E> \<u> f \<b>"
        using claim2[OF opt_unfold(1)] case1 by simp+
      show ?case
      proof(rule ccontr, goal_cases)
        case 1
        then obtain d where d_prop:"flow_network_spec.isbflow fstv sndv make_pair \<E> \<u> d \<b>" 
                             "cost_flow_spec.\<C> \<E> \<c> d < cost_flow_spec.\<C> \<E> \<c> f"
          using claim2_result(2) by(auto simp add: cost_flow_spec.is_Opt_def)
        define d' where "d' =
    (\<lambda>e'. let e = edge_of (fstv' e')
           in if e' \<in> \<E>1 then real_of_ereal (\<u> e) - d e
              else if e' \<in> \<E>2 then d e
                   else if e' \<in> \<E>3 then d (get_edge e')
                        else undefined)"
        have d'_flow: "flow_network_spec.isbflow fstv' sndv' make_pair' \<E>' \<u>' d' \<b>'" 
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
    hence opt_unfold: "flow_network_spec.isbflow fstv sndv make_pair \<E> \<u> f \<b>"
    "(\<And> f'. flow_network_spec.isbflow fstv sndv make_pair \<E> \<u> f' \<b> \<Longrightarrow> cost_flow_spec.\<C> \<E> \<c> f \<le> cost_flow_spec.\<C> \<E> \<c> f')"
        by(auto simp add: cost_flow_spec.is_Opt_def)
      have claim1_result: "flow_network_spec.isbflow fstv' sndv' make_pair' \<E>' \<u>' f' \<b>' \<and>
                           cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f'" 
        using  case1 by(auto intro!: claim1[OF opt_unfold(1)]) 
      hence claim1_result:"cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f'" 
        "flow_network_spec.isbflow fstv' sndv' make_pair' \<E>' \<u>' f' \<b>'"
        by auto
      show ?case
      proof(rule ccontr, goal_cases)
        case 1
        then obtain d' where d'_prop:"flow_network_spec.isbflow fstv' sndv' make_pair' \<E>' \<u>' d' \<b>'" 
                             "cost_flow_spec.\<C> \<E>' \<c>' d' < cost_flow_spec.\<C> \<E>' \<c>' f'"
          using claim1_result 
          by(auto simp add: cost_flow_spec.is_Opt_def)
        define d where "d = (\<lambda>e. if e \<in> flow_network_spec.infty_edges \<E> \<u> then d' (vtovedge e)
          else d' (outedge e))"
        have d_flow: "flow_network_spec.isbflow fstv sndv make_pair \<E> \<u> d \<b>" 
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

definition "new_\<c> \<E> \<u> \<c> = (\<lambda> e'. if e' \<in> new_\<E>2 \<E> \<u> then \<c> (edge_of (fst e')) else if e' \<in> new_\<E>1 \<E> \<u> 
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
  assumes "flow_network fst snd id Pair (ereal o \<u>) \<E>"
  assumes "\<nexists> x. (x,x) \<in> \<E>"
  defines "\<E>1 \<equiv> new_\<E>1 \<E> \<u>"
  defines "\<E>2 \<equiv> new_\<E>2 \<E> \<u>"
  defines "\<E>' \<equiv> \<E>1 \<union> \<E>2"
  defines "\<u>' \<equiv> (\<lambda> e. PInfty)"
  defines "\<c>' \<equiv> new_\<c> \<E> \<u> \<c>"
  defines "\<b>' \<equiv> new_\<b> \<E> \<u> \<b>"
shows 
   "flow_network fst snd id Pair \<u>' \<E>'" (is ?case1) and
   "\<And> f f'. flow_network_spec.isbflow fst snd id \<E> (ereal o \<u>) f \<b> \<Longrightarrow> f' = new_f \<E> \<u> f
       \<Longrightarrow>flow_network_spec.isbflow fst snd id \<E>' \<u>' f' \<b>' \<and> (cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f')" 
      (is "\<And> f f'. ?a f \<Longrightarrow> ?b f f' \<Longrightarrow> ?c  f f'") and
"\<And> f f'. flow_network_spec.isbflow fst snd id \<E>' \<u>' f' \<b>' \<Longrightarrow> f = old_f f' \<Longrightarrow>
          flow_network_spec.isbflow fst snd id \<E> (ereal o \<u>) f \<b> \<and> (cost_flow_spec.\<C> \<E> \<c> f = cost_flow_spec.\<C> \<E>' \<c>' f')"
      (is "\<And> f f'. ?x f' \<Longrightarrow> ?y f f'\<Longrightarrow> ?z f f'") and
"cost_flow_spec.is_Opt fst snd id (ereal o \<u>) \<E> \<c> \<b> f \<Longrightarrow> f' = new_f \<E> \<u> f \<Longrightarrow>
 cost_flow_spec.is_Opt fst snd id  \<u>' \<E>' \<c>' \<b>' f'"
 and
"cost_flow_spec.is_Opt fst snd id  \<u>' \<E>' \<c>' \<b>' f' \<Longrightarrow> f = old_f f' \<Longrightarrow>
 cost_flow_spec.is_Opt fst snd id (ereal o \<u>) \<E> \<c> \<b> f " and
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
   ultimately show residual':"flow_network fst snd id Pair \<u>' \<E>'"
     using assms(1) 
     by(auto simp add: flow_network_def \<u>'_def multigraph_def flow_network_axioms_def)
   have cost_flow: "cost_flow_network fst snd id Pair \<u> \<E>" 
     using assms(1)
     by (auto simp add: comp_def cost_flow_network_def)
   have cost_flow': "cost_flow_network fst snd id Pair \<u>' \<E>'"
     using residual'
     by (auto simp add: comp_def cost_flow_network_def)
   have flow_network': "flow_network fst snd id Pair \<u>' \<E>'"
     using residual'
     by (auto simp add: comp_def cost_flow_network_def)
   have flow_network: "flow_network fst snd id Pair \<u> \<E>"
     using assms(1)
     by (auto simp add: comp_def cost_flow_network_def)
   have mgraph': "multigraph fst snd id Pair \<E>'"
     using flow_network_def residual' by blast
   have mgraph: "multigraph fst snd id Pair \<E>"
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
       using case1 by(auto simp add: flow_network_spec.isbflow_def)
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
               snd e = edge (a, b)} = 
             {}" for a b
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
         have d2: "v = edge x1 \<Longrightarrow> x1 \<in> \<E> \<Longrightarrow> f' (edge x1, vertex (snd x1)) 
                        + f' (edge x1, vertex (fst x1)) = \<u> x1 "
          unfolding case1(2) Let_def \<E>1_def \<E>2_def  
          apply(subst if_P)
          apply force
          apply(subst if_not_P)
          using assms(2) apply force
          apply(subst if_P)
          by force+
         show ?thesis 
          unfolding flow_network_spec.ex_def  multigraph_spec.delta_minus_def
           multigraph_spec.delta_plus_def
          apply(simp only: empty_simper \<E>'_def \<E>1_def \<E>2_def \<b>'_def )
          using edge x1_in_E 
          by (auto simp add: d1 intro: d2)
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
           using assms(2) 
            apply (simp add: not_infty_ereal)
           apply(rule cong[OF refl, of _ _ ])
           apply(subst sum_inj_on[of "edge_of o fst" "{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}" \<u>, 
                    simplified, symmetric ])
           subgoal
             by(auto split: hitchcock_wrapper.split simp add: inj_on_def)
           by(force intro: cong[of "sum _", OF refl] split: hitchcock_wrapper.split simp add: image_Collect)
         have summation_snd: "(\<Sum>e'\<in>{(edge (a, x1), vertex x1) |a. (a, x1) \<in> \<E>}. f (edge_of (fst e'))) =
                               sum f {e \<in> \<E>. snd e = x1}"
           apply(subst sum_inj_on[of "edge_of o fst" "{(edge (a, x1), vertex x1) |a. (a, x1) \<in> \<E>}" f, 
                    simplified, symmetric ])
           subgoal
             by(auto split: hitchcock_wrapper.split simp add: inj_on_def)
           by(force intro: cong[of "sum _", OF refl] split: hitchcock_wrapper.split simp add:  image_Collect) 
         have summation_fst: 
             "(\<Sum>e'\<in>{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}. f (edge_of (fst e'))) =
                    sum f {e \<in> \<E>. fst e = x1}"
           apply(subst sum_inj_on[of "edge_of o fst" "{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}" f, 
                    simplified, symmetric ])
           subgoal
             by(auto split: hitchcock_wrapper.split simp add: inj_on_def)
           by(force intro: cong[of "sum _", OF refl] split: hitchcock_wrapper.split simp add:  image_Collect) 
         have final_helper: "v = vertex x1 \<Longrightarrow>
                  \<forall>x. (x, x) \<notin> \<E> \<Longrightarrow>
                   - (\<Sum>x\<in>{(edge (x1, b), vertex x1) |b. (x1, b) \<in> \<E>}. \<u> (edge_of (fst x)) - f (edge_of (fst x))) -
                (\<Sum>x\<in>{(edge (a, x1), vertex x1) |a. (a, x1) \<in> \<E>}. f (edge_of (fst x))) =
                \<b> x1 - sum \<u> (multigraph_spec.delta_plus \<E> fst x1)"
          using 1 
          by(subst sym[OF ex_b])
            (auto simp add: flow_network_spec.ex_def  multigraph_spec.delta_minus_def
                  multigraph_spec.delta_plus_def summation_u summation_fst summation_snd sum_subtractf
                  \<E>'_def \<E>1_def \<E>2_def dVs_def )
        have second_final_helper: "v = vertex x1 \<Longrightarrow>
    \<forall>x. (x, x) \<notin> \<E> \<Longrightarrow>
    - (\<Sum>e'\<in>{e. ((\<exists>a b. e = (edge (a, b), vertex a) \<and> (a, b) \<in> \<E>) \<or>
                  (\<exists>a b. e = (edge (a, b), vertex b) \<and> (a, b) \<in> \<E>)) \<and>
                 snd e = vertex x1}.
         if \<exists>a b. e' = (edge (a, b), vertex b) \<and> (a, b) \<in> \<E> then f (edge_of (fst e'))
         else if e' \<in> {(edge e, vertex (fst e)) |e. e \<in> \<E>} then \<u> (edge_of (fst e')) - f (edge_of (fst e'))
              else undefined) =
    \<b> x1 - sum \<u> (multigraph_spec.delta_plus \<E> fst x1)"
          apply(simp only:a4[of x1] set_sum_split summation_split )
          apply(subst sum_if_not_P[where i="\<lambda> y x. x", simplified]) 
          apply force
          apply(subst sum_if_P[where i="\<lambda> y x. x", simplified]) apply force
          apply(subst sum_if_P[where i="\<lambda> y x. x", simplified]) 
          by (auto intro: final_helper )
        have "- (sum f' {e \<in> {(edge e, vertex (fst e)) |e. e \<in> \<E>} \<union> {(edge e, vertex (snd e)) |e. e \<in> \<E>}. snd e = v} -
       0) =
    (case v of edge e \<Rightarrow> \<u> e | vertex x \<Rightarrow> \<b> x - sum \<u> (multigraph_spec.delta_plus \<E> fst x))"
          using vertex assms(2)
          unfolding case1(2) Let_def  \<E>1_def \<E>2_def 
          by (auto intro: second_final_helper)
        thus ?thesis
          by(auto simp only: empty_simper sum.empty 
                   simp add: flow_network_spec.ex_def  multigraph_spec.delta_minus_def
                             multigraph_spec.delta_plus_def \<E>'_def \<E>1_def \<E>2_def \<b>'_def)
      qed
    qed
    show ?case
    proof(rule, goal_cases)
      case 1
      then show ?case 
        by(auto simp add: b'_met flow_network_spec.isbflow_def isuflow')
    next
      case 2
      then show ?case 
        unfolding cost_flow_spec.\<C>_def
        unfolding \<E>'_def \<E>1_def \<E>2_def \<c>'_def case1(2) 
        apply(subst comm_monoid_add_class.sum.union_disjoint)
        using finites apply (simp, simp)
        using assms(2) apply force
        apply(subst setcompr_eq_image)+
        apply(subst sum_inj_on, simp add: inj_on_def)+
        apply simp
        apply(subst if_distrib[ of "(*) (if _ then _ else _ )"])
        apply(subst sum_if_not_P)
        using assms(2)
        by(auto simp add: sum_if_P)
    qed
  qed
  show claim2:"\<And> f f'. ?x f' \<Longrightarrow> ?y f f' \<Longrightarrow> ?z f f'"
     unfolding new_f_def old_f_def
  proof(goal_cases)
    case (1 f f')
    note case1=this
    show ?case 
    proof(rule, goal_cases)
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
         by (auto simp add: flow_network_spec.isbflow_def  \<b>'_def)
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
      proof(rule, goal_cases)
        case (1 e)
        hence dVs': "edge e  \<in> dVs \<E>'" "vertex (snd e) \<in> dVs \<E>'"
          unfolding dVs_def \<E>'_def \<E>1_def \<E>2_def
          by blast+
        hence "real_of_ereal (\<u> e) = - flow_network_spec.ex fst snd \<E>' f' (edge e)"
         using case1(1)
         by (auto simp add: flow_network_spec.isbflow_def  \<b>'_def)
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
     proof(rule, goal_cases)
       case (1 v)
       hence "vertex v \<in> dVs \<E>'"
         by(auto simp add: \<E>'_def \<E>1_def \<E>2_def dVs_def , blast, metis insertI1 insert_commute)
       hence "- (sum f' (multigraph_spec.delta_minus  \<E>' snd (vertex v)) 
                         - sum f' (multigraph_spec.delta_plus \<E>' fst (vertex v))) =
                    \<b> v - real_of_ereal (sum \<u> (multigraph_spec.delta_plus \<E> fst v))"
         using case1(1) 
         by(auto simp add: flow_network_spec.isbflow_def \<b>'_def flow_network_spec.ex_def)
       moreover have "multigraph_spec.delta_plus \<E>' fst (vertex v) = {}"
         by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def  multigraph_spec.delta_plus_def)
       moreover have "sum f' (multigraph_spec.delta_minus \<E>' snd (vertex v)) = 
                     sum f' ( multigraph_spec.delta_minus \<E>' snd (vertex v) \<inter> \<E>1) +
                     sum f' (multigraph_spec.delta_minus \<E>' snd (vertex v) \<inter> \<E>2)"
         unfolding  multigraph_spec.delta_minus_def
         unfolding \<E>'_def
         apply(subst sym[OF comm_monoid_add_class.sum.union_disjoint])
         using \<E>'_def finiteE'  Es_non_inter 
         by(auto intro: cong[of "sum f'", OF refl]) 
       moreover have "sum f' (multigraph_spec.delta_minus \<E>' snd (vertex v) \<inter> \<E>2) = 
                      sum (\<lambda> e. f' (edge e, vertex (snd e))) (multigraph_spec.delta_minus \<E> snd v)"
         apply(subst sum_inj_on[of "(\<lambda> e. (edge e, vertex (snd e)))" _ f', simplified, symmetric])
         subgoal
           unfolding inj_on_def by simp
         apply(rule cong[of "sum f'", OF refl])
         unfolding multigraph_spec.delta_minus_def multigraph_spec.delta_minus_def
         by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def)
        
       moreover have "sum f' ( multigraph_spec.delta_minus \<E>' snd (vertex v) \<inter> \<E>1) = 
                     sum (\<lambda> e. \<u> e - f' (edge e, vertex (snd e))) (multigraph_spec.delta_plus \<E> fst v)"
         apply(subst (2) sum_cong flow_distr_two_edges)
          apply(rule sym[OF flow_distr_two_edges])
         subgoal
           unfolding \<E>1_def  multigraph_spec.delta_plus_def by fast
         apply(subst sum_inj_on[of "(\<lambda> e. (edge e, vertex (fst e)))" _ "ereal o f'", 
                simplified, symmetric])
         subgoal
           unfolding inj_on_def by simp
         apply(rule cong[of "sum f'", OF refl])
         unfolding multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def
         by(auto simp add:  \<E>'_def \<E>1_def \<E>2_def)
       moreover have "sum (\<lambda> e. \<u> e - f' (edge e, vertex (snd e))) (multigraph_spec.delta_plus \<E> fst v)
                      = sum \<u> (multigraph_spec.delta_plus \<E> fst v)
                         - sum (\<lambda> e. f' (edge e, vertex (snd e))) (multigraph_spec.delta_plus \<E> fst v)"
         by(auto simp add: sum_subtractf[of _ _ "multigraph_spec.delta_plus \<E> fst v"])
       ultimately show ?case
         by(simp add: flow_network_spec.ex_def case1(2))
     qed
     ultimately show ?case
       by(simp add: flow_network_spec.isbflow_def)
   next
     case 2
     show ?case 
       unfolding cost_flow_spec.\<C>_def \<c>'_def 
       unfolding \<E>'_def
       apply(subst comm_monoid_add_class.sum.union_disjoint)
       using \<E>'_def finiteE' apply blast
       using \<E>'_def finiteE' apply blast
        apply (simp add: Es_non_inter)
       apply(subst sum_if_P[of \<E>2 _ ])
        apply simp
       apply(subst sum_if_not_P[of \<E>1 _ ])
       using Es_non_inter apply auto[1]
       using Es_non_inter sum_if_P[of \<E>1 _ ] collapse_to_img[of "\<lambda> e. (edge e, vertex (snd e))" \<E> ] 
             sum_inj_on[of "\<lambda> e. (edge e, vertex (snd e))" \<E> 
                    "\<lambda> e. f' e *  \<c> (edge_of (fst e))", simplified, symmetric]
             collapse_to_img[of "\<lambda> e. (edge e, vertex (snd e))" \<E> ]
       by(auto simp add: inj_on_def \<E>2_def case1(2) image_def) 
         (smt (verit, ccfv_threshold) Collect_cong prod.collapse snd_conv)
   qed
 qed
  show  "\<nexists> C. closed_w \<E>' C"
  proof(rule, goal_cases)
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
  show "cost_flow_spec.is_Opt fst snd id (ereal \<circ> \<u>) \<E> \<c> \<b> f \<Longrightarrow>
    f' = new_f \<E> \<u> f \<Longrightarrow> cost_flow_spec.is_Opt fst snd id \<u>' \<E>' \<c>' \<b>' f'"
  proof(goal_cases)
    case 1
    hence bflow:"flow_network_spec.isbflow fst snd id \<E> (ereal o \<u>) f \<b>"
      using assms(1) cost_flow_network.intro cost_flow_spec.is_Opt_def by blast
    hence bflow':"flow_network_spec.isbflow fst snd id \<E>' \<u>' f' \<b>'"
      using "1"(2) claim1 by blast 
    moreover have "flow_network_spec.isbflow fst snd id \<E>' \<u>' g' \<b>' \<Longrightarrow>
           cost_flow_spec.\<C> \<E>' \<c>' f' \<le> cost_flow_spec.\<C> \<E>' \<c>' g'" for g'
    proof-
      assume asm: "flow_network_spec.isbflow fst snd id \<E>' \<u>' g' \<b>'"
      have "flow_network_spec.isbflow fst snd id \<E> (ereal o \<u>) (old_f g') \<b>"
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
  show "cost_flow_spec.is_Opt fst snd id \<u>' \<E>' \<c>' \<b>' f' \<Longrightarrow>
    f = old_f f' \<Longrightarrow> cost_flow_spec.is_Opt fst snd id (ereal \<circ> \<u>) \<E> \<c> \<b> f"
  proof(goal_cases)
    case 1
    hence bflow':"flow_network_spec.isbflow fst snd id  \<E>' \<u>' f' \<b>'" 
      using cost_flow' cost_flow_spec.is_Opt_def by blast
    hence bflow:"flow_network_spec.isbflow fst snd id \<E> (ereal o \<u>) f \<b>"
      using "1"(2) claim2 by blast 
    moreover have "flow_network_spec.isbflow fst snd id \<E> (ereal o \<u>) g \<b> \<Longrightarrow>
           cost_flow_spec.\<C> \<E> \<c> f \<le> cost_flow_spec.\<C> \<E> \<c> g" for g
    proof-
      assume asm: "flow_network_spec.isbflow fst snd id \<E> (ereal o \<u>) g \<b>"
      have "flow_network_spec.isbflow fst snd id  \<E>' \<u>' (new_f \<E> \<u> g) \<b>'"
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