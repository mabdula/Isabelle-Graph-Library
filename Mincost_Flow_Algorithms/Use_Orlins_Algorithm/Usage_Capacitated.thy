subsection \<open>Flows in Multigraphs with Capacities\<close>

theory Usage_Capacitated
  imports Instantiation 
          Flow_Theory.Hitchcock_Reduction Flow_Theory.STFlow
begin

  instantiation hitchcock_wrapper::(linorder, linorder) linorder
begin

fun less_eq_hitchcock_wrapper where
"less_eq_hitchcock_wrapper (edge e) (vertex v) = True"|
"less_eq_hitchcock_wrapper (edge e) (edge d) = (e \<ge> d)"|
"less_eq_hitchcock_wrapper (vertex u) (vertex v) = (u \<ge> v)"|
"less_eq_hitchcock_wrapper (vertex v) (edge e) = False"

fun less_hitchcock_wrapper where
"less_hitchcock_wrapper (edge e) (vertex v) = True"|
"less_hitchcock_wrapper (edge e) (edge d) = (e > d)"|
"less_hitchcock_wrapper (vertex u) (vertex v) = (u > v)"|
"less_hitchcock_wrapper (vertex v) (edge e) = False"
instance 
  apply(intro Orderings.linorder.intro_of_class  class.linorder.intro
              class.order_axioms.intro class.order.intro class.preorder.intro
              class.linorder_axioms.intro) 
  subgoal for x y 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>) force+
  subgoal for x
    by(cases x) auto 
  subgoal for x y z
    by(all \<open>cases x\<close>, all \<open>cases y\<close>, all \<open>cases z\<close>)(auto split: if_split simp add: less_le_not_le)
  subgoal for a b
    by(all \<open>cases a\<close>, all \<open>cases b\<close>)
      (auto split: if_split simp add: less_le_not_le)
  subgoal for x y 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>)
      (auto split: if_split simp add: less_le_not_le)
  done
end

 instantiation hitchcock_edge::(linorder, linorder) linorder
begin

fun less_eq_hitchcock_edge::"('a, 'b) hitchcock_edge \<Rightarrow> ('a, 'b) hitchcock_edge \<Rightarrow> bool" where
"less_eq_hitchcock_edge (outedge e) (outedge d) = (e \<le> d)"|
"less_eq_hitchcock_edge (inedge e) (inedge d) = (e \<le> d)"|
"less_eq_hitchcock_edge (vtovedge e) (vtovedge d) = (e \<le> d)"|
"less_eq_hitchcock_edge (dummy x y) (dummy a b) = ((x, y) \<le> (a, b))"|
"less_eq_hitchcock_edge (outedge e) _ = False"|
"less_eq_hitchcock_edge (inedge e) (outedge d) = True"|
"less_eq_hitchcock_edge (inedge e) _ = False"|
"less_eq_hitchcock_edge (vtovedge e) (dummy x y) = False"|
"less_eq_hitchcock_edge (vtovedge e)_ = True"|
"less_eq_hitchcock_edge (dummy x y) _ = True"

fun less_hitchcock_edge::"('a, 'b) hitchcock_edge \<Rightarrow> ('a, 'b) hitchcock_edge \<Rightarrow> bool" where
"less_hitchcock_edge (outedge e) (outedge d) = (e < d)"|
"less_hitchcock_edge (inedge e) (inedge d) = (e < d)"|
"less_hitchcock_edge (vtovedge e) (vtovedge d) = (e < d)"|
"less_hitchcock_edge (dummy x y) (dummy a b) = ((x, y) < (a, b))"|
"less_hitchcock_edge (outedge e) _ = False"|
"less_hitchcock_edge (inedge e) (outedge d) = True"|
"less_hitchcock_edge (inedge e) _ = False"|
"less_hitchcock_edge (vtovedge e) (dummy x y) = False"|
"less_hitchcock_edge (vtovedge e)_ = True"|
"less_hitchcock_edge (dummy x y) _ = True"

instance 
proof(intro Orderings.linorder.intro_of_class  class.linorder.intro
              class.order_axioms.intro class.order.intro class.preorder.intro
              class.linorder_axioms.intro, goal_cases)
  case (1 x y)
  then show ?case 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>) force+
next
  case (2 x)
  then show ?case 
    by(cases x) auto
next
  case (3 x y z)
  then show ?case 
    apply(all \<open>cases x\<close>, all \<open>cases y\<close>, all \<open>cases z\<close>)
    by(auto split: if_split simp add: less_le_not_le ) (metis order.trans)+
next
  case (4 x y)
  then show ?case 
    apply(all \<open>cases x\<close>, all \<open>cases y\<close>)
    by(auto split: if_split simp add: less_le_not_le) (metis nle_le)+
next
  case (5 x y)
  then show ?case 
   by(all \<open>cases x\<close>, all \<open>cases y\<close>)
     (auto split: if_split simp add: less_le_not_le)
qed
end

locale with_capacity =
fixes fst::"('edge_type::linorder) \<Rightarrow> ('a::linorder)"
and snd::"('edge_type::linorder) \<Rightarrow> ('a::linorder)"
and create_edge::"'a \<Rightarrow> 'a \<Rightarrow> 'edge_type"
and \<E>_impl::"'edge_type list"
and \<c>_impl:: "'c_type"
and \<u>_impl:: "(('edge_type::linorder \<times> ereal) \<times> color) tree"
and \<b>_impl:: "(('a::linorder \<times> real) \<times> color) tree"
and c_lookup::"'c_type \<Rightarrow> 'edge_type \<Rightarrow> real option"
begin

definition "\<E>_impl_infty = (filter (\<lambda> e. the (flow_lookup \<u>_impl e) = PInfty) \<E>_impl)"

definition "\<E>_impl_finite = (filter (\<lambda> e. the (flow_lookup \<u>_impl e) < PInfty) \<E>_impl)"

definition "\<E>1_impl = map inedge \<E>_impl_finite"
definition "\<E>2_impl = map outedge \<E>_impl_finite"
definition "\<E>3_impl = map (vtovedge::'edge_type \<Rightarrow> ('a, 'edge_type) hitchcock_edge) \<E>_impl_infty"
definition "\<E>'_impl = \<E>1_impl@\<E>2_impl@\<E>3_impl"

definition "\<c>'_impl = \<c>_impl"

definition "c_lookup' c e = (case e of inedge d \<Rightarrow> Some 0 |
                                       outedge d \<Rightarrow> c_lookup c d |
                                       vtovedge d \<Rightarrow> c_lookup c d |
                                       dummy _ _ \<Rightarrow> None)"

definition "b_lifted = foldr (\<lambda> x tree. bal_update ((vertex::'a \<Rightarrow> ('a, 'edge_type) hitchcock_wrapper) x) (the (bal_lookup \<b>_impl x)) tree) 
            (vs fst snd \<E>_impl) Leaf"

definition " vertices_done = foldr (\<lambda> xy tree. let u = the (flow_lookup \<u>_impl xy) in
                                    bal_update (vertex (fst xy)) 
                                    ((the (bal_lookup tree (vertex (fst xy)) )) - real_of_ereal u) tree) 
            \<E>_impl_finite b_lifted"

definition "\<b>'_impl = foldr (\<lambda> e tree. 
                        bal_update ((edge::'edge_type \<Rightarrow> ('a, 'edge_type) hitchcock_wrapper) e) 
                               (real_of_ereal (the (flow_lookup \<u>_impl e))) tree) \<E>_impl_finite vertices_done"


definition "final_state_cap = final_state (new_fstv_gen fst) (new_sndv_gen fst snd)
                                (new_create_edge_gen) \<E>'_impl \<c>'_impl \<b>'_impl c_lookup'"


definition "final_flow_impl_cap =  final_flow_impl (new_fstv_gen fst) (new_sndv_gen fst snd)
                                (new_create_edge_gen) \<E>'_impl \<c>'_impl \<b>'_impl c_lookup'"

definition "final_flow_impl_original = 
            (let finite_flow = foldr 
                      (\<lambda> e tree. flow_update e (the_default 0 (flow_lookup final_flow_impl_cap (outedge e))) tree)  
                         \<E>_impl_finite flow_empty
             in  foldr (\<lambda> e tree. flow_update e (the_default 0 (flow_lookup final_flow_impl_cap (vtovedge e))) tree)  
                         \<E>_impl_infty finite_flow )"

lemma dom_final_flow_impl_original:"dom (flow_lookup final_flow_impl_original) = set \<E>_impl"
  unfolding final_flow_impl_original_def Let_def
  apply(subst dom_fold)
  apply(simp add: flow_invar_fold flow_map.invar_update flow_map.invar_empty)
  apply(subst dom_fold)
  by (auto simp add: flow_map.map_empty dom_def \<E>_impl_finite_def \<E>_impl_infty_def
                     flow_invar_fold flow_map.invar_update flow_map.invar_empty)

end

lemma flow_lookup_fold: "flow_invar T \<Longrightarrow> flow_lookup  (foldr (\<lambda>e. flow_update e (f e) )AS T) e
          = (if e \<in> set AS then Some (f e) else flow_lookup T e)"
  by(induction AS)
    (auto simp add: flow_map.map_update flow_invar_fold flow_map.invar_update)

lemma b'impl_lookup_general: 
 "bal_invar T \<Longrightarrow> bal_lookup
     (foldr (\<lambda>e. bal_update (edge e) (f e)) ES T)
     x = (case x of edge e \<Rightarrow> if e \<in> set ES then Some (f e) else bal_lookup T x
                    |_ \<Rightarrow> bal_lookup T x)"
  by(induction ES)
    (auto split: hitchcock_wrapper.split simp add: bal_invar_fold bal_map.map_update)

lemma bal_lookup_fold: 
 "bal_invar T \<Longrightarrow> bal_lookup
     (foldr (\<lambda>e. bal_update e (f e)) ES T)
     e = ( if e \<in> set ES then Some (f e) else bal_lookup T e)"
  by(induction ES)
    (auto split: hitchcock_wrapper.split simp add: bal_invar_fold bal_map.map_update)

locale with_capacity_proofs =
with_capacity where fst = "fst::'edge_type::linorder \<Rightarrow> 'a::linorder"
and create_edge = create_edge 
and \<E>_impl = \<E>_impl
and \<u>_impl = \<u>_impl +

cost_flow_network where fst = fst
and snd = snd
and create_edge = create_edge
and \<E> = \<E>
and \<u> = \<u>
and \<c> = \<c>

for fst create_edge \<E>_impl \<u>_impl \<E> \<u> \<c>+
fixes \<b>
assumes c_domain: "\<E> \<subseteq> dom (c_lookup \<c>_impl)"
and     u_domain: "dom (flow_lookup \<u>_impl) = \<E>"
and     b_domain: "dom (bal_lookup \<b>_impl) = \<V>"
and  set_invar_E: "set_invar \<E>_impl"
and bal_invar_b: "bal_invar \<b>_impl"
and       Es_are: "\<E> = to_set \<E>_impl"
and cs_are: "\<c> = the o (c_lookup \<c>_impl)"
and  us_are: "\<u> = the_default PInfty o (flow_lookup \<u>_impl)"
and bs_are:"\<b> = the_default 0 o (bal_lookup \<b>_impl)"
begin

lemma infty_edges_are:"to_set \<E>_impl_infty = infty_edges"
  using  u_domain
  unfolding \<E>_impl_infty_def infty_edges_def 
  by(force simp add: infty_edges_def  to_set_def Es_are us_are the_default_def dom_def)

lemma infty_edges_invar: "set_invar \<E>_impl_infty"
  using invar_filter set_invar_E by (auto simp add: \<E>_impl_infty_def)

lemma finite_edges_are:"to_set \<E>_impl_finite = \<E> - infty_edges"
  using  u_domain
  unfolding \<E>_impl_finite_def infty_edges_def 
  by(force simp add: infty_edges_def to_set_def Es_are us_are the_default_def dom_def) 

lemma finite_edges_invar: "set_invar \<E>_impl_finite"
  using invar_filter set_invar_E by (auto simp add: \<E>_impl_finite_def )

lemma E1_impl_are: "to_set \<E>1_impl = new_\<E>1_gen \<E> \<u>"
  using finite_edges_are
  by(auto simp add: to_set_def \<E>1_impl_def new_\<E>1_gen_def)
 
lemma E2_impl_are: "to_set \<E>2_impl = new_\<E>2_gen \<E> \<u>"
  using finite_edges_are
  by(auto simp add: to_set_def \<E>2_impl_def new_\<E>2_gen_def)

lemma E3_impl_are: "to_set \<E>3_impl = new_\<E>3_gen \<E> \<u>"
  using infty_edges_are
  by(auto simp add: to_set_def \<E>3_impl_def new_\<E>3_gen_def)

lemma correctness_of_algo:"correctness_of_algo fst snd \<E>_impl create_edge \<b>_impl"
 using Es_are b_domain E_not_empty  multigraph_axioms 
  by(auto intro!: correctness_of_algo.intro 
        simp add: to_set_def to_list_def function_generation.\<E>_def[OF selection_functions.function_generation_axioms]
                     function_generation.N_def[OF selection_functions.function_generation_axioms]
                      set_invar_E bal_invar_b  domD make_pair_def)

lemmas vs_and_es = function_generation_proof.vs_and_es[OF correctness_of_algo.function_generation_proof,
                   OF correctness_of_algo]

lemmas es_def = function_generation.es_def[OF selection_functions.function_generation_axioms]

lemma vs_Are:"set (vs fst snd \<E>_impl) = \<V>"
  apply(simp add: vs_def vs_and_es(2) es_def dVs_def )
  by(auto intro!: cong[of "image vertex" _ "\<Union> _" "\<Union> _", OF refl] cong[of "\<Union>", OF refl] 
     simp add:  Es_are to_set_def to_list_def selection_functions.make_pair_def make_pair_def)

lemma dom_b_listed: "dom (bal_lookup b_lifted) = vertex ` \<V>"
  unfolding b_lifted_def bal_lookup_def bal_update_def
  apply(subst dom_fold[simplified flow_lookup_def flow_update_def])
  using flow_map.invar_empty 
  by(auto simp add: RBT_Set.empty_def flow_empty_def vs_Are )
 
lemma pre_b_lifted_lookup:"bal_invar T \<Longrightarrow> bal_lookup (foldr (\<lambda>x. bal_update (vertex x) (the (bal_lookup \<b>_impl x))) xs T) x =
    (case x of edge edge_type \<Rightarrow> bal_lookup T x | vertex y \<Rightarrow> if y \<in> set xs then Some (the (bal_lookup \<b>_impl y)) 
     else  bal_lookup T x)"
  apply(induction xs)
  subgoal
    by(auto split: hitchcock_wrapper.split)
  apply simp
  apply(subst bal_map.map_update)
  by(auto intro!: flow_invar_fold[simplified flow_invar_def flow_update_def]
                       flow_map.invar_update[simplified flow_invar_def flow_update_def]
             split: hitchcock_wrapper.split
             simp add:  bal_lookup_def bal_invar_def bal_update_def)

lemma b_lifted_lookup: "bal_lookup b_lifted x = 
                        (case x of vertex y \<Rightarrow> if y \<in> \<V> then Some (the (bal_lookup \<b>_impl y))
                                               else None |
                         _ \<Rightarrow> None)"
  unfolding b_lifted_def
  apply(subst  pre_b_lifted_lookup)
  using bal_map.invar_empty[simplified RBT_Set.empty_def bal_empty_def]  vs_Are 
  by(auto split: hitchcock_wrapper.split 
       simp add: cong[OF bal_map.map_empty[simplified RBT_Set.empty_def bal_empty_def] refl] )

lemma vertices_done_general_lookup:
"x \<in> dom (bal_lookup bs) \<Longrightarrow> bal_invar bs \<Longrightarrow> distinct ES \<Longrightarrow> bal_lookup (foldr
     (\<lambda>xy tree.
         let u = the (flow_lookup \<u>_impl xy)
         in bal_update (vertex (fst xy))
             (the (bal_lookup tree (vertex (fst xy))) - real_of_ereal u) tree)
         ES bs) x = 
    (case x of vertex u \<Rightarrow> Some (
            the (bal_lookup bs (vertex u))
          -  sum (\<lambda> e.  real_of_ereal (the (flow_lookup \<u>_impl e))) {e | e. e \<in> set ES \<and> u = fst e})
|  _ \<Rightarrow> bal_lookup bs x)"
proof(induction ES)
  case Nil
  then show ?case 
   by(auto split: hitchcock_wrapper.split)
next
  case (Cons a ES)
  then show ?case 
  apply simp
  apply(subst bal_map.map_update)
  subgoal
    by(auto intro: bal_invar_fold)
  by(auto split: hitchcock_wrapper.split) 
    (((subst sym[OF minus_distr], subst add.commute, subst sym[OF sum.insert]);
      (force intro!: cong[of uminus, OF refl] cong[of "sum _", OF refl] simp add: )+),
      metis)
qed

lemma bal_invar_b_lifted: "bal_invar b_lifted"
  using  bal_map.invar_empty 
  by(auto intro: bal_invar_fold simp add:b_lifted_def   RBT_Set.empty_def bal_empty_def)

lemma flow_network2: "flow_network fst snd create_edge
                       (the_default PInfty \<circ> flow_lookup \<u>_impl) \<E>"
  using flow_network_axioms us_are by auto

lemma bal_lookup_vertices_done:"x \<in>  \<V> \<Longrightarrow> bal_lookup vertices_done (vertex x) =
             Some (\<b> x - sum (real_of_ereal o \<u>) 
                        ((delta_plus  x) - (delta_plus_infty  x)))"
  unfolding vertices_done_def
  apply(subst vertices_done_general_lookup)
  using dom_b_listed  bal_invar_b_lifted finite_edges_invar 
  apply(auto simp add: set_invar_def)[3]
  using u_domain b_domain 
  by(simp add: b_lifted_lookup bs_are us_are, unfold delta_plus_def flow_network_spec.delta_plus_infty_def the_default_def)
    (cases "bal_lookup \<b>_impl x", blast, simp,intro sum_cong_extensive, 
          (force simp add: Es_are \<E>_impl_finite_def to_set_def delta_plus_def 
              dom_def the_default_def )+)

lemma dom_vertices_done:"dom (bal_lookup vertices_done) = vertex ` \<V>"
  using fst_E_V
  by (auto simp add: vertices_done_def bal_dom_fold bal_invar_b_lifted dom_b_listed \<E>_impl_finite_def Es_are to_set_def)

lemma bal_invar_vertices_done: "bal_invar vertices_done"
  by(auto intro: bal_invar_fold simp add: bal_invar_b_lifted vertices_done_def)

lemma b'_impl_dom:"dom (bal_lookup \<b>'_impl) = vertex ` \<V> \<union> edge ` (\<E> - infty_edges)"
  unfolding \<b>'_impl_def
  apply(subst bal_dom_fold, simp add: bal_invar_vertices_done)
  using u_domain
  unfolding \<E>_impl_finite_def infty_edges_def 
  by(subst dom_vertices_done)(force simp add: us_are Es_are to_set_def dom_def the_default_def)


lemma bal_invar_b'_impl: "bal_invar \<b>'_impl"
  by (simp add: \<b>'_impl_def bal_invar_fold bal_invar_vertices_done)

lemma b'_impl_lookup:"x \<in> vertex ` \<V> \<union> edge ` (\<E> - infty_edges) \<Longrightarrow>
         the ( bal_lookup \<b>'_impl x) = new_\<b>_gen fst \<E> \<u> \<b> x"
  using finite_edges_are  u_domain
  by(auto split: hitchcock_wrapper.split 
       simp add: to_set_def us_are bal_lookup_vertices_done bal_invar_vertices_done 
                 b'impl_lookup_general \<b>'_impl_def new_\<b>_gen_def dom_def the_default_def)

lemma old_f_gen_final_flow_impl_original_cong:"e \<in> \<E> \<Longrightarrow>
         old_f_gen \<E> \<u> (abstract_flow_map final_flow_impl_cap) e = abstract_flow_map final_flow_impl_original e"
  unfolding old_f_gen_def final_flow_impl_original_def Let_def  abstract_flow_map_def the_default_def abstract_real_map_def
  apply(subst flow_lookup_fold, simp add: flow_invar_fold flow_map.invar_empty flow_map.invar_update)+
  by (auto simp add:sym[OF infty_edges_are, simplified to_set_def]  flow_map.map_empty finite_edges_are[simplified sym[OF infty_edges_are] to_set_def])

lemma set_invar_E':"set_invar \<E>'_impl"
 using  set_invar_E 
  by (auto intro!: distinct_map_filter distinct_filter simp add: distinct_map inj_on_def  set_invar_def
                   \<E>'_impl_def \<E>1_impl_def \<E>2_impl_def \<E>3_impl_def  \<E>_impl_finite_def \<E>_impl_infty_def)

lemma V_new_graph:"dVs (multigraph_spec.make_pair (new_fstv_gen fst) (new_sndv_gen fst snd) ` to_set \<E>'_impl)
                         = vertex ` \<V> \<union> edge ` (\<E> - \<E>\<^sub>\<infinity>)"
proof-
  have 1:"x \<notin> edge `
             (set \<E>_impl - {e \<in> set \<E>_impl. the_default \<infinity> (flow_lookup \<u>_impl e) = \<infinity>}) \<Longrightarrow>
         x \<in> dVs ((\<lambda>x. (edge x, vertex (fst x))) `
                   {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) \<noteq> \<infinity>}) \<Longrightarrow>
         x \<in> vertex ` dVs ((\<lambda>x. (fst x, snd x)) ` set \<E>_impl)" for x 
  proof(goal_cases)
  case (1)
   then obtain e where "x = edge e \<or> x = vertex (fst e)" "e \<in> set \<E>_impl" 
                  " the (flow_lookup \<u>_impl e) \<noteq> \<infinity>" by(auto simp add: dVs_def)
   moreover hence "x \<noteq> edge e" using u_domain 1(1) 
     by(force simp add: dom_def the_default_def Es_are case_simp(1) to_set_def)
  ultimately show ?case 
    unfolding dVs_def
    by(fastforce intro!: imageI intro: exI[of _ "{fst e, snd e}"] simp add: dVs_def)
  qed
  moreover have 2:"x \<notin> edge `
             (set \<E>_impl - {e \<in> set \<E>_impl. the_default \<infinity> (flow_lookup \<u>_impl e) = \<infinity>}) \<Longrightarrow>
         x \<in> dVs ((\<lambda>x. (edge x, vertex (snd x))) `
                   {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) \<noteq> \<infinity>}) \<Longrightarrow>
         x \<in> vertex ` dVs ((\<lambda>x. (fst x, snd x)) ` set \<E>_impl)" for x
  proof(goal_cases)
    case 1
    note 2 = this
   then obtain e where "x = edge e \<or> x = vertex (snd e)" "e \<in> set \<E>_impl" 
                  " the (flow_lookup \<u>_impl e) \<noteq> \<infinity>" by(auto simp add: dVs_def)
    moreover hence "x \<noteq> edge e" using u_domain 2(1) 
     by(force simp add: dom_def the_default_def Es_are case_simp(1) to_set_def)
    ultimately show ?case 
    unfolding dVs_def
    by(fastforce intro!: imageI intro: exI[of _ "{fst e, snd e}"] simp add: dVs_def)
   qed
   moreover have 3:"x \<notin> edge `
             (set \<E>_impl - {e \<in> set \<E>_impl. the_default \<infinity> (flow_lookup \<u>_impl e) = \<infinity>}) \<Longrightarrow>
         x \<in> dVs ((\<lambda>x. (vertex (fst x), vertex (snd x))) `
                   {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) = \<infinity>}) \<Longrightarrow>
         x \<in> vertex ` dVs ((\<lambda>x. (fst x, snd x)) ` set \<E>_impl)" for x
   proof(goal_cases)
     case 1
     note 3=1
   then obtain e where " x = vertex (fst e) \<or> x = vertex (snd e)" "e \<in> set \<E>_impl" 
                  " the (flow_lookup \<u>_impl e) = \<infinity>" by(auto simp add: dVs_def)
   thus ?case 
    unfolding dVs_def
    by(fastforce intro!: imageI intro: exI[of _ "{fst e, snd e}"] simp add: dVs_def)
qed
  moreover have 4:"vertex xa
          \<notin> dVs ((\<lambda>x. (edge x, vertex (fst x))) `
                  {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) \<noteq> \<infinity>}) \<Longrightarrow>
          vertex xa
          \<notin> dVs ((\<lambda>x. (vertex (fst x), vertex (snd x))) `
                  {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) = \<infinity>}) \<Longrightarrow>
          xa \<in> dVs ((\<lambda>x. (fst x, snd x)) ` set \<E>_impl) \<Longrightarrow>
          vertex xa
          \<in> dVs ((\<lambda>x. (edge x, vertex (snd x))) `
                  {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) \<noteq> \<infinity>})" for xa
  proof(goal_cases)
    case 1
   note 4 = 1
  obtain e where e_prop:"xa = fst e \<or> xa = snd e" "e \<in>  set \<E>_impl"
    using 4(3) by (auto simp add: dVs_def make_pair)
  show ?case 
  proof(rule disjE[OF e_prop(1)], goal_cases)
    case 1
    hence "the (flow_lookup \<u>_impl e) = \<infinity>"
      using 4(1)  e_prop(2)
      by(auto simp add:dVs_def)
    moreover have "the (flow_lookup \<u>_impl e) \<noteq> \<infinity>"
      using 4(2)  e_prop(2) 1
      by(auto simp add:dVs_def) 
    ultimately show ?case by simp
  next
    case 2
     have "the (flow_lookup \<u>_impl e) \<noteq> \<infinity>"
      using 4(2)  e_prop(2) 2
      by(auto simp add:dVs_def) 
    then show ?case 
      using 2 e_prop(2) by auto
  qed
qed
  moreover have 5:"edge e
          \<notin> dVs ((\<lambda>x. (edge x, vertex (fst x))) `
                  {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) \<noteq> \<infinity>}) \<Longrightarrow>
          edge e
          \<notin> dVs ((\<lambda>x. (vertex (fst x), vertex (snd x))) `
                  {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) = \<infinity>}) \<Longrightarrow>
          e \<in> set \<E>_impl \<Longrightarrow>
          edge e
          \<notin> dVs ((\<lambda>x. (edge x, vertex (snd x))) `
                  {x \<in> set \<E>_impl. the (flow_lookup \<u>_impl x) \<noteq> \<infinity>}) \<Longrightarrow>
          the_default \<infinity> (flow_lookup \<u>_impl e) = \<infinity>" for e
  proof(goal_cases)
    case 1
    note 5 = 1
  have "the (flow_lookup \<u>_impl e) = \<infinity>"
    using 5(1) 5(3) by(auto simp add:dVs_def)
  moreover have "e \<in> dom(flow_lookup \<u>_impl)"
    using u_domain Es_are 5(3)
    by(auto simp add:the_default_def to_set_def  dom_def)
  ultimately show ?case
    by(auto simp add: dom_def the_default_def)
qed
  show ?thesis
    by(subst infty_edges_def)
      (auto simp add: \<E>'_impl_def \<E>1_impl_def \<E>2_impl_def \<E>_impl_finite_def \<E>_impl_infty_def \<E>3_impl_def
            to_set_def  new_fstv_gen_def new_sndv_gen_def multigraph_spec.make_pair_def
            image_Un image_comp Es_are us_are intro: 1 2 3 4 5)
qed


lemma filter_neg_filter_empty:"filter P xs = ys \<Longrightarrow> filter (\<lambda> x. \<not> P x) xs = zs 
      \<Longrightarrow> ys =   [] \<Longrightarrow> zs  = [] \<Longrightarrow> xs = []" 
  by(induction ys, all \<open>induction xs\<close>, auto)
    (meson list.discI)
  
lemma E'_non_empt:"to_list \<E>'_impl \<noteq> []"
  using E_not_empty filter_neg_filter_empty
  by(auto simp add: to_list_def \<E>'_impl_def \<E>1_impl_def \<E>2_impl_def \<E>3_impl_def Es_are
          \<E>_impl_infty_def  \<E>_impl_finite_def to_set_def)

lemma finite_E':"finite (set \<E>'_impl)"
  by(auto simp add: to_list_def \<E>'_impl_def \<E>1_impl_def \<E>2_impl_def \<E>3_impl_def Es_are
          \<E>_impl_infty_def  \<E>_impl_finite_def to_set_def)
  
lemma multigraph':"multigraph (new_fstv_gen fst)  (new_sndv_gen fst snd)
      new_create_edge_gen
     (function_generation.\<E> \<E>'_impl to_set)"
  using finite_E' E'_non_empt 
  by(auto intro:  multigraph.intro 
       simp add:  new_create_edge_gen_def new_fstv_gen_def new_sndv_gen_def 
                    to_set_def to_list_def function_generation.\<E>_def[OF function_generation])

lemma collapse_union_ofE1E2E3:"to_set \<E>1_impl \<union> to_set \<E>2_impl \<union> to_set \<E>3_impl = to_set \<E>'_impl"
  by (simp add: Un_assoc \<E>'_impl_def to_set_def)

lemma E1_are: "to_set \<E>1_impl = inedge ` (\<E> - \<E>\<^sub>\<infinity>)"
  using u_domain infty_edges_def dom_def
  by(fastforce split: option.split 
            simp add: \<E>1_impl_def Es_are  \<E>_impl_finite_def to_set_def us_are the_default_def)

lemma E2_are: "to_set \<E>2_impl = outedge ` (\<E> - \<E>\<^sub>\<infinity>)"
  using u_domain infty_edges_def dom_def
  by(fastforce split: option.split 
            simp add: \<E>2_impl_def Es_are  \<E>_impl_finite_def to_set_def us_are the_default_def)

lemma E3_are: "to_set \<E>3_impl = vtovedge ` ( \<E>\<^sub>\<infinity>)"
  using u_domain infty_edges_def dom_def
  by(fastforce split: option.split 
            simp add: \<E>3_impl_def Es_are  \<E>_impl_infty_def to_set_def us_are the_default_def)

interpretation correctness_of_algo_red: correctness_of_algo
  where fst ="new_fstv_gen fst"
and snd ="new_sndv_gen fst snd"
and \<c>_impl = \<c>'_impl
and \<E>_impl  = \<E>'_impl
and create_edge = new_create_edge_gen
and \<b>_impl = \<b>'_impl
and c_lookup = "c_lookup'"
  using set_invar_E'  bal_invar_b'_impl  b'_impl_dom V_new_graph  E'_non_empt  multigraph' 
  by(intro correctness_of_algo.intro)
    (auto simp add: function_generation.N_def[OF function_generation] )
 
lemma E'_impl_in_cost'_dom:"e \<in> set \<E>'_impl \<Longrightarrow> e \<in> dom (c_lookup' \<c>'_impl)"
  using c_domain u_domain
  by(force simp add: \<E>'_impl_def \<E>1_impl_def \<E>2_impl_def \<E>3_impl_def \<c>'_impl_def Let_def c_lookup'_def \<E>_impl_finite_def
dom_def \<E>_impl_infty_def Es_are to_set_def image_def)

lemma c'_dom_is:" dom (c_lookup' \<c>'_impl) =
           inedge ` UNIV \<union> vtovedge ` dom (c_lookup \<c>_impl) \<union> outedge ` dom (c_lookup \<c>_impl)"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  show ?case 
  proof(cases x)
    case (outedge x1)
    hence "x1 \<in> dom (c_lookup \<c>_impl)" 
      using 1 by(auto simp add: c_lookup'_def \<c>'_impl_def)
    then show ?thesis 
      using outedge c_domain by simp
  next
    case (inedge x2)
    then show ?thesis by simp
  next
    case (vtovedge x3)
    hence "x3 \<in> dom (c_lookup \<c>_impl)" 
      using 1 by(auto simp add: c_lookup'_def \<c>'_impl_def)
    then show ?thesis 
      using vtovedge c_domain by simp
  next
    case (dummy x41 x42)
    then show ?thesis 
      using 1 by(auto simp add: c_lookup'_def dom_def) 
    qed
next
  case (2 x)
  then show ?case 
  using c_domain 
   by(force simp add: \<E>'_impl_def \<E>1_impl_def \<E>2_impl_def \<E>3_impl_def \<c>'_impl_def Let_def c_lookup'_def \<E>_impl_finite_def
           dom_def \<E>_impl_infty_def Es_are to_set_def image_def)
qed

lemma c'_impl_lookup:"x \<in> set \<E>'_impl \<Longrightarrow> the (c_lookup' \<c>'_impl x) = new_\<c>_gen D fst \<E> \<u> \<c> x"
  by(auto split: hitchcock_edge.split 
          simp add: \<E>'_impl_def \<E>3_impl_def \<E>2_impl_def \<E>1_impl_def to_set_def cs_are
                    new_\<c>_gen_def new_fstv_gen_def sym[OF E1_impl_are] sym[OF E2_impl_are] sym[OF E3_impl_are]
                      \<c>'_impl_def c_lookup'_def)+

lemma new_gen_c_unfold:"new_\<c>_gen (dom (c_lookup \<c>_impl)) fst \<E> \<u> \<c> = Instantiation.\<c> \<c>'_impl c_lookup'"
  unfolding selection_functions.\<c>_def
  apply(rule ext)
  subgoal for e
    apply(cases "e \<in> set \<E>'_impl")
    subgoal 
      using  E'_impl_in_cost'_dom[of e]  c'_impl_lookup[of e "(dom (c_lookup \<c>_impl))", symmetric] 
      by (fastforce intro: option_Some_theE[of _ "the (c_lookup' \<c>'_impl e)"])
    subgoal
   using c_domain    
   by(auto split: hitchcock_edge.split simp add: c_lookup'_def \<c>'_impl_def dom_def cs_are
              sym[OF E1_impl_are] sym[OF E2_impl_are] sym[OF E3_impl_are]
                           sym[OF collapse_union_ofE1E2E3, simplified to_set_def] to_set_def new_\<c>_gen_def) 
  done
  done

lemma new_b_domain_cong: "x \<in> vertex ` \<V> \<union> edge ` (\<E> - \<E>\<^sub>\<infinity>) \<Longrightarrow> new_\<b>_gen fst \<E> \<u> \<b> x = selection_functions.\<b> \<b>'_impl x "
 by(auto simp add:  selection_functions.\<b>_def new_\<b>_gen_def new_\<b>_gen_def  b'_impl_lookup b'_impl_dom[simplified dom_def, symmetric])

lemma cost_flow_network3: "cost_flow_network (new_fstv_gen fst) (new_sndv_gen fst snd)
      new_create_edge_gen (\<lambda>e. PInfty) (to_set \<E>'_impl)"
  apply(rule cost_flow_network.intro)
  apply(rule flow_network.intro)
  subgoal
    using multigraph'
    by(auto split: hitchcock_edge.split 
          simp add: function_generation.\<E>_def[OF function_generation] comp_def
                     new_fstv_gen_def new_sndv_gen_def )
  by(auto intro: flow_network_axioms.intro)

context
assumes no_infinite_cycle: "\<not> has_neg_infty_cycle make_pair \<E> \<c> \<u>"
begin


lemma no_cycle_in_reduction:"no_cycle_cond (new_fstv_gen fst) (new_sndv_gen fst snd) \<c>'_impl \<E>'_impl c_lookup'"
proof(rule no_cycle_condI, goal_cases)
  case (1 C)
  hence "has_neg_cycle (multigraph_spec.make_pair (new_fstv_gen fst) (new_sndv_gen fst snd)) (to_set \<E>'_impl)
     (function_generation.\<c> \<c>'_impl c_lookup')"
    by(auto intro!: has_neg_cycleI[of _ _ C] 
             simp add: function_generation.\<E>_def[OF function_generation]
                add.commute[of _ "_ \<c>'_impl c_lookup' _"])
  hence "has_neg_infty_cycle local.make_pair \<E> \<c> \<u>"
  using sym[OF reduction_of_mincost_flow_to_hitchcock_general(4)[OF flow_network_axioms, of "(dom (c_lookup \<c>_impl))" \<c>]]
  unfolding  sym[OF E1_impl_are]  sym[OF E2_impl_are]  sym[OF E3_impl_are] 
            collapse_union_ofE1E2E3 function_generation.\<E>_def[OF function_generation]
            new_gen_c_unfold 
  by(auto simp add: Es_are cs_are \<c>_def)
  thus False
    using no_infinite_cycle by simp
qed

corollary correctness_of_implementation_success:
 "return (final_state_cap) = success \<Longrightarrow>  
        is_Opt \<b> (abstract_flow_map (final_flow_impl_original))"
    apply(rule is_Opt_cong[of "old_f_gen \<E> \<u> (abstract_flow_map final_flow_impl_cap)"
                                , OF  old_f_gen_final_flow_impl_original_cong refl], simp)
    apply(rule reduction_of_mincost_flow_to_hitchcock_general(5)[OF flow_network_axioms refl, of "(dom (c_lookup \<c>_impl))" \<c> \<b>])
    apply(unfold final_flow_impl_cap_def sym[OF E1_impl_are] sym[OF E2_impl_are] sym[OF E3_impl_are]
              collapse_union_ofE1E2E3 \<u>_def  function_generation.\<u>_def[OF function_generation])
    apply(unfold new_gen_c_unfold)
    using V_new_graph  no_cycle_in_reduction 
    by(fastforce simp add: final_state_cap_def 
         intro!: cost_flow_spec.is_Opt_cong[OF refl sym[OF new_b_domain_cong]] 
                correctness_of_algo.correctness_of_implementation(1)
           [OF correctness_of_algo_red.correctness_of_algo_axioms, of \<c>'_impl,
            simplified \<u>_def function_generation.\<u>_def[OF function_generation]
                      \<E>_def function_generation.\<E>_def[OF function_generation] ])

corollary correctness_of_implementation_failure:
 "return (final_state_cap) = failure \<Longrightarrow> 
         \<nexists> f. isbflow  f \<b> "
proof(rule nexistsI, goal_cases)
  case (1 f)
  have "flow_network_spec.isbflow (new_fstv_gen fst) (new_sndv_gen fst snd) (to_set \<E>'_impl) (\<lambda>e. PInfty)  
        (new_f_gen fst \<E> \<u>  f)
        (selection_functions.\<b> \<b>'_impl)"
    apply(rule cost_flow_spec.isbflow_cong[OF refl])
    using V_new_graph   conjunct1[OF reduction_of_mincost_flow_to_hitchcock_general(2)[OF flow_network_axioms 
                         1(2) refl, of "(\<lambda> _. 0)"]]
    by(auto intro: new_b_domain_cong 
         simp add: sym[OF E1_impl_are] sym[OF E2_impl_are] sym[OF E3_impl_are] collapse_union_ofE1E2E3)
  moreover have "\<nexists>f. flow_network_spec.isbflow (new_fstv_gen fst) (new_sndv_gen fst snd) (to_set \<E>'_impl) (\<lambda>e. PInfty)  f 
              (selection_functions.\<b> \<b>'_impl)"
    using no_cycle_in_reduction 1(1) 
    by(intro correctness_of_algo.correctness_of_implementation(2)
           [OF correctness_of_algo_red.correctness_of_algo_axioms, of \<c>'_impl,
            simplified \<u>_def function_generation.\<u>_def[OF function_generation]
                      \<E>_def function_generation.\<E>_def[OF function_generation]])
       (auto simp add: final_state_cap_def) 
  ultimately show ?case by simp
qed


corollary correctness_of_implementation_excluded_case:
 "return final_state_cap = notyetterm \<Longrightarrow>  False"
  using no_cycle_in_reduction
  by(auto intro: correctness_of_algo.correctness_of_implementation(3)
           [OF correctness_of_algo_red.correctness_of_algo_axioms, of \<c>'_impl] simp add:  final_state_cap_def)

lemmas correctness_of_implementation = correctness_of_implementation_success 
                                       correctness_of_implementation_failure
                                       correctness_of_implementation_excluded_case
(*
lemma final_flow_domain: "dom (flow_lookup final_flow_impl_cap) = (set \<E>'_impl)"
  using correctness_of_algo.final_flow_domain[OF correctness_of_algo_red.correctness_of_algo_axioms
         no_cycle_in_reduction] 
  by(auto simp add: final_flow_impl_cap_def \<E>_def function_generation.\<E>_def[OF function_generation] to_set_def)
*)
end
definition "make_pair_capacity = make_pair"
end
lemmas  make_pair_capacity_def[code] = multigraph_spec.make_pair_def
global_interpretation flow_with_capacity: with_capacity
  where fst = fst
and snd = snd
and create_edge = create_edge
and \<E>_impl = \<E>_impl
and \<c>_impl = \<c>_impl
and \<u>_impl = \<u>_impl
and \<b>_impl = \<b>_impl
and c_lookup = c_lookup
for fst snd create_edge \<E>_impl \<c>_impl \<u>_impl \<b>_impl c_lookup
defines final_flow_impl_cap = flow_with_capacity.final_flow_impl_cap
and final_state_cap=flow_with_capacity.final_state_cap
and final_flow_impl_original = flow_with_capacity.final_flow_impl_original 

  done

definition "\<E>_impl = [(1::nat, 2::nat), (1,3), (3,2), (2,4), (2,5),
(3,5), (4,6), (6,5), (2,6)]"
value "\<E>_impl"

definition "b_list =  [(1::nat,128::real), (2,0), (3,1), (4,-33), (5,-32), (6,-64)]"

definition "\<b>_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) b_list Leaf"
value "\<b>_impl"

definition "c_list = [( (1::nat, 2::nat), 1::real),
 ((1,3), 4), ((3,2), 2), ((2,4), 3), ((2,5), 1),
((3,5), 5), ((4,6), 2), ((6,5), 1), ((2,6), 9)]"

definition "\<c>_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) c_list Leaf"
value "\<c>_impl"

definition "u_list = [( (1::nat, 2::nat), 20),
 ((1,3), 108), ((3,2), PInfty), ((2,4), PInfty), ((2,5), PInfty),
((3,5), PInfty), ((4,6), 45), ((6,5), PInfty), ((2,6), PInfty)]"

definition "\<u>_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) u_list Leaf"
value "\<u>_impl"

value "final_state_cap fst snd  \<E>_impl \<c>_impl \<u>_impl \<b>_impl flow_lookup"
value "final_flow_impl_cap fst snd \<E>_impl \<c>_impl \<u>_impl \<b>_impl flow_lookup"
value "final_flow_impl_original fst snd  \<E>_impl \<c>_impl \<u>_impl \<b>_impl flow_lookup"
value "inorder (final_flow_impl_original fst snd  \<E>_impl \<c>_impl \<u>_impl \<b>_impl flow_lookup)"

instantiation edge_wrapper::(linorder) linorder
begin

fun less_eq_edge_wrapper::"'a edge_wrapper \<Rightarrow> 'a edge_wrapper \<Rightarrow> bool" where
"less_eq_edge_wrapper (old_edge e) (old_edge d) = (e \<le> d)"|
"less_eq_edge_wrapper (new_edge e) (new_edge d) = (e \<le> d)"|
"less_eq_edge_wrapper (new_edge e) (old_edge d) = False"|
"less_eq_edge_wrapper (old_edge e) (new_edge d) = True"

fun less_edge_wrapper::"'a edge_wrapper \<Rightarrow> 'a edge_wrapper \<Rightarrow> bool" where
"less_edge_wrapper (old_edge e) (old_edge d) = (e < d)"|
"less_edge_wrapper (new_edge e) (new_edge d) = (e < d)"|
"less_edge_wrapper (new_edge e) (old_edge d) = False"|
"less_edge_wrapper (old_edge e) (new_edge d) = True"

instance 
  apply(intro Orderings.linorder.intro_of_class  class.linorder.intro
              class.order_axioms.intro class.order.intro class.preorder.intro
              class.linorder_axioms.intro)
  subgoal for x y 
    by(all \<open>cases x\<close>, all \<open>cases y\<close>) force+
  subgoal for x
    by(cases x) auto
   subgoal for x y z
     by(all \<open>cases x\<close>, all \<open>cases y\<close>, all \<open>cases z\<close>)
       (auto split: if_split simp add: less_le_not_le) 
  subgoal for a b
    by(all \<open>cases a\<close>, all \<open>cases b\<close>)
     (auto split: if_split simp add: less_le_not_le)
  subgoal for a b
   by(all \<open>cases a\<close>, all \<open>cases b\<close>)
     (auto split: if_split simp add: less_le_not_le)
  done
end

datatype cost_dummy = cost_dummy

locale solve_maxflow =
fixes fst::"('edge_type::linorder) \<Rightarrow> ('a::linorder)"
and snd::"('edge_type::linorder) \<Rightarrow> ('a::linorder)"
and create_edge::"'a \<Rightarrow> 'a \<Rightarrow> 'edge_type"
and \<E>_impl::"'edge_type list"
and \<u>_impl:: "(('edge_type::linorder \<times> ereal) \<times> color) tree"
and s::'a
and t::'a
begin

definition "\<E>_impl' = map old_edge \<E>_impl @ [new_edge (create_edge t s)]"

definition "\<c>_impl' = cost_dummy"

definition "c_lookup' c (e::'edge_type edge_wrapper) = (case e of old_edge _ \<Rightarrow> Some (0::real) |
                                       new_edge _ \<Rightarrow> Some (-1))"

definition "\<b>_impl' = foldr (\<lambda> x tree. bal_update x 0 tree) (vs fst snd \<E>_impl) Leaf"

definition "u_sum = foldr (\<lambda> e acc. acc + the (flow_lookup \<u>_impl e)) \<E>_impl 0"

definition "\<u>_impl' = flow_update (new_edge (create_edge t s)) u_sum 
                    (foldr (\<lambda> e tree. flow_update (old_edge e) (the (flow_lookup \<u>_impl e)) tree) \<E>_impl Leaf)"

definition "final_state_maxflow = final_state_cap 
(\<lambda> e. case e of old_edge e \<Rightarrow> fst e | new_edge e \<Rightarrow> fst e)
(\<lambda> e. case e of old_edge e \<Rightarrow> snd e | new_edge e \<Rightarrow> snd e)
\<E>_impl' \<c>_impl' \<u>_impl' \<b>_impl' c_lookup'"

definition "final_flow_impl_maxflow =  final_flow_impl_original 
(\<lambda> e. case e of old_edge e \<Rightarrow> fst e | new_edge e \<Rightarrow> fst e)
(\<lambda> e. case e of old_edge e \<Rightarrow> snd e | new_edge e \<Rightarrow> snd e)
\<E>_impl' \<c>_impl' \<u>_impl' \<b>_impl' c_lookup'"

definition "final_flow_impl_maxflow_original = 
            ( foldr (\<lambda> e tree. flow_update e 
                        (the_default 0 (flow_lookup final_flow_impl_maxflow (old_edge e))) tree) 
                         \<E>_impl flow_empty)"
end

global_interpretation solve_maxflow_by_orlins: solve_maxflow where
    fst = fst 
and snd = snd
and create_edge = create_edge
and \<E>_impl = \<E>_impl
and \<u>_impl = \<u>_impl
and s = s
and t = t
for fst snd create_edge \<E>_impl \<u>_impl s t
defines final_state_maxflow = solve_maxflow.final_state_maxflow
and final_flow_impl_maxflow = solve_maxflow.final_flow_impl_maxflow
and final_flow_impl_maxflow_original = solve_maxflow.final_flow_impl_maxflow_original
  done

lemma capacity_Opt_cong:
  fixes fst snd make_pair u c E b f create_edge
  assumes cost_flow_network1: "cost_flow_network  fst snd  create_edge u E"
     and cost_flow_network2: "cost_flow_network  fst snd  create_edge u' E"
     and "\<And> e. e \<in> E \<Longrightarrow> u e = u' e"
     and "cost_flow_spec.is_Opt fst snd  u E c b f" 
   shows "cost_flow_spec.is_Opt fst snd  u' E c b f" 
  using assms(3,4)
  by(simp add: cost_flow_spec.is_Opt_def flow_network_spec.isbflow_def
               flow_network_spec.isuflow_def)

lemma capacity_bflow_cong:
  fixes fst snd make_pair u c E b f create_edge
  assumes cost_flow_network1: "flow_network  fst snd  create_edge u E"
     and cost_flow_network2: "flow_network  fst snd  create_edge u' E"
     and "\<And> e. e \<in> E \<Longrightarrow> u e = u' e"
     and "flow_network_spec.isbflow fst snd  E u  b f" 
   shows "flow_network_spec.isbflow fst snd  E u' b f" 
  using assms(3,4)
  by(simp add: flow_network_spec.isbflow_def  flow_network_spec.isuflow_def)

locale solve_maxflow_proofs =
solve_maxflow where fst = "fst::'edge_type::linorder \<Rightarrow> 'a::linorder"
and snd = "snd::'edge_type::linorder \<Rightarrow> 'a::linorder"
and create_edge = create_edge 
and \<E>_impl = \<E>_impl
and \<u>_impl = \<u>_impl +

flow_network where fst = fst
and snd = snd
and create_edge = create_edge
and \<E> = \<E>
and \<u> = \<u>

for fst snd create_edge \<E>_impl \<u>_impl \<E> \<u>+
assumes  u_domain: "dom (flow_lookup \<u>_impl) = \<E>"
and  set_invar_E: "set_invar \<E>_impl"
and  Es_are: "\<E> = to_set \<E>_impl"
and  us_are: "\<u> = the_default PInfty o (flow_lookup \<u>_impl)"
assumes s_in_V: "s \<in> \<V>"
assumes t_in_V: "t \<in> \<V>"
assumes s_neq_t: "s \<noteq> t"
begin

definition "\<c>' = the o (c_lookup' cost_dummy)"
definition "\<u>' = the_default PInfty o (flow_lookup \<u>_impl')"

lemma in_E_same_cap:"e \<in> set \<E>_impl \<Longrightarrow> flow_lookup \<u>_impl' (old_edge e) = flow_lookup \<u>_impl e"
  unfolding \<u>_impl'_def Es_are 
  apply(subst foldr_map[of "(\<lambda>e. flow_update e (the (flow_lookup \<u>_impl (get_old_edge e))))" 
                     old_edge, simplified comp_def, simplified, symmetric])
  apply(subst flow_map.map_update)   
  using u_domain 
  by(force intro: flow_invar_fold[OF flow_invar_Leaf] 
        simp add: flow_map.invar_update dom_def Es_are to_set_def flow_lookup_fold[OF flow_invar_Leaf])+

lemma dom_final_flow_impl_maxflow:"dom (flow_lookup final_flow_impl_maxflow) = set \<E>_impl'"
  by(simp add: final_flow_impl_maxflow_def flow_with_capacity.dom_final_flow_impl_original)

lemma abstract_flows_are:"abstract_flow_map final_flow_impl_maxflow_original =
(\<lambda>e. abstract_flow_map final_flow_impl_maxflow (old_edge e))"
  using dom_final_flow_impl_maxflow
  by (fastforce simp add: flow_lookup_fold flow_map.invar_empty the_default_def
            flow_map.map_empty \<E>_impl'_def dom_def abstract_real_map_def
             final_flow_impl_maxflow_original_def abstract_flow_map_def)

lemma multigraph': "multigraph (prod.fst \<circ> make_pair') (prod.snd \<circ> make_pair') create_edge' (set \<E>_impl')" 
  by(auto intro!: multigraph.intro simp add: finite_E  fst_create_edge snd_create_edge \<E>_impl'_def)

lemma flow_network_axioms': "flow_network_axioms (\<lambda>e. case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty |
                   Some _ \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e 
                     | new_edge b \<Rightarrow> sum \<u> \<E>)"
  using u_sum_pos u_non_neg 
  by(auto intro!: flow_network_axioms.intro  split: edge_wrapper.split option.split)

lemma dom_u'_impl: "dom (flow_lookup \<u>_impl') = set \<E>_impl'"
  unfolding  \<u>_impl'_def  \<E>_impl'_def
  apply(subst dom_update_insert[simplified sym[OF flow_lookup_def] sym[OF flow_update_def]])
  by(auto intro!: conjunct1[OF flow_invar_fold[simplified flow_invar_def]]
            flow_map.invar_update[simplified flow_invar_def] 
        simp add: flow_invar_Leaf[simplified flow_invar_def] dom_fold flow_invar_Leaf flow_map.map_empty [simplified RBT_Set.empty_def flow_empty_def]) 

lemma dom_b'_impl: "dom (bal_lookup \<b>_impl') = \<V>"
 by(force simp add: dVs_eq dVs_swap Es_are to_set_def 
                      vs_def  function_generation.vs_def[OF function_generation]
                      function_generation.es_def[OF function_generation] to_list_def
                      bal_map.map_specs(1)[simplified RBT_Set.empty_def bal_empty_def]
                      bal_map.invar_empty[simplified RBT_Set.empty_def bal_empty_def]
                     bal_dom_fold  \<b>_impl'_def 
                     image_comp make_pair''(3) selection_functions.make_pair_def 
                     make_pair''(2) image_iff)

lemma set_invar':"set_invar \<E>_impl'"
  using set_invar_E
  by(auto simp add: distinct_map inj_on_def set_invar_def \<E>_impl'_def)

lemma bal_invar':"bal_invar \<b>_impl'"
  by(auto intro: bal_invar_fold simp add: \<b>_impl'_def bal_map.invar_empty[simplified RBT_Set.empty_def bal_empty_def])

lemma u_impl'_same_u:"flow_lookup \<u>_impl' (old_edge e) = Some u \<Longrightarrow> \<u> e = u"
  unfolding \<u>_impl'_def
  apply(subst (asm) flow_map.map_update)
  apply (simp add: flow_invar_Leaf flow_invar_fold flow_map.invar_update, simp)
  apply(subst (asm) foldr_map[of "(\<lambda>e. flow_update e (the (flow_lookup \<u>_impl (get_old_edge e))))" old_edge,
                     simplified comp_def, simplified, symmetric])
  apply(subst (asm) flow_lookup_fold)
  apply (simp add: flow_invar_Leaf)
  using u_domain
  by (cases "old_edge e \<in> old_edge ` set \<E>_impl")
     (force simp add:   flow_map.map_empty[simplified RBT_Set.empty_def flow_empty_def]
                        us_are the_default_def Es_are to_set_def dom_def )+

lemma u_sum_is: "u_sum = sum \<u> (set \<E>_impl)"
  unfolding u_sum_def
  using set_invar_E  u_domain us_are
  by(subst distinct_sum)(force intro: foldr_cong simp add: Es_are to_set_def  the_default_def set_invar_def)+

lemma u_impl'_sum:"flow_lookup \<u>_impl' (new_edge e) = Some u \<Longrightarrow> sum \<u> (set \<E>_impl) = u"
  unfolding \<u>_impl'_def
  apply(subst (asm) flow_map.map_update)
  apply (simp add: flow_invar_Leaf flow_invar_fold flow_map.invar_update, simp)
  apply(subst (asm) foldr_map[of "(\<lambda>e. flow_update e (the (flow_lookup \<u>_impl (get_old_edge e))))" old_edge,
                     simplified comp_def, simplified, symmetric])
  apply(subst (asm) flow_lookup_fold)
  apply (simp add: flow_invar_Leaf)
  apply(subst (asm) flow_map.map_empty[simplified RBT_Set.empty_def flow_empty_def])
  by(cases "e = create_edge t s")(auto simp add: u_sum_is  image_iff)


lemma with_capacity_proofs_axioms: 
"with_capacity_proofs_axioms (prod.snd o make_pair') \<c>_impl' \<b>_impl' c_lookup' (prod.fst o make_pair') \<E>_impl' \<u>_impl' (set \<E>_impl')
     (\<lambda>e. case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty |
                   Some _ \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e 
                     | new_edge b \<Rightarrow> sum \<u> \<E>) 
     (\<lambda>e. case e of old_edge x \<Rightarrow> 0 | new_edge b \<Rightarrow> - 1)
     (the_default 0 \<circ> bal_lookup \<b>_impl')"   
  using dom_u'_impl  same_Vs_s_t[OF s_in_V t_in_V s_neq_t] dom_b'_impl set_invar'  bal_invar' u_impl'_same_u u_impl'_sum
  by(auto intro!: with_capacity_proofs_axioms.intro split: edge_wrapper.split option.split 
             simp add:  the_default_def comp_def to_set_def \<E>_impl'_def Es_are c_lookup'_def 
                       make_pair_def multigraph_spec.make_pair)

lemma with_capacity_proofs:"with_capacity_proofs snd' \<c>_impl' \<b>_impl'
                     c_lookup' fst' create_edge' \<E>_impl' \<u>_impl' (set \<E>_impl')
     (\<lambda>e. case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty |
                   Some _ \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e 
                     | new_edge b \<Rightarrow> sum \<u> \<E>) 
     (case_edge_wrapper (\<lambda>x. 0) (\<lambda>b. - 1))
     (the_default 0 \<circ> bal_lookup \<b>_impl')"
  using multigraph' flow_network_axioms'  with_capacity_proofs_axioms
  by(auto intro!: with_capacity_proofs.intro cost_flow_network.intro flow_network.intro
        simp add: fst'_def snd'_def)

lemma cost_flow_network1: "cost_flow_network fst' snd'  create_edge' (case_edge_wrapper \<u> (\<lambda>b. sum \<u> \<E>)) (set \<E>_impl')"
  using multigraph' flow_network_axioms' u_sum_pos u_non_neg 
  by(auto intro!: cost_flow_network.intro flow_network.intro flow_network_axioms.intro split: edge_wrapper.split option.split
          simp add: fst'_def snd'_def)

lemma cost_flow_network2: "cost_flow_network fst' snd' create_edge' 
               (\<lambda>e. case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty |
                   Some _ \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e 
                     | new_edge b \<Rightarrow> sum \<u> \<E>) (set \<E>_impl')"
  using multigraph' flow_network_axioms' u_sum_pos u_non_neg 
  by(auto intro!: cost_flow_network.intro flow_network.intro flow_network_axioms.intro split: edge_wrapper.split option.split
          simp add: fst'_def snd'_def)

lemma capacity_cong:"e \<in> (set \<E>_impl') \<Longrightarrow>
    (case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty | Some x \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e | new_edge b \<Rightarrow> sum \<u> \<E>) =
    (case e of old_edge e \<Rightarrow> \<u> e | new_edge b \<Rightarrow> sum \<u> \<E>)"
    using  dom_u'_impl  in_E_same_cap u_domain
    by(auto split: edge_wrapper.split option.split simp add: \<E>_impl'_def Es_are  to_set_def)

lemma E'_are: "(\<E>' s t) = set \<E>_impl'"
  unfolding \<E>'_def[OF s_in_V t_in_V s_neq_t]
  by(simp add:  \<E>_impl'_def Es_are to_set_def)

lemma b_impl'_0_cong: "v \<in> dVs (make_pair' ` \<E>' s t) \<Longrightarrow> (the_default 0 \<circ> bal_lookup \<b>_impl') v = 0"
  unfolding same_Vs[OF s_in_V t_in_V s_neq_t] \<b>_impl'_def o_apply
  apply(subst  bal_lookup_fold)
  using   bal_map.invar_empty[simplified RBT_Set.empty_def bal_empty_def] 
  by(auto simp add: vs_def function_generation.vs_def[OF function_generation]
             bal_lookup_fold function_generation.es_def[OF function_generation]
             dVs_eq  to_list_def  Es_are to_set_def image_Un image_comp the_default_def
             selection_functions.make_pair_def make_pair_def bal_lookup_def lookup.simps(1)) 

lemma capacity_aux_rewrite:"the_default PInfty (flow_lookup \<u>_impl' e) =(case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty
             | Some x \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e | new_edge b \<Rightarrow> sum \<u> \<E>)"
  using in_E_same_cap dom_u'_impl u_impl'_sum
  by(fastforce split: option.split edge_wrapper.split 
               simp add: Es_are to_set_def \<E>_impl'_def us_are the_default_def)


context
  assumes no_infty_path:"\<not> has_infty_st_path make_pair \<E> \<u> s t"
begin

lemma no_infinite_cycle: "\<not> has_neg_infty_cycle make_pair' ( set \<E>_impl') \<c>' \<u>'"
proof(rule not_has_neg_infty_cycleI, goal_cases)
  case (1 D)
  have top: "set D \<subseteq> set \<E>_impl'"
  "foldr (\<lambda>e. (+) (\<c>' e)) D 0 < 0" 
    "closed_w (make_pair' ` set \<E>_impl') (map make_pair' D)" "(\<forall>e\<in>set D. \<u>' e = \<infinity>)" 
    using 1 by auto
  have "new_edge (create_edge t s) \<in> set D"
    using top(1,2)
    by(induction D)(auto simp add: \<E>_impl'_def \<c>'_def c_lookup'_def)
  then obtain D1 D2 where D_prop:"D = D1@[new_edge (create_edge t s)]@D2" "new_edge (create_edge t s) \<notin> set D1"
    by (metis single_in_append split_list_first)
  then obtain u where u_prop: "awalk (make_pair' ` set \<E>_impl') u
                    (map make_pair' (D1@[new_edge (create_edge t s)]@D2)) u"
      "0 < length (map make_pair' (D1@[new_edge (create_edge t s)]@D2))"
    using top(3) by(auto simp add: closed_w_def)
  hence awalk_u_t:"awalk (make_pair' ` set \<E>_impl') u (map make_pair' D1) t" 
    by (auto simp add: awalk_Cons_iff  create_edge'(1))
  obtain D21 D22 where D2_prop:"[new_edge (create_edge t s)]@D2 = D21@[new_edge (create_edge t s)]@D22"
                             "new_edge (create_edge t s) \<notin> set D22" 
    by (metis append.left_neutral append_Cons split_list_last)
  hence awalk_s_u:"awalk (make_pair' ` set \<E>_impl') s (map make_pair' D22) u" 
    using u_prop(1) by(auto simp add: awalk_Cons_iff  create_edge'(2))
  hence awalk_s_t:"awalk (make_pair' ` set \<E>_impl') s (map make_pair' (D22@D1)) t"
    using awalk_u_t by auto
  have in_E:"set (D22 @ D1) \<subseteq> old_edge ` \<E>" 
  proof(rule, goal_cases)
    case (1 e)
    hence "e \<in> set \<E>_impl'" "e \<noteq> new_edge (create_edge t s)"
      using D_prop D2_prop top(1) by auto
    thus ?case
      by(simp add: Es_are to_set_def \<E>_impl'_def)
  qed
  have same_path:"map make_pair (map get_old_edge (D22 @ D1)) = map make_pair' (D22@D1)" 
    using map_make_pair'_is_make_pair_of_get_old_edge[OF in_E] by simp
  have not_nil:"D22@D1 \<noteq> Nil" 
    using awalk_s_t s_neq_t by auto
  have "awalk (make_pair ` \<E>) s (map make_pair (map get_old_edge (D22@D1))) t"
    using not_nil  in_E 
    by (subst same_path)(fastforce intro: subset_mono_awalk'[OF awalk_s_t] simp add: make_pair)
  moreover have path_set_in_E:"set (map get_old_edge (D22@D1)) \<subseteq> \<E>"
    using in_E by auto
  moreover have " e \<in> set (map get_old_edge (D22@D1)) \<Longrightarrow> \<u> e = PInfty" for e
  proof(goal_cases)
    case 1
    hence "old_edge e \<in> set D" 
      using in_E D_prop(1) D2_prop(1) by auto
    hence "\<u>' (old_edge e) = \<infinity>"
      using top(4) by auto
    moreover have "e \<in> set \<E>_impl"
      using "1" Es_are path_set_in_E by(auto simp add: to_set_def)
    ultimately show ?case
      using in_E_same_cap[of e]
      by(simp add: \<u>'_def the_default_def us_are \<u>_def Es_are to_set_def comp_def)
  qed
  ultimately have "has_infty_st_path local.make_pair \<E> \<u> s t"
    using not_nil 
    by(fastforce intro!: has_infty_st_pathI[of _ _ _ "map get_old_edge (D22@D1)"]) 
  thus ?case 
    using no_infty_path by simp
qed

lemma "\<u>' =  (\<lambda>e. case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty
              | Some x \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e | new_edge b \<Rightarrow> sum \<u> \<E>)" 
  using \<u>'_def capacity_aux_rewrite by auto

lemma correctness_of_implementation_success:
 "return final_state_maxflow = success \<Longrightarrow> is_max_flow s t (abstract_flow_map final_flow_impl_maxflow_original)"
  apply(rule maxflow_to_mincost_flow_reduction(4)[OF s_in_V t_in_V s_neq_t _ abstract_flows_are])+
  apply(subst E'_are)
  apply(rule capacity_Opt_cong[OF  cost_flow_network2 cost_flow_network1  capacity_cong], simp)
  apply(rule cost_flow_spec.is_Opt_cong[OF refl, of _ _ _ "the_default 0 o bal_lookup \<b>_impl'"])
   apply(rule b_impl'_0_cong)
  apply(simp add: E'_are make_pair'_is(1))
  unfolding final_flow_impl_maxflow_def fst'_def2(2) snd'_def2(2) final_flow_impl_original_def
  apply(rule with_capacity_proofs.correctness_of_implementation_success[OF with_capacity_proofs])
  using no_infinite_cycle
  by(auto simp add: final_state_maxflow_def final_state_cap_def \<E>_impl'_def fst'_def2(1) 
     snd'_def2(1) \<c>'_def \<c>_impl'_def \<u>'_def with_capacity_proofs.cs_are[OF  with_capacity_proofs]
    with_capacity_proofs.us_are[OF  with_capacity_proofs]
    capacity_aux_rewrite make_pair'_is(2))

notation is_s_t_flow ( "_ is _ -- _ flow")

lemma correctness_of_implementation_failure:
 "return final_state_maxflow = failure \<Longrightarrow> False"
proof(rule ccontr,  goal_cases)
  case 1
  have f_prop: "(\<lambda> x. 0) is s -- t flow" 
    using s_in_V t_in_V s_neq_t  u_non_neg
    by(auto simp add:  is_s_t_flow_def isuflow_def ex_def zero_ereal_def)  
  have no_flow:"\<nexists>f. flow_network_spec.isbflow fst' snd'
               (set \<E>_impl') (\<lambda>e. case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty |
        Some x \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e | new_edge b \<Rightarrow> sum \<u> \<E>)f 
           (the_default 0 \<circ> bal_lookup \<b>_impl')"
  proof(rule  with_capacity_proofs.correctness_of_implementation_failure[OF with_capacity_proofs], goal_cases)
    case 1
    then show ?case 
    using no_infinite_cycle
    by(simp add: \<c>'_def \<c>_impl'_def \<u>'_def make_pair'_is(1)
        with_capacity_proofs.cs_are[OF with_capacity_proofs]
        with_capacity_proofs.us_are[OF with_capacity_proofs])
next
  case 2
  thus ?case
    using "1"(1)
    by(simp add: final_state_cap_def fst'_def2(1) local.final_state_maxflow_def snd'_def2(1))
qed
   have a:"flow_network_spec.isbflow fst' snd' 
          (set \<E>_impl') (\<lambda>e. case e of old_edge e \<Rightarrow> \<u> e | new_edge b \<Rightarrow> sum \<u> \<E>)
       (\<lambda>e. case e of old_edge e \<Rightarrow> (\<lambda> x. 0) e | new_edge b \<Rightarrow> ex (\<lambda> x. 0) t) (\<lambda>e. 0)"
     using maxflow_to_mincost_flow_reduction(1)[OF s_in_V t_in_V s_neq_t f_prop refl] E'_are by auto
   have b:"flow_network_spec.isbflow fst' snd' (set \<E>_impl')
          (\<lambda>e. case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty |
        Some x \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e | new_edge b \<Rightarrow> sum \<u> \<E>) 
       (\<lambda>e. case e of old_edge e \<Rightarrow> (\<lambda> x. 0) e | new_edge b \<Rightarrow> ex (\<lambda> x. 0) t) (\<lambda>e. 0)"
     using capacity_aux_rewrite capacity_cong cost_flow_network.axioms[OF cost_flow_network2]
           cost_flow_network.axioms[OF cost_flow_network1] 
     by (force intro: capacity_bflow_cong[OF _ _ _ a])
   have "flow_network_spec.isbflow fst' snd' (set \<E>_impl') 
     (\<lambda>e. case flow_lookup \<u>_impl' e of None \<Rightarrow> PInfty
           | Some x \<Rightarrow> case e of old_edge e \<Rightarrow> \<u> e | new_edge b \<Rightarrow> sum \<u> \<E>)
    (\<lambda>e. case e of old_edge e \<Rightarrow> (\<lambda> x. 0) e | new_edge b \<Rightarrow> ex (\<lambda> x. 0) t) (the_default 0 \<circ> bal_lookup \<b>_impl')"
     using b_impl'_0_cong E'_are 
     by (force intro!: cost_flow_spec.isbflow_cong[OF  _ _ b] simp add: make_pair'_is(1))
   thus ?case 
     using no_flow 
     by (simp add: fst'_def snd'_def)
 qed

lemma correctness_of_implementation_excluded_case:
 "return final_state_maxflow = notyetterm \<Longrightarrow> False"
  using  no_infinite_cycle[simplified \<c>'_def o_apply c_lookup'_def \<u>'_def edge_wrapper.case_distrib[of the]
                                           option.sel \<E>_impl'_def]  make_pair'_is(1) 
    no_infinite_cycle
    with_capacity_proofs.correctness_of_implementation_excluded_case[OF with_capacity_proofs]
     with_capacity_proofs.cs_are[OF with_capacity_proofs]
    with_capacity_proofs.us_are[OF with_capacity_proofs]
  by (intro with_capacity_proofs.correctness_of_implementation_excluded_case[of snd' \<c>_impl' \<b>_impl' c_lookup' fst'
                          create_edge' \<E>_impl' \<u>_impl' _  _ _ "the_default 0 \<circ> bal_lookup \<b>_impl'"])
     (auto simp add:  final_state_cap_def \<c>'_def \<c>_impl'_def \<u>'_def fst'_def2(2)
             final_state_maxflow_def   snd'_def2(2) )
 
lemmas correctness_of_implementation = correctness_of_implementation_success
                                       correctness_of_implementation_failure
                                       correctness_of_implementation_excluded_case
  
end
end
 
value "final_state_maxflow fst snd Pair \<E>_impl \<u>_impl 1 3"
value "final_flow_impl_maxflow fst snd Pair \<E>_impl \<u>_impl 1 3"
value "final_flow_impl_maxflow_original fst snd Pair \<E>_impl \<u>_impl 1 3"
value "inorder  (final_flow_impl_maxflow_original fst snd Pair \<E>_impl \<u>_impl 1 3)" 
end