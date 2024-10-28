section \<open>Characterising the Existence of Optimum Flows\<close>

theory Existence_Optflows
  imports Usage_Capacitated
begin
hide_const \<E>_impl es \<c>_impl \<b>_impl \<u>_impl \<b>

locale cost_flow_network_flow_existence
= cost_flow_network 
where fst = fst for fst:: "('edge_type::linorder) \<Rightarrow> ('a::linorder)"
begin

definition "no_neg_cycle = (\<not>(\<exists>D. closed_w (make_pair ` \<E>) (map make_pair D) \<and>
              foldr (\<lambda>e. (+) (\<c> e)) D 0 < 0 \<and> set D \<subseteq> \<E> \<and> (\<forall>e\<in>set D. \<u> e = PInfty)))"

lemma es_exist: "\<exists> es. set es = \<E> \<and> distinct es"
  using finite_E
 by(induction \<E> rule: finite_induct)(auto intro: exI[of _ "_ # _"])
 
definition "\<E>_impl = (SOME es. set es = \<E> \<and> distinct es)"

lemma \<E>_impl_prop: "set \<E>_impl = \<E>" "distinct \<E>_impl"
  using  es_exist[simplified sym[OF some_eq_ex]] 
  by (auto simp add: \<E>_impl_def) 

definition "\<c>_impl = cost_dummy"
definition "c_lookup _ x = Some (\<c> x)"

lemma u_impl_exists: "\<exists> u_impl. dom (flow_lookup u_impl) = \<E> \<and> (\<forall> e \<in> \<E>. flow_lookup u_impl e = Some (\<u> e))
                                \<and> flow_invar u_impl"
  using  finite_E
proof(induction  rule: finite_induct)
  case empty
  then show ?case 
    by (auto intro: exI[of _ flow_empty] simp add: flow_map.invar_empty flow_map.map_empty)
next
  case (insert e F)
  then obtain u_impl where u_impl_prop:"dom (flow_lookup u_impl) = F " "(\<forall>e\<in>F. flow_lookup u_impl e = Some (\<u> e))"
                           "flow_invar u_impl" by auto
  show ?case 
   using  flow_map.map_update[OF u_impl_prop(3)] u_impl_prop
   by(auto intro!: exI[of _ "flow_update e (\<u> e) u_impl"] domI flow_map.invar_update) force+
qed

definition "\<u>_impl = (SOME u_impl. dom (flow_lookup u_impl) = \<E> \<and> (\<forall> e \<in> \<E>. flow_lookup u_impl e = Some (\<u> e))
                                \<and> flow_invar u_impl)"

lemma \<u>_impl_props: "dom (flow_lookup \<u>_impl) = \<E>" "(\<forall> e \<in> \<E>. flow_lookup \<u>_impl e = Some (\<u> e))"
                                "flow_invar \<u>_impl"
  using  u_impl_exists[simplified sym[OF some_eq_ex]] 
  by (auto simp add: \<u>_impl_def) 

thm with_capacity_proofs.correctness_of_implementation[of _ _ _ make_pair create_edge _ _ \<E> \<u> \<c> ]

lemma cost_flow_network_impl:"cost_flow_network (prod.fst \<circ> make_pair) (prod.snd \<circ> make_pair) make_pair create_edge (the_default PInfty \<circ> flow_lookup \<u>_impl) \<E>"
proof -
  have "snd = prod.snd \<circ> make_pair \<and> fst = prod.fst \<circ> make_pair"
    by (auto simp add: make_pair''(1) make_pair''(2))
  then show "cost_flow_network (prod.fst \<circ> make_pair) (prod.snd \<circ> make_pair) make_pair create_edge (the_default PInfty \<circ> flow_lookup \<u>_impl) \<E>"
    using cost_flow_network_axioms \<u>_impl_props(1,2)
    by(force split: option.split simp add: cost_flow_network_def flow_network_def flow_network_axioms_def the_default_def 
                     dom_def)
qed

lemma cost_flow_network2:"flow_network (prod.fst \<circ> make_pair) (prod.snd \<circ> make_pair) make_pair create_edge \<u> \<E>"
  using finite_E  by(auto intro!: flow_network.intro multigraph.intro flow_network_axioms.intro 
                           simp add: create_edge E_not_empty u_non_neg)

lemma b_impl_exists: "\<exists> b_impl. dom (bal_lookup b_impl) = \<V>  \<and> 
                         (\<forall> v \<in> \<V>. bal_lookup b_impl v = Some (b v)) \<and> bal_invar b_impl"
    using  \<V>_finite
proof(induction  rule: finite_induct)
  case empty
  then show ?case 
    by (auto intro: exI[of _ bal_empty] simp add: bal_map.invar_empty bal_map.map_empty)
next
  case (insert u V)
  then obtain b_impl where b_impl_prop:"dom (bal_lookup b_impl) = V " 
                         "(\<forall>v \<in> V. bal_lookup b_impl v = Some (b v))"
                           "bal_invar b_impl" by auto
  show ?case 
   using  bal_map.map_update[OF b_impl_prop(3)] b_impl_prop
   by(auto intro!: exI[of _ "bal_update u (b u) b_impl"] domI bal_map.invar_update) force+
qed

definition "b_impl b = (SOME b_impl.  dom (bal_lookup b_impl) = \<V>  \<and> 
                         (\<forall> v \<in> \<V>. bal_lookup b_impl v = Some (b v)) \<and> bal_invar b_impl)"

lemma b_impl_props: "dom (bal_lookup (b_impl b)) = \<V> " "(\<forall> v \<in> \<V>. bal_lookup (b_impl b) v = Some (b v))"
                                "bal_invar (b_impl b)"
  using  b_impl_exists[simplified sym[OF some_eq_ex]] 
  by (auto simp add: b_impl_def) force

lemma with_capacity_proofs: "with_capacity_proofs \<c>_impl (b_impl b) c_lookup make_pair create_edge \<E>_impl \<u>_impl \<E> 
(the_default PInfty \<circ> flow_lookup \<u>_impl) \<c> (the_default 0 \<circ> bal_lookup (b_impl b))"
  apply(rule with_capacity_proofs.intro[OF cost_flow_network_impl], rule with_capacity_proofs_axioms.intro)
  using b_impl_props[of b]
  by (auto simp add: \<E>_impl_prop \<u>_impl_props set_invar_def to_set_def c_lookup_def)


interpretation algo_locale: with_capacity_proofs
  where \<c>_impl = \<c>_impl and \<b>_impl = "(b_impl b)" 
  and c_lookup = c_lookup and make_pair = make_pair and create_edge = create_edge
  and \<E>_impl = \<E>_impl and \<u>_impl = \<u>_impl and \<E> = \<E>
  and \<u> = "the_default PInfty \<circ> flow_lookup \<u>_impl" and \<c> = \<c>
 and \<b> = "the_default 0 \<circ> bal_lookup (b_impl b)"
  using with_capacity_proofs by simp

lemma algo_locale_isbflow_def:"algo_locale.isbflow f b = flow_network.isbflow (prod.fst o make_pair) (prod.snd o make_pair)
                                 make_pair (the_default PInfty \<circ> flow_lookup \<u>_impl) \<E> f b"
  by auto
thm algo_locale.correctness_of_implementation

lemma existence_of_optimum_flow:
"(\<exists> f. is_Opt b f) \<longleftrightarrow> ((\<exists> f. f is b flow) \<and> no_neg_cycle )"
proof(rule, goal_cases)
  case 1
  then obtain f where isopt: "is_Opt b f" by auto
  hence fbflow:"f is b flow"
    using is_Opt_def by blast
  moreover have no_neg_cycle
    unfolding no_neg_cycle_def
  proof(rule nexistsI, goal_cases)
    case (1 D)
    then obtain u where u_prop: "awalk (make_pair ` \<E>) u (map make_pair D) u" " 0 < length (map make_pair D)"
      by (auto simp add: closed_w_def)
    have rcap:"0 < Rcap f (set (map F D))"
      using 1(1) 
      by (auto simp add: Min_gr_iff Rcap_def)
    have same_path:"(map (to_vertex_pair \<circ> F) D) = (map make_pair D)" 
      by simp
    have fstv_is: "fstv (hd (map F D)) = u"
      using u_prop(2) awalk_hd[OF u_prop(1)]
      by(cases D)(auto simp add:  make_pair'')
    have sndv_is: "sndv (last (map F D)) = u"
      using u_prop(2) awalk_last[OF u_prop(1)]
      by(cases D rule: rev_cases)(auto simp add:  make_pair'')
    have augpath:"augpath f (map F D)"
      using 1(1) u_prop(1,2) rcap
      by(auto simp add: same_path fstv_is sndv_is augpath_def  prepath_def closed_w_def intro: subset_mono_awalk)
    have rescost_neg: "foldr (\<lambda>e. (+) (\<cc> e)) (map F D) 0 = foldr (\<lambda>e. (+) (\<c> e)) D 0"
      by(induction D) auto
    have D_EE: "set (map F D) \<subseteq> \<EE>"
      using 1(1)
      by(force simp add: \<EE>_def )
    obtain C where C_prop:"augcycle f C"
      apply(rule augcycle_from_non_distinct_cycle[OF augpath])
      using D_EE  rescost_neg 1(1) 
      by (auto simp add: fstv_is sndv_is)
    have rcap2:"Rcap f (set C) > 0"
      using C_prop augcycle_def augpath_rcap by blast
    hence g_gtr_0:"real_of_ereal (min 1 (Rcap f (set C))) > 0" 
      by(cases "Rcap f (set C)") (auto simp add: min_def)
    have g_less_rcap: "ereal (real_of_ereal (min 1 (Rcap f (set C)))) \<le> Rcap f (set C)"
      using rcap2 by(cases "Rcap f (set C)") (auto simp add: min_def)
    have in_EE: "set C \<subseteq> \<EE>" 
      using C_prop augcycle_def by blast
    have "augment_edges f (real_of_ereal (min 1 (Rcap f (set C)))) C is b flow"
      using  C_prop 1(1) g_less_rcap 
      by(auto simp add: \<EE>_def zero_ereal_def augcycle_def
                  intro!: aug_cycle_pres_b[OF fbflow order.strict_implies_order[OF g_gtr_0] ])
    moreover have "\<C> (augment_edges f (real_of_ereal (min 1 (Rcap f (set C)))) C) < \<C> f"
      using C_prop 1(1) in_EE  g_gtr_0 
      by(subst cost_change_aug)(auto intro!: mult_pos_neg simp add: augcycle_def  \<CC>_def)    
    ultimately show ?case 
      using isopt by(auto simp add: is_Opt_def)
  qed
  ultimately show ?case by auto
next
  case 2
  then obtain f where f_prop: "f is b flow" by auto
  have no_neg_cycle:"(\<not>(\<exists>D. closed_w (make_pair ` \<E>) (map make_pair D) \<and>
              foldr (\<lambda>e. (+) (\<c> e)) D 0 < 0 \<and> set D \<subseteq> \<E> \<and> (\<forall>e\<in>set D. \<u> e = PInfty)))"
    using 2 by(auto simp add: no_neg_cycle_def)
  have a1:"f is \<lambda>x. the_default 0 (bal_lookup (b_impl b) x) flow"
    using b_impl_props[of b] 
    by( auto intro: isbflow_cong[OF _ _ f_prop] simp add: the_default_def  make_pair'')
  have a_flow:"algo_locale.isbflow f (the_default 0 \<circ> bal_lookup (b_impl b))"
    using \<u>_impl_props  a1 
    by(intro capacity_bflow_cong[OF cost_flow_network2 algo_locale.flow_network_axioms])
      (auto simp add: make_pair''  comp_def the_default_def)
  have no_neg_cycle':"\<nexists>D. closed_w (make_pair ` \<E>) (map make_pair D) \<and>
      foldr (\<lambda>e. (+) (\<c> e)) D 0 < 0 \<and>
      set D \<subseteq> \<E> \<and> (\<forall>e\<in>set D. (the_default PInfty \<circ> flow_lookup \<u>_impl) e = PInfty)"
    using no_neg_cycle \<u>_impl_props(1,2) 
    by(force simp add: the_default_def) 
  have an_opt:"algo_locale.is_Opt (the_default 0 \<circ> bal_lookup (b_impl b))
   (abstract_flow_map (with_capacity.final_flow_impl_original make_pair \<E>_impl \<c>_impl \<u>_impl (b_impl b) c_lookup))"
    using  algo_locale.correctness_of_implementation[OF no_neg_cycle'] a_flow 
            IntermediateSummary.return.exhaust by blast
  have another_opt:"is_Opt (the_default 0 \<circ> bal_lookup (b_impl b))
   (abstract_flow_map (with_capacity.final_flow_impl_original make_pair \<E>_impl \<c>_impl \<u>_impl (b_impl b) c_lookup))"
    using  cost_flow_network_axioms  \<u>_impl_props 
    by(subst comp_def) 
      (force intro!: capacity_Opt_cong[OF cost_flow_network_impl _ _ an_opt, of \<u>, simplified comp_def make_pair'' ] 
           simp add: the_default_def)
   have "is_Opt b
   (abstract_flow_map (with_capacity.final_flow_impl_original make_pair \<E>_impl \<c>_impl \<u>_impl (b_impl b) c_lookup))"
     using b_impl_props(1)
     by(auto intro!: is_Opt_cong[OF refl _  another_opt] simp add: the_default_def b_impl_props(2) split: option.split)     
   then show ?case 
     by auto
qed

end

locale flow_network_max_flow_existence
= flow_network 
where fst = fst for fst:: "('edge_type::linorder) \<Rightarrow> ('a::linorder)"
begin

context 
  fixes s t
  assumes s_in_V: "s \<in> \<V>"
  assumes t_in_V: "t \<in> \<V>"
  assumes s_neq_t: "s \<noteq> t"
begin

definition "no_infty_path = (\<not>(\<exists>D. awalk UNIV s (map make_pair D) t
                               \<and> set D \<subseteq> \<E> \<and> (\<forall>e\<in>set D. \<u> e = PInfty)))"

lemma es_exist: "\<exists> es. set es = \<E> \<and> distinct es"
  using finite_E
 by(induction \<E> rule: finite_induct)(auto intro: exI[of _ "_ # _"])
 
definition "\<E>_impl = (SOME es. set es = \<E> \<and> distinct es)"

lemma \<E>_impl_prop: "set \<E>_impl = \<E>" "distinct \<E>_impl"
  using  es_exist[simplified sym[OF some_eq_ex]] 
  by (auto simp add: \<E>_impl_def) 

lemma u_impl_exists: "\<exists> u_impl. dom (flow_lookup u_impl) = \<E> \<and> (\<forall> e \<in> \<E>. flow_lookup u_impl e = Some (\<u> e))
                                \<and> flow_invar u_impl"
  using  finite_E
proof(induction  rule: finite_induct)
  case empty
  then show ?case 
    by (auto intro: exI[of _ flow_empty] simp add: flow_map.invar_empty flow_map.map_empty)
next
  case (insert e F)
  then obtain u_impl where u_impl_prop:"dom (flow_lookup u_impl) = F " "(\<forall>e\<in>F. flow_lookup u_impl e = Some (\<u> e))"
                           "flow_invar u_impl" by auto
  show ?case 
   using  flow_map.map_update[OF u_impl_prop(3)] u_impl_prop
   by(auto intro!: exI[of _ "flow_update e (\<u> e) u_impl"] domI flow_map.invar_update) force+
qed

definition "\<u>_impl = (SOME u_impl. dom (flow_lookup u_impl) = \<E> \<and> (\<forall> e \<in> \<E>. flow_lookup u_impl e = Some (\<u> e))
                                \<and> flow_invar u_impl)"

lemma \<u>_impl_props: "dom (flow_lookup \<u>_impl) = \<E>" "(\<forall> e \<in> \<E>. flow_lookup \<u>_impl e = Some (\<u> e))"
                                "flow_invar \<u>_impl"
  using  u_impl_exists[simplified sym[OF some_eq_ex]] 
  by (auto simp add: \<u>_impl_def) 

lemma flow_network_impl:"flow_network (prod.fst \<circ> make_pair) (prod.snd \<circ> make_pair) make_pair create_edge (the_default PInfty \<circ> flow_lookup \<u>_impl) \<E>"
proof -
  have "snd = prod.snd \<circ> make_pair \<and> fst = prod.fst \<circ> make_pair"
    by (auto simp add: make_pair''(1) make_pair''(2))
  then show "flow_network (prod.fst \<circ> make_pair) (prod.snd \<circ> make_pair) make_pair create_edge (the_default PInfty \<circ> flow_lookup \<u>_impl) \<E>"
    using flow_network_axioms \<u>_impl_props(1,2)
    by(force split: option.split simp add:  flow_network_def flow_network_axioms_def the_default_def dom_def)
qed

lemma flow_network2:"flow_network (prod.fst \<circ> make_pair) (prod.snd \<circ> make_pair) make_pair create_edge \<u> \<E>"
  using finite_E  by(auto intro!: flow_network.intro multigraph.intro flow_network_axioms.intro 
                           simp add: create_edge E_not_empty u_non_neg)

lemma b_impl_exists: "\<exists> b_impl. dom (bal_lookup b_impl) = \<V>  \<and> 
                         (\<forall> v \<in> \<V>. bal_lookup b_impl v = Some (b v)) \<and> bal_invar b_impl"
    using  \<V>_finite
proof(induction  rule: finite_induct)
  case empty
  then show ?case 
    by (auto intro: exI[of _ bal_empty] simp add: bal_map.invar_empty bal_map.map_empty)
next
  case (insert u V)
  then obtain b_impl where b_impl_prop:"dom (bal_lookup b_impl) = V " 
                         "(\<forall>v \<in> V. bal_lookup b_impl v = Some (b v))"
                           "bal_invar b_impl" by auto
  show ?case 
   using  bal_map.map_update[OF b_impl_prop(3)] b_impl_prop
   by(auto intro!: exI[of _ "bal_update u (b u) b_impl"] domI bal_map.invar_update) force+
qed

definition "b_impl b = (SOME b_impl.  dom (bal_lookup b_impl) = \<V>  \<and> 
                         (\<forall> v \<in> \<V>. bal_lookup b_impl v = Some (b v)) \<and> bal_invar b_impl)"

lemma b_impl_props: "dom (bal_lookup (b_impl b)) = \<V> " "(\<forall> v \<in> \<V>. bal_lookup (b_impl b) v = Some (b v))"
                                "bal_invar (b_impl b)"
  using  b_impl_exists[simplified sym[OF some_eq_ex]] 
  by (auto simp add: b_impl_def) force

lemma solve_maxflow_proofs: "solve_maxflow_proofs s t make_pair create_edge \<E>_impl \<u>_impl \<E> (the_default PInfty \<circ> flow_lookup \<u>_impl)"
  apply(rule solve_maxflow_proofs.intro[OF flow_network_impl], rule solve_maxflow_proofs_axioms.intro)
  by(auto simp add: \<E>_impl_prop \<u>_impl_props set_invar_def to_set_def s_in_V t_in_V s_neq_t)


interpretation algo_locale: solve_maxflow_proofs
  where  make_pair = make_pair and create_edge = create_edge
  and \<E>_impl = \<E>_impl and \<u>_impl = \<u>_impl and \<E> = \<E>
  and \<u> = "the_default PInfty \<circ> flow_lookup \<u>_impl" 
  using solve_maxflow_proofs by simp

lemma algo_locale_isbflow_def:"algo_locale.isbflow f b = flow_network.isbflow (prod.fst o make_pair) (prod.snd o make_pair)
                                 make_pair (the_default PInfty \<circ> flow_lookup \<u>_impl) \<E> f b"
  by auto

lemma to_maxflow_from_algo: "algo_locale.is_s_t_flow f s t \<Longrightarrow> f is s--t flow"
proof(goal_cases)
  case 1
  hence all_props:"algo_locale.isuflow f" "algo_locale.ex f s \<le> 0"
        "s \<in> algo_locale.\<V>" "t \<in> algo_locale.\<V>" "s \<noteq> t" 
        "(\<And> x. x\<in>algo_locale.\<V> \<Longrightarrow> x \<noteq> s \<Longrightarrow> x \<noteq> t \<Longrightarrow> algo_locale.ex f x = 0)"
    using algo_locale.is_s_t_flow_def[of f s t] by auto
  have "isuflow f"
    using all_props(1) \<u>_impl_props(2) 
    by(subst (asm)  algo_locale.isuflow_def )(auto simp add:  isuflow_def the_default_def)
  moreover have "ex f s \<le> 0"
    using all_props(2) \<u>_impl_props(2) 
     by (auto simp add: algo_locale.ex_def   algo_locale.delta_minus_def algo_locale.delta_plus_def make_pair'' ex_def delta_plus_def delta_minus_def)
   moreover have "(\<And> x. x\<in>\<V> \<Longrightarrow> x \<noteq> s \<Longrightarrow> x \<noteq> t \<Longrightarrow> ex f x = 0)"
     using all_props(6)
   by (auto simp add: algo_locale.ex_def   algo_locale.delta_minus_def algo_locale.delta_plus_def make_pair'' ex_def delta_plus_def delta_minus_def)
  ultimately show ?case
    using s_in_V t_in_V s_neq_t by(auto intro!: is_s_t_flowI)
qed

lemma to_alog_max_flow: "f is s--t flow \<Longrightarrow> algo_locale.is_s_t_flow f s t"
proof(goal_cases)
  case 1
  hence all_props:"isuflow f" "ex f s \<le> 0" "s \<in>\<V>" "t \<in> \<V>" "s \<noteq> t" 
        "(\<And> x. x\<in>\<V> \<Longrightarrow> x \<noteq> s \<Longrightarrow> x \<noteq> t \<Longrightarrow>ex f x = 0)"
     by (auto simp add: is_s_t_flow_def)
  have "algo_locale.isuflow f"
    using all_props(1) \<u>_impl_props(2) 
    by(subst  algo_locale.isuflow_def )(auto simp add:  isuflow_def the_default_def)
  moreover have "algo_locale.ex f s \<le> 0"
    using all_props(2) \<u>_impl_props(2) 
     by (auto simp add: algo_locale.ex_def   algo_locale.delta_minus_def algo_locale.delta_plus_def make_pair'' ex_def delta_plus_def delta_minus_def)
   moreover have "(\<And> x. x\<in>\<V> \<Longrightarrow> x \<noteq> s \<Longrightarrow> x \<noteq> t \<Longrightarrow> algo_locale.ex f x = 0)"
     using all_props(6)
   by (auto simp add: algo_locale.ex_def   algo_locale.delta_minus_def algo_locale.delta_plus_def make_pair'' ex_def delta_plus_def delta_minus_def)
  ultimately show ?case
    using s_in_V t_in_V s_neq_t flow_network_impl 
    by(auto intro!: flow_network.is_s_t_flowI)
qed

lemma existence_of_maximum_flow:
"(\<exists> f. is_max_flow s t f) \<longleftrightarrow>  no_infty_path"
proof(rule, goal_cases)
  case 1
  then obtain f where isopt: " is_max_flow s t f" by auto
  define b where "b = (\<lambda>x. if x = s then ex\<^bsub>f\<^esub> t else if x = t then - ex\<^bsub>f\<^esub> t else 0)"
  hence fbflow:"f is s--t flow" "f is b flow"
    using isopt is_max_flow_def[OF s_in_V t_in_V s_neq_t]s_t_flow_is_ex_bflow[of f s t]  by blast+
  moreover have no_infty_path
    unfolding no_infty_path_def
  proof(rule nexistsI, goal_cases)
    case (1 D)
    hence u_prop: "awalk UNIV s (map make_pair D) t" " set D \<subseteq> \<E>" "(\<forall>e\<in>set D. \<u> e = PInfty)"
        and Dlen: "length D > 0" 
      using s_neq_t by(auto simp add: awalk_def)
    have rcap:"0 < Rcap f (set (map F D))"
      using 1(1) 
      by (auto simp add:  Rcap_def)
    have same_path:"(map (to_vertex_pair \<circ> F) D) = (map make_pair D)" 
      by simp
    have fstv_is: "fstv (hd (map F D)) = s"
      using Dlen awalk_hd[OF u_prop(1)]
      by(cases D)(auto simp add:  make_pair'')
    have sndv_is: "sndv (last (map F D)) = t"
      using Dlen awalk_last[OF u_prop(1)]
      by(cases D rule: rev_cases)(auto simp add:  make_pair'')
    have augpath:"augpath f (map F D)" "prepath (map F D)"
      using 1(1) u_prop(1) Dlen rcap
      by(auto simp add: same_path fstv_is sndv_is augpath_def  prepath_def closed_w_def intro: subset_mono_awalk)
    have D_EE: "set (map F D) \<subseteq> \<EE>"
      using 1(1)
      by(force simp add: \<EE>_def)
    obtain ds where ds_prop:"prepath ds" "distinct ds" "set ds \<subseteq> set (map F D)" "fstv (hd (map F D)) = fstv (hd ds)"
       "sndv (last (map F D)) = sndv (last ds)" "ds \<noteq> []"
      apply(cases "distinct (map F D)")
      subgoal
      using D_EE augpath(2) unfolding   prepath_def by blast
    by(auto intro: prepath_drop_cycles[OF augpath(2) ])
    have rcap2:"Rcap f (set ds) > 0"
      using ds_prop(3) u_prop(3) by(auto simp add: Rcap_def )
    hence g_gtr_0:"real_of_ereal (min 1 (Rcap f (set ds))) > 0" 
      by(cases "Rcap f (set ds)") (auto simp add: min_def)
    have augpath_ds: "augpath f ds"
      using  ds_prop(1) rcap2 by (auto simp add: augpath_def)
    have g_less_rcap: "ereal (real_of_ereal (min 1 (Rcap f (set ds)))) \<le> Rcap f (set ds)"
      using rcap2 by(cases "Rcap f (set ds)") (auto simp add: min_def)
    have after_augment: "augment_edges f (real_of_ereal (min 1 (Rcap f (set ds)))) ds 
            is \<lambda>v. if v = fstv (hd ds) then b v + real_of_ereal (min 1 (Rcap f (set ds)))
            else if v = sndv (last ds) then b v - real_of_ereal (min 1 (Rcap f (set ds))) else b v flow"
      using augpath_ds g_less_rcap ds_prop D_EE fstv_is sndv_is s_neq_t g_gtr_0  fbflow(2)
      by(auto intro!: augment_path_validness_b_pres_source_target_distinct)
    have "augment_edges f (real_of_ereal (min 1 (Rcap f (set ds)))) ds is s -- t flow"
    proof(rule is_s_t_flowI[OF _ _ s_in_V t_in_V s_neq_t], goal_cases)
      case 1
      then show ?case 
        using after_augment isbflow_def by blast
    next
      case 2
      have "ex\<^bsub>augment_edges f (real_of_ereal (min 1 (Rcap f (set ds)))) ds\<^esub> s = 
           - (b s + (real_of_ereal (min 1 (Rcap f (set ds)))))"
        using after_augment s_in_V ds_prop(4) fstv_is 
        by(fastforce simp add: isbflow_def)
      also have "... \<le> - b s" 
        using g_gtr_0 by argo
      also have "... = ex f s"
        using b_def fbflow(1) s_t_flow_excess_s_t by force
      also have "... \<le> 0" 
        using fbflow(1)
        by(simp add: is_s_t_flow_def)
     finally show ?case by simp
    next
      case (3 x)
      have "ex\<^bsub>augment_edges f (real_of_ereal (min 1 (Rcap f (set ds)))) ds\<^esub> x = 
            ex f x"
        using after_augment 3 t_in_V ds_prop(4,5) sndv_is s_neq_t fstv_is fbflow(2)
        by(fastforce simp add: isbflow_def)
      moreover  have "... = 0" 
        using "3"(1) "3"(2) "3"(3) fbflow(1) is_s_t_flow_def by blast
      ultimately show ?case by simp
    qed
    moreover have "ex\<^bsub>augment_edges f (real_of_ereal (min 1 (Rcap f (set ds)))) ds\<^esub> t
                   > ex f t"
    proof-
       have "ex\<^bsub>augment_edges f (real_of_ereal (min 1 (Rcap f (set ds)))) ds\<^esub> t =
           - (b t - (real_of_ereal (min 1 (Rcap f (set ds)))))"
        using after_augment s_in_V ds_prop(4,5) fstv_is  s_neq_t sndv_is t_in_V by (auto simp add: isbflow_def)
      moreover  have "... > - b t" 
        using g_gtr_0 by argo
      moreover have "- b t = ex f t"
        using b_def fbflow(1) s_t_flow_excess_s_t by force
      ultimately show "ex\<^bsub>augment_edges f (real_of_ereal (min 1 (Rcap f (set ds)))) ds\<^esub> t > ex f t"
        by simp
    qed
    ultimately show ?case 
      using isopt by(auto simp add: is_max_flow_def[OF s_in_V t_in_V s_neq_t])
  qed
  thus ?case by simp
next
  case 2
  have no_infty_path:" (\<not>(\<exists>D. awalk UNIV s (map make_pair D) t \<and> set D \<subseteq> \<E> \<and> (\<forall>e\<in>set D. \<u> e = PInfty)))"
    using 2 by(auto simp add: no_infty_path_def)
  have no_infty_path':"\<nexists>D. awalk (make_pair ` \<E>) s (map make_pair D) t \<and>
        0 < length D \<and> set D \<subseteq> \<E> \<and> (\<forall>e\<in>set D. (the_default PInfty \<circ> flow_lookup \<u>_impl) e = PInfty)"
  proof(rule nexistsI, goal_cases)
    case (1 D)
    moreover hence "awalk UNIV s (map make_pair D) t" 
      using awalk_ends s_neq_t by(auto intro: subset_mono_awalk')
    moreover have "(\<forall>e\<in>set D. \<u> e = PInfty)" 
      using 1 \<E>_impl_prop(1) \<u>_impl_props(2) algo_locale.in_E_same_cap 
            algo_locale.u_impl'_same_u by fastforce
    ultimately show ?case 
      using no_infty_path by blast
  qed
  have success:"return_impl (solve_maxflow.final_state_maxflow make_pair create_edge \<E>_impl \<u>_impl s t) = success"
    using algo_locale.correctness_of_implementation(2,3)[OF no_infty_path'] IntermediateSummary.return.exhaust by blast
  have max_flow_algo:"algo_locale.is_max_flow s t
 (abstract_flow_map (solve_maxflow.final_flow_impl_maxflow_original make_pair create_edge \<E>_impl \<u>_impl s t))"
    using algo_locale.correctness_of_implementation(1)[OF no_infty_path' success] by simp
  have "is_max_flow s t
 (abstract_flow_map (solve_maxflow.final_flow_impl_maxflow_original make_pair create_edge \<E>_impl \<u>_impl s t))"
  proof(rule is_max_flowI[OF s_in_V t_in_V s_neq_t], goal_cases)
    case 1
    have "algo_locale.is_s_t_flow (abstract_flow_map 
           (solve_maxflow.final_flow_impl_maxflow_original make_pair create_edge \<E>_impl \<u>_impl s t)) s t"
      using max_flow_algo by(subst(asm) algo_locale.is_max_flow_def[OF s_in_V t_in_V s_neq_t]) simp
    thus ?case
      by(auto intro: to_maxflow_from_algo)
    case (2 g)
    hence "algo_locale.is_s_t_flow g s t"
      by(force intro!: to_alog_max_flow) 
    hence "algo_locale.ex g t \<le> algo_locale.ex (abstract_flow_map
                (solve_maxflow.final_flow_impl_maxflow_original make_pair create_edge \<E>_impl \<u>_impl s t)) t"
      using algo_locale.is_max_flow_def max_flow_algo s_in_V s_neq_t t_in_V by blast
    moreover have "algo_locale.ex g t = ex g t"
       by (auto simp add: algo_locale.ex_def algo_locale.delta_minus_def algo_locale.delta_plus_def make_pair'' ex_def delta_plus_def delta_minus_def)
     moreover have " algo_locale.ex (abstract_flow_map
                (solve_maxflow.final_flow_impl_maxflow_original make_pair create_edge \<E>_impl \<u>_impl s t)) t
             =  ex (abstract_flow_map
                (solve_maxflow.final_flow_impl_maxflow_original make_pair create_edge \<E>_impl \<u>_impl s t)) t"
       by (auto simp add: algo_locale.ex_def algo_locale.delta_minus_def algo_locale.delta_plus_def make_pair'' ex_def delta_plus_def delta_minus_def)   
    ultimately show ?case by auto
  qed
  thus ?case by auto
qed
end
end
end
