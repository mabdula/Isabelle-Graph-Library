section \<open>Single-Source-Single-Target Flows\<close>

theory STFlow
  imports Decomposition Cost_Optimality
begin

datatype 'b edge_wrapper = is_old: old_edge 'b | new_edge 'b

context 
  flow_network_spec
begin

definition is_s_t_flow ( "_ is _ -- _ flow") where
  "is_s_t_flow f s t = (isuflow f \<and> ex f s \<le> 0 \<and> s \<in> \<V> \<and> t \<in> \<V> \<and> s \<noteq> t \<and> 
                      (\<forall> x \<in> \<V>. x\<noteq> s \<longrightarrow> x \<noteq> t \<longrightarrow> ex f x = 0))"

lemma is_s_t_flowI:
  "\<lbrakk>isuflow f; ex f s \<le> 0; s \<in> \<V>; t \<in> \<V>; s \<noteq> t;
                      (\<And> x. \<lbrakk>x \<in> \<V>; x\<noteq> s; x \<noteq> t\<rbrakk> \<Longrightarrow> ex f x = 0)\<rbrakk> \<Longrightarrow> is_s_t_flow f s t"
  by(auto simp add: is_s_t_flow_def)

lemma is_s_t_flowE:
  "\<lbrakk>is_s_t_flow f s t; (\<lbrakk>isuflow f; ex f s \<le> 0; s \<in> \<V>; t \<in> \<V>; s \<noteq> t;
                      (\<And> x. \<lbrakk>x \<in> \<V>; x\<noteq> s; x \<noteq> t \<rbrakk>\<Longrightarrow> ex f x = 0)\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: is_s_t_flow_def)
end

context 
  flow_network
begin
lemma s_t_flow_excess_s_t:
  "f is s -- t flow \<Longrightarrow> ex f t = - ex f s"
proof(goal_cases)
  case 1
  hence props:"isuflow f" "ex f s \<le> 0" "s \<in> \<V>" "t \<in> \<V>" "s \<noteq> t" 
    "(\<And>x. \<lbrakk>x \<in> \<V>; x\<noteq> s; x \<noteq> t\<rbrakk> \<Longrightarrow> ex f x = 0)"
    by (auto simp add: is_s_t_flow_def)
  hence bflow: "isbflow f (\<lambda> v. -ex f v)"
    by(auto simp add: isbflow_def)
  have "-ex f s = (\<Sum>v\<in>\<V> - {t}. - ex\<^bsub>f\<^esub> v)"
    apply(rule forw_subst[of _ "(\<V> - {t, s}) \<union> {s}"])
    using  sum.union_disjoint  \<V>_finite  props 
    by auto
  also have "... = sum f (\<Delta>\<^sup>+ (\<V> - {t}) ) - sum f (\<Delta>\<^sup>- (\<V> - {t}))"
    by(auto intro: flow_value[OF bflow, of "\<V> - {t}"])
  also have "... = sum f (\<delta>\<^sup>- t - \<delta>\<^sup>+ t) - sum f (\<delta>\<^sup>+ t  - \<delta>\<^sup>- t)"
    using make_pair
    by (auto intro!: diff_eq_split cong[of "sum f"] 
        simp add:  Delta_plus_def Delta_minus_def  delta_plus_def delta_minus_def)
  also have "... = sum f (\<delta>\<^sup>- t - (\<delta>\<^sup>+ t \<inter> \<delta>\<^sup>- t)) - sum f (\<delta>\<^sup>+ t - (\<delta>\<^sup>+ t \<inter> \<delta>\<^sup>- t))"
    by(auto intro: diff_eq_split  cong[of "sum f"])
  also have "... = (sum f (\<delta>\<^sup>- t - (\<delta>\<^sup>+ t \<inter> \<delta>\<^sup>- t)) + sum f (\<delta>\<^sup>+ t \<inter> \<delta>\<^sup>- t)) -
                    (sum f (\<delta>\<^sup>+ t - (\<delta>\<^sup>+ t \<inter> \<delta>\<^sup>- t)) + sum f (\<delta>\<^sup>+ t \<inter> \<delta>\<^sup>- t))"
    by simp
  also have "... = ex f t"
    unfolding ex_def
    by(rule diff_eq_split)
      (subst sym[OF sum.union_disjoint ], 
        auto intro!: cong[ of "sum f", OF refl]
        simp add: inf_commute delta_plus_finite delta_minus_finite)+
  finally show ?case by simp
qed 

lemma s_t_flow_is_ex_bflow:
  "f is s -- t flow \<Longrightarrow> (f is (\<lambda> x. if x = s then ex f t else if x = t then - ex f t else 0) flow)"
  using s_t_flow_excess_s_t[of f s t] 
  by(simp add: is_s_t_flow_def isbflow_def)

lemma u_sum_pos: "0 \<le> sum \<u> \<E>"
  by (auto intro: sum_nonneg simp add: u_non_neg)

lemma zero_flow_is_s_t_flow: 
  "\<lbrakk>s \<in> \<V>; t \<in> \<V>; s \<noteq> t\<rbrakk> \<Longrightarrow> is_s_t_flow (\<lambda> e. 0) s t "
  using u_non_neg
  by(auto intro!: is_s_t_flowI isuflowI
      simp add: zero_ereal_def ex_def)

lemma ex_less_sum_cap:
  assumes "isuflow f" "x \<in> \<V>"
  shows " ex f x \<le> sum \<u> \<E>"
proof-
  have "ex f x \<le> sum f (\<delta>\<^sup>- x)"
    using assms delta_plus_def 
    by(auto intro: sum_nonneg simp add: ex_def isuflow_def)
  also have "... \<le> sum \<u> (\<delta>\<^sup>- x)"
    using assms 
    by(subst sym[OF sum_ereal])(fastforce intro!: sum_mono simp add: isuflow_def delta_minus_def )
  also have "... \<le> sum \<u> \<E>"
    using assms(2)  u_non_neg 
    by (auto intro: sum_mono2 simp add: delta_minus_def finite_E)
  finally show ?thesis by simp
qed

lemma augment_along_s_t_path:
  assumes "is_s_t_flow f s t" "0 \<le> \<gamma>" "ereal \<gamma> \<le> Rcap f (set p)" "set p \<subseteq> \<EE>" "distinct p"
    "fstv (hd p) = s" "sndv (last p) = t" "augpath f p" "s \<in> \<V>" "t \<in> \<V>"
  shows "is_s_t_flow (augment_edges  f \<gamma> p) s t"
  using s_t_flow_excess_s_t[OF assms(1)] assms 
    augment_path_validness_b_pres_source_target_distinct[OF
      s_t_flow_is_ex_bflow[OF assms(1)] assms(2)  assms(8,3,4,5)]
  by(auto simp add: is_s_t_flow_def isbflow_def ex_def intro: augment_path_validness_pres)
end

context 
  flow_network_spec
begin
subsection \<open>Decomposition of $s$-$t$-Flows\<close>

fun make_pair' where
  "make_pair' (old_edge e) = ((fst e), (snd e))"|
  "make_pair' (new_edge e) = ( (fst e), (snd e))"

fun fst' where
  "fst' (old_edge e) = fst e"|
  "fst' (new_edge e) = fst e"

fun snd' where
  "snd' (old_edge e) = snd e"|
  "snd' (new_edge e) = snd e"

lemma make_pair'_alt: "make_pair' = (\<lambda> e. case e of old_edge e \<Rightarrow> (fst e, snd e) |
                                           new_edge e \<Rightarrow> (fst e, snd e))"
  by(auto split: edge_wrapper.split)

lemma fst'_def2: "fst' = case_edge_wrapper fst fst"
  "case_edge_wrapper fst fst = fst'"
  by(auto intro!: ext split: edge_wrapper.split)

lemma snd'_def2: "snd' = case_edge_wrapper snd snd"
  "case_edge_wrapper snd snd =snd'"
  by(auto intro!: ext split: edge_wrapper.split)
end

context 
  flow_network
begin
lemma case_edge_wrapper_make_pair:"case_edge_wrapper make_pair make_pair = make_pair'" 
  by(auto split: edge_wrapper.split simp add: make_pair')

fun create_edge' where
  "create_edge' x y = old_edge (create_edge x y)"

fun get_old_edge where
  "get_old_edge (old_edge e) = e"

lemma fst'_def: "fst' = prod.fst o make_pair'" 
  apply(rule ext)
  subgoal for x
    by(cases x) auto
  done

lemma snd'_def: "snd' = prod.snd o make_pair'" 
  apply(rule ext)
  subgoal for x
    by(cases x) auto
  done

lemma make_pair'_is_make_pair_of_get_old_edge:
  assumes "X \<subseteq> old_edge ` Y"
  shows "make_pair' ` X = make_pair ` get_old_edge ` X"
proof-
  obtain Yr where Yr: "X = old_edge ` Yr" 
    using assms by blast
  show ?thesis
    unfolding Yr
    by (metis (no_types, lifting) case_edge_wrapper_make_pair edge_wrapper.simps(5)
        flow_network.get_old_edge.simps flow_network_axioms image_cong image_image)
qed

lemma map_make_pair'_is_make_pair_of_get_old_edge:
  assumes "set X \<subseteq> old_edge ` Y"
  shows "map make_pair'  X = map (make_pair o get_old_edge) X"
  using assms
  by(induction X) (auto simp add: make_pair)

lemma  fst_of_wrapped_edges:"fst x1 = fst' (old_edge x1)" "snd x1 = snd' (old_edge x1)"
  "fst x1 = fst' (new_edge x1)" "snd x1 = snd' (new_edge x1)"
  by (auto simp add: fst'_def snd'_def)

interpretation network_of_network: flow_network where
  fst = fst' and snd = snd' and create_edge = create_edge'
  and \<E> = "old_edge ` \<E> \<union> {new_edge (create_edge t s)}"
  and \<u> = " (\<lambda> e. case e of  old_edge e \<Rightarrow> \<u> e |  _ \<Rightarrow> sum \<u> \<E>)"
  using  make_pair create_edge  E_not_empty u_non_neg make_pair'.elims[of "create_edge' _ _", OF refl] u_sum_pos
  by(auto simp add: finite_E make_pair[OF refl refl] create_edge 
      flow_network_axioms_def flow_network_def multigraph_def fst'_def snd'_def
      split: edge_wrapper.split)

lemma make_pair'_is: "network_of_network.make_pair = make_pair'"
  "make_pair' = network_of_network.make_pair"
  using fst'_def network_of_network.fstv.simps(1) network_of_network.sndv.simps(1)
    network_of_network.to_vertex_pair.simps(1) network_of_network.to_vertex_pair_fst_snd snd'_def
  by auto

lemma s_t_flow_decomposition:
  assumes "f is s -- t flow"
  obtains css cws pss pws where "length css = length cws"
    "length pss = length pws"
    "(\<And> w. w\<in>set cws \<union> set pws \<Longrightarrow> 0 < w)"
    "(\<And> cs. cs\<in>set css \<Longrightarrow> flowcycle f cs \<and> set cs \<subseteq> support f \<and> distinct cs)"
    "(\<And> ps. ps\<in>set pss \<Longrightarrow> flowpath f ps \<and> set ps \<subseteq> support f \<and> distinct ps
                  \<and> fst (hd ps) = s \<and> snd (last ps) = t)"
    "(\<And> e. e\<in> \<E> \<Longrightarrow> f e = (\<Sum>i<length css. if e \<in> set (css ! i) then cws ! i else 0) +
                  (\<Sum>i<length pss. if e \<in> set (pss ! i) then pws ! i else 0))"
    "(is_integral_flow f \<Longrightarrow> (\<forall>w\<in>set cws \<union> set pws. \<exists>n. w = real n))"
proof(cases "Abs f > 0", goal_cases)
  case 1
  hence True: "0 < Abs f" by simp
  hence props:"isuflow f" "ex f s \<le> 0" "s \<in> \<V>" "t \<in> \<V>" "s \<noteq> t" 
    "(\<And>x. \<lbrakk>x \<in> \<V>; x\<noteq> s; x \<noteq> t\<rbrakk> \<Longrightarrow> ex f x = 0)"
    using assms by (auto simp add: is_s_t_flow_def)
  hence ex_t:"ex f t \<ge> 0" 
    using assms s_t_flow_excess_s_t by auto
  have support: "support f \<noteq> {}"
    using True assms(1) sum_nonpos[of \<E> f] 
    by (force simp add: Abs_def support_def  is_s_t_flow_def isuflow_def )
  define f' where "f' = (\<lambda> e. case e of
                   old_edge e \<Rightarrow> f e |
                   _ \<Rightarrow> ex f t)"
  have "network_of_network.flow_non_neg t s f'"
    using props  ex_t
    by (subst network_of_network.flow_non_neg_def)
      (auto simp add: f'_def network_of_network.flow_non_neg_def isuflow_def)
  moreover have "0 < network_of_network.Abs t s f'"
    using True finite_E  props(2) s_t_flow_excess_s_t[OF assms(1)]
    unfolding network_of_network.Abs_def f'_def
    by(subst comm_monoid_add_class.sum.union_disjoint)
      (auto intro: forw_subst[OF sum_inj_on, of old_edge \<E>, simplified ] 
        simp add: Abs_def inj_on_def)
  moreover have "network_of_network.is_circ t s f'"
  proof(rule network_of_network.is_circI , goal_cases)
    case (1 v)
    hence v_possibilities: "(v \<noteq> s \<and> v \<noteq> t \<and> v \<in> \<V>) \<or> v = s \<or> v = t " 
      using create_edge make_pair' by ( auto simp add:  dVs_def make_pair'_is(1)) blast+
    have disj3E: "\<lbrakk>A \<or> B \<or> C; (A \<Longrightarrow> P); (B \<Longrightarrow> P); (C \<Longrightarrow> P)\<rbrakk> 
                  \<Longrightarrow> P" for A B C D P by auto
    show ?case 
    proof(rule disj3E[OF v_possibilities], goal_cases)
      case 1
      hence  u_props:  "v \<in> \<V>" "v \<noteq> s" "v \<noteq> t" by auto
      have "network_of_network.delta_plus t s v = old_edge ` (delta_plus v)"
        using u_props create_edge make_pair
        unfolding network_of_network.delta_plus_def 
        by(auto simp add: fst'_def snd'_def delta_plus_def)
      moreover have "network_of_network.delta_minus t s v = old_edge ` (delta_minus v)"
        using u_props create_edge make_pair
        unfolding network_of_network.delta_minus_def 
        by(auto simp add: fst'_def snd'_def delta_minus_def)
      ultimately have "network_of_network.ex t s f' v = ex f v"
        unfolding ex_def network_of_network.ex_def
        by(auto simp add: f'_def sum_inj_on[of old_edge, simplified inj_on_def, simplified])
      thus ?case 
        using  assms u_props
        by(simp add:  is_s_t_flow_def)
    next
      case 2
      have "network_of_network.delta_plus t s v = old_edge ` (delta_plus s)"
        using 2  props(5) create_edge make_pair
        unfolding network_of_network.delta_plus_def 
        by(auto simp add: fst'_def snd'_def delta_plus_def)
          (metis eq_fst_iff make_pair'.simps(2))
      moreover have "network_of_network.delta_minus t s v = 
                     insert (new_edge (create_edge t s)) (old_edge ` (delta_minus s))"
        using 2 create_edge make_pair'
        unfolding network_of_network.delta_minus_def
        by(auto simp add: fst'_def snd'_def delta_minus_def)
      ultimately have "network_of_network.ex t s f' v =
                      sum f (delta_plus s) - sum f (delta_minus s) + ex f s"
        using assms ex_def s_t_flow_excess_s_t
        by(unfold network_of_network.ex_def f'_def  ex_def)
          (auto intro: forw_subst[OF comm_monoid_add_class.sum.insert] 
            simp add: sum_inj_on[of old_edge, simplified inj_on_def, simplified] 
            delta_minus_finite)  
      then show ?case
        using ex_def by fastforce
    next
      case 3
      have "network_of_network.delta_minus t s v = old_edge ` (delta_minus t)"
        using 3  props(5)  create_edge make_pair'
        unfolding network_of_network.delta_minus_def 
        by(auto simp add: fst'_def snd'_def delta_minus_def)
          (metis make_pair'.simps(2) snd_conv)
      moreover have "network_of_network.delta_plus t s v = 
                     insert (new_edge (create_edge t s)) (old_edge ` (delta_plus t))"
        using 3 create_edge make_pair
        unfolding network_of_network.delta_plus_def
        by(auto simp add: fst'_def snd'_def delta_plus_def)
      ultimately have "network_of_network.ex t s f' v =
                      sum f (delta_plus t) - sum f (delta_minus t) + ex f t"
        unfolding network_of_network.ex_def f'_def  ex_def
        by(auto intro: forw_subst[OF comm_monoid_add_class.sum.insert] 
            simp add: sum_inj_on[of old_edge, simplified inj_on_def, simplified] 
            delta_plus_finite)
      then show ?case 
        using ex_def by fastforce
    qed
  qed
  moreover have "network_of_network.support t s f' \<noteq> {}"
    using support
    unfolding network_of_network.support_def f'_def support_def
    by fastforce
  ultimately have "\<exists>css ws. length css = length ws \<and> set css \<noteq> {} \<and> (\<forall>w\<in>set ws. 0 < w) \<and>
   (\<forall>cs\<in>set css.
       network_of_network.flowcycle f' cs \<and>
       set cs \<subseteq> network_of_network.support t s f' \<and> distinct cs) \<and>
   (\<forall>e\<in>old_edge ` \<E> \<union>
        {new_edge (create_edge t s)}.
       f' e = (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0)) \<and>
          (network_of_network.is_integral_flow t s f' \<longrightarrow> (\<forall>w\<in>set ws. \<exists>n. w = real n))"
    by(fastforce intro!: network_of_network.flowcycle_decomposition[of t s f', OF  _ _ _ _ refl])
  then obtain css ws where css_ws:
    "length css = length ws" "set css \<noteq> {}" "(\<forall>w\<in>set ws. 0 < w)"
    "(\<forall>cs\<in>set css.
       network_of_network.flowcycle f' cs \<and>
       set cs \<subseteq> network_of_network.support t s f' \<and> distinct cs)"
    "(\<forall>e\<in>old_edge ` \<E> \<union> {new_edge (create_edge t s)}.
       f' e = (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0))"
    "(network_of_network.is_integral_flow t s f' \<Longrightarrow> (\<forall>w\<in>set ws. \<exists>n. w = real n))"
    by auto
  have css_distinct: "\<And> cs. cs\<in>set css \<Longrightarrow> distinct cs"
    using css_ws(4) by blast
  define css_ws where "css_ws = zip css ws"
  define css_ws_cycles where "css_ws_cycles = filter (\<lambda> x. set (prod.fst x) \<subseteq> old_edge ` \<E>) css_ws"
  define css_ws_paths where "css_ws_paths = filter (\<lambda> x. \<not> set (prod.fst x) \<subseteq> old_edge ` \<E>) css_ws"
  have sum1:" (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0) =
          (\<Sum>i< length css_ws. let (cs, w) = (css_ws ! i) in 
                          if e \<in> set cs then w else 0)" for e
    unfolding css_ws_def lessThan_atLeast0 by (auto simp add: css_ws(1))
  have sum2:"(\<Sum>i<length css_ws. let (cs, w) = css_ws ! i in if e \<in> set cs then w else 0) =
            (\<Sum>i<length css_ws. (map (\<lambda> x. let (cs, w) = x in if e \<in> set cs then w else 0) css_ws) ! i)"
    for e  by simp
  have sum3:" (\<Sum>i<length css_ws. (map (\<lambda> x. let (cs, w) = x in if e \<in> set cs then w else 0) css_ws) ! i) =
              sum_list (map (\<lambda> x. let (cs, w) = x in if e \<in> set cs then w else 0) css_ws)"
    for e
    unfolding lessThan_atLeast0 sum_list_sum_nth[of "map _ _", symmetric, simplified] 
    by simp
  have sum4:"sum_list (map (\<lambda> x. let (cs, w) = x in if e \<in> set cs then w else 0) css_ws) = 
             sum_list (map (\<lambda> x. let (cs, w) = x in if e \<in> set cs then w else 0) css_ws_cycles)
            + sum_list (map (\<lambda> x. let (cs, w) = x in if e \<in> set cs then w else 0) css_ws_paths)" for e
    by(auto simp add: css_ws_cycles_def css_ws_paths_def  sum_list_map_filter_split)
  define css' where "css' = map (map (get_old_edge) o prod.fst) css_ws_cycles "
  define cws where "cws = map  prod.snd css_ws_cycles"
  define get_s_t_path where
    "get_s_t_path (P::('edge_type) edge_wrapper list)
                    = (let first1 = takeWhile is_old P;
                           first2 = dropWhile is_old P;
                           second = dropWhile (\<lambda> e. \<not> is_old e) first2
                       in map get_old_edge (second@first1))" for P
  define pss where "pss = map (map (get_old_edge) o prod.fst) css_ws_paths"
  define cws where "cws = map  prod.snd css_ws_cycles " 
  define pss where "pss = map (get_s_t_path o prod.fst) css_ws_paths"
  define pws where "pws = map  prod.snd css_ws_paths" 
  have "length css' = length cws"
    unfolding css'_def cws_def by auto
  moreover have "length pss = length pws"
    unfolding pss_def pws_def by simp
  moreover have "\<forall>w\<in>set cws \<union> set pws. 0 < w"
    using  css_ws(3) 
    by(auto intro: set_zip_rightD simp add: cws_def pws_def css_ws_paths_def css_ws_cycles_def css_ws_def)
  moreover have "\<forall>cs\<in>set css'. flowcycle f cs \<and> set cs \<subseteq> support f \<and> distinct cs"
    unfolding css'_def css_ws_cycles_def css_ws_def
  proof(rule ballI, goal_cases)
    case (1 cs')
    then obtain cs where cs_prop: "cs \<in> set css" " set cs \<subseteq> old_edge ` \<E>"
      "cs' = map network_of_network.get_old_edge cs"
      by auto (metis set_zip_leftD)
    hence cs_further_prop:"network_of_network.flowcycle f' cs"
      "set cs \<subseteq> network_of_network.support t s f'"  "distinct cs"
      using css_ws(4) by auto
    have cs_non_empty: "cs \<noteq> Nil" "cs' \<noteq> Nil"
      using cs_further_prop(1) network_of_network.flowcycle_def 
      by (force simp add:  cs_prop(3))+
    have "awalk UNIV (prod.fst (make_pair' (hd cs))) (map make_pair' cs)
     (prod.fst (make_pair' (hd cs)))"
      using cs_further_prop(1) fst'_def snd'_def  make_pair'_is(1)
      unfolding network_of_network.flowcycle_def network_of_network.flowpath_def 
        network_of_network.multigraph_path_def     
      by auto
    hence "awalk (make_pair' ` set cs) (prod.fst (make_pair' (hd cs))) (map make_pair' cs)
                   (prod.fst (make_pair' (hd cs)))" 
      using cs_non_empty(1)
      by(auto intro: subset_mono_awalk'[of UNIV _ _ _ "(make_pair' ` set cs)", simplified])
    moreover have "(fst (hd cs')) =  (prod.fst (make_pair' (hd cs)))" 
      apply(subst cs_prop(3) , subst list.map_sel(1))
      using cs_prop(2) list.set_sel(1)[OF cs_non_empty(1)]
      by auto
    moreover have "(map make_pair cs') = (map make_pair' cs) "
      using cs_prop(3)  cs_prop(2)  make_pair by auto
    moreover hence "make_pair ` set cs' = (id o make_pair') ` set cs " 
      using cs_prop(3)  cs_prop(2)  make_pair 
      by (metis id_comp list.set_map)
    ultimately have "awalk (make_pair ` set cs') (fst (hd cs')) (map make_pair cs') (fst (hd cs'))"
      by(simp only:)
        (fastforce intro!: awalk_image[OF _ _ refl, of "make_pair' ` set cs" "prod.fst (make_pair' (hd cs))"
            "map make_pair' cs" "prod.fst (make_pair' (hd cs))", simplified image_comp])
    hence "awalk UNIV (fst (hd cs')) (map make_pair cs') (fst (hd cs'))"
      by (meson subset_UNIV subset_mono_awalk)
    moreover hence "(fst (hd cs')) = (snd (last cs'))"
      using awalk_fst_last cs_non_empty(2) 
      by (metis Nil_is_map_conv last_map make_pair' snd_conv)
    moreover have e_E:"e \<in> set cs' \<Longrightarrow> e \<in>\<E>" for e
    proof(goal_cases)
      case 1
      then obtain d where "e = get_old_edge d" "d \<in> set cs" 
        unfolding cs_prop(3) by auto
      thus ?case 
        using cs_prop(2) by auto
    qed
    moreover have posf:"e \<in> set cs' \<Longrightarrow> 0 < f e" for e
    proof(goal_cases)
      case 1
      then obtain d where "e = get_old_edge d" "d \<in> set cs" 
        unfolding cs_prop(3) by auto
      moreover hence "f' d > 0"
        using cs_further_prop(1) 
        by(auto simp add: network_of_network.flowcycle_def network_of_network.flowpath_def )
      ultimately show ?case 
        using cs_prop(2)
        by (auto simp add: f'_def)
    qed
    ultimately have "flowcycle f  cs'"
      using cs_non_empty(2) 
      by(auto simp add:flowcycle_def flowpath_def  multigraph_path_def )
    moreover have "set cs' \<subseteq> support f "
      using e_E posf by (force simp add: support_def)
    moreover have "distinct cs'"
    proof-
      have "distinct cs \<Longrightarrow> inj_on network_of_network.get_old_edge (set cs)"
      proof(rule inj_onI, goal_cases)
        case (1 x y)
        thus ?case
          using cs_prop(2)  by(cases x, all \<open>cases y\<close>) auto
      qed
      thus ?thesis
        using cs_further_prop(3) 
        by(auto simp add:  cs_prop(3) distinct_map)
    qed
    ultimately show ?case by simp
  qed
  moreover have "\<forall>ps\<in>set pss. flowpath f ps \<and> set ps \<subseteq> support f \<and> distinct ps \<and>
                        fst (hd ps) = s \<and> snd (last ps) = t"
    unfolding pss_def
  proof(rule ballI, goal_cases)
    case (1 ps)
    then obtain cs' ws' where cs'_ws'_prop:"ps = get_s_t_path cs'" "(cs', ws') \<in> set css_ws_paths"
      by auto
    hence cs_prop:"cs' \<in> set css" "\<not> set cs' \<subseteq> old_edge ` \<E>"                                
      using set_zip_leftD by(fastforce simp add: css_ws_paths_def css_ws_def)+
    hence "new_edge (create_edge t s)  \<in> set cs'"
      and cs'subset_E:"set cs' \<subseteq> insert (new_edge (create_edge t s)) (old_edge ` \<E>)"
      using css_ws(4) unfolding network_of_network.support_def
      by auto
    then obtain C1 C2 where cs'_split:"cs' = C1@[new_edge (create_edge t s)]@C2" 
      by (metis in_set_conv_decomp_first single_in_append)
    have C1C2_in_E:"set C1 \<union> set C2 \<subseteq> old_edge ` \<E>"
    proof(rule ccontr)
      assume "\<not> set C1 \<union> set C2 \<subseteq> old_edge ` \<E>"
      moreover have "set C1 \<union> set C2 \<subseteq> old_edge ` \<E>
                  \<union> {new_edge (create_edge t s)}"
        using css_ws(4) cs'_split cs_prop(1) unfolding network_of_network.support_def
        by force
      ultimately have "new_edge (create_edge t s) \<in> set C1 \<union> set C2"
        by auto
      hence "\<not> distinct cs'" 
        using cs'_split by force
      thus False 
        using cs_prop(1) css_distinct by force
    qed
    have ps_is:"ps = map get_old_edge (C2@C1)"
      unfolding  cs'_ws'_prop(1) get_s_t_path_def cs'_split Let_def map_append
    proof(rule arg_cong2[where f = append], all \<open>rule arg_cong[where f= "map get_old_edge"]\<close>, goal_cases)
      case 1
      have "dropWhile is_old (C1 @ ([new_edge (create_edge t s)] @ C2)) = 
             [new_edge (create_edge t s)] @ C2" 
        using C1C2_in_E
        by(auto simp add: dropWhile_append)
      moreover have "dropWhile (\<lambda>e. \<not> is_old e) ([new_edge (create_edge t s)] @ C2) = C2"
        using  C1C2_in_E dropWhile_nothing[of C2 "\<lambda>e. \<not> is_old e"]
        by(force simp add: dropWhile_append ) 
      ultimately show ?case
        using cs'subset_E C1C2_in_E cs'_split by simp
    next
      case 2
      hence "takeWhile is_old (C1 @ new_edge (create_edge t s) # C2) =takeWhile is_old C1"
        by(auto simp add: takeWhile_tail) 
      moreover have "takeWhile is_old C1 = C1" 
        using C1C2_in_E by(auto intro!: takeWhile_everything)
      ultimately show ?case
        using cs'subset_E C1C2_in_E cs'_split by simp
    qed
    have flowpath':"network_of_network.flowcycle f' cs'"
      using cs_prop(1) css_ws(4) network_of_network.flowcycle_def by blast
    hence flowcycle_elt:"cs' \<noteq> []" "(fst' (hd cs')) = (snd' (last cs'))"
      "awalk UNIV (fst' (hd cs')) (map make_pair' cs') (snd' (last cs'))" "(\<forall>e\<in>set cs'. 0 < f' e)"
      using cs'_split  flowpath' network_of_network.flowpath_def 
        network_of_network.flowcycle_def network_of_network.multigraph_path_def 
      by (auto simp add: make_pair'_is(1))
    have "awalk UNIV s (map make_pair' (C2@C1)) t"
      using flowcycle_elt(2) flowcycle_elt(3)  props(5) 
      by(auto simp add:awalk_Cons_iff snd'_def  fst'_def  create_edge' cs'_split )   
    moreover hence C2C1_Nil:"C2@C1 \<noteq> []" 
      by (metis awalk_ends list.simps(8) props(5))
    ultimately have awalk_C2C1:"awalk (make_pair' ` set (C2@C1)) s (map make_pair' (C2@C1)) t"      
      by(fastforce intro!: subset_mono_awalk'[of UNIV s "(map make_pair' (C2 @ C1))" t])
    moreover have "(make_pair' ` set (C2@C1)) \<subseteq> make_pair ` \<E>"
      using C1C2_in_E  make_pair' by auto
    moreover have "(map make_pair' (C2@C1)) = map make_pair (map get_old_edge (C2@C1))"
      using C1C2_in_E  make_pair'  by auto
    ultimately have awalk_in_E: "awalk (make_pair ` \<E> ) s (map make_pair (map get_old_edge (C2@C1))) t"
      using subset_mono_awalk[of "(make_pair' ` set (C2 @ C1))" s
          "(map make_pair' (C2 @ C1))" t "make_pair ` \<E>"] by metis
    have "awalk UNIV s (map make_pair ps) t"
      using awalk_in_E ps_is  C2C1_Nil 
      by (fastforce intro!: subset_mono_awalk'[where C=UNIV,simplified])
    moreover have e_E:"e \<in> set ps \<Longrightarrow> e \<in>\<E>" for e 
      using ps_is C1C2_in_E by auto
    moreover have posf:"e \<in> set ps \<Longrightarrow> 0 < f e" for e
    proof(goal_cases)
      case 1
      then obtain d where "d = old_edge e" "d \<in> set (C1@C2)" 
        using ps_is C1C2_in_E by auto
      moreover hence "f' d > 0"
        using flowpath' cs'_split
        by(auto simp add: network_of_network.flowcycle_def network_of_network.flowpath_def )
      ultimately show ?case 
        using e_E[OF 1]
        by(auto simp add: f'_def) 
    qed
    moreover have fstp:"(fst (hd ps)) = s"
      using  hd_map[of ps "make_pair", symmetric, simplified ]
        awalk_hd[OF awalk_in_E[simplified ps_is[symmetric]]]  ps_is C2C1_Nil 
      by (subst sym[OF make_pair''(1)])auto
    moreover have sndp:"(snd (last ps)) = t"
      using  last_map[of ps "make_pair", symmetric, simplified ]
        awalk_last[OF awalk_in_E[simplified ps_is[symmetric]]]  ps_is C2C1_Nil 
      by (subst sym[OF make_pair''(2)])auto  
    ultimately have "flowpath f ps"
      by(simp add: flowpath_def ps_is multigraph_path_def)
    moreover have "set ps \<subseteq> support f"
      using e_E posf by (force simp add: support_def)
    moreover have "distinct ps"
    proof((subst ps_is distinct_map inj_on_def)+, rule conjI, goal_cases)
      case 1
      thus ?case
        using cs'_split cs_prop(1) css_distinct by force
    next
      case 2
      thus ?case
        apply (rule ballI, rule ballI)
        subgoal for x y
          using C1C2_in_E
          by(cases x, all \<open>cases y\<close>) auto
        done
    qed
    ultimately show ?case 
      using fstp sndp by auto
  qed
  moreover have "\<forall>e\<in>\<E>. f e =
           (\<Sum>i<length css'. if e \<in> set (css' ! i) then cws ! i else 0) +
           (\<Sum>i<length pss. if e \<in> set (pss ! i) then pws ! i else 0)"
  proof(rule ballI, goal_cases)
    case (1 e)
    note case1=this
    have "f e =  f' (old_edge e)"
      by(simp add: f'_def)
    also have "... = (\<Sum>i<length css. if (old_edge e) \<in> set (css ! i) then ws ! i else 0)"
      using css_ws(5) 1 by auto
    also have "... = (\<Sum>x\<leftarrow>css_ws_cycles. let (cs, w) = x in if (old_edge e) \<in> set cs then w else 0) +
                      (\<Sum>x\<leftarrow>css_ws_paths. let (cs, w) = x in if (old_edge e) \<in> set cs then w else 0)"
      using sum1 sum2 sum3 sum4 by simp
    also have "... = (\<Sum>i<length css'. if e \<in> set (css' ! i) then cws ! i else 0) +
                     (\<Sum>i<length pss. if e \<in> set (pss ! i) then pws ! i else 0)"
    proof(rule sum_eq_split, goal_cases)
      case 1
      then show ?case
        unfolding lessThan_atLeast0 monoid_add_class.sum_list_sum_nth cws_def 
        apply(simp add: css'_def)
        apply(rule sum_cong, split prod.split, rule allI, rule allI, rule impI)
      proof(goal_cases)
        case (1 i cs cw)
        hence length:"i < length css_ws_cycles" by simp
        hence " (cs, cw) \<in> set css_ws_cycles" 
          using 1(2)[symmetric] 
          by(fastforce intro!: nth_mem)
        hence "cs \<in> set css" and in_E: "set cs \<subseteq> old_edge ` \<E>"
          unfolding css_ws_cycles_def css_ws_def
          by(auto intro: set_zip_leftD)
        show ?case
          using 1 in_E 
          by (auto intro!: image_eqI  simp add: nth_map[OF length] css_ws_cycles_def )
      qed
    next
      case 2
      then show ?case 
        unfolding lessThan_atLeast0 monoid_add_class.sum_list_sum_nth pss_def
        apply (simp add: css'_def length_map)
        apply(rule sum_cong, split prod.split, rule allI, rule allI, rule impI)
      proof(goal_cases)
        case (1 i ps pw)
        hence length:"i < length css_ws_paths" by simp
        hence " (ps, pw) \<in> set css_ws_paths" 
          using 1(2)[symmetric] 
          by(fastforce intro!: nth_mem)
        hence ps_in_css:"ps \<in> set css" and not_in_E: "\<not> set ps \<subseteq> old_edge ` \<E>"
          unfolding css_ws_paths_def css_ws_def
          by(auto intro: set_zip_leftD)
        hence "new_edge (create_edge t s)  \<in> set ps"
          and cs'subset_E:"set ps \<subseteq> insert (new_edge (create_edge t s)) (old_edge ` \<E>)"
          using css_ws(4) unfolding network_of_network.support_def
          by auto
        then obtain C1 C2 where cs'_split:"ps = C1@[new_edge (create_edge t s)]@C2" 
          by (metis in_set_conv_decomp_first single_in_append)
        have C1C2_in_E:"set C1 \<union> set C2 \<subseteq> old_edge ` \<E>"
        proof(rule ccontr)
          assume "\<not> set C1 \<union> set C2 \<subseteq> old_edge ` \<E>"
          moreover have "set C1 \<union> set C2 \<subseteq> old_edge ` \<E>
                  \<union> {new_edge (create_edge t s)}"
            using css_ws(4) cs'_split not_in_E cs'subset_E 
            by(auto simp add: network_of_network.support_def)
          ultimately have "new_edge (create_edge t s) \<in> set C1 \<union> set C2"
            by auto
          hence "\<not> distinct ps" 
            using cs'_split by force
          thus False 
            using  css_distinct
            by (simp add: ps_in_css)
        qed
        have ps_is:"get_s_t_path ps = map get_old_edge (C2@C1)"
          unfolding   get_s_t_path_def cs'_split Let_def
          unfolding   Let_def map_append
        proof(rule arg_cong2[where f = append], all \<open>rule arg_cong[where f= "map get_old_edge"]\<close>, goal_cases)
          case 1
          have "dropWhile is_old (C1 @ ([new_edge (create_edge t s)] @ C2)) = 
             [new_edge (create_edge t s)] @ C2" 
            using C1C2_in_E
            by(auto simp add: dropWhile_append)
          moreover have "dropWhile (\<lambda>e. \<not> is_old e) ([new_edge (create_edge t s)] @ C2) = C2"
            using  C1C2_in_E dropWhile_nothing[of C2 "\<lambda>e. \<not> is_old e"]
            by(force simp add: dropWhile_append ) 
          ultimately show ?case
            using cs'subset_E C1C2_in_E cs'_split by simp
        next
          case 2
          hence "takeWhile is_old (C1 @ new_edge (create_edge t s) # C2) =takeWhile is_old C1"
            by(auto simp add: takeWhile_tail) 
          moreover have "takeWhile is_old C1 = C1" 
            using C1C2_in_E by(auto intro!: takeWhile_everything)
          ultimately show ?case
            using cs'subset_E C1C2_in_E cs'_split by simp
        qed
        have if_cond_same:"(old_edge e \<in> set ps) = (e \<in> set (get_s_t_path ps))"
          using C1C2_in_E
          by(subst ps_is)(force simp add: cs'_split)  
        show ?case 
          using if_cond_same  1 by(auto simp add: pws_def)
      qed
    qed
    finally show ?case  by simp
  qed
  moreover have "is_integral_flow f \<Longrightarrow> \<forall>w\<in>set cws \<union> set pws. \<exists>n. w = real n"
  proof(rule ballI, goal_cases)
    case (1 w)
    have "is_integral ( ex f t)"
      unfolding ex_def using 1(1)
      by (fastforce intro!: integral_sub sum_integral simp add: delta_minus_def delta_plus_finite[simplified  delta_plus_def]  
          delta_plus_def is_integral_def is_integral_flow_def
          delta_minus_finite[simplified delta_minus_def])+
    hence "\<exists> n::nat. ex f t = n"
      using ex_t  zero_le_imp_eq_int by (fastforce simp add: is_integral_def)
    hence "network_of_network.is_integral_flow t s f'"
      using 1(1) 
      by(subst network_of_network.is_integral_flow_def )
        (auto intro: exI[of _ "int _"] 
          simp add:  f'_def is_integral_flow_def)
    hence "\<And> w. w\<in>set ws \<Longrightarrow> \<exists>n. w = real n"
      using css_ws(6) by simp
    moreover have "w \<in> set ws"
      using 1(2) 
      by(auto intro: set_zip_rightD
          simp add: cws_def pws_def css_ws_cycles_def css_ws_paths_def css_ws_def)
    ultimately show ?case by simp
  qed
  ultimately show ?thesis
    by(auto intro!: 1(1)[of css' cws pss pws])
next
  case 2
  show ?thesis 
    using 2(2) conjunct1[OF assms[simplified is_s_t_flow_def]]  sum_pos2[of \<E> _ f, OF finite_E]
    by (force intro!: 2(1)[of Nil Nil Nil Nil] simp add:  Abs_def isuflow_def )
qed
end
subsection \<open>Maximum Flow and Minimum Cut\<close>

text \<open>As we have a notion of $s$-$t$-flows, we should also formalise the Maxflow-Mincut Theorem\<close>

context 
  flow_network_spec
begin
definition "is_s_t_cut s t X= (s \<in> X \<and> t \<in> \<V> - X \<and> X \<subseteq> \<V>)"

lemma is_s_t_cutI: "\<lbrakk>s \<in> X; t \<in> \<V> - X; X \<subseteq> \<V>\<rbrakk> \<Longrightarrow> is_s_t_cut s t X"
  by(auto simp add: is_s_t_cut_def)

lemma is_s_t_cutE: "is_s_t_cut s t X \<Longrightarrow> (\<lbrakk>s \<in> X; t \<in> \<V> - X; X \<subseteq> \<V> \<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: is_s_t_cut_def)

definition "is_min_cut s t X = (is_s_t_cut s t X \<and> (\<forall> Y. is_s_t_cut s t Y \<longrightarrow> Cap X \<le> Cap Y))"

lemma is_min_cutI: "\<lbrakk>is_s_t_cut s t X; (\<And> Y. is_s_t_cut s t Y \<Longrightarrow> Cap X \<le> Cap Y)\<rbrakk> \<Longrightarrow>
                     is_min_cut s t X"
  by(auto simp add: is_min_cut_def)

lemma is_min_cutE: " is_min_cut s t X \<Longrightarrow>
                      (\<lbrakk>is_s_t_cut s t X; (\<And> Y. is_s_t_cut s t Y \<Longrightarrow> Cap X \<le> Cap Y)\<rbrakk> \<Longrightarrow> P)
                    \<Longrightarrow> P"
  by(auto simp add: is_min_cut_def)

definition "is_max_flow s t f = (f is s -- t flow \<and> (\<forall> g. g is s -- t flow \<longrightarrow> ex f t \<ge> ex g t))"

lemma is_max_flowI: "\<lbrakk>f is s -- t flow;
                     (\<And> g. g is s -- t flow \<Longrightarrow> ex f t \<ge> ex g t)\<rbrakk> \<Longrightarrow> is_max_flow s t f"
  by(auto simp add: is_max_flow_def)

lemma is_max_flowE: "\<lbrakk> is_max_flow s t f; (\<lbrakk>f is s -- t flow;
                     (\<And> g. g is s -- t flow \<Longrightarrow> ex f t \<ge> ex g t)\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: is_max_flow_def)

end
context 
  flow_network
begin
context 
  fixes s t::'a
  assumes s_in_V: "s \<in> \<V>"
  assumes t_in_V: "t \<in> \<V>"
  assumes s_neq_t: "s \<noteq> t"
begin

lemma same_Vs_s_t: "dVs (make_pair' ` (old_edge ` \<E> \<union> {new_edge (create_edge t s)})) = \<V>"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  then obtain e where "x = prod.fst e \<or> x = prod.snd e" "e \<in> make_pair' `( old_edge ` \<E> \<union> {new_edge (create_edge t s)})"
    by (meson "1" fst_eqD in_dVsE(1) snd_eqD)
  hence "x \<in> \<V> \<or> x = s \<or> x = t"
    by(auto simp add: create_edge' make_pair' dVs_def)+
  then show ?case 
    using s_in_V t_in_V by blast
next
  case (2 x)
  then obtain e where "prod.fst e = x \<or> prod.snd e = x" "e \<in> make_pair ` \<E>" 
    by(force simp add: dVs_def) 
  then obtain e where "prod.fst (make_pair e) = x \<or> prod.snd (make_pair e) = x" "e \<in> \<E>" by auto
  hence  "prod.fst (make_pair' (old_edge e)) = x \<or> prod.snd (make_pair' (old_edge e)) = x" 
    "old_edge e \<in> old_edge ` \<E> \<union> {new_edge (create_edge t s)}"
    by(auto simp add: make_pair)
  then show ?case
    by(force intro!: exI[of _ "{prod.fst (make_pair' (old_edge e)) , prod.snd (make_pair' (old_edge e))}"]
        simp add: dVs_def )
qed

lemma mincut_exists:
  obtains mincut where  "is_min_cut s t mincut"
proof(goal_cases)
  case 1
  have finite_number_of_cuts_finite:"finite {X . is_s_t_cut s t X}"
    by (auto intro: finite_subset[of _ "Pow \<V>"] simp add: \<V>_finite is_s_t_cut_def)
  have finite_number_of_cuts_pos:"{X . is_s_t_cut s t X} \<noteq> {}"
    using t_in_V  s_in_V  s_neq_t 
    by (auto intro: exI[of _ "\<V> - {t}"] simp add: is_s_t_cut_def)
  define mincap where "mincap = Min {Cap X | X. is_s_t_cut s t  X}"
  have "mincap \<in> {Cap X | X. is_s_t_cut s t X}"
    using finite_imageI[OF finite_number_of_cuts_finite, of Cap] finite_number_of_cuts_pos
    by( auto intro: linorder_class.Min_in simp add: mincap_def image_Collect[symmetric])
  then obtain X where X_prop: "Cap X = mincap" "is_s_t_cut s t X" by auto
  have mincut: "is_min_cut s t X" 
    using X_prop finite_imageI[OF finite_number_of_cuts_finite, of Cap]
    by(auto intro!: Min.coboundedI  simp add: image_Collect[symmetric] is_min_cut_def mincap_def )
  thus ?thesis
    by(auto intro: 1)   
qed

lemma stcut_ex: 
  assumes "f is s--t flow" "is_s_t_cut s t Y" 
  shows "ex f t = (\<Sum>x\<in>Y. ereal (- ex\<^bsub>f\<^esub> x))" 
proof-
  have props:"isuflow f" "ex f s \<le> 0" "s \<in> \<V>" "t \<in> \<V>" "s \<noteq> t" 
    "(\<And>x.  \<lbrakk>x \<in> \<V>; x\<noteq> s; x \<noteq> t \<rbrakk>\<Longrightarrow> ex f x = 0)"
    "s \<in> Y" "t \<notin> Y" "Y \<subseteq> \<V>"
    using assms
    by (auto simp add: is_s_t_flow_def is_s_t_cut_def)
  have a1:"ex f t = - ex f s" 
    using assms(1)  s_t_flow_excess_s_t by blast
  also have a2:"... = (\<Sum>x\<in>Set.insert s Y. ereal (- ex\<^bsub>f\<^esub> x))"
    using Rescut_around_in_V[OF props(3), of f] props \<V>_finite 
    by(subst sum.insert_remove)(fastforce intro!: sum.neutral finite_subset[OF _ \<V>_finite])+
  also have a3:"... = (\<Sum>x\<in>Y. ereal (- ex\<^bsub>f\<^esub> x))"
    by (simp add: insert_absorb props(7))
  finally show ?thesis by simp
qed

lemma ex_less_cut_cap:
  assumes "is_s_t_cut s t X" "is_s_t_flow f s t"
  shows   "ex f t \<le> Cap X"
  using  assms
  by(unfold stcut_ex[OF assms(2,1)])
    (force elim!: is_s_t_flowE is_s_t_cutE 
      intro!: ordered_comm_monoid_add_class.sum_mono  s_t_flow_is_ex_bflow[OF assms(2)]
      order.trans[OF _ flow_less_cut, OF _ s_t_flow_is_ex_bflow[OF assms(2)]]
      simp add: s_t_flow_excess_s_t[OF assms(2)]) 

lemma max_flow_no_augpath:
  assumes   "is_max_flow s t f" 
  shows     "\<not> resreach f s t"
proof-
  have props:"isuflow f" "ex f s \<le> 0" "s \<in> \<V>" "t \<in> \<V>" "s \<noteq> t" 
    "(\<And>x.  \<lbrakk>x \<in> \<V>; x\<noteq> s; x \<noteq> t\<rbrakk> \<Longrightarrow> ex f x = 0)"
    using assms(1)
    by (auto simp add: is_s_t_flow_def is_max_flow_def)
  hence bflow: "isbflow f (\<lambda> v. -ex f v)"
    by(auto simp add: isbflow_def)
  show ?thesis 
  proof(rule notI, goal_cases)
    case 1
    note maxflow=this
    show ?case 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain p where p_prop: "augpath f p" "fstv (hd p) = s" "sndv (last p) = t" "set p \<subseteq> \<EE>"
        "p \<noteq> []"
        using resreach_imp_augpath[of f s t] s_neq_t maxflow
        by(auto simp add: augpath_def prepath_def)
      then obtain q where q_prop: "augpath f q" "fstv (hd q) = s" "sndv (last q) = t" "set q \<subseteq> \<EE>"
        "distinct q" "q \<noteq> []"
        by(cases "distinct p") 
          (fastforce elim!: prepath_drop_cycles[of p "set p"] intro!: Min_antimono simp add: Rcap_def augpath_def)+
      define \<gamma> where "\<gamma> = (if Rcap f (set q) < PInfty then real_of_ereal (Rcap f (set q)) else 1)"
      have gamma_geq_0:"0 \<le> \<gamma>"
        using augpath_def order.order_iff_strict q_prop(1) 
        by(auto intro: real_of_ereal_pos simp add:  \<gamma>_def)
      moreover hence gamma_soft:"ereal \<gamma> \<le> Rcap f (set q)"
        using augpath_def order.order_iff_strict q_prop(1)
        by(auto simp add: ereal_real \<gamma>_def)
      ultimately have bflow':"augment_edges f \<gamma>
                     q is \<lambda>v. if v = s then - ex\<^bsub>f\<^esub> v + \<gamma> else if v = t then - ex\<^bsub>f\<^esub> v - \<gamma> else - ex\<^bsub>f\<^esub> v flow"
        using q_prop(4) q_prop(5)  s_neq_t 
        by(auto intro!: augment_path_validness_b_pres_source_target_distinct[OF bflow _ q_prop(1), simplified q_prop(2,3)])
      moreover have "\<gamma> > 0"
        using gamma_soft gamma_geq_0
        by(auto simp add: augpath_rcap q_prop(1) \<gamma>_def zero_less_real_of_ereal)
      ultimately have "ex\<^bsub>augment_edges f \<gamma> q\<^esub> t > ex\<^bsub>f\<^esub> t"
        using s_neq_t t_in_V by (fastforce simp add: isbflow_def)
      moreover have "augment_edges f \<gamma> q is s--t flow "
        using bflow' \<open>0 < \<gamma>\<close> props(2) props(6) s_in_V s_neq_t t_in_V 
        by (auto simp add: is_s_t_flow_def isbflow_def)
      ultimately show False 
        using maxflow  assms by(auto simp add: is_max_flow_def)
    qed
  qed
qed

theorem max_flow_min_cut:
  assumes "is_max_flow s t f"
  shows "is_min_cut s t X \<Longrightarrow>ex f t = Cap X" (is "?asm2 \<Longrightarrow> ?thesis1")
    and max_flow_Rescut_s_t_cut: "is_s_t_cut s t (Rescut f s)" (is ?thesis2)
proof-
  have props:"isuflow f" "ex f s \<le> 0" "s \<in> \<V>" "t \<in> \<V>" "s \<noteq> t" 
    "(\<And>x.  \<lbrakk>x \<in> \<V>; x\<noteq> s; x \<noteq> t\<rbrakk> \<Longrightarrow> ex f x = 0)"
    using assms(1)
    by (auto simp add: is_s_t_flow_def is_max_flow_def)
  hence bflow: "isbflow f (\<lambda> v. -ex f v)"
    by(auto simp add: isbflow_def)
  have t_not_in_Rescut:"t \<notin> Rescut f s"
    using max_flow_no_augpath[OF assms(1)] s_neq_t by (auto simp add:  Rescut_def)
  show rescut_s_t_cut: "is_s_t_cut s t (Rescut f s)" 
    using Rescut_around_in_V[OF props(3), of f] t_not_in_Rescut props(4)
    by(auto simp add: Rescut_def is_s_t_cut_def)
  assume asm2:?asm2
  from rescut_s_t_cut have a1:"ex f t = (\<Sum>x\<in>Rescut f s. ereal (- ex\<^bsub>f\<^esub> x))"
    using assms(1) by(fastforce intro!: stcut_ex simp add: is_max_flow_def)
  also have a4:"... = Cap (Rescut f s)"
    using Rescut_around_in_V[OF props(3), of f]
    by(force intro!: flow_saturates_res_cut[OF bflow])
  also have a5:"Cap (Rescut f s) \<ge> Cap X"
    using asm2 Rescut_around_in_V Rescut_def s_in_V t_not_in_Rescut 
    by (auto simp add: is_min_cut_def is_s_t_cut_def Rescut_def)
  also have a6:"Cap X \<ge> ex\<^bsub>f\<^esub> t" 
    using assms asm2
    by(subst stcut_ex[of _ X])
      (force intro!: flow_less_cut[OF bflow] simp add: is_max_flow_def is_min_cut_def is_s_t_cut_def)+
  finally show ?thesis1 by simp
qed

lemma sends_min_cut_then_maxflow:
  assumes "is_s_t_flow f s t" "ex f t = Cap X" "is_min_cut s t X"
  shows "is_max_flow s t f"
  using assms  ereal_less_eq(3) ex_less_cut_cap 
  by (fastforce intro!: is_max_flowI elim!:  is_min_cutE)

subsection \<open>Reduction of Maximum Flow to Minimum Cost Flow\<close>

definition "\<E>' = old_edge ` \<E> \<union> {new_edge (create_edge t s)}"

interpretation cost_network_of_network: cost_flow_network where
  fst = fst' and snd = snd'  and create_edge = create_edge'
  and \<E> = \<E>'
  and \<u> = " (\<lambda> e. case e of  old_edge e \<Rightarrow> \<u> e |  _ \<Rightarrow> sum \<u> \<E>)" 
  and \<c> = "(\<lambda> e. case e of old_edge _ \<Rightarrow> 0 | _ \<Rightarrow> -1)"
  using u_non_neg u_sum_pos
  by(auto simp add: cost_flow_network_def \<E>'_def fst'_def snd'_def create_edge' finite_E
      intro!: flow_network.intro multigraph.intro flow_network_axioms.intro
      split: edge_wrapper.split)

lemma same_Vs:"cost_network_of_network.\<V> = \<V>"
proof(rule set_eqI, all \<open>rule\<close>, goal_cases)
  case (1 x)
  then obtain e where "e \<in> \<E>'" "x = prod.fst (make_pair' e) \<or> x = prod.snd (make_pair' e)"
    by (auto simp add: cost_network_of_network.make_pair' dVs_def make_pair'_is(2))
  moreover then obtain d where "(d \<in> \<E> \<and> e = old_edge d) \<or> x = s \<or> x = t"
    unfolding \<E>'_def by(auto simp add: create_edge') 
  ultimately have "(d \<in> \<E> \<and> (x = fst d \<or> x = snd d)) \<or> x = s \<or> x = t"
    by force
  then show ?case using s_in_V t_in_V make_pair'
    by(auto simp add: dVs_def)
next
  case (2 x)
  then obtain e where "(e \<in> \<E> \<and> (prod.fst (make_pair e) = x \<or> prod.snd (make_pair e) = x))"
    by (auto simp add: dVs_def) (metis fst_eqD snd_conv)+
  hence "(old_edge e \<in> old_edge ` \<E> \<and> (prod.fst (make_pair' (old_edge e)) = x \<or> prod.snd (make_pair' (old_edge e)) = x))"
    using make_pair by auto
  then show ?case 
    by (force intro!: exI[of _ "{prod.fst (make_pair' (old_edge e)), prod.snd (make_pair' (old_edge e))}"]
        simp add: dVs_def \<E>'_def make_pair'_is(1))  
qed

lemma t_delta_plus:"cost_network_of_network.delta_plus t 
       = Set.insert (new_edge (create_edge t s)) (old_edge ` delta_plus t)"
  by(subst cost_network_of_network.delta_plus_def )
    (auto simp add:  delta_plus_def  create_edge'(1) \<E>'_def fst'_def )

lemma s_delta_minus:"cost_network_of_network.delta_minus s
       = Set.insert (new_edge (create_edge t s)) (old_edge ` delta_minus s)"
  by(subst cost_network_of_network.delta_minus_def )
    (auto simp add:  delta_minus_def  create_edge'(2) \<E>'_def snd'_def )

lemma delta_plus_same:
  "\<lbrakk>x \<noteq> t; x \<in> \<V>\<rbrakk> \<Longrightarrow> cost_network_of_network.delta_plus x  = (old_edge ` delta_plus x)"
  using s_neq_t create_edge'(1) make_pair' make_pair''(1) 
  by (subst  cost_network_of_network.delta_plus_def)(auto simp add:  delta_plus_def   \<E>'_def fst'_def)

lemma delta_minus_same:
  "\<lbrakk>x \<noteq> s; x \<in> \<V>\<rbrakk> \<Longrightarrow> cost_network_of_network.delta_minus x  = (old_edge ` delta_minus x)"
  using s_neq_t create_edge'(2) make_pair' make_pair''(2) 
  by (subst  cost_network_of_network.delta_minus_def)(auto simp add:  delta_minus_def   \<E>'_def snd'_def)

lemma maxflow_to_mincost_flow_reduction:
  "\<And> f f'. \<lbrakk> f is s--t flow;
         f' = (\<lambda> e. case e of old_edge e \<Rightarrow> f e |  _ \<Rightarrow> ex f t)\<rbrakk> \<Longrightarrow>
         cost_network_of_network.isbflow f' (\<lambda> e. 0) \<and> cost_network_of_network.\<C> f' = - ex f t" 
  (is "\<And> f f'. \<lbrakk>?a1 f f'; ?b1 f f'\<rbrakk> \<Longrightarrow> ?c1 f f'")
  "\<And> f f'. \<lbrakk> cost_network_of_network.isbflow f' (\<lambda> e. 0);
         f = (\<lambda> e. f' (old_edge e))\<rbrakk> \<Longrightarrow>
         f is s--t flow \<and> cost_network_of_network.\<C> f' = - ex f t"
  (is "\<And> f f'. \<lbrakk>?a2 f f'; ?b2 f f'\<rbrakk> \<Longrightarrow> ?c2 f f'")
  "\<And> f f'.\<lbrakk> is_max_flow s t f ;
         f' = (\<lambda> e. case e of old_edge e \<Rightarrow> f e |  _ \<Rightarrow> ex f t)\<rbrakk> \<Longrightarrow>
         cost_network_of_network.is_Opt (\<lambda> e. 0) f'"
  (is "\<And> f f'. \<lbrakk>?a3 f f' ; ?b3 f f' \<rbrakk>\<Longrightarrow> ?c3 f f'")
  "\<And> f f'. \<lbrakk> cost_network_of_network.is_Opt (\<lambda> e. 0) f' ;
         f = (\<lambda> e. f' (old_edge e)) \<rbrakk>\<Longrightarrow>
         is_max_flow s t f"
  (is "\<And> f f'. \<lbrakk>?a4 f f'; ?b4 f f'\<rbrakk> \<Longrightarrow> ?c4 f f'")
proof-
  show goal1:"\<And> f f'. \<lbrakk>?a1 f f'; ?b1 f f'\<rbrakk> \<Longrightarrow> ?c1 f f'"
  proof(goal_cases)
    case (1 f f')
    note f_def = 1(1)[simplified is_s_t_flow_def]
    hence uflow:"isuflow f" by simp
    note f'_def= 1(2)
    have same_ex:"ex\<^bsub>f\<^esub> t = - ex\<^bsub>f\<^esub> s"
      using "1"(1) s_t_flow_excess_s_t by blast
    show ?case
    proof(rule conjI, goal_cases)
      case 1
      have "cost_network_of_network.isuflow f'"
        using ex_less_sum_cap t_in_V uflow f_def same_ex
        by (subst  cost_network_of_network.isuflow_def)(fastforce simp add: isuflow_def \<E>'_def f'_def)
      moreover have "(\<forall>v\<in>cost_network_of_network.\<V>. - cost_network_of_network.ex f' v = 0)"
      proof(subst same_Vs, rule ballI, goal_cases)
        case (1 v)
        have t_delta_plus:"cost_network_of_network.delta_plus t 
       = Set.insert (new_edge (create_edge t s)) (old_edge ` delta_plus t)"
          by(subst cost_network_of_network.delta_plus_def )
            (auto simp add:  delta_plus_def  create_edge'(1) \<E>'_def fst'_def )
        have "- cost_network_of_network.ex f' t = 0"
        proof-
          have "ex\<^bsub>f\<^esub> t + (\<Sum>x\<in>old_edge ` \<delta>\<^sup>+ t. case x of old_edge x \<Rightarrow> f x | new_edge b \<Rightarrow> ex\<^bsub>f\<^esub> t) =
              (\<Sum>x\<in>old_edge ` \<delta>\<^sup>- t. case x of old_edge x \<Rightarrow> f x | new_edge b \<Rightarrow> ex\<^bsub>f\<^esub> t)"        
            by(subst sum_inj_on)(auto intro: forw_subst[OF sum_inj_on] simp add: inj_on_def  ex_def)
          thus ?thesis
            unfolding cost_network_of_network.ex_def t_delta_plus delta_minus_same[OF not_sym[OF s_neq_t] t_in_V]
            by(subst sum.insert)(auto simp add: delta_plus_finite f'_def ) 
        qed
        moreover have "- cost_network_of_network.ex f' s = 0"
        proof-
          have "(\<Sum>x\<in>old_edge ` \<delta>\<^sup>+ s. case x of old_edge x \<Rightarrow> f x | new_edge b \<Rightarrow> ex\<^bsub>f\<^esub> t) =
                 ex\<^bsub>f\<^esub> t + (\<Sum>x\<in>old_edge ` \<delta>\<^sup>- s. case x of old_edge x \<Rightarrow> f x | new_edge b \<Rightarrow> ex\<^bsub>f\<^esub> t) "
            using  same_ex
            by(subst sum_inj_on)(auto intro: forw_subst[OF sum_inj_on] simp add: inj_on_def  ex_def algebra_simps)
          thus ?thesis
            unfolding cost_network_of_network.ex_def s_delta_minus delta_plus_same[OF s_neq_t s_in_V]
            by(subst sum.insert)(auto simp add: delta_minus_finite f'_def) 
        qed
        moreover note one = 1
        moreover have "\<lbrakk>v \<noteq> s; v \<noteq> t\<rbrakk> \<Longrightarrow> cost_network_of_network.ex f' v = 0"
        proof(goal_cases)
          case 1
          have "sum (case_edge_wrapper f (\<lambda>b. ex\<^bsub>f\<^esub> t)) (old_edge ` \<delta>\<^sup>- v) =
                sum (case_edge_wrapper f (\<lambda>b. ex\<^bsub>f\<^esub> t)) (old_edge ` \<delta>\<^sup>+ v)"
            using  "1" f_def one
            by (subst sum_inj_on)(auto intro: forw_subst[OF sum_inj_on] simp add: ex_def inj_on_def)
          then show ?case 
            using 1
            by(auto simp add: delta_minus_same delta_plus_same  one f'_def  cost_network_of_network.ex_def)
        qed
        ultimately show ?case 
          by fastforce
      qed
      ultimately show ?case 
        by(auto simp add: cost_network_of_network.isbflow_def)
    next
      case 2
      show ?case 
        unfolding cost_network_of_network.\<C>_def 
        by(simp add: \<E>'_def, subst sum.insert)
          (auto intro: forw_subst[OF sum_inj_on] simp add: f'_def inj_on_def finite_E)
    qed
  qed
  show goal2:"\<And> f f'. \<lbrakk>?a2 f f'; ?b2 f f'\<rbrakk> \<Longrightarrow> ?c2 f f'"
  proof(goal_cases)
    case (1 f f')
    note 2 = this
    note f'_def = 2(1)[simplified cost_network_of_network.isbflow_def]
    hence uflow:"cost_network_of_network.isuflow f'"  by simp
    note f_def= 2(2)
    show ?case
    proof(rule conjI, goal_cases)
      case 1
      have v_ex:"v \<in> \<V> \<Longrightarrow> (sum f' (cost_network_of_network.delta_minus v) 
              - sum f' (cost_network_of_network.delta_plus v)) = 0" for v
        using f'_def 1
        by(auto simp add: same_Vs  cost_network_of_network.ex_def)
      have "isuflow f"
        using uflow[simplified cost_network_of_network.isuflow_def]
        by(auto simp add: isuflow_def  \<E>'_def f_def)
      moreover have "\<lbrakk>v\<in>\<V>; v \<noteq> s; v \<noteq> t\<rbrakk> \<Longrightarrow> ex f v = 0" for v
      proof(goal_cases)
        case 1
        hence "sum f' (cost_network_of_network.delta_minus v) = sum (f' \<circ> old_edge) (\<delta>\<^sup>- v)"
          "sum f' (cost_network_of_network.delta_plus v) = sum (f' \<circ> old_edge) (\<delta>\<^sup>+ v)"
          by(auto simp add: delta_minus_same  delta_plus_same sum_inj_on inj_on_def)
        thus ?case
          using v_ex[of v] 1 
          by (auto simp add: ex_def f_def)
      qed
      moreover have "ex f s \<le> 0"
      proof-
        have "f' (new_edge (create_edge t s)) + sum f' (old_edge ` \<delta>\<^sup>- s) = sum f' (old_edge ` \<delta>\<^sup>+ s) \<Longrightarrow>
              (\<Sum>e\<in>\<delta>\<^sup>- s. f' (old_edge e)) \<le> (\<Sum>e\<in>\<delta>\<^sup>+ s. f' (old_edge e)) "
          using \<E>'_def cost_network_of_network.isuflow_def uflow 
          by (auto simp add: sum_inj_on inj_on_def)
        moreover have "finite (old_edge ` \<delta>\<^sup>- s)" "new_edge (create_edge t s) \<notin> old_edge ` \<delta>\<^sup>- s"
          by(auto simp add:  delta_minus_finite)
        ultimately show ?thesis
          using v_ex[OF s_in_V] 
          by(auto simp add: ex_def f_def s_delta_minus delta_minus_finite delta_plus_same 
              s_in_V s_neq_t)
      qed
      moreover have "ex f t \<ge> 0"
      proof-
        have "sum f' (old_edge ` \<delta>\<^sup>- t) = f' (new_edge (create_edge t s)) + sum f' (old_edge ` \<delta>\<^sup>+ t) \<Longrightarrow>
             (\<Sum>e\<in>\<delta>\<^sup>+ t. f' (old_edge e)) \<le> (\<Sum>e\<in>\<delta>\<^sup>- t. f' (old_edge e))"
          using \<E>'_def cost_network_of_network.isuflow_def uflow 
          by (auto simp add: sum_inj_on inj_on_def)
        moreover have "finite (old_edge ` \<delta>\<^sup>+ t)" "new_edge (create_edge t s) \<notin> old_edge ` \<delta>\<^sup>+ t"
          by(auto simp add: delta_plus_finite)
        ultimately show ?thesis
          using v_ex[OF t_in_V] 
          by(auto simp add: ex_def f_def t_delta_plus delta_plus_finite delta_minus_same t_in_V not_sym[OF s_neq_t])
      qed
      ultimately show ?case 
        using is_s_t_flow_def s_in_V s_neq_t t_in_V by blast
    next
      case 2
      have helper:"finite (old_edge ` \<delta>\<^sup>+ t)" "new_edge (create_edge t s) \<notin> old_edge ` \<delta>\<^sup>+ t"
        "finite (old_edge ` \<E>)" "new_edge (create_edge t s) \<notin> old_edge ` \<E>"
        by(auto simp add: delta_plus_finite finite_E) 
      hence ex_t_is:"- cost_network_of_network.ex f' t =
       (\<Sum>e\<in>\<delta>\<^sup>+ t. f' (old_edge e)) + f' (new_edge (create_edge t s))
     - (\<Sum>e\<in>\<delta>\<^sup>- t. f' (old_edge e))" 
        by(auto simp add: cost_network_of_network.ex_def t_delta_plus
            delta_minus_same[OF not_sym[OF s_neq_t] t_in_V] 
            sum_inj_on inj_on_def delta_plus_finite) 
      show ?case
        unfolding cost_network_of_network.\<C>_def 
        apply(simp add: \<E>'_def)
        using ex_t_is helper 
        by(auto intro: forw_subst[OF sum_inj_on] 
            simp add: ex_def f_def inj_on_def finite_E f'_def same_Vs t_in_V)
    qed
  qed
  show  "\<And> f f'. \<lbrakk>?a3 f f'; ?b3 f f'\<rbrakk> \<Longrightarrow> ?c3 f f'"
  proof(goal_cases)
    case (1 f f')
    show ?case
      using 1(1) goal1[OF _ 1(2)] goal2
      by(simp add: cost_network_of_network.is_Opt_def is_max_flow_def)
  qed
  show  "\<And> f f'. \<lbrakk>?a4 f f'; ?b4 f f'\<rbrakk> \<Longrightarrow> ?c4 f f'"
  proof(goal_cases)
    case (1 f f')
    show ?case
      using 1(1) goal2[OF _ 1(2)] goal1
      by(force simp add: cost_network_of_network.is_Opt_def is_max_flow_def)
  qed
qed

lemma no_maxflow_resreach_standard_proof:
  assumes "is_s_t_flow f s t " "\<not> resreach f s t"
  shows   "is_max_flow s t f"
proof-
  have props:"isuflow f"  "s \<in> \<V>" "t \<in> \<V>" 
    using assms(1)
    by (auto simp add: is_s_t_flow_def is_max_flow_def)
  hence bflow: "isbflow f (\<lambda> v. -ex f v)"
    by(auto simp add: isbflow_def)
  have t_not_in_Rescut:"t \<notin> Rescut f s" 
    using assms(2) s_neq_t by(auto simp add: Rescut_def)
  have rescut_s_t_cut: "is_s_t_cut s t (Rescut f s)"  
    using Rescut_around_in_V[OF props(2), of f] t_not_in_Rescut props(3)
    by(auto simp add: Rescut_def is_s_t_cut_def)
  obtain X where X_exists: "is_min_cut s t X"
    using mincut_exists by auto
  from rescut_s_t_cut have a1:"ex f t = (\<Sum>x\<in>Rescut f s. ereal (- ex\<^bsub>f\<^esub> x))"
    using assms(1) by(fastforce intro!: stcut_ex simp add: is_max_flow_def)
  also have a4:"... = Cap (Rescut f s)"
    using Rescut_around_in_V[OF props(2), of f]
    by(force intro!: flow_saturates_res_cut[OF bflow])
  also have a5:"Cap (Rescut f s) \<ge> Cap X"
    using X_exists Rescut_around_in_V Rescut_def s_in_V t_not_in_Rescut 
    by (auto simp add: is_min_cut_def is_s_t_cut_def Rescut_def)
  also have a6:"Cap X \<ge> ex\<^bsub>f\<^esub> t" 
    using assms X_exists
    by(subst stcut_ex[of _ X])
      (force intro!: flow_less_cut[OF bflow] simp add: is_max_flow_def is_min_cut_def is_s_t_cut_def)+
  finally have "Cap X = ereal ex\<^bsub>f\<^esub> t"
    by auto
  thus ?thesis 
    using X_exists assms(1) 
    by(auto intro!: sends_min_cut_then_maxflow)
qed

lemma no_maxflow_resreach:
  assumes "is_s_t_flow f s t " "\<not> resreach f s t"
  shows   "is_max_flow s t f"
proof-
  note s_t_flow = assms(1)
  define f' where "f' = (\<lambda>e. case e of old_edge e \<Rightarrow> f e | new_edge b \<Rightarrow> ex\<^bsub>f\<^esub> t)"
  show ?thesis
  proof(rule maxflow_to_mincost_flow_reduction(4)[of f' f])
    show "f = (\<lambda>e. f' (old_edge e))" by(simp add: f'_def)
    have bflow_f':"cost_network_of_network.isbflow f' (\<lambda>e. 0)" 
      using s_t_flow_excess_s_t[OF s_t_flow, symmetric] cost_network_of_network.isbflow_def
        maxflow_to_mincost_flow_reduction(1)[OF s_t_flow refl, 
          simplified cost_network_of_network.isbflow_def]
        same_Vs_s_t t_in_V  create_edge'  dVs_def 
      by(auto simp add:  \<E>'_def cost_network_of_network.isuflow_def  f'_def 
          intro: fst_E_V s_in_V snd_E_V  is_s_t_flowE[OF s_t_flow] isuflowE ex_less_sum_cap
          split: edge_wrapper.split)
    show "cost_network_of_network.is_Opt (\<lambda>e. 0) f'"
    proof(subst cost_network_of_network.is_opt_iff_no_augcycle[OF bflow_f'],
        rule ccontr, goal_cases)
      case 1
      then obtain C where C_prop:"cost_network_of_network.augcycle f' C" by auto
      hence C_unfolded:
        "cost_network_of_network.\<CC> C < 0"
        "cost_network_of_network.augpath f' C"
        "cost_network_of_network.fstv (hd C) = cost_network_of_network.sndv (last C)"
        "distinct C" "set C \<subseteq> cost_network_of_network.\<EE>"
        by(auto simp add: cost_network_of_network.augcycle_def)
      have F_new_edge_in_C:"F (new_edge (create_edge t s)) \<in> set C"
      proof(rule ccontr, goal_cases)
        case 1
        hence "cost_network_of_network.\<CC> C \<ge> 0"
          using C_unfolded(5)cost_network_of_network.\<EE>_def 
          by(auto intro!:  ordered_comm_monoid_add_class.sum_nonneg 
              split: edge_wrapper.split 
              simp add: \<E>'_def cost_network_of_network.\<CC>_def)
        thus ?case
          using C_unfolded(1) by auto
      qed
      have B_new_edge_not_in_C:"B (new_edge (create_edge t s)) \<notin> set C"
      proof(rule ccontr, goal_cases)
        case 1
        note 1 = 1[simplified not_not]
        have helper: "finite (set C - {F (new_edge (create_edge t s))})" 
          "B (new_edge (create_edge t s)) \<in> set C - {F (new_edge (create_edge t s))}"
          "\<forall>x\<in>set C - {F (new_edge (create_edge t s))} - {B (new_edge (create_edge t s))}.
                   cost_network_of_network.\<cc> x = 0"
          using 1 C_unfolded(5) cost_network_of_network.\<EE>_def 
          by(auto split: edge_wrapper.split simp add:  \<E>'_def)
        have "cost_network_of_network.\<CC> C = 0" 
          using 1 C_unfolded(5)  
          by(auto split: edge_wrapper.split 
              simp add: cost_network_of_network.\<CC>_def cost_network_of_network.\<EE>_def
              comm_monoid_add_class.sum.remove[OF _ F_new_edge_in_C, simplified] 
              comm_monoid_add_class.sum.remove[OF helper(1,2)] \<E>'_def 
              comm_monoid_add_class.sum.neutral[OF  helper(3)])
        thus False 
          using C_unfolded(1) by linarith 
      qed
      obtain C1 C2 where C_split:"C = C1@[F (new_edge (create_edge t s))] @ C2"
        using split_list F_new_edge_in_C by fastforce
      hence C_cases1:"C2 \<noteq> [] \<Longrightarrow> cost_network_of_network.augpath f' (C2)" 
        "C1 \<noteq> [] \<Longrightarrow> cost_network_of_network.augpath f' (C1)"  
        using C_unfolded(2) cost_network_of_network.augpath_split2
          cost_network_of_network.augpath_split1 by blast+
      from C_split have C_cases2:
        "C2 \<noteq> [] \<Longrightarrow> cost_network_of_network.fstv (hd C2) = s" 
        "C1 \<noteq> [] \<Longrightarrow> cost_network_of_network.sndv (last C1) = t"
        using cost_network_of_network.augpath_split3[of f' "C1@[F (new_edge (create_edge t s))]" C2, simplified]
        using C_unfolded(2)  C_split  cost_network_of_network.augpath_split3[of f' "C1" "[F (new_edge (create_edge t s))]@C2", simplified]
        by(auto simp add: snd'_def create_edge' fst'_def)
      note C_cases = C_cases1 C_cases2
      have C_or:"C1 \<noteq> [] \<or> C2 \<noteq> []"
        using C_split C_unfolded(3) s_neq_t 
        by(auto simp add:  fst'_def snd'_def create_edge' cost_network_of_network.vs_to_vertex_pair_pres(1,2)
            flow_network_spec.fstv.simps(1)flow_network_spec.sndv.simps(1))
      have C2C1_augphat_f':
        "cost_network_of_network.augpath f' (C2@C1)"
        "cost_network_of_network.fstv (hd (C2@C1)) = s"
        "cost_network_of_network.sndv (last (C2@C1)) = t"
      proof(goal_cases)
        case 1
        thus ?case
          using C_split C_unfolded(3) cost_network_of_network.augpath_app C_cases C_or
          by(cases C1, all \<open>cases C2\<close>) force+
      next
        case 2
        thus ?case
          using C_or C_cases(3)  C_split C_unfolded(3) cost_network_of_network.vs_to_vertex_pair_pres(2)
            create_edge'(2)
          by(cases C1, all \<open>cases C2\<close>) (auto simp add: make_pair'_is(1))
      next
        case 3
        thus ?case
          using C_or  cost_network_of_network.vs_to_vertex_pair_pres(1) create_edge'(1)
            C_split C_unfolded(3) cost_network_of_network.vs_to_vertex_pair_pres(1) 
            C_cases(4) 
          by (cases C1, all \<open>cases C2\<close>)(auto simp add: make_pair'_is(1))
      qed
      have "F (new_edge (create_edge t s)) \<notin> set C1" 
        "F (new_edge (create_edge t s)) \<notin> set C2" 
        "B (new_edge (create_edge t s)) \<notin> set C1" 
        "B (new_edge (create_edge t s)) \<notin> set C2" 
        using C_split C_unfolded (4)  B_new_edge_not_in_C by auto
      hence C1_C2_in:"set C1 \<subseteq> F ` old_edge ` \<E> 
                      \<union> B ` old_edge ` \<E>" 
        "set C2 \<subseteq> F ` old_edge ` \<E> 
                      \<union> B ` old_edge ` \<E>" 
        using  C_unfolded(5) cost_network_of_network.\<EE>_def 
        by(auto simp add: \<E>'_def C_split ) 
      define p where "p = (map (\<lambda> e. case e of F e \<Rightarrow> F (get_old_edge e)
                             | B e \<Rightarrow> B (get_old_edge e)))
                        (C2@C1)"
      have big_cong_C1C2:"e \<in> set C1 \<union> set C2 \<Longrightarrow>( to_vertex_pair o (case_Redge
                  (\<lambda>e. F (cost_network_of_network.get_old_edge e))
                  (\<lambda>e. B (cost_network_of_network.get_old_edge e)))) e
           = cost_network_of_network.to_vertex_pair e" 
        "e \<in> set (C2@C1) \<Longrightarrow> (fstv o
                  (case_Redge
                  (\<lambda>e. F (cost_network_of_network.get_old_edge e))
                  (\<lambda>e. B (cost_network_of_network.get_old_edge e)))) e
                  = cost_network_of_network.fstv e"
        "e \<in> set (C2@C1) \<Longrightarrow> (sndv o
                  (case_Redge
                  (\<lambda>e. F (cost_network_of_network.get_old_edge e))
                  (\<lambda>e. B (cost_network_of_network.get_old_edge e)))) e
                  = cost_network_of_network.sndv e"
        "e \<in> set (C2@C1) \<Longrightarrow> cost_network_of_network.rcap f' e = rcap f
             (case_Redge (\<lambda>e. F (cost_network_of_network.get_old_edge e))
                               (\<lambda>e. B (cost_network_of_network.get_old_edge e)) e)" 
        for e      
        using C1_C2_in make_pair  
        by(auto split: edge_wrapper.split Redge.split
            simp add: cost_network_of_network.make_pair''  fst_of_wrapped_edges[symmetric]
            f'_def make_pair'_is(1))     
      have "prepath p"
        using C2C1_augphat_f'(1)[ simplified cost_network_of_network.augpath_def]
        unfolding prepath_def p_def cost_network_of_network.prepath_def map_map
      proof(subst list.map_cong0[OF big_cong_C1C2(1)], goal_cases)
        case 2
        thus ?case
        proof(subst list.map_sel(1) last_map, goal_cases)
          case 2
          note one = this
          thus ?case
          proof(subst list.map_sel(1) last_map, goal_cases)
            case 2
            note one = this
            show ?case
            proof(subst big_cong_C1C2(2)[of "hd (C2@C1)", simplified o_apply], goal_cases)
              case 2
              thus ?case
                using one 
                by(subst big_cong_C1C2(3)[of "last (C2@C1)", simplified o_apply])
                  (force intro!: last_in_set)+
            next
              case 1
              thus ?case
                using one
                by(intro hd_in_set )  auto
            qed 
          qed force
        qed force
      qed force
      moreover have "0 < Rcap f (set p)"     
        using C2C1_augphat_f'(1) big_cong_C1C2(4) 
        by (auto simp add: Rcap_def cost_network_of_network.Rcap_def p_def cost_network_of_network.augpath_def)
      ultimately have "augpath f p"
        by(auto simp add: augpath_def) 
      moreover have "fstv (hd p) = s"
        using C_or  big_cong_C1C2(2)[OF hd_in_set, symmetric]
        by (cases "C2@C1")(auto simp add: C2C1_augphat_f'(2)[symmetric] p_def)
      moreover have "sndv (last p) = t"
        using C_or  big_cong_C1C2(3)[OF last_in_set, symmetric]
        by (cases "C2@C1" rule: rev_cases)(auto simp add: C2C1_augphat_f'(3)[symmetric] p_def)
      moreover have "set p \<subseteq> \<EE>"
        using C1_C2_in
        by(auto simp add:  p_def  \<EE>_def)
      ultimately have "resreach f s t"
        by(auto intro!: augpath_imp_resreach)
      thus False 
        using assms(2) by simp 
    qed
  qed
qed

lemma maxflow_iff_not_resreach:
  assumes "is_s_t_flow f s t " 
  shows   "is_max_flow s t f \<longleftrightarrow> \<not> resreach f s t"
  using assms max_flow_no_augpath no_maxflow_resreach by blast

lemma Rescut_mincut_maxflow:
  assumes "is_s_t_flow f s t"
    "is_min_cut s t (Rescut f s)"
  shows "is_max_flow s t f" 
  using assms(2) maxflow_iff_not_resreach[OF assms(1)]
  by(auto simp add: is_min_cut_def is_s_t_cut_def Rescut_def)

lemma Rescut_of_maxflow_is_mincut:
  assumes "is_max_flow s t f"
  shows "is_min_cut s t (Rescut f s)"
proof-
  have stflow: "is_s_t_flow f s t" 
    using assms by(auto elim: is_max_flowE)
  obtain X where mincutX:"is_min_cut s t X"
    using mincut_exists by auto
  have s_in_Rescut_f_s: "s \<in> Rescut f s"
    using assms is_s_t_cutE max_flow_Rescut_s_t_cut by blast
  have "(\<Sum>x\<in>Rescut f s. ereal (if x = s then ex\<^bsub>f\<^esub> t else if x = t then - ex\<^bsub>f\<^esub> t else 0)) =
    ereal (ex\<^bsub>f\<^esub> t + 0)"
    using max_flow_Rescut_s_t_cut[OF assms] 
    by(subst insert_Diff[symmetric, OF s_in_Rescut_f_s])
      (auto intro: is_min_cutE[OF mincutX]
        elim!:  is_s_t_cutE[of s t "(Rescut f s)"] 
        simp add:  comm_monoid_add_class.sum.neutral 
        comm_monoid_add_class.sum.insert_remove[OF finite_Rescut[OF s_in_V]])
  hence "Cap (Rescut f s) = ereal (ex\<^bsub>f\<^esub> t + 0)"
    using max_flow_Rescut_s_t_cut[OF assms]    
    by(subst flow_saturates_res_cut[symmetric, OF _ Rescut_around_in_V[OF s_in_V]])
      (auto intro: s_t_flow_is_ex_bflow[OF stflow])
  then show ?thesis 
    using max_flow_Rescut_s_t_cut[OF assms]  max_flow_min_cut(1)[OF assms mincutX]
    by(auto intro: is_min_cutE[OF mincutX] simp add:  is_min_cut_def)
qed

theorem maxflow_iff_Rescut_is_mincut:
  assumes "is_s_t_flow f s t" 
  shows   "is_max_flow s t f \<longleftrightarrow> is_min_cut s t (Rescut f s)"
  using Rescut_mincut_maxflow Rescut_of_maxflow_is_mincut assms by blast

end
end
end