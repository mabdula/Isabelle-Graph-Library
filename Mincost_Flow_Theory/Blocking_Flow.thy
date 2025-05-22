theory Blocking_Flow 
  imports STFlow Directed_Set_Graphs.Dist
begin

(*TODO: Later, move to appropriate places elsewhere.*)

definition "abstract_real_map mp x = (case mp x of None \<Rightarrow> 0 | Some y \<Rightarrow> y)"

lemma abstract_real_map_empty: "abstract_real_map (\<lambda> _ . None) = (\<lambda> _ . 0)"
  by(auto simp add: abstract_real_map_def)

lemma abstract_real_map_some: "mp x = Some y \<Longrightarrow> abstract_real_map mp x = y"
  by(auto simp add: abstract_real_map_def)

lemma abstract_real_map_none: "mp x = None \<Longrightarrow> abstract_real_map mp x = 0"
  by(auto simp add: abstract_real_map_def)

definition "unsaturated_path_simple G (u::_ \<Rightarrow> 'a::order) f s p t = (vwalk_bet G s p t
                                     \<and> (\<forall> e \<in> set (edges_of_vwalk p). f e < u e))"

lemma unsaturated_path_simple_mono: "unsaturated_path_simple G u f s p t  \<Longrightarrow>
     (\<And> e. e \<in> set (edges_of_vwalk p) \<Longrightarrow> f' e \<le> f e) \<Longrightarrow> unsaturated_path_simple G u f' s p t "
  by(auto intro: preorder_class.order.strict_trans1[of "f' _" "f _" "u _"] 
      simp add: unsaturated_path_simple_def)

context multigraph_spec
begin
definition "multigraph_distance u v = distance (make_pair ` \<E>) u v"

definition "multigraph_distance_set S v = distance_set (make_pair ` \<E>) S v"

definition "multi_level_graph S = {e | e. e \<in> \<E> \<and> multigraph_distance_set S (fst e) + 1 =
                                                   multigraph_distance_set S (snd e)}"

end

context multigraph
begin
lemma multi_level_graph_is: "multi_level_graph S = 
  {e | e. e \<in> \<E> \<and> make_pair e \<in> level_graph  (make_pair ` \<E>) S}"
  by (auto simp add: multi_level_graph_def multigraph_distance_set_def level_graph_def 
      split_beta  make_pair'' make_pair')

lemma multigraph_path_multigraph_distance:
  assumes  "multigraph_path p" "p \<noteq> []" "fst (hd p) = s" "snd (last p) = t" "set p \<subseteq> \<E>"
  shows "multigraph_distance s t \<le> length p"
proof-
  have length_verts:"length p = length (awalk_verts s (map make_pair p)) - 1"
    apply(subst awalk_verts_length[of UNIV _ _  t])
    using assms(1,2,3,4) by(auto elim: multigraph_pathE)
  show ?thesis
    apply(unfold multigraph_distance_def length_verts)
    apply(rule vwalk_bet_dist)
    using assms subset_mono_awalk'[of UNIV s "map make_pair p" t  "make_pair ` \<E>"]
    by(auto intro: awalk_imp_vwalk elim: multigraph_pathE)
qed  
end

context flow_network_spec
begin

definition "is_blocking_flow s t f = (is_s_t_flow f s t \<and> 
                                     (\<nexists> p. multigraph_path p \<and> p \<noteq> [] \<and>
                                           fst (hd p) = s \<and> snd (last p) = t \<and> set p \<subseteq> \<E> \<and>
                                           (\<forall> e \<in> set p. f e < \<u> e)))"

interpretation residual_multigraph_spec: 
  multigraph_spec  "{e | e. e \<in> \<EE> \<and> rcap f e > 0}"  fstv sndv to_vertex_pair 
  "\<lambda> u v. F (create_edge u v)" for f
  done

definition "residual_distance f u v =
            residual_multigraph_spec.multigraph_distance f u v"

definition "residual_level_graph f s = residual_multigraph_spec.multi_level_graph f {s}"

interpretation residual_level_flow: flow_network_spec fstv sndv to_vertex_pair
  "\<lambda> u v. F (create_edge u v)" "residual_level_graph f s" 
  "rcap f" 
  for f s
  done

definition "residual_level_blocking_flow f s t g= 
       residual_level_flow.is_blocking_flow f s s t g"

text \<open>Augmentation by flow in residual graph\<close>

definition "augment_residual_flow f rf = (\<lambda> e. f e + rf (F e) - rf (B e))"
end
context flow_network
begin
interpretation residual_network_spec: 
  flow_network_spec fstv sndv to_vertex_pair 
  "\<lambda> u v. F (create_edge u v)" \<EE> "rcap f"for f
  done

lemma same_V: "residual_network_spec.\<V> = \<V>" 
  using  make_pair'
  by(auto simp add: \<EE>_def dVs_def image_Un Setcompr_eq_image image_comp)

lemma augment_s_t_flow_by_residual_s_t_flow:
  assumes "is_s_t_flow f s t"  "residual_network_spec.is_s_t_flow f rf s t "
  shows   "is_s_t_flow (augment_residual_flow f rf) s t"
  unfolding augment_residual_flow_def
proof(rule is_s_t_flowI)
  show "s \<in> \<V>"  "t \<in> \<V>"  "s \<noteq> t"
    using assms(1) by(auto elim: is_s_t_flowE)
  show "isuflow (\<lambda>e. f e + rf (residual_network_spec.F e) - rf (residual_network_spec.B e))"
  proof(rule isuflowI)
    fix e
    assume asm: "e \<in> \<E>"
    have e_props:"ereal (f e) \<le> \<u> e" "0 \<le> f e"
      "ereal (rf (F e)) \<le> \<u> e - f e" "0 \<le>  (rf (F e))"
      "(rf (B e)) \<le> f e" "0 \<le> (rf (B e))"
           apply(all \<open>rule isuflowE[of f, OF is_s_t_flowE[OF assms(1)], simplified]\<close>)
           apply(all \<open>rule  residual_network_spec.isuflowE[of f rf, OF 
                  residual_network_spec.is_s_t_flowE[OF assms(2)], simplified]\<close>)
      using asm
      by(force simp add: \<EE>_def)+
    show "ereal (f e + rf (F e) - rf (B e)) \<le> \<u> e" "0 \<le> f e + rf (F e) - rf (B e)"
      using e_props 
      by (auto simp add: ereal_le_le ereal_umst zero_ereal_def)
  qed
  have many_finites:
    "finite {e. (\<exists>d. e = fa d \<and> d \<in> \<E>) \<and> fb e = (x::'v)}" for fa fb x
    by (simp add: finite_E)
  have some_disjoint:
    "{e. (\<exists>d. e = F d \<and> d \<in> \<E>) \<and> fa e = x} \<inter>
     {e. (\<exists>d. e = B d \<and> d \<in> \<E>) \<and> fb e = y} =
      {}" for fa fb x y by blast
  have sum_set_simps:
    "{e. (\<exists>d. e = F d \<and> d \<in> \<E>) \<and> sndv e = s} = F` {e. e \<in> \<E> \<and> snd e = s}" 
    "{e. (\<exists>d. e = B d \<and> d \<in> \<E>) \<and> fstv e = s} = B` {e. e \<in> \<E> \<and> snd e = s}" 
    "{e. (\<exists>d. e = F d \<and> d \<in> \<E>) \<and> fstv e = s} = F` {e. e \<in> \<E> \<and> fst e = s}" 
    "{e. (\<exists>d. e = B d \<and> d \<in> \<E>) \<and> sndv e = s} = B` {e. e \<in> \<E> \<and> fst e = s}"  for s      
    by auto
  note help1 = comm_monoid_add_class.sum.union_disjoint[OF
                                       many_finites  many_finites some_disjoint]
  show "ex\<^bsub>\<lambda>e. f e + rf (residual_network_spec.F e) - rf (residual_network_spec.B e)\<^esub> s \<le> 0"
  proof-
    have "ex\<^bsub>f\<^esub> s \<le> 0" "residual_network_spec.ex rf s \<le> 0" 
      by(auto intro: is_s_t_flowE[OF assms(1)] residual_network_spec.is_s_t_flowE[OF assms(2)])
    then show ?thesis
      using help1[of rf fstv s fstv ]  help1[of rf  sndv s sndv]
      by(auto intro: ordered_ab_semigroup_add_class.add_mono
          simp add: conj_disj_distribR Collect_disj_eq
          comm_monoid_add_class.sum.distrib[of "\<lambda> e. f e" "\<lambda> e.  rf (F e) - rf (B e)", simplified]
          comm_monoid_add_class.sum.distrib[of "\<lambda> e. rf (F e)" "\<lambda> e. - rf (B e)", simplified]
          sum_set_simps sum_negf sum_inj_on[OF F_and_B_inj_on(1)] 
          sum_inj_on[OF F_and_B_inj_on(2)] finite_E
          ex_def residual_network_spec.ex_def
          residual_network_spec.delta_minus_def residual_network_spec.delta_plus_def
          delta_plus_def delta_minus_def \<EE>_def flow_network_spec.ex_def 
          multigraph_spec.delta_minus_def multigraph_spec.delta_plus_def
          semigroup_add_class.add.assoc[of "_::real" _ "- _", simplified minus_real_def[symmetric]])
  qed
  note helper3=comm_monoid_add_class.sum.union_disjoint
                              [OF many_finites many_finites some_disjoint]
  show "ex\<^bsub>\<lambda>e. f e + rf (residual_network_spec.F e) - rf (residual_network_spec.B e)\<^esub> x = 0" 
    if asm: "x \<in> \<V>" "x \<noteq> s" "x \<noteq> t" for x
  proof(goal_cases)
    case 1
    have "ex\<^bsub>f\<^esub> x = 0" "residual_network_spec.ex rf x = 0"
      using asm 
      by(auto intro: is_s_t_flowE[OF assms(1)] residual_network_spec.is_s_t_flowE[OF assms(2)] 
          simp add: same_V)
    then show ?case 
      by(auto simp add: ex_def delta_plus_def residual_network_spec.ex_def delta_minus_def \<EE>_def
          residual_network_spec.delta_minus_def residual_network_spec.delta_plus_def 
          flow_network_spec.ex_def multigraph_spec.delta_minus_def conj_disj_distribR 
          Collect_disj_eq multigraph_spec.delta_plus_def 
          comm_monoid_add_class.sum.distrib[of "\<lambda> e. f e" "\<lambda> e.  rf (F e) - rf (B e)", simplified]
          comm_monoid_add_class.sum.distrib[of "\<lambda> e. rf (F e)" "\<lambda> e. - rf (B e)", simplified]
          semigroup_add_class.add.assoc[of "_::real" _ "- _", simplified minus_real_def[symmetric]]
          sum_set_simps[of x]  sum_inj_on[OF F_and_B_inj_on(1)] sum_inj_on[OF F_and_B_inj_on(2)] 
          sum_negf helper3[of rf sndv x sndv x, simplified sum_set_simps]
          helper3[of rf fstv x fstv x, simplified sum_set_simps])
  qed
qed

lemma residual_level_graph_in_E: "residual_level_graph f s \<subseteq> \<EE>"
  by(auto simp add: residual_level_graph_def multigraph_spec.multi_level_graph_def)

lemma residual_level_graph_in_E_pos: "residual_level_graph f s \<subseteq> {e| e. e \<in> \<EE> \<and> rcap f e > 0}"
  by(auto simp add: residual_level_graph_def multigraph_spec.multi_level_graph_def)

lemma in_E_level_craph_cases: 
  "e \<in> \<EE> \<Longrightarrow> (e \<in> residual_level_graph f s \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> P e) \<Longrightarrow>
  (e \<notin> residual_level_graph f s\<Longrightarrow> e \<in> \<EE>  \<Longrightarrow> P e) \<Longrightarrow> P e"
  by auto

lemma augpath_length_less_res_distance:
  assumes "augpath f p" "p \<noteq> []" "fstv (hd p) = s" "sndv (last p) = x" "set p \<subseteq> \<EE>"
  shows   "residual_distance f s x \<le> length p"
proof-
  from assms have p_props:
    "awalk (to_vertex_pair ` \<EE>) s (map to_vertex_pair p) x" 
    "0 < Rcap f (set p)" "p \<noteq> []"  "set p \<subseteq> \<EE>"
    by(force elim!: augpathE prepathE intro: subset_mono_awalk')+
  hence p_pos:"set p \<subseteq> {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}"
    by (simp add: rcap_extr_non_zero subset_iff)
  have "awalk (to_vertex_pair `  {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}) s (map to_vertex_pair p) x"  
    using subset_mono_awalk'[OF p_props(1)] p_pos p_props(3) by auto
  hence vwalk_found: "vwalk_bet (to_vertex_pair `  {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}) s
                              (awalk_verts s (map to_vertex_pair p)) x" 
    by(auto intro!: awalk_imp_vwalk)
  show ?thesis 
    using vwalk_bet_dist[OF vwalk_found,  simplified]
    by(auto simp add: multigraph_spec.multigraph_distance_def residual_distance_def
                      awalk_verts_length[OF p_props(1)])
qed

lemma augpath_in_lg_length_res_distance:
  assumes "augpath f p" "p \<noteq> []" "fstv (hd p) = s" "sndv (last p) = x" 
          "set p \<subseteq> residual_level_graph f s"
  shows   "residual_distance f s x  = length p"
proof-
  from assms have p_props:
    "awalk (to_vertex_pair ` residual_level_graph f s) s (map to_vertex_pair p) x" 
    "0 < Rcap f (set p)" "p \<noteq> []"  "set p \<subseteq> residual_level_graph f s"
    using residual_level_graph_in_E_pos
    by(force elim!: augpathE prepathE intro: subset_mono_awalk')+
  have "awalk (to_vertex_pair ` residual_level_graph f s) s (map to_vertex_pair p) x"  
    using subset_mono_awalk'[OF p_props(1)] p_props p_props(3) by auto
  hence vwalk_found: "vwalk_bet (to_vertex_pair ` residual_level_graph f s) s
                              (awalk_verts s (map to_vertex_pair p)) x" 
    by(auto intro!: awalk_imp_vwalk)
  hence "length (awalk_verts s (map to_vertex_pair p)) = 
        distance_set (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}) {s} x + 1"
    by(force intro!: walk_in_level_graph_distance(1) 
        intro: back_subst[of "\<lambda> E. vwalk_bet E s (awalk_verts s (map to_vertex_pair p)) x"
          " {to_vertex_pair uu|uu . uu \<in> \<EE> \<and> _ uu}"]
        simp add: residual_level_graph_def multigraph_spec.multi_level_graph_def
        multigraph_spec.multigraph_distance_set_def  level_graph_def
        image_Collect vs_to_vertex_pair_pres split_pairs)
  thus ?thesis 
    by(auto simp add: awalk_verts_length[OF p_props(1)]
        multigraph_spec.multigraph_distance_def  multigraph_spec.multigraph_distance_set_def
        distance_set_def residual_distance_def plus_1_eSuc(2))
qed

lemma resreach_residual_dist_less_infty:
  assumes "resreach f s x"
  shows   "residual_distance f s x < \<infinity>"
proof-
  from assms obtain p where p_props:
    "awalk (to_vertex_pair ` \<EE>) s (map to_vertex_pair p) x" 
    "0 < Rcap f (set p)" "p \<noteq> []"  "set p \<subseteq> \<EE>"            
    by(auto simp add: resreach_def)
  moreover hence "fstv (hd p) = s"  "sndv (last p) = x" 
    using awalk_fst_last[of "map to_vertex_pair p"] 
    by (auto simp add: last_map list.map_sel(1) vs_to_vertex_pair_pres)
  moreover hence "augpath f p"
    using p_props by(auto intro!: augpathI prepathI intro:subset_mono_awalk')
  ultimately show ?thesis
    by(intro preorder_class.order.strict_trans1[OF 
          augpath_length_less_res_distance[of f p s x]])
      auto
qed

lemma resdist_less_Pinfty_augpath_same_length:
  assumes "residual_distance f s x < \<infinity>"  "s \<noteq> x"
  obtains p where "augpath f p" "fstv (hd p) = s" "sndv (last p) = x" 
                  "length p = residual_distance f s x" "set p \<subseteq> residual_level_graph f s"
proof(goal_cases)
  case 1
  obtain vp where vp:"residual_distance f s x =
                   length vp -1" "vwalk_bet (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}) s vp x"
    using assms(1) dist_set_less_infty_get_path[of _ "{s}" x]
    by(force simp add: multigraph_spec.multigraph_distance_set_def
                       residual_distance_def distance_set_def
                        multigraph_spec.multigraph_distance_def) 
  hence awalk:"awalk (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}) s (edges_of_vwalk vp) x"
    by(auto intro: vwalk_imp_awalk)
  moreover then obtain p where p_prop:" map to_vertex_pair p = edges_of_vwalk vp"
    "set p \<subseteq> {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}" 
    using list_in_image_map[of "edges_of_vwalk vp" to_vertex_pair "{uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}"]
    by blast
  hence  aaa:"edges_of_vwalk vp = map to_vertex_pair p" by auto
  moreover hence p_vp:"s = prod.fst (hd (edges_of_vwalk vp))" 
    "x = prod.snd (last (edges_of_vwalk vp))" "vp \<noteq> []" "p \<noteq> []"
    using assms(2) awalk  vp(2)
    by((subst awalk_hd awalk_last; auto elim: vwalk_betE) | auto)+
  ultimately have augpath: "augpath f p" "fstv (hd p) = s" "sndv (last p) = x"
    using p_prop(2)
    by(auto intro!: augpathI prepathI 
        intro: subset_mono_awalk[of "to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}"] Rcap_strictI'
        simp add: vs_to_vertex_pair_pres last_map list.map_sel(1))
  moreover have "length p = residual_distance f s x"
    using p_prop(1) vp(1) 
    by(auto simp add:  edges_of_vwalk_length length_map[of to_vertex_pair p, symmetric])
  moreover have "set p \<subseteq> residual_level_graph f s"
  proof-
    have path_in_lg:"vwalk_bet (level_graph (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}) {s}) s vp x"
      using  vp(1)  p_prop(1) edges_of_vwalk_length[of vp] p_vp(4) not_less_eq_eq 
      by (force intro: dist_walk_in_level_graph[OF vp(2), of "{s}", simplified] 
          simp add: multigraph_spec.multigraph_distance_set_def
                    residual_distance_def distance_set_def multigraph_spec.multigraph_distance_def)
    show ?thesis
      using walk_in_level_graph_distance(2)[OF path_in_lg, simplified] p_prop(2) to_vertex_pair_fst_snd
      by(auto simp add: level_graph_def residual_level_graph_def  multigraph_spec.multi_level_graph_def
          aaa multigraph_spec.multigraph_distance_set_def image_def)
  qed
  ultimately show ?thesis
    by(auto intro!: 1)
qed

lemma resdist_triangle_single_edge:
  assumes "rcap f e >0 " "e \<in> \<EE>" "fstv e = x" "sndv e = y"
  shows "residual_distance f s y \<le> residual_distance f s x + 1"
  using assms
  by(auto intro!: distance_neighbourhood' 
      simp add:  neighbourhood_def  multigraph_spec.multigraph_distance_def 
                 residual_distance_def to_vertex_pair_fst_snd)

lemma not_both_directions_in_level_graph:
  assumes "(F e) \<in> residual_level_graph f s" 
    "(B e) \<in> residual_level_graph f s" 
    "resreach f s (fst e) \<or> resreach f s (snd e) \<or> fst e = s \<or> snd e = s"
  shows False
proof-
  have dist_less_pinfty:"residual_distance f s (snd e) < \<infinity>"
  proof(rule disjE[OF assms(3)], goal_cases)
    case 1
    hence "residual_distance f s (fst e) < \<infinity>"
      using resreach_residual_dist_less_infty by blast
    then obtain i where "enat i + 1 =
         distance (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}) s (snd e)"
      using assms(1) 
      by(auto simp add: multigraph_spec.multigraph_distance_set_def residual_level_graph_def
          multigraph_spec.multi_level_graph_def residual_distance_def
          multigraph_spec.multigraph_distance_def distance_set_def) 
    thus ?thesis 
      using assms(1) 
      by(auto simp add: plus_1_eSuc(2) residual_distance_def multigraph_spec.multigraph_distance_def
          intro!: exI[of _ "i+1"])
  next
    case 2
    thus ?thesis 
    proof(cases rule: disjE[OF 2])
      case 1
      then show ?thesis 
        using resreach_residual_dist_less_infty by blast
    next
      case 2
      hence s_in_lg:"s  \<in> dVs {to_vertex_pair uu |uu. uu \<in> \<EE> \<and> 0 < \<uu>\<^bsub>f\<^esub>uu}"
        using assms(1,2)  make_pair'[symmetric]
        by(force intro!: exI[of _ "{fst e, snd e}"] 
            simp add: image_Collect dVs_def residual_level_graph_def
            multigraph_spec.multi_level_graph_def)+
      have fst_snd_e_less_1:"residual_distance f (fst e) (snd e) \<le> 1"
        using assms(1,2) make_pair 
        by(auto intro!: distance_neighbourhood exI[of _ "F e"]
            simp add: neighbourhood_def residual_level_graph_def distance_set_def
            multigraph_spec.multi_level_graph_def image_Collect
             multigraph_spec.multigraph_distance_def residual_distance_def)
      moreover hence  "fst e = s \<Longrightarrow>
                      residual_distance f (snd e) (fst e) \<le> 2" 
        using assms(1,2) make_pair 
        by(auto simp add: multigraph_spec.multigraph_distance_set_def distance_set_def
            neighbourhood_def residual_level_graph_def 
            multigraph_spec.multi_level_graph_def image_Collect
            multigraph_spec.multigraph_distance_def residual_distance_def
            dest: sym[of "distance _ _ _ + 1" "distance _ _ _ "] ) 
      moreover have "snd e = s \<Longrightarrow>
                      residual_distance f (snd e) (snd e) = 0" 
        using s_in_lg assms(1,2) make_pair fst_snd_e_less_1
        by(auto simp add: neighbourhood_def residual_level_graph_def residual_distance_def
            multigraph_spec.multi_level_graph_def image_Collect multigraph_spec.multigraph_distance_def
            intro!: distance_0I)
      ultimately show ?thesis
        using 2 enat_ile enat_0 by fastforce
    qed
  qed
  have dist_plus:"residual_distance f s (snd e) = residual_distance f s (fst e) + 1"
                 "residual_distance f s (fst e) = residual_distance f s (snd e) + 1"   
    using assms
    by(auto simp add: residual_level_graph_def multigraph_spec.multi_level_graph_def
              residual_distance_def distance_set_def
              multigraph_spec.multigraph_distance_set_def multigraph_spec.multigraph_distance_def)
  hence "residual_distance f s (snd e) = residual_distance f s (snd e) + 2" by simp
  then show ?thesis 
    using dist_less_pinfty by simp
qed

lemma residual_level_blocking_flow_to_residual_flow:
  assumes "residual_level_blocking_flow f s t rf"
    "\<And> e. e \<notin> residual_level_graph f s \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> rf e = 0"
    "isuflow f"
  shows "residual_network_spec.is_s_t_flow f rf s t"
proof-
  have rf_s_t_flow: "flow_network_spec.is_s_t_flow fstv sndv to_vertex_pair
                      (residual_level_graph f s) (rcap f) rf s t"
    using assms(1) by(auto simp add: flow_network_spec.is_blocking_flow_def
        flow_network_spec.residual_level_blocking_flow_def)
  let ?lg =  "to_vertex_pair `
              multigraph_spec.multi_level_graph {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}
                 fstv sndv to_vertex_pair {s}"
  show?thesis
  proof(rule residual_network_spec.is_s_t_flowI)

    show "s \<in> residual_network_spec.\<V>"  "t \<in> residual_network_spec.\<V>"  "s \<noteq> t"
      using rf_s_t_flow 
      by(auto intro: set_mp[OF dVs_subset, of ?lg, simplified multigraph_spec.multi_level_graph_def]
          simp add: flow_network_spec.is_s_t_flow_def residual_level_graph_def multigraph_spec.multi_level_graph_def)
    show "residual_network_spec.isuflow f rf" 
    proof(rule residual_network_spec.isuflowI)
      fix e
      assume asm: "e \<in> \<EE>"
      have uflow: "flow_network_spec.isuflow (residual_level_graph f s) (rcap f) rf"
        using rf_s_t_flow by(auto simp add: flow_network_spec.is_s_t_flow_def)
      show "ereal (rf e) \<le> \<uu>\<^bsub>f\<^esub>e" "0 \<le> rf e"
        using uflow assms(2)[of e] is_flow_rcap_non_neg[OF assms(3) asm]
        by(all \<open>cases "e \<in> residual_level_graph f s"\<close>)
          (auto simp add: residual_level_graph_def multigraph_spec.multi_level_graph_def
            flow_network_spec.isuflow_def isuflow_def asm zero_ereal_def) 
    qed
    have same_excess:
      "flow_network_spec.ex fstv sndv (residual_level_graph f s) rf x = 
           residual_network_spec.ex rf x" for x
    proof-
      have subsets:
        "multigraph_spec.delta_minus (residual_level_graph f s) sndv x
          \<subseteq> residual_network_spec.delta_minus x"
        "multigraph_spec.delta_plus (residual_level_graph f s) fstv x
          \<subseteq> residual_network_spec.delta_plus x"
        by(auto simp add: multigraph_spec.delta_minus_def residual_network_spec.delta_minus_def
            multigraph_spec.delta_plus_def residual_network_spec.delta_plus_def
            residual_level_graph_def multigraph_spec.multi_level_graph_def)
      have finites: "finite (residual_network_spec.delta_minus x)"
        "finite (residual_network_spec.delta_plus x)"
        by (auto simp add: finite_\<EE> residual_network_spec.delta_minus_def 
            residual_network_spec.delta_plus_def)
      have zero_other:
        "\<forall>i\<in>residual_network_spec.delta_minus x -
            multigraph_spec.delta_minus (residual_level_graph f s) sndv x. rf i = 0"
        "\<forall>i\<in>residual_network_spec.delta_plus x -
            multigraph_spec.delta_plus (residual_level_graph f s) fstv x. rf i = 0" 
        using assms(2)
        by(auto simp add:  multigraph_spec.delta_minus_def  multigraph_spec.delta_plus_def)
      show ?thesis
        by(auto simp add: residual_network_spec.ex_def flow_network_spec.ex_def
            comm_monoid_add_class.sum.mono_neutral_left[OF finites(1) subsets(1) zero_other(1)]
            comm_monoid_add_class.sum.mono_neutral_left[OF finites(2) subsets(2) zero_other(2)])
    qed
    show "residual_network_spec.ex rf s \<le> 0"
      using same_excess rf_s_t_flow
      by(auto simp add: flow_network_spec.is_s_t_flow_def)
    show "x \<in> residual_network_spec.\<V> \<Longrightarrow> x \<noteq> s \<Longrightarrow> x \<noteq> t
            \<Longrightarrow> residual_network_spec.ex rf x = 0" for x
    proof(goal_cases)
      case 1
      show ?case 
      proof(cases "x \<in> dVs (to_vertex_pair ` residual_level_graph f s)")
        case True
        then show ?thesis 
          using same_excess rf_s_t_flow 1
          by(auto simp add: flow_network_spec.is_s_t_flow_def)
      next
        case False
        hence all_zero:"\<forall>x\<in>residual_network_spec.delta_minus x. rf x = 0"
          "\<forall>x\<in>residual_network_spec.delta_plus x. rf x = 0"
          by(auto intro!: assms(2) 
              dest: sndv_in_verts fstv_in_verts
              simp add: residual_network_spec.delta_minus_def residual_network_spec.delta_plus_def)
        show ?thesis 
          by(auto simp add: residual_network_spec.ex_def
              comm_monoid_add_class.sum.neutral[OF all_zero(1)]
              comm_monoid_add_class.sum.neutral[OF all_zero(2)])
      qed
    qed
  qed
qed

lemma blocking_flow_augment_dist_increase:
  assumes  "residual_level_blocking_flow f s t rf"  "is_s_t_flow f s t"
           "\<And> e. e \<notin> residual_level_graph f s \<Longrightarrow> e \<in> \<EE> \<Longrightarrow> rf e = 0"
           "resreach f s t"
    and f'_def: "f' = augment_residual_flow f rf"
  shows "residual_distance f' s t > residual_distance f s t"
proof-
  have is_s_t_flow_unfolded:
    "isuflow f" "s \<in> \<V>"  "t \<in> \<V>"  "s \<noteq> t" "ex\<^bsub>f\<^esub> s \<le> 0"
    "\<And> x. x\<in>\<V> \<Longrightarrow> x \<noteq> s \<Longrightarrow> x \<noteq> t \<Longrightarrow> ex\<^bsub>f\<^esub> x = 0"
    using assms(2)  by(auto elim: is_s_t_flowE)
  hence is_s_t_flow_f':"is_s_t_flow f' s t "
    by(auto intro!: augment_s_t_flow_by_residual_s_t_flow assms
        residual_level_blocking_flow_to_residual_flow 
        simp add: f'_def)
  have residual_flow: "residual_network_spec.is_s_t_flow f rf s t"
    by(auto intro!: residual_level_blocking_flow_to_residual_flow[OF
          assms(1,3) is_s_t_flow_unfolded(1)])
  have new_augpath_in_pos_res_edges_or_level_graph:
    "augpath f' p \<Longrightarrow> set p \<subseteq> \<EE> \<Longrightarrow> set p \<subseteq> { e | e . e \<in> \<EE> \<and> rcap f e > 0} 
        \<union> erev ` (residual_level_graph f s)" for p
  proof(rule, goal_cases)
    case (1 e)
    note one = this
    hence rcapef': "rcap f' e > 0" 
      by(auto intro: augpath_rcap_pos_strict')
    have rcapfegeq0:"rcap f e \<ge> 0" "e \<in> \<EE>"
      using assms(2)  one(2,3)
      by(auto intro: is_flow_rcap_non_neg simp add: is_s_t_flow_def)
    have "rcap f e = 0 \<Longrightarrow> rcap f' e > 0 \<Longrightarrow> e \<in> erev ` (residual_level_graph f s)"
    proof(cases e, goal_cases)
      case (1 ee)
      have a1:"f' ee < \<u> ee" 
        using "1" rcapef' ereal_diff_nonpos 
        by (auto  simp add: linorder_not_le[symmetric])
      have a2:"f ee = \<u> ee"
        using "1"(1,3)   u_non_neg   
        by(cases "\<u> ee") auto
      hence a3:"rf (F ee) = 0"
        using residual_flow rcapfegeq0(2) "1"(1,3) 
        by(auto simp add: residual_network_spec.is_s_t_flow_def residual_network_spec.isuflow_def 1)
      hence "rf (B ee) > 0"
        using a2 a1 by(cases "\<u> ee")(auto simp add: augment_residual_flow_def f'_def )    
      then show ?thesis
        using  assms(3) erev_\<EE>  rcapfegeq0(2)
        by(force simp add: 1(3) intro!: image_eqI[of "B ee"])
    next
      case (2 ee)
      have a1:"f' ee > 0" 
        using 2 rcapef' ereal_diff_nonpos 
        by (auto  simp add: linorder_not_le[symmetric])
      have a2:"f ee = 0"
        using 2(1,3)   u_non_neg   
        by(cases "\<u> ee") auto
      hence a3:"rf (B ee) = 0"
        using residual_flow rcapfegeq0(2) 2(1,3) 
        by(auto simp add: residual_network_spec.is_s_t_flow_def residual_network_spec.isuflow_def 1)
      hence "rf (F ee) > 0"
        using a2 a1 by(cases "\<u> ee")(auto simp add: augment_residual_flow_def f'_def )    
      then show ?thesis
        using  assms(3) erev_\<EE>  rcapfegeq0(2)
        by(force simp add: 2(3) intro!: image_eqI[of "B ee"])
    qed
    thus ?case 
      using rcapef' rcapfegeq0(1,2) by force
  qed
  have reach_before_pos_after_in_lg_unsatured_before:
    "rf e < rcap f e"
    if asms: "rcap f' e > 0" "e \<in> residual_level_graph f s" 
      "resreach f s (fstv e) \<or> fstv e = s"for e
  proof(cases e)
    case (F ee)
    hence "f' ee < \<u> ee" 
      using asms(1) by(cases "\<u> ee") auto
    hence "f ee + rf (F ee) - rf (B ee) < \<u> ee"
      by(auto simp add: f'_def augment_residual_flow_def)
    hence "f ee + rf (F ee) < \<u> ee" 
      using asms(2,3)  flow_network_spec.erev_\<EE>[of e] residual_level_graph_in_E[of f s] 
      by (subst (asm) assms(3)[of "B ee"])
        (auto intro!: not_both_directions_in_level_graph simp add: F )
    then show ?thesis 
      using  u_non_neg
      by(cases "\<u> ee") (auto simp add: F)
  next
    case (B ee)
    hence "f' ee > 0" 
      using asms(1) by(cases "\<u> ee") auto
    hence "f ee + rf (F ee) - rf (B ee) > 0"
      by(auto simp add: f'_def augment_residual_flow_def)
    hence "f ee - rf (B ee) > 0" 
      using asms(2,3)  flow_network_spec.erev_\<EE>[of e] residual_level_graph_in_E[of f s] 
      by (subst (asm) assms(3)[of "F ee"])
        (auto intro!: not_both_directions_in_level_graph simp add: B )
    then show ?thesis 
      using  u_non_neg
      by(cases "\<u> ee") (auto simp add: B)
  qed
  have augpath_f'_has_edge_not_in_level:
    "\<exists> e \<in> set p. e \<notin> residual_level_graph f s"
    if asms: "augpath f' p" "set p \<subseteq> \<EE>" "fstv (hd p) = s"  "sndv (last p) = t" for p
  proof(rule ccontr, goal_cases)
    case 1
    hence p_in_lg:"set p \<subseteq> residual_level_graph f s" 
      by auto
    hence pos_ufe:"e \<in> set p \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e" for e
      by(auto simp add: residual_level_graph_def multigraph_spec.multi_level_graph_def)
    hence augpathpf:"augpath f p" 
      using asms(1) by(fastforce intro!: augpath_from_prepath  simp add: augpath_def)
    have pos_uf'e:"e \<in> set p \<Longrightarrow> 0 < \<uu>\<^bsub>f'\<^esub>e" for e
      using augpath_rcap_pos_strict that(1) by blast
    moreover have "e \<in> set p \<Longrightarrow> ereal (rf e) < \<uu>\<^bsub>f\<^esub>e" for e
      using augpath_rcap_pos_strict[OF asms(1)]  p_in_lg  
        e_in_augpath_resreach_fstv_e[OF augpathpf asms(2,3)]
      by(auto intro!: reach_before_pos_after_in_lg_unsatured_before)
    moreover have "flow_network_spec.is_s_t_flow fstv sndv to_vertex_pair
                       (residual_level_graph f s) (rcap f) rf s t"
      using assms(1)
      by(auto simp add: flow_network_spec.is_blocking_flow_def
          flow_network_spec.residual_level_blocking_flow_def)
    ultimately have "\<not> residual_level_blocking_flow f s t rf"
      using p_in_lg asms(1,3,4) 
      by(auto simp add: residual_level_blocking_flow_def prepath_def
          flow_network_spec.is_blocking_flow_def augpath_def 
          residual_network_spec.multigraph_path_def
          intro!: exI[of _ p])
    thus False 
      using assms(1) by simp
  qed
  have find_shorter_path_in_lg:
    "\<exists> p'. prepath p'\<and> fstv (hd p') = s \<and> sndv (last p') = t 
            \<and> length p' + n \<le> length p \<and> set p' \<subseteq> residual_level_graph f s \<and> p' \<noteq> []"
    if asms:  "prepath p" "fstv (hd p) = s" "sndv (last p) = t"
      "n = length (filter (\<lambda> e. e \<notin> residual_level_graph f s) p)"
      "set p \<subseteq> {e | e. e \<in> \<EE> \<and> rcap f e > 0 } \<union> erev ` (residual_level_graph f s)"
    for p n
    using asms
  proof(induction n arbitrary: p rule: less_induct)
    case (less n)
    show ?case
    proof(cases n)
      case 0
      then show ?thesis
        using residual_level_graph_in_E_pos less(2-)
        by(auto intro!: exI[of _ p] Rcap_strictI' elim: prepathE simp add: filter_empty_conv)
    next
      case (Suc nn)
      hence "0 < length (filter (\<lambda>e. e \<notin> residual_level_graph f s) p)"
        using less by auto
      then obtain a where "a \<in> set p" "a \<notin> residual_level_graph f s"
        using zero_less_iff_neq_zero by force
      then obtain p1 p2 e where p_split:
        "p = p1@[e]@p2" "\<forall> d \<in> set p1. d \<in> residual_level_graph f s" "e \<notin> residual_level_graph f s"
        using extract_first_x[of a p "\<lambda> e. e \<notin> residual_level_graph f s"] by auto 
      show ?thesis
      proof(cases "sndv e = s")
        case True
        hence "p2 \<noteq> []" 
          using less is_s_t_flow_unfolded(4) p_split(1) by force
        hence augpath: "prepath p2" "fstv (hd p2) = s" "sndv (last p2) = t"
          "set p2 \<subseteq> {e |e. e \<in> \<EE> \<and> 0 < \<uu>\<^bsub>f\<^esub>e} \<union> erev ` residual_level_graph f s"
          using prepath_split2[of "p1@[e]" p2] prepath_split3[of  "p1@[e]" p2] less
          by (auto simp add: True p_split(1))
        have n_geq_number_p2:"nn = length (filter (\<lambda>e. e \<notin> residual_level_graph f s) p2)"
          using less(5) Suc by(auto simp add: p_split less(5))
        then obtain p' where "prepath p'" "fstv (hd p') = s" "sndv (last p') = t" 
          "length p' + length (filter (\<lambda>e. e \<notin> residual_level_graph f s) p2) \<le> length p2"
          "set p' \<subseteq> residual_level_graph f s" " p' \<noteq> []"
          using less(1)[ OF _ augpath(1-3) refl] augpath(4)  Suc less p_split(1) by auto
        thus ?thesis 
          by(auto intro!: exI[of _ p'] simp add: Suc[simplified  n_geq_number_p2] p_split) 
      next
        case False
        note sndv_e_not_s = this
        show ?thesis
        proof(cases "e \<in>  {e \<in> \<EE>. rcap f e > 0}")
          case True
          hence augpath_prefix:
            "augpath f (p1@[e])" "fstv (hd (p1@[e])) = s" "sndv (last (p1@[e])) = sndv e"
            "set (p1@[e]) \<subseteq> \<EE>"
            using Suc less(2-) p_split(1,2) residual_level_graph_in_E_pos[of f s]
            by(auto intro!: augpathI prepath_split1[of "p1@[e]" p2] Rcap_strictI'
                elim!: augpathE 
                simp add: hd_append)
          hence resreach: "resreach f s (sndv e)"
            using augpath_imp_resreach by force
          note dist_s_sndv_e_less_pinfty = resreach_residual_dist_less_infty[OF resreach]
          moreover have e_triangle:"residual_distance f s (sndv e) \<le> residual_distance f s (fstv e) + 1"
            using True by(auto intro!: resdist_triangle_single_edge[OF _ _ refl refl, of f e s])
          ultimately have snd_strict_closer:
            "residual_distance f s (sndv e) < residual_distance f s (fstv e) + 1"
            using p_split(3) True
            by(auto simp add: residual_level_graph_def multigraph_spec.multi_level_graph_def
                              residual_distance_def multigraph_spec.multigraph_distance_def
                              multigraph_spec.multigraph_distance_set_def distance_set_def)
          have fstv_e_sndv_e_in_pos_dVs:
            "fstv e \<in> dVs (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu})"
            "sndv e \<in> dVs (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu})"
            using True by(auto simp add: vs_to_vertex_pair_pres intro!: dVsI')
          have lengthp1e_geq_dist:"residual_distance f s (fstv e) = length (p1)"
          proof(cases p1)
            case Nil
            then show ?thesis 
              using augpath_prefix(2) distance_0[of s ] fstv_e_sndv_e_in_pos_dVs(1)
              by (auto simp add:  zero_enat_def residual_distance_def  multigraph_spec.multigraph_distance_def)
          next
            case (Cons a list)
            show ?thesis 
              using augpath_split1[OF augpath_prefix(1)] augpath_prefix(2,3) 
                prepath_split3[of p1 "[e]"] Cons p_split(2) 
              by (intro augpath_in_lg_length_res_distance)
                 (auto intro: augpathE[OF  augpath_prefix(1)])
          qed
          obtain p1' where p1':"augpath f p1'" "fstv (hd p1') = s" "sndv (last p1') = sndv e"
            "length p1' = residual_distance f s (sndv e)" "set p1' \<subseteq> residual_level_graph f s" 
            using sndv_e_not_s 
            by(auto intro: resdist_less_Pinfty_augpath_same_length[OF dist_s_sndv_e_less_pinfty])
          have lengthp1'_better:"length (p1') \<le> length (p1)"
            using snd_strict_closer 
            by(auto intro!: enat_less_plus_1_leq 
                simp add: enat_ord_code(1)[symmetric] lengthp1e_geq_dist[symmetric] p1'(4) )
          hence length_new_path_less:"length (p1'@p2) < length p"
            by(auto simp add: p_split(1))
          have "prepath (p1' @ p2)" 
            using prepath_split2[of "p1@[e]" p2] p_split(1) less(2) p1'(3)
              prepath_split3[of "p1@[e]" p2]
            by (cases p2)(auto intro: augpathE[OF p1'(1)] intro!: prepath_append)
          moreover have "fstv (hd (p1' @ p2)) = s" 
            using hd_append2 p1'(1,2) 
            by (auto elim!: augpathE prepathE)
          moreover have "sndv (last (p1' @ p2)) = t"
            using less(4) p1'(3) p_split(1) by fastforce 
          moreover have n_geq_number_p2:"nn = length (filter (\<lambda>e. e \<notin> residual_level_graph f s) (p1' @ p2))"
            using less(5) Suc p1'(5)
            by(auto simp add: p_split subset_code(1))
          moreover have "set (p1' @ p2) \<subseteq> {e |e. e \<in> \<EE> \<and> 0 < \<uu>\<^bsub>f\<^esub>e} \<union> erev ` residual_level_graph f s"
            using less.prems(5) p1'(5) p_split(1) residual_level_graph_in_E_pos by auto
          ultimately obtain p' where p'_prop:
            "prepath p'" "fstv (hd p') = s" "sndv (last p') = t" 
            "length p' + nn \<le> length (p1' @ p2)"  "set p' \<subseteq> residual_level_graph f s" " p' \<noteq> []"
            using  less(1)[of nn "p1'@p2"] Suc by auto
          then show ?thesis 
            using Suc  lengthp1'_better
            by(auto intro!: exI[of _ p'] simp add: p_split)
        next
          case False
          note false = this
          hence e_in_reverse_lg:
            "e \<in> erev ` residual_level_graph f s" "erev e \<in> residual_level_graph f s"
            using less.prems(5) p_split(1) erve_erve_id by auto
          hence "erev e \<in> {e \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>e}"
            using residual_level_graph_in_E_pos by auto
          hence fstv_e_sndv_e_in_pos_dVs:
            "fstv e \<in> dVs (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu})"
            "sndv e \<in> dVs (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu})"
            by(auto intro!: dVsI'[of "to_vertex_pair (erev e)",
                  simplified to_vertex_pair_erev_swap_arg fst_swap snd_swap]
                simp add:  vs_to_vertex_pair_pres to_vertex_pair_erev_swap_arg[symmetric])
          have lengthp1e_geq_dist:"residual_distance f s (fstv e) = length (p1)"
          proof(cases p1)
            case Nil
            moreover hence "fstv e = s" 
              using less.prems(2) p_split(1) by auto
            ultimately show ?thesis 
              using distance_0[of s] fstv_e_sndv_e_in_pos_dVs(1)
              by (auto simp add: zero_enat_def residual_distance_def multigraph_spec.multigraph_distance_def)
          next
            case (Cons a list)
            show ?thesis 
              using less.prems(1,2,3) local.Cons p_split(1)  p_split(2) residual_level_graph_in_E_pos
                prepath_cases prepath_split3[of "p1" "[e]@p2", simplified] 
              by (intro augpath_in_lg_length_res_distance)
                (fastforce intro!: augpathI  Rcap_strictI intro: prepath_split1)+
          qed
          have dist_second_one_less:
            "residual_distance f s (fstv e) = residual_distance f s (sndv e) + 1"
            using e_in_reverse_lg(2)
            by(auto simp add: multigraph_spec.multigraph_distance_set_def residual_level_graph_def
                multigraph_spec.multi_level_graph_def  vs_erev(1,2)
                residual_distance_def multigraph_spec.multigraph_distance_def distance_set_def)
          hence dist_s_fstv_e_less_pinfty:  "residual_distance f s (sndv e) < \<infinity>"
            using enat_ord_simps(4) lengthp1e_geq_dist by fastforce
          obtain p1' where p1':
            "augpath f p1'" "fstv (hd p1') = s" "sndv (last p1') = sndv e"
            "length p1' =  residual_distance f s (sndv e)"
            "set p1' \<subseteq> residual_level_graph f s" 
            using sndv_e_not_s
            by(auto intro: resdist_less_Pinfty_augpath_same_length[OF dist_s_fstv_e_less_pinfty])
          have less_length: "length p1' +1 = length p1"
            using lengthp1e_geq_dist 
            by (auto simp add: dist_second_one_less p1'(4)[symmetric]  eSuc_plus_1[symmetric] enat.inject[symmetric])
          hence lengthp1'_better:"length (p1') < length (p1@[e])"
            by simp
          hence length_new_path_less:"length (p1'@p2) < length p"
            by(auto simp add: p_split(1))
          have "p1' \<noteq> []" "p1 \<noteq> []"
            using less_length  p1'(1) by(auto elim!: augpathE prepathE)
          hence "prepath (p1' @ p2)"
            using prepath_split2[of "p1@[e]" p2]less(2)
            using prepath_split3[of "p1@[e]" "p2", simplified] less.prems(1)
            by (cases p2) 
               (auto intro: augpathE[OF p1'(1)] intro!: prepath_append 
                  simp add: p1'(3) p_split(1))
          moreover have "fstv (hd (p1' @ p2)) = s" 
            using hd_append2 p1'(1,2) 
            by (auto elim!: augpathE prepathE)
          moreover have "sndv (last (p1' @ p2)) = t"
            using less(4) p1'(3) p_split(1) by fastforce 
          moreover have n_geq_number_p2:"nn = length (filter (\<lambda>e. e \<notin> residual_level_graph f s) (p1' @ p2))"
            using less(5) Suc p1'(5)
            by(auto simp add: p_split subset_code(1))
          moreover have "set (p1' @ p2) \<subseteq> {e |e. e \<in> \<EE> \<and> 0 < \<uu>\<^bsub>f\<^esub>e} \<union> erev ` residual_level_graph f s"
            using less.prems(5) p1'(5) p_split(1) residual_level_graph_in_E_pos by auto
          ultimately obtain p' where p'_prop:
            "prepath p'" "fstv (hd p') = s" "sndv (last p') = t" 
            "length p' + nn \<le> length (p1' @ p2)"  "set p' \<subseteq> residual_level_graph f s" "p' \<noteq> []"
            using  less(1)[of nn "p1'@p2"] Suc by auto
          then show ?thesis 
            using Suc  lengthp1'_better
            by(auto intro!: exI[of _ p'] simp add: p_split)
        qed
      qed
    qed
  qed

  note dist_s_t_not_infty = resreach_residual_dist_less_infty[OF assms(4)]

  show ?thesis
  proof(cases "residual_distance f' s t")
    case infinity
    then show ?thesis 
      using dist_s_t_not_infty 
      by(auto simp add: residual_distance_def)
  next
    case (enat dist)
    obtain p where p_prop:"augpath f' p" "fstv (hd p) = s" "sndv (last p) = t"
      "(length p) =residual_distance f' s t" "set p \<subseteq> residual_level_graph f' s" "set p \<subseteq> \<EE>"
      using enat is_s_t_flow_unfolded(4) residual_level_graph_in_E[of f' s]
      by (auto intro:resdist_less_Pinfty_augpath_same_length[of f' s t])
    then obtain e where e_prop: "e\<in>set p" "e \<notin> residual_level_graph f s"
      using augpath_f'_has_edge_not_in_level  by force
    have prepath:"prepath p"
      using augpathE p_prop(1) by auto
    have "set p \<subseteq> {e |e. e \<in> \<EE> \<and> 0 < \<uu>\<^bsub>f\<^esub>e} \<union> erev ` residual_level_graph f s"
      by (intro new_augpath_in_pos_res_edges_or_level_graph)
        (auto simp add: p_prop(1)  p_prop(6))
    then obtain p' where p'_prop:"prepath p'" "fstv (hd p') = s" "sndv (last p') = t"
      "length p' + length (filter (\<lambda>e. e \<notin> residual_level_graph f s) p) \<le> length p"
      "set p' \<subseteq> residual_level_graph f s" "p' \<noteq> []"
      using find_shorter_path_in_lg[OF prepath p_prop(2,3) refl] by auto
    moreover have "filter (\<lambda>e. e \<notin> residual_level_graph f s) p \<noteq> []"
      using e_prop 
      by (auto simp add: filter_empty_conv)
    ultimately have "length p' < length p"
      using nat_less_le by fastforce
    moreover have " residual_distance f s t = length p'"
      using p'_prop  residual_level_graph_in_E_pos   
      by(auto intro!: augpath_in_lg_length_res_distance augpathI Rcap_strictI')
    ultimately show ?thesis
      using p_prop(4)[symmetric]
      by(auto simp add: residual_distance_def)
  qed
qed

lemma resreach_dist_number_of_verts_bound:
  assumes  "resreach f s t"
  shows "residual_distance f s t < card \<V>"
proof-
  note dist_s_t_le_infty = resreach_residual_dist_less_infty[OF assms(1)]
  hence "distance (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu}) s t
             < enat (card (dVs (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu})))"
    by(auto intro!: distance_less_vert_card
             simp add: multigraph_spec.multigraph_distance_def distance_set_def finite_\<EE>
                       residual_distance_def)
  moreover have "card (dVs (to_vertex_pair ` {uu \<in> \<EE>. 0 < \<uu>\<^bsub>f\<^esub>uu})) \<le> card \<V>"
    using \<V>_finite
    by(auto intro!: card_mono simp add: dVs_def \<EE>_def make_pair')+
  ultimately show ?thesis
    using less_enatE
    by(fastforce simp add: residual_distance_def multigraph_spec.multigraph_distance_def
                           distance_set_def)
qed

end
end