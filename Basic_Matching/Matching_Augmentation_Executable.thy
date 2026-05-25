theory Matching_Augmentation_Executable
  imports
   Matching
   Directed_Set_Graphs.Summary
   Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor
   "HOL-Data_Structures.Map_Specs"
   Undirected_Set_Graphs.Directed_Undirected
   Berge
begin

lemma UD_symmetric_diff_hom:
  assumes "symmetric_digraph A" 
          "symmetric_digraph B" 
    shows "UD (A \<oplus> B) = UD A \<oplus> UD B"
  using assms
  by(simp add: UD_diff_hom symmetric_diff_def UD_union_hom)

lemma symmetric_sym_diff_pres:
   "\<lbrakk>symmetric_digraph A; symmetric_digraph B\<rbrakk> \<Longrightarrow> symmetric_digraph (A \<oplus> B)"
  by(auto simp add:  symmetric_digraph_def symmetric_diff_def)

locale matching_augmentation_spec =
  buddy_map: Map buddy_empty buddy_upd buddy_delete buddy_lookup buddy_invar
  for  buddy_empty
  and  buddy_upd::"'v \<Rightarrow> 'v \<Rightarrow> 'buddy \<Rightarrow> 'buddy"
  and  buddy_delete buddy_lookup buddy_invar
begin

fun augment_impl
  where
"augment_impl M [] = M"|
"augment_impl M [v] = M"|
"augment_impl M (u#v#vs) = 
   (let M' = buddy_upd v u (buddy_upd u v M)
    in augment_impl M' vs)"

lemmas [code] = augment_impl.simps
definition "\<M> M = upairs_of_map (buddy_lookup M)"
definition "\<M>_dir M = dpairs_of_map (buddy_lookup M)"

lemmas \<M>_def' = \<M>_def[simplified upairs_of_map_def]
lemmas \<M>_dir_def' = \<M>_dir_def[simplified dpairs_of_map_def]

definition "symmetric_buddies M = (\<forall> u v. buddy_lookup M u = Some v \<longleftrightarrow> buddy_lookup M v = Some u)"

lemma symmetric_buddiesI:
  "(\<And> u v. buddy_lookup M u = Some v \<Longrightarrow> buddy_lookup M v = Some u) \<Longrightarrow> symmetric_buddies M"
and symmetric_buddiesE:
  "symmetric_buddies M \<Longrightarrow>
   ((\<And> u v. buddy_lookup M u = Some v \<longleftrightarrow> buddy_lookup M v = Some u) \<Longrightarrow>P)
   \<Longrightarrow>P"
and symmetric_buddiesD:
  "symmetric_buddies M \<Longrightarrow> buddy_lookup M u = Some v \<longleftrightarrow> buddy_lookup M v = Some u"
proof(goal_cases)
  case 1
  thus ?case
    unfolding symmetric_buddies_def by blast
qed(auto simp add: symmetric_buddies_def)

definition "no_self_loop_buddy M = (\<forall> u. buddy_lookup M u \<noteq> Some u)"

lemma no_self_loop_buddyE:
  "no_self_loop_buddy M \<Longrightarrow> ((\<And> u. buddy_lookup M u = Some u \<Longrightarrow> False) \<Longrightarrow> P) \<Longrightarrow> P"
and no_self_loop_buddyI:
  "(\<And> u. buddy_lookup M u = Some u \<Longrightarrow> False) \<Longrightarrow> no_self_loop_buddy M "
  by(auto simp add: no_self_loop_buddy_def)

lemma no_self_loop_buddy_dblton_graph:
 "no_self_loop_buddy M \<Longrightarrow> dblton_graph (\<M> M)"
  by(force intro!: dblton_graphI elim!: no_self_loop_buddyE simp add: \<M>_def' doubleton_eq_iff)

lemma no_self_loop_buddy_and_\<M>_dir:
  "no_self_loop_buddy M \<longleftrightarrow> (\<nexists> x. (x,x) \<in> \<M>_dir M)"
  by(auto simp add: no_self_loop_buddy_def \<M>_dir_def')

definition "invar_matching G M = 
  (buddy_invar M \<and> symmetric_buddies M \<and> no_self_loop_buddy M \<and>
   graph_matching G (\<M> M) \<and> finite (\<M> M))"

lemma invar_matchingE:
  "invar_matching G M \<Longrightarrow> 
   (\<lbrakk>buddy_invar M; symmetric_buddies M; no_self_loop_buddy M; 
     graph_matching G (\<M> M); finite (\<M> M)\<rbrakk>
    \<Longrightarrow> P)
   \<Longrightarrow> P"
and invar_matchingI:
  "\<lbrakk>buddy_invar M; symmetric_buddies M; no_self_loop_buddy M;
    graph_matching G (\<M> M); finite (\<M> M)\<rbrakk>
   \<Longrightarrow> invar_matching G M"
and invar_matchingD:
  "invar_matching G M \<Longrightarrow> buddy_invar M"
  "invar_matching G M \<Longrightarrow> symmetric_buddies M"
  "invar_matching G M \<Longrightarrow> no_self_loop_buddy M"
  "invar_matching G M \<Longrightarrow> graph_matching G (\<M> M)"
  "invar_matching G M \<Longrightarrow> finite (\<M> M)"
  by(auto simp add: invar_matching_def)

end

locale matching_augmentation = matching_augmentation_spec 
begin

lemmas buddies = 
 buddy_map.invar_empty
 buddy_map.invar_update
 buddy_map.map_update
 buddy_map.map_empty
  
lemma \<M>_dir_one_upd_change:
  assumes "buddy_invar M"  "M' = buddy_upd v u (buddy_upd u v M)"
  shows  "buddy_invar M'"
         "\<M>_dir M'  = \<M>_dir M - ({(u, x) |  x. buddy_lookup M u = Some x}
                                    \<union> {(v, x) | x . buddy_lookup M v = Some x})
                                \<union> {(u, v), (v, u)}"
         "buddy_lookup M' = (buddy_lookup M) (u \<mapsto> v, v \<mapsto> u)"
  using assms(1)
  by(auto simp add: assms(2) \<M>_dir_def' buddies(2,3) 
                    if_split[of "\<lambda> x. x = Some _" "_ = _" "Some _"])

lemma augment_impl_effect:
  assumes"buddy_invar M" "distinct P" "even (length P)"
  shows "buddy_invar (augment_impl M P)"
  "\<M>_dir (augment_impl M P) = \<M>_dir M - {(u, v) | u v. u \<in> set P \<and> buddy_lookup M u = Some v} \<union>
                  \<Union> {{(u, v), (v, u)} | u v i. u = P!i \<and> v = P!(i+1) \<and> i+1 < length P \<and> even i}"
proof-
  have buddy_invar_it: "buddy_invar (augment_impl M P)" for P
    using assms(1)
    apply(induction P arbitrary: M rule: augment_impl.induct)
    using buddies(2) by auto
  thus "buddy_invar (augment_impl M P)"
    by simp
  show "\<M>_dir (augment_impl M P) = 
      \<M>_dir M - {(u, v) | u v. u \<in> set P \<and> buddy_lookup M u = Some v} \<union>
               \<Union> {{(u, v), (v, u)} | u v i. u = P!i \<and> v = P!(i+1) \<and> i+1 < length P \<and> even i}"
    using assms
  proof(induction M P rule: augment_impl.induct)
    case (1 M)
    then show ?case 
      by (auto simp add: symmetric_diff_def)
  next
    case (2 M v)
    then show ?case 
     by (auto simp add: symmetric_diff_def)
  next
    case (3 M uu vv vs)
    note IH = this
    let ?U = "\<Union>{{(u, v), (v, u)} | u v i. u = (vs)!i \<and>
                    v = (vs)!(i+1) \<and> i+1 < length ( vs) \<and> even i}"
    define U where "U = ?U"
    have Big_extract_first:
         "\<Union> {{(u, v), (v, u)} | u v i. u = (uu # vv # vs)!i \<and> v = (uu # vv # vs)!(i+1) 
                       \<and> i+1 < length (uu # vv # vs) \<and> even i} = 
          {(uu, vv), (vv, uu)} \<union> ?U"
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 e)
      then obtain u v i where uvi: 
        "e = (u, v) \<or> e = (v, u)" "u = (uu # vv # vs)!i" "v = (uu # vv # vs)!(i+1)"
        "i+1 < length (uu # vv # vs)" "even i"
        by auto
      show ?case 
      proof(cases i)
        case 0
        then show ?thesis 
          using uvi by fastforce
      next
        case (Suc ii)
        hence "u = vs!(i-2) \<and> v = vs!((i-2) + 1)" "(i-2)+1 < length vs \<and> even (i-2)"
          apply(cases ii)
          using uvi(2-) Suc
          by auto
        then show ?thesis
          using uvi(1) by blast
      qed   
    next
      case (2 e)
      show ?case
      proof(cases rule: UnE[OF 2], goal_cases)
        case 1
        then show ?case 
          by (force intro!: exI[of _ "{(uu, vv), (vv, uu)}"] 
                     intro: exI[of _ uu] exI[of _ vv])
      next
        case 2
        then obtain u v i where uvi: 
          "e = (u, v) \<or> e = (v, u)"  "u = vs!i" "v = vs!(i+1)" "i+1 < length vs" "even i"
        by auto
      then show ?case 
        by (force intro!: exI[of _ "{(u, v), (v, u)}"] 
                   intro: exI[of _ u] exI[of _ v])
      qed
    qed
    have IH_precond: "distinct vs"  "even (length vs)"
      using IH(3,4) by auto
    show ?case
    proof((subst augment_impl.simps Let_def)+, goal_cases)
      case 1
      show ?case
      proof(subst IH(1)[OF refl \<M>_dir_one_upd_change(1)[OF IH(2) refl] IH_precond], goal_cases)
        case 1
        show ?case
          using IH(3) 
          by ((subst \<M>_dir_one_upd_change[OF IH(2) refl] Big_extract_first U_def[symmetric])+)
             (auto simp add: if_split[of "\<lambda> x. x = Some _" "_ = _" "Some _"])
      qed
    qed
  qed
qed

lemma symmetric_buddy_matching:
  assumes "symmetric_buddies M" "no_self_loop_buddy M" 
  shows "matching (\<M> M)"
  using assms
  apply(auto simp add: symmetric_buddies_def \<M>_def' matching_def no_self_loop_buddy_def)
  by (metis option.sel)+

lemma \<M>_\<M>_dir_UD:
  shows "\<M> M = UD (\<M>_dir M)"
  by(auto simp add: \<M>_def' \<M>_dir_def' UD_def)

lemma symmetric_digraph_iff_symmetric_buddies:
  "symmetric_buddies M  \<longleftrightarrow> symmetric_digraph (\<M>_dir M)"
  by(auto simp add: symmetric_buddies_def symmetric_digraph_def \<M>_dir_def')

lemma symmetric_buddies_unique:
 "\<lbrakk>symmetric_buddies M; {u, v} \<in> \<M> M; {u, v'} \<in> \<M> M\<rbrakk> \<Longrightarrow> v = v'"
  by(auto simp add: \<M>_def' symmetric_buddies_def doubleton_eq_iff)

lemma 
  assumes "buddy_invar M"
  "alt_path (\<M> M) p"
  "even (length p)"
  "symmetric_buddies M"
  "distinct p"
  "length p \<ge> 2 \<Longrightarrow> hd p \<notin> Vs (\<M> M)"
  "length p \<ge> 2 \<Longrightarrow> last p \<notin> Vs (\<M> M)"
shows augment_impl_correct_general: "\<M> (augment_impl M p) = \<M> M \<oplus> (set (edges_of_path p))"
  and augment_impl_symmetry_general:"symmetric_buddies (augment_impl M p)"
  and augment_impl_dir_correct_general:
     "\<M>_dir (augment_impl M p) = \<M>_dir M \<oplus> {(u, v) | u v. {u, v} \<in> set (edges_of_path p)}"
  and augment_impl_no_self_loop_buddy_pres: 
     "no_self_loop_buddy M \<Longrightarrow> no_self_loop_buddy (augment_impl M p)"
proof-
  have substracted_are:
        "{(u, v) |u v. u \<in> set p \<and> buddy_lookup M u = Some v} = 
        {(u, v) | u v. {u, v} \<in> set (edges_of_path p)} \<inter> \<M>_dir M"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    then obtain u v where uv: "e = (u, v)" "u \<in> set p" "buddy_lookup M u = Some v" 
      by auto
    hence uv_in_M: "{u, v} \<in> \<M> M"
      using \<M>_def' by blast
    have "{u, v} \<in> set (edges_of_path p)"
    proof-
      have h0: "length p < 2 \<Longrightarrow> False" 
        using \<open>u \<in> set p\<close> assms(3) by fastforce
      have h1: "p = p1@[a,u,b]@p2 \<Longrightarrow> ?thesis" for p1 a b p2
      proof(goal_cases)
        case 1
        have edges_of_p_split:
            "edges_of_path p = edges_of_path (p1@[a]) @[{a, u},{u, b}]@(edges_of_path (b#p2))"
          by (metis "1" append_Cons append_Nil edges_of_path.simps(3) edges_of_path_symmetric_split)
        hence "({a, u} \<in> \<M> M \<and> {u, b} \<notin> \<M> M) 
               \<or> ({a, u} \<notin> \<M> M \<and> {u, b} \<in> \<M> M) " 
          using assms(2)[simplified edges_of_p_split]
          by (metis alt_list_adjacent)
        hence "v=a \<or>  v = b" 
          using  symmetric_buddies_unique[OF assms(4) uv_in_M]  
           by (auto simp add: insert_commute)
         thus ?thesis
           using edges_of_p_split by auto
       qed
      have h2:"p = [u, a]@p' \<Longrightarrow> False" for a p'
         using assms(6) edges_are_Vs uv_in_M by auto
       have h3:"p = p'@[a, u] \<Longrightarrow> False" for a p'
         using assms(7) edges_are_Vs uv_in_M by auto
       show ?thesis
       proof(rule element_of_list_cases[OF uv(2)], goal_cases)
         case 1
         then show ?case 
           using h0 by force
       next
         case (2 p')
         then show ?case 
           using h2 h0
           by (cases p') auto
       next
         case (3 p')
         then show ?case 
           using h3 h0
           by (cases p' rule: rev_cases)  auto
       next
         case (4 a b p1 p2)
         show ?case 
           by(auto intro!: h1[OF 4])
       qed
     qed
     thus ?case
       using uv_in_M
       by (simp add: \<M>_dir_def' uv(1,3))
   next
     case (2 e)
     then obtain u v where uv: "e = (u, v)" "{u, v} \<in> set (edges_of_path p)" "(u, v) \<in> \<M>_dir M"
       by auto
     hence "u \<in> set p" "buddy_lookup M u = Some v"
       by (auto intro: v_in_edge_in_path simp add: \<M>_dir_def')
     thus ?case
       by(simp add: uv(1))
   qed
  have added_are:
   "\<Union> {{(u, v), (v, u)} | u v i. u = p ! i \<and> v = p ! (i + 1) \<and> i + 1 < length p \<and> even i}
    = {(u, v) | u v. {u, v} \<in> set (edges_of_path p)} - \<M>_dir M"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    then obtain u v i where uvi: "e = (u, v) \<or> e = (v, u)"
          "u = p ! i" "v = p ! (i + 1)" "i + 1 < length p" "even i"
      by blast
    have p_split: "p = take i p @(u# v# drop (i+2) p)"
      by(subst id_take_nth_drop[OF  uvi(4)])
        (auto simp add: uvi(2) take_Suc_conv_app_nth[OF add_lessD1, OF uvi(4)] uvi(3))
    have uv_in_p:"{u, v} \<in> set (edges_of_path p)" 
      by(subst p_split, subst edges_of_path_append_2[of  "[_]@_" "_@[_]", simplified])
        (auto simp add: edges_of_path_snoc_2)
    have uv_index:"{u, v} = edges_of_path p ! i"
      using edges_of_path_index uvi(2,3,4) by auto
    have "{u, v} \<notin> \<M> M"
      unfolding uv_index
      apply(rule alternating_list_even_index)
      using assms(2) uvi(4,5) 
      by (auto simp add: edges_of_path_length less_diff_conv)
    thus ?case
      using uv_in_p uvi(1)
      by(auto simp add: insert_commute \<M>_\<M>_dir_UD in_UDI dest:  in_UDI)
  next
    case (2 e)
    then obtain u v where uv: "e = (u, v)" "{u, v} \<in> set (edges_of_path p)"
                          "(u, v) \<notin> \<M>_dir M" by auto
    hence uv_not_in_M: "{u, v} \<notin> \<M> M" 
      using  assms(4) 
      by(auto simp add: \<M>_\<M>_dir_UD symmetric_digraph_iff_symmetric_buddies
                 elim!: in_UD_symE)
    obtain i where i: "(edges_of_path p) ! i = {u, v}" "i < length (edges_of_path p)"
      by (meson in_set_conv_nth uv(2))
    hence eveni: "even i" 
      using alternating_list_odd_index assms(2) uv_not_in_M by fastforce
    have pi: "p ! i = u \<and>  p ! Suc i = v \<or>
              p ! i = v \<and>  p ! Suc i = u"
      using i 
      by(auto simp add: edges_of_path_index edges_of_path_length doubleton_eq_iff)
    thus ?case
      using uv(1) eveni i(2)
      by (force intro!: exI[of _ "{(u, v), (v, u)}"] 
              simp add: doubleton_eq_iff edges_of_path_length ) 
  qed
  show M_dir_new_is:
      "\<M>_dir (augment_impl M p) = \<M>_dir M \<oplus> {(u, v) | u v. {u, v} \<in> set (edges_of_path p)}"
    unfolding augment_impl_effect(2)[OF assms(1,5,3)] substracted_are  added_are
    by(auto simp add: symmetric_diff_def)
  thus "\<M> (augment_impl M p) = \<M> M \<oplus> set (edges_of_path p)"
    using assms(4,5) 
    by(simp add: \<M>_\<M>_dir_UD symmetric_digraph_by_def UD_symmetric_diff_hom
                 symmetric_digraph_iff_symmetric_buddies 
                 UD_inverse_of_D[OF distinc_p_dblton_edges])
  show "symmetric_buddies (augment_impl M p)"
    using assms(4)
    by(auto simp add: symmetric_digraph_iff_symmetric_buddies M_dir_new_is
              intro!: symmetric_sym_diff_pres symmetric_digraph_by_def)
  show "no_self_loop_buddy M \<Longrightarrow> no_self_loop_buddy (augment_impl M p)"
    using assms(5)
    by(unfold no_self_loop_buddy_and_\<M>_dir M_dir_new_is symmetric_diff_def D_of_edges_of_path)
      (auto dest!: distinct_no_self_loop_in_edges_of_vwalk)
qed

lemma 
 assumes "buddy_invar M" "symmetric_buddies M"
         "distinct p" "matching_augmenting_path (\<M> M) p"
 shows augment_impl_correct:
       "\<M> (augment_impl M p) = \<M> M \<oplus> set (edges_of_path p)"
 and augment_impl_stays_symmetric: 
       "symmetric_buddies (augment_impl M p)"
 and augment_impl_no_loops: "no_self_loop_buddy M \<Longrightarrow> no_self_loop_buddy (augment_impl M p)"
  using assms
  by(all \<open>intro augment_impl_correct_general augment_impl_symmetry_general
                augment_impl_no_self_loop_buddy_pres\<close>)
    (auto intro: aug_paths_are_even simp add: matching_augmenting_path_def)

lemma augmentation_correct:
  assumes "invar_matching G M"
          "graph_augmenting_path G (\<M> M) p"
    shows "invar_matching G (augment_impl M p)"
          "\<M> (augment_impl M p) = \<M> M \<oplus> set (edges_of_path p)"
          "card (\<M> (augment_impl M p)) > card (\<M> M)"
  using assms Berge_2(3)
    by(auto elim!: invar_matchingE 
           intro!: invar_matchingI augment_impl_effect(1) augment_impl_stays_symmetric 
                   new_matching_bigger aug_paths_are_even augment_impl_no_loops
                   symmetric_buddy_matching finite_symm_diff
         simp add: augment_impl_correct)+ 

lemma empty_matching_props:
  "invar_matching G buddy_empty"
  "\<M> buddy_empty = {}"
   by(auto intro!: invar_matchingI symmetric_buddiesI no_self_loop_buddyI 
         simp add: buddies \<M>_def')

end
end