theory Alt_Dist
  imports "Directed_Set_Graphs.enat_misc" Berge_Lemma.Alternating_Lists Directed_Set_Graphs.Dist
          "HOL-Library.Multiset"                                                        
begin

section \<open>Alternating Distances\<close>

subsection \<open>Alternating Distance from a vertex\<close>

named_theorems parity_simps

datatype parity = Even | Odd

definition of_parity[parity_simps]: "of_parity parity = (case parity of Even \<Rightarrow> even | Odd \<Rightarrow> odd)"

definition other_parity[parity_simps]: "other_parity parity = (case parity of Even \<Rightarrow> Odd | Odd \<Rightarrow> Even)"

definition next_alt_list_parity[parity_simps]: 
  "next_alt_list_parity prev_parity f P1 P2 = (case prev_parity of Even \<Rightarrow> f P1 P2 | Odd \<Rightarrow> f P2 P1)"

locale alt_dist =
  fixes P1 P2::"('a \<times> 'a) \<Rightarrow> bool"
begin

definition
  "alt_vwalk_bet parity G u p v =
     (Vwalk.vwalk_bet G u p v \<and> alt_list P1 P2 (edges_of_vwalk p) \<and> of_parity (other_parity parity) (length p))"

lemma alt_vwalk_betE: 
  "alt_vwalk_bet parity G u p v \<Longrightarrow>
    \<lbrakk>\<lbrakk>Vwalk.vwalk_bet G u p v; alt_list P1 P2 (edges_of_vwalk p); of_parity (other_parity parity) (length p)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: alt_vwalk_bet_def)

lemma alt_vwalk_betI: 
  "\<lbrakk>Vwalk.vwalk_bet G u p v; alt_list P1 P2 (edges_of_vwalk p); of_parity (other_parity parity) (length p)\<rbrakk> 
    \<Longrightarrow> alt_vwalk_bet parity G u p v"
  by (auto simp: alt_vwalk_bet_def)

definition
  "alt_distance (parity:: parity) G u v = 
  (INF p. if alt_vwalk_bet parity G u p v
          then length p - 1
          else \<infinity>)"

lemma dist_le_odd_dist: "distance G u v \<le> alt_distance parity G u v "
  apply (auto simp: distance_def alt_distance_def image_def alt_vwalk_bet_def
              intro!: complete_lattice_class.Inf_lower enat_ile split: parity.splits)
  apply (smt (verit, del_insts) Collect_disj_eq mem_Collect_eq wellorder_InfI)
  by (meson vwalk_bet_def)

lemma alt_vwalk_bet_alt_dist:
  "\<lbrakk>alt_vwalk_bet parity G u p v\<rbrakk> \<Longrightarrow> 
     alt_distance parity G u v \<le> length p - 1"
  by (auto simp: alt_distance_def image_def alt_vwalk_bet_def
           intro!: complete_lattice_class.Inf_lower enat_ile)

lemma alt_vwalk_bet_subset:
  "\<lbrakk>alt_vwalk_bet parity G u p v; G \<subseteq> G'\<rbrakk> \<Longrightarrow> alt_vwalk_bet parity G' u p v"
  using vwalk_bet_subset
  by (auto simp: alt_vwalk_bet_def)

definition 
  "alt_reachable parity G u v = (\<exists>p. alt_vwalk_bet parity G u p v)"

lemma alt_reachable_vwalk_bet_iff:
  "alt_reachable parity G u v \<longleftrightarrow> (\<exists>p. alt_vwalk_bet parity G u p v)"
  by (auto simp: alt_reachable_def)

lemma alt_reachableE:
  "alt_reachable parity G u v \<Longrightarrow> \<lbrakk>\<And>p. alt_vwalk_bet parity G u p v \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: alt_reachable_def)

lemma alt_reachable_vwalk_betD:
  "alt_vwalk_bet parity G u p v \<Longrightarrow> alt_reachable parity G u v"
  using iffD2[OF alt_reachable_vwalk_bet_iff]
  by force

lemma alt_reachable_dist:
  "alt_reachable parity G u v \<Longrightarrow> alt_distance parity G u v < \<infinity>"
  apply(clarsimp simp add: alt_reachable_vwalk_bet_iff)
  by (auto simp: alt_distance_def image_def alt_vwalk_bet_def intro!: complete_lattice_class.Inf_lower enat_ile)

lemma alt_unreachable_dist:
  "\<not>alt_reachable parity G u v \<Longrightarrow> alt_distance parity G u v = \<infinity>"
  apply(clarsimp simp add: alt_reachable_vwalk_bet_iff)
  apply (auto simp: alt_distance_def image_def alt_vwalk_bet_def intro!: complete_lattice_class.Inf_lower enat_ile)
  by (smt (verit, del_insts) Inf_top_conv(1) inf.order_iff mem_Collect_eq top_greatest)

lemma alt_dist_reachable:
  "alt_distance parity G u v < \<infinity> \<Longrightarrow> alt_reachable parity G u v"
  using wellorder_InfI       
  apply(auto simp: alt_distance_def image_def alt_reachable_vwalk_bet_iff alt_vwalk_bet_def)
  by (smt (verit, ccfv_threshold) Collect_disj_eq Inf_top_conv(1) enat.distinct(2) mem_Collect_eq top_enat_def)    

lemma alt_reachable_dist_2:
  assumes "alt_reachable parity G u v"
  obtains p where "alt_vwalk_bet parity G u p v""alt_distance parity G u v = length p - 1"
  using assms
  apply(clarsimp simp add: alt_reachable_vwalk_bet_iff alt_distance_def image_def alt_vwalk_bet_def)
  by (smt (verit, del_insts) Collect_disj_eq Inf_lower enat_ile mem_Collect_eq not_infinity_eq wellorder_InfI)

lemma alt_reachable_reachable_in_dVs:
  assumes "alt_reachable parity G u v"
  shows "reachable G u v"
  using assms
  by (auto elim!: alt_reachableE alt_vwalk_betE simp: reachable_vwalk_betD)

lemma alt_reachable_in_dVs:
  assumes "alt_reachable parity G u v"
  shows "u \<in> dVs G" "v \<in> dVs G"
  using assms alt_reachable_reachable_in_dVs reachable_in_dVs
  by metis+

lemma alt_vwalk_bet_nonempty'[simp]: "\<not> alt_vwalk_bet parity E u [] v" 
  unfolding alt_vwalk_bet_def by simp

lemma hd_of_alt_vwalk_bet:
  "alt_vwalk_bet parity dG v p v' \<Longrightarrow> \<exists>p'. p = v # p'"
  by(auto elim!: alt_vwalk_betE simp: hd_of_vwalk_bet)

lemma hd_of_alt_vwalk_bet': 
  "alt_vwalk_bet parity dG v p v' \<Longrightarrow> v = hd p"
  by(auto elim!: alt_vwalk_betE simp: hd_of_vwalk_bet')

lemma hd_of_alt_vwalk_bet'': "alt_vwalk_bet parity dG u p v \<Longrightarrow> u \<in> set p"
  using hd_of_alt_vwalk_bet
  by force 

lemma last_of_alt_vwalk_bet: 
  "alt_vwalk_bet parity dG v p v' \<Longrightarrow> v' = last p"
  by(auto simp: neq_Nil_conv alt_vwalk_bet_def dest: last_of_vwalk_bet)

lemma last_of_alt_vwalk_bet': 
  "alt_vwalk_bet parity dG v p v' \<Longrightarrow> \<exists>p'. p = p' @ [v']"
  by(auto simp: alt_vwalk_bet_def dest: append_butlast_last_id[symmetric] last_of_vwalk_bet')

end

lemma alt_vwalk_bet_append_1:
  assumes "alt_dist.alt_vwalk_bet P1 P2 Even G u (p1 @ p2) v" "p1 \<noteq> []"
  shows                (*"alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1)"*)
  "\<exists>parity'.
    alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1) \<and>
    next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 parity' G (last p1) (last p1 # p2) v"
  using assms
  apply(auto simp add: alt_list_append_1 edges_of_vwalk_append_3
                       vwalk_bet_prefix_is_vwalk_bet alt_dist.alt_vwalk_bet_def parity_simps
             split: parity.splits)
  apply(rule exI[where x = Odd])
  apply(auto simp add: alt_list_append_1 edges_of_vwalk_append_3 vwalk_bet_suffix_is_vwalk_bet'
                       vwalk_bet_prefix_is_vwalk_bet alt_dist.alt_vwalk_bet_def parity_simps
             split: parity.splits)
  apply (metis alt_list_split_2 edges_of_path_length edges_of_path_length' edges_of_vwalk_length even_plus_one_iff)
  apply(rule exI[where x = Even])
  apply(auto simp add: alt_list_append_1 edges_of_vwalk_append_3 vwalk_bet_suffix_is_vwalk_bet'
                       vwalk_bet_prefix_is_vwalk_bet alt_dist.alt_vwalk_bet_def parity_simps
             split: parity.splits)
  by (metis alt_list_split_1 edges_of_path_length edges_of_path_length' edges_of_vwalk_length even_plus_one_iff)

lemma alt_vwalk_bet_appendE_1:
  assumes "alt_dist.alt_vwalk_bet P1 P2 Even G u (p1 @ p2) v" "p1 \<noteq> []"
  obtains parity' where
    "alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1)"
    "next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 parity' G (last p1) (last p1 # p2) v"
  using alt_vwalk_bet_append_1[OF assms]
  by auto

lemma alt_vwalk_bet_append_1':
  assumes "alt_dist.alt_vwalk_bet P1 P2 Odd G u (p1 @ p2) v" "p1 \<noteq> []"
  shows                (*"alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1)"*)
  "\<exists>parity'.
    alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1) \<and>
    next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 (other_parity parity') G (last p1) (last p1 # p2) v"
  using assms
  apply(auto simp add: alt_list_append_1 edges_of_vwalk_append_3
                       vwalk_bet_prefix_is_vwalk_bet alt_dist.alt_vwalk_bet_def parity_simps
             split: parity.splits)
  apply(rule exI[where x = Odd])
  apply(auto simp add: alt_list_append_1 edges_of_vwalk_append_3 vwalk_bet_suffix_is_vwalk_bet'
                       vwalk_bet_prefix_is_vwalk_bet alt_dist.alt_vwalk_bet_def parity_simps
             split: parity.splits)
  apply (metis alt_list_split_2 edges_of_path_length edges_of_path_length' edges_of_vwalk_length even_plus_one_iff)
  apply(rule exI[where x = Even])
  apply(auto simp add: alt_list_append_1 edges_of_vwalk_append_3 vwalk_bet_suffix_is_vwalk_bet'
                       vwalk_bet_prefix_is_vwalk_bet alt_dist.alt_vwalk_bet_def parity_simps
             split: parity.splits)
  by (metis alt_list_split_1 edges_of_path_length edges_of_path_length' edges_of_vwalk_length even_plus_one_iff)

lemma alt_vwalk_bet_appendE_1':
  assumes "alt_dist.alt_vwalk_bet P1 P2 Odd G u (p1 @ p2) v" "p1 \<noteq> []"
  obtains parity' where
  "alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1)"
  "next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 (other_parity parity') G (last p1) (last p1 # p2) v"
  using alt_vwalk_bet_append_1'[OF assms]
  by auto

lemma alt_vwalk_bet_append_2:
  assumes
    "alt_dist.alt_vwalk_bet P1 P2 parity G u p1 (last p1)"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G (last p1) (last p1 # p2) v"
    "p1 \<noteq> []"
  shows "alt_dist.alt_vwalk_bet P1 P2 Even G u (p1 @ p2) v"
  using assms
  apply(auto simp add: alt_list_append_1 edges_of_vwalk_append_3 vwalk_bet_suffix_is_vwalk_bet'
                       vwalk_bet_prefix_is_vwalk_bet alt_dist.alt_vwalk_bet_def parity_simps
             split: parity.splits)
  using vwalk_bet_transitive apply fastforce
  apply (metis alt_list_append_2 assms(3) edges_of_path_length edges_of_path_length' edges_of_vwalk_length even_plus_one_iff)
  apply (metis list.sel(3) vwalk_bet_transitive)
  by (simp add: alt_list_append_3 edges_of_vwalk_length)

lemma alt_vwalk_bet_append_3:
  assumes 
    "alt_dist.alt_vwalk_bet P1 P2 parity G u p1 (last p1)"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G (last p1) (last p1 # p2) v"
    "p1 \<noteq> []"
  shows "alt_dist.alt_vwalk_bet P1 P2 Odd G u (p1 @ p2) v"
  using assms
  apply(auto simp add: alt_list_append_1 edges_of_vwalk_append_3 vwalk_bet_suffix_is_vwalk_bet'
                       vwalk_bet_prefix_is_vwalk_bet alt_dist.alt_vwalk_bet_def parity_simps
             split: parity.splits)
  using vwalk_bet_transitive apply fastforce
  subgoal sorry
  apply (metis list.sel(3) vwalk_bet_transitive)
  by (simp add: alt_list_append_3 edges_of_vwalk_length)

lemma alternating_list_even_last:
  assumes "alt_dist.alt_vwalk_bet P1 P2 Even G u p v" "length p \<ge> 2"
  shows "P2 (last (edges_of_vwalk p))"
  using assms
  apply(elim alt_dist.alt_vwalk_betE)
  apply(auto dest!: alternating_list_even_last simp: parity_simps edges_of_vwalk_length)
  apply(auto simp: eval_nat_numeral Suc_le_length_iff)
  done

lemma alternating_list_odd_last:
  assumes "alt_dist.alt_vwalk_bet P1 P2 Odd G u p v" "length p \<ge> 2"
  shows "P1 (last (edges_of_vwalk p))"
  using assms
  apply(elim alt_dist.alt_vwalk_betE)
  by(auto dest!: alternating_list_odd_last simp: parity_simps edges_of_vwalk_length)

lemma alt_triangle_ineq_reachable_1: 
  assumes "alt_dist.alt_reachable P1 P2 parity G u v" "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 (other_parity parity) G v w"
  shows "alt_dist.alt_distance P1 P2 Odd G u w \<le> 
           alt_dist.alt_distance P1 P2 parity G u v + next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G v w"
proof-
  obtain p q
    where p_q: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v"
               "alt_dist.alt_distance P1 P2 parity G u v = length p - 1"
          "(next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2) (other_parity parity) G v q w"
          "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G v w = length q - 1"
    using assms
    apply (cases parity)
    by (auto elim!: alt_dist.alt_reachable_dist_2 simp: parity_simps)
  hence "alt_dist.alt_vwalk_bet P1 P2 Odd G u (p @ tl q) w"
    by (smt (verit) alt_dist.alt_vwalk_betE alt_vwalk_bet_append_3 list.collapse next_alt_list_parity 
                    parity.exhaust parity.simps(3) parity.simps(4) vwalk_bet_def)
  hence "alt_dist.alt_distance P1 P2 Odd G u w \<le> length (p @ tl q) - 1"
    apply(intro alt_dist.alt_vwalk_bet_alt_dist)
    by auto
  moreover have "length (p @ tl q) = length p + (length q - 1)"
    using p_q(2)
    by (cases q; auto)
  ultimately have "alt_dist.alt_distance P1 P2 Odd G u w \<le> length p + (length q - 1) - 1"
    by (auto simp: eval_nat_numeral)
  thus ?thesis
    using p_q
    by(cases p; auto elim!:alt_dist.alt_vwalk_betE simp add: eval_nat_numeral)
qed

lemma alt_triangle_ineq_reachable_2: 
  assumes "alt_dist.alt_reachable P1 P2 parity G u v" "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G v w"
  shows "alt_dist.alt_distance P1 P2 Even G u w \<le> 
           alt_dist.alt_distance P1 P2 parity G u v + next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G v w"
proof-
  obtain p q
    where p_q: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v"
               "alt_dist.alt_distance P1 P2 parity G u v = length p - 1"
          "(next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2) parity G v q w"
          "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G v w = length q - 1"
    using assms
    apply (cases parity)
    by (auto elim!: alt_dist.alt_reachable_dist_2 simp: parity_simps)
  hence "alt_dist.alt_vwalk_bet P1 P2 Even G u (p @ tl q) w"
    by (smt (verit) alt_dist.alt_vwalk_betE alt_vwalk_bet_append_2 list.collapse next_alt_list_parity 
                    parity.exhaust parity.simps(3) parity.simps(4) vwalk_bet_def)
  hence "alt_dist.alt_distance P1 P2 Even G u w \<le> length (p @ tl q) - 1"
    apply(intro alt_dist.alt_vwalk_bet_alt_dist)
    by auto
  moreover have "length (p @ tl q) = length p + (length q - 1)"
    using p_q(2)
    by (cases q; auto)
  ultimately have "alt_dist.alt_distance P1 P2 Even G u w \<le> length p + (length q - 1) - 1"
    by (auto simp: eval_nat_numeral)
  thus ?thesis
    using p_q
    by(cases p; auto elim!:alt_dist.alt_vwalk_betE simp add: eval_nat_numeral)
qed

lemma alt_triangle_ineq_1:
  "alt_dist.alt_distance P1 P2 Odd G u w \<le> 
           alt_dist.alt_distance P1 P2 parity G u v + next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G v w"
 proof(cases "alt_dist.alt_reachable P1 P2 parity G u v")
  case reach_u_v: True
  then show ?thesis
  proof(cases "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 (other_parity parity) G v w")
    case reach_v_w: True
    then show ?thesis
      using alt_triangle_ineq_reachable_1[OF reach_u_v reach_v_w]
      by auto
  next
    case not_reach_v_w: False
    hence "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G v w = \<infinity>"
      apply (cases parity)
      by (auto simp add: alt_dist.alt_unreachable_dist parity_simps)
    then show ?thesis
      by simp
  qed
next
  case not_reach_u_v: False
  hence "alt_dist.alt_distance P1 P2 parity G u v = \<infinity>"
    apply (cases parity)
    by (auto simp add: alt_dist.alt_unreachable_dist parity_simps)
  then show ?thesis
    by simp
qed

lemma alt_triangle_ineq_2:
  "alt_dist.alt_distance P1 P2 Even G u w \<le> 
           alt_dist.alt_distance P1 P2 parity G u v + next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G v w"
 proof(cases "alt_dist.alt_reachable P1 P2 parity G u v")
  case reach_u_v: True
  then show ?thesis
  proof(cases "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G v w")
    case reach_v_w: True
    then show ?thesis
      using alt_triangle_ineq_reachable_2[OF reach_u_v reach_v_w]
      by auto
  next
    case not_reach_v_w: False
    hence "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G v w = \<infinity>"
      apply (cases parity)
      by (auto simp add: alt_dist.alt_unreachable_dist parity_simps)
    then show ?thesis
      by simp
  qed
next
  case not_reach_u_v: False
  hence "alt_dist.alt_distance P1 P2 parity G u v = \<infinity>"
    apply (cases parity)
    by (auto simp add: alt_dist.alt_unreachable_dist parity_simps)
  then show ?thesis
    by simp
qed


lemma distance_split_1:
  "\<lbrakk>alt_dist.alt_distance P1 P2 Even G u v \<noteq> \<infinity>; 
    alt_dist.alt_distance P1 P2 Even G u v =
      alt_dist.alt_distance P1 P2 parity G u w +
      next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G w v \<rbrakk> \<Longrightarrow>
       \<exists>w'. alt_dist.alt_reachable P1 P2 parity G u w' \<and>
            alt_dist.alt_distance P1 P2 parity G u w' = alt_dist.alt_distance P1 P2 parity G u w \<and>
            next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G w' v \<and>
            next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G w' v = 
            next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G w v "
  apply(auto simp only: parity_simps split: parity.splits)
  apply (metis alt_dist.alt_unreachable_dist enat.distinct(2) plus_eq_infty_iff_enat)
  by (metis alt_dist.alt_unreachable_dist enat.distinct(2) plus_eq_infty_iff_enat)

lemma alt_dist_inf: "v \<notin> dVs G \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G u v = \<infinity>"
proof(rule ccontr, goal_cases)
  case 1
  hence "alt_dist.alt_reachable P1 P2 parity G u v"
    by(auto intro!: alt_dist.alt_dist_reachable)
  hence "v \<in>dVs G"
    by (simp add: alt_dist.alt_reachable_in_dVs(2))
  then show ?case
    using 1
    by auto
qed

lemma alt_dist_inf_2: "v \<notin> dVs G \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G v u = \<infinity>"
proof(rule ccontr, goal_cases)
  case 1
  hence "alt_dist.alt_reachable P1 P2 parity G v u"
    by(auto intro!: alt_dist.alt_dist_reachable)
  hence "v \<in>dVs G"
    by (simp add: alt_dist.alt_reachable_in_dVs(1))
  then show ?case
    using 1
    by auto
qed

lemma alt_dist_eq: "\<lbrakk>\<And>p. alt_dist.alt_vwalk_bet P1 P2 parity G' u p v \<Longrightarrow> alt_dist.alt_vwalk_bet P1 P2 parity G u (map f p) v\<rbrakk> \<Longrightarrow>
                   alt_dist.alt_distance P1 P2 parity G u v \<le> alt_dist.alt_distance P1 P2 parity G' u v"
  apply(auto simp: alt_dist.alt_distance_def image_def intro!: Inf_lower)
  apply (smt (verit, ccfv_threshold) Un_iff length_map mem_Collect_eq wellorder_InfI)
  by (meson alt_dist.alt_vwalk_bet_nonempty')

lemma alt_distance_subset: "G \<subseteq> G' \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G' u v \<le> alt_dist.alt_distance P1 P2 parity G u v"
  by (metis enat_ord_simps(3) alt_dist.alt_reachable_dist_2 alt_dist.alt_unreachable_dist alt_dist.alt_vwalk_bet_alt_dist alt_dist.alt_vwalk_bet_subset)

lemma odd_alt_distance_neighbourhood:
  "\<lbrakk>v \<in> neighbourhood G u; P1 (u,v)\<rbrakk> \<Longrightarrow> alt_dist.alt_distance P1 P2 Odd G u v \<le> 1"
proof(goal_cases)
  case 1
  hence "vwalk_bet G u [u,v] v"
    by auto
  moreover have "P1 (u,v)"
    using 1(2) .
  ultimately have "alt_dist.alt_vwalk_bet P1 P2 Odd G u [u,v] v"
    by (auto intro!: alt_dist.alt_vwalk_betI simp: parity_simps alt_list_step alt_list_empty split: parity.splits)
  moreover have "length [u,v] = 2"
    by auto
  ultimately show ?case
    by(force dest!: alt_dist.alt_vwalk_bet_alt_dist simp: one_enat_def)
qed

lemma even_alt_distance_neighbourhood:
  "\<lbrakk>w \<in> neighbourhood G v; v \<in> neighbourhood G u; P1 (u,v); P2 (v,w)\<rbrakk> \<Longrightarrow> alt_dist.alt_distance P1 P2 Even G u w \<le> 2"
proof(goal_cases)
  case 1
  hence "vwalk_bet G u [u,v,w] w"
    by auto
  moreover have "P1 (u,v)"
    using 1(3) .
  moreover have "P2 (v,w)"
    using 1(4) .
  ultimately have "alt_dist.alt_vwalk_bet P1 P2 Even G u [u,v,w] w"
    by (auto intro!: alt_dist.alt_vwalk_betI simp: parity_simps alt_list_step alt_list_empty split: parity.splits)
  moreover have "length [u,v,w] = 3"
    by auto
  ultimately show ?case
    by(auto dest!: alt_dist.alt_vwalk_bet_alt_dist simp: one_enat_def eval_enat_numeral)
qed

subsection \<open>Shortest Paths\<close>
context alt_dist
begin

definition "alt_shortest_path parity G u p v = (alt_distance parity G u v = length p -1 \<and> alt_vwalk_bet parity G u p v)"

lemma alt_shortest_path_props[elim]:
  "alt_shortest_path parity G u p v \<Longrightarrow> (\<lbrakk>alt_distance parity G u v = length p -1; alt_vwalk_bet parity G u p v\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: alt_shortest_path_def)

lemma alt_shortest_path_intro:
  "\<lbrakk>alt_distance parity G u v = length p -1; alt_vwalk_bet parity G u p v\<rbrakk> \<Longrightarrow> alt_shortest_path parity G u p v"
  by (auto simp: alt_shortest_path_def)

lemma alt_shortest_path_vwalk: "alt_shortest_path parity G u p v \<Longrightarrow> alt_vwalk_bet parity G u p v"
  by auto

lemma alt_shortest_path_dist: "alt_shortest_path parity G u p v \<Longrightarrow> alt_distance parity G u v = length p - 1"
  by auto

end

lemma alt_shortest_path_split_1:
  "\<lbrakk>alt_dist.alt_shortest_path P1 P2 Even G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow>
     \<exists>parity'.
       alt_dist.alt_shortest_path P1 P2 parity' G u (p1 @ [x]) x \<and> 
       next_alt_list_parity parity' alt_dist.alt_shortest_path P1 P2 parity' G x (x # p2) v"
proof(goal_cases)
  case 1
  then obtain parity where 
         "alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x"
         "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x (x # p2) v"
    by (auto dest!: alt_dist.alt_shortest_path_vwalk simp: split_vwalk vwalk_bet_pref
                elim!: alt_vwalk_bet_appendE_1[where ?p1.0 = "p1 @ [x]", simplified])

  hence "alt_dist.alt_reachable P1 P2 parity G u x" 
        "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G x v"
    by (auto dest!: alt_dist.alt_reachable_vwalk_betD simp: parity_simps split: parity.splits)

  have "alt_dist.alt_distance P1 P2 parity G u x \<ge> length (p1 @ [x]) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>alt_dist.alt_reachable P1 P2 parity G u x\<close>
    obtain p where 
       "alt_dist.alt_vwalk_bet P1 P2 parity G u p x"
       "alt_dist.alt_distance P1 P2 parity G u x = enat (length p - 1)"
      by (auto intro: alt_dist.alt_reachable_dist_2 simp: parity_simps split: parity.splits)
    ultimately have "length p - 1 < length (p1 @ [x]) - 1"
      by auto 
    hence "length (p @ p2) - 1 < length (p1 @ x # p2) - 1"      by auto

    have "alt_dist.alt_vwalk_bet P1 P2 Even G u ((butlast p @ [x]) @ p2) v"
      using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x (x # p2) v\<close> 
            \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>
      apply(intro alt_vwalk_bet_append_2)
      apply(auto )
      apply(cases p)
      apply (auto simp: parity_simps split: parity.splits)
      by (metis alt_dist.alt_vwalk_bet_def append_butlast_last_id last.simps vwalk_bet_props)+
    moreover have "p = (butlast p) @ [x]"
      using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>
      apply (cases p)
      by (auto dest!: alt_dist.last_of_alt_vwalk_bet
               simp: parity_simps  alt_dist.alt_vwalk_bet_nonempty' 
                     append_butlast_last_id 
                 split: parity.splits )
    ultimately have "alt_dist.alt_distance P1 P2 Even G u v \<le> length (p @ p2) -1"
      apply(intro alt_dist.alt_vwalk_bet_alt_dist)
      by auto[1]
    moreover have "alt_dist.alt_distance P1 P2 Even G u v = length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Even G u (p1 @ x # p2) v\<close>
      by (rule alt_dist.alt_shortest_path_dist)
    ultimately show ?case
      using \<open>length (p @ p2) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "alt_dist.alt_distance P1 P2 parity G u x \<le> length (p1 @ [x]) - 1"
    using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
    by (auto intro!: alt_dist.alt_vwalk_bet_alt_dist simp only: parity_simps split: parity.splits)

  moreover have "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G x v \<ge> length (x # p2) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G x v\<close>
    obtain p where 
       "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x p v"
       "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G x v = enat (length p - 1)"
      by (auto intro: alt_dist.alt_reachable_dist_2 simp: parity_simps split: parity.splits)
    ultimately have "length p - 1 < length (x # p2) - 1"
      by auto 
    hence "length (p1 @ p) - 1 < length (p1 @ x # p2) - 1"
      by auto

    have "alt_dist.alt_vwalk_bet P1 P2 Even G u ((p1 @ [x]) @ (tl p)) v"
      using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close> 
            \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x p v\<close>
      apply(intro alt_vwalk_bet_append_2)
      apply(auto )
      apply(cases p)
      apply (auto simp: parity_simps split: parity.splits)
      apply (meson alt_dist.alt_vwalk_bet_nonempty')
      apply (meson alt_dist.alt_vwalk_bet_nonempty')
      apply (metis alt_dist.alt_vwalk_betE list.sel(1) vwalk_bet_def)
      by (metis alt_dist.alt_vwalk_betE list.sel(1) vwalk_bet_def)

    moreover have "p = x # (tl p)"
      using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x p v\<close> 
      by (fastforce dest!: alt_dist.hd_of_alt_vwalk_bet simp: parity_simps split: parity.splits)
    ultimately have "alt_dist.alt_distance P1 P2 Even G u v \<le> length (p1 @ p) -1"
      apply(intro alt_dist.alt_vwalk_bet_alt_dist)
      by auto[1]
    moreover have "alt_dist.alt_distance P1 P2 Even G u v = length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Even G u (p1 @ x # p2) v\<close>
      by (rule alt_dist.alt_shortest_path_dist)
    ultimately show ?case
      using \<open>length (p1 @ p) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G x v \<le> length (x # p2) - 1"
    using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x (x # p2) v\<close>
    by (auto intro!: alt_dist.alt_vwalk_bet_alt_dist simp only: parity_simps split: parity.splits)
  ultimately show ?case
    apply (intro exI[where x = parity])
    using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
    using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x (x # p2) v\<close>
    by (auto simp add: alt_dist.alt_shortest_path_def parity_simps split: parity.splits)
qed


lemma alt_shortest_path_split_2:
  "\<lbrakk>alt_dist.alt_shortest_path P1 P2 Odd G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow>
     \<exists>parity'.
       alt_dist.alt_shortest_path P1 P2 parity' G u (p1 @ [x]) x \<and>
       next_alt_list_parity parity' alt_dist.alt_shortest_path P1 P2 (other_parity parity') G x (x # p2) v"
proof(goal_cases)
  case 1
  then obtain parity where 
         "alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x"
         "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x (x # p2) v"
    by (auto dest!: alt_dist.alt_shortest_path_vwalk simp: split_vwalk vwalk_bet_pref
                elim!: alt_vwalk_bet_appendE_1'[where ?p1.0 = "p1 @ [x]", simplified])

  hence "alt_dist.alt_reachable P1 P2 parity G u x" 
        "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 (other_parity parity) G x v"
    by (auto dest!: alt_dist.alt_reachable_vwalk_betD simp: parity_simps split: parity.splits)

  have "alt_dist.alt_distance P1 P2 parity G u x \<ge> length (p1 @ [x]) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>alt_dist.alt_reachable P1 P2 parity G u x\<close>
    obtain p where 
       "alt_dist.alt_vwalk_bet P1 P2 parity G u p x"
       "alt_dist.alt_distance P1 P2 parity G u x = enat (length p - 1)"
      by (auto intro: alt_dist.alt_reachable_dist_2 simp: parity_simps split: parity.splits)
    ultimately have "length p - 1 < length (p1 @ [x]) - 1"
      by auto 
    hence "length (p @ p2) - 1 < length (p1 @ x # p2) - 1"      by auto

    have "alt_dist.alt_vwalk_bet P1 P2 Odd G u ((butlast p @ [x]) @ p2) v"
      using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x (x # p2) v\<close> 
            \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>
      apply(intro alt_vwalk_bet_append_3)
      apply(auto )
      apply(cases p)
      apply (auto simp: alt_dist.alt_vwalk_bet_nonempty' parity_simps split: parity.splits)
      by (metis alt_dist.alt_vwalk_bet_def append_butlast_last_id last.simps vwalk_bet_props)+
    moreover have "p = (butlast p) @ [x]"
      using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>
      apply (cases p)
      by (auto dest!: alt_dist.last_of_alt_vwalk_bet
               simp: parity_simps  alt_dist.alt_vwalk_bet_nonempty' 
                     append_butlast_last_id 
                 split: parity.splits )
    ultimately have "alt_dist.alt_distance P1 P2 Odd G u v \<le> length (p @ p2) -1"
      apply(intro alt_dist.alt_vwalk_bet_alt_dist)
      by auto[1]
    moreover have "alt_dist.alt_distance P1 P2 Odd G u v = length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u (p1 @ x # p2) v\<close>
      by (rule alt_dist.alt_shortest_path_dist)
    ultimately show ?case
      using \<open>length (p @ p2) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "alt_dist.alt_distance P1 P2 parity G u x \<le> length (p1 @ [x]) - 1"
    using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
    by (auto intro!: alt_dist.alt_vwalk_bet_alt_dist simp only: parity_simps split: parity.splits)

  moreover have "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G x v \<ge> length (x # p2) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>next_alt_list_parity parity alt_dist.alt_reachable P1 P2 (other_parity parity) G x v\<close>
    obtain p where 
       "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x p v"
       "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G x v = enat (length p - 1)"
      by (auto intro: alt_dist.alt_reachable_dist_2 simp: parity_simps split: parity.splits)
    ultimately have "length p - 1 < length (x # p2) - 1"
      by auto 
    hence "length (p1 @ p) - 1 < length (p1 @ x # p2) - 1"
      by auto

    have "alt_dist.alt_vwalk_bet P1 P2 Odd G u ((p1 @ [x]) @ (tl p)) v"
      using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close> 
            \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x p v\<close>
      apply(intro alt_vwalk_bet_append_3)
      apply(auto )
      apply(cases p)
      apply (auto simp: parity_simps split: parity.splits)
      apply (meson alt_dist.alt_vwalk_bet_nonempty')
      apply (meson alt_dist.alt_vwalk_bet_nonempty')
      apply (metis alt_dist.alt_vwalk_betE list.sel(1) vwalk_bet_def)
      by (metis alt_dist.alt_vwalk_betE list.sel(1) vwalk_bet_def)

    moreover have "p = x # (tl p)"
      using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x p v\<close> 
      by (fastforce dest!: alt_dist.hd_of_alt_vwalk_bet simp: parity_simps split: parity.splits)
    ultimately have "alt_dist.alt_distance P1 P2 Odd G u v \<le> length (p1 @ p) -1"
      apply(intro alt_dist.alt_vwalk_bet_alt_dist)
      by auto[1]
    moreover have "alt_dist.alt_distance P1 P2 Odd G u v = length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u (p1 @ x # p2) v\<close>
      by (rule alt_dist.alt_shortest_path_dist)
    ultimately show ?case
      using \<open>length (p1 @ p) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G x v \<le> length (x # p2) - 1"
    using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x (x # p2) v\<close>
    by (auto intro!: alt_dist.alt_vwalk_bet_alt_dist simp only: parity_simps split: parity.splits)
  ultimately show ?case
    apply (intro exI[where x = parity])
    using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
    using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x (x # p2) v\<close>
    by (auto simp add: alt_dist.alt_shortest_path_def parity_simps split: parity.splits)
qed

lemma alt_shortest_path_split_alt_distance:
  "\<lbrakk>alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow> 
    (\<exists>parity'. alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance P1 P2 parity G u v)"
proof(goal_cases)
  case 1
  then show ?case
  proof(cases parity)
    case Even
    then show ?thesis
      using alt_shortest_path_split_1[OF 1[simplified Even]]
      apply (auto dest!: alt_dist.alt_shortest_path_dist)
      by (metis "1" Nat.add_diff_assoc alt_dist.alt_shortest_path_dist enat_ord_simps(1) le_add1 length_Cons length_append plus_1_eq_Suc)
  next
    case Odd
    then show ?thesis
      using alt_shortest_path_split_2[OF 1[simplified Odd]]
      apply (auto dest!: alt_dist.alt_shortest_path_dist)
      by (metis "1" Nat.add_diff_assoc alt_dist.alt_shortest_path_dist enat_ord_simps(1) le_add1 length_Cons length_append plus_1_eq_Suc)
  qed
qed


lemma shortest_path_split_distance':
  "\<lbrakk>x \<in> set p; alt_dist.alt_shortest_path P1 P2 parity G u p v\<rbrakk> \<Longrightarrow> (\<exists>parity'. alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance P1 P2 parity G u v)"
  apply(subst (asm) in_set_conv_decomp_last)
  by (auto simp: alt_shortest_path_split_alt_distance)

lemma alt_shortest_path_exists:
  assumes "alt_dist.alt_reachable P1 P2 parity G u v"
  obtains p where "alt_dist.alt_shortest_path P1 P2 parity G u p v"
  using assms 
  by (force elim!: alt_dist.alt_reachable_dist_2 simp: alt_dist.alt_shortest_path_def)

lemma alt_shortest_path_exists_2:
  assumes "alt_dist.alt_distance P1 P2 parity G u v < \<infinity>"
  obtains p where "alt_dist.alt_shortest_path P1 P2 parity G u p v"
  using assms 
  by (force dest!: alt_dist.alt_dist_reachable elim!: alt_shortest_path_exists simp: alt_dist.alt_shortest_path_def)

lemma not_distinct_props: 
  "\<not>distinct xs \<Longrightarrow> (\<And>x1 x2 xs1 xs2 xs3. \<lbrakk>xs = xs1 @ x1# xs2 @ x2 # xs3; x1 = x2\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  using not_distinct_decomp
  by fastforce

datatype 'a labelled_vtx = Vtx (label: "parity") (vtx: "'a")

lemma alt_vwalk_bet_vertex_decompE_1:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys) v"
  obtains parity q r where
    "(xs @ y # ys) = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "alt_dist.alt_vwalk_bet P1 P2 parity G u q y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G y r v"
  using assms
  by (smt (verit, best) alt_vwalk_bet_append_1 append_butlast_last_cancel list.sel(3) snoc_eq_iff_butlast')

lemma alt_vwalk_bet_vertex_decompE_1_test:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 parity' G u (xs @ y # ys) v" "parity' = Even"
  obtains parity q r where
    "(xs @ y # ys) = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "alt_dist.alt_vwalk_bet P1 P2 parity G u q y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G y r v"
  using assms
  by (smt (verit, best) alt_vwalk_bet_append_1 append_butlast_last_cancel list.sel(3) snoc_eq_iff_butlast')

lemma alt_vwalk_bet_vertex_decompE_2:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ y # ys) v"
  obtains parity q r where
    "(xs @ y # ys) = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "alt_dist.alt_vwalk_bet P1 P2 parity G u q y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G y r v"
  using assms
  by (smt (verit, del_insts) alt_vwalk_bet_appendE_1' append_butlast_last_cancel list.sel(3) snoc_eq_iff_butlast')

lemma True_imp: "P \<Longrightarrow> (x = x \<longrightarrow> P)"
  by auto

lemma True_imp_2: "P \<Longrightarrow> (True \<longrightarrow> P)"
  by auto

lemma False_imp: "True \<Longrightarrow> (Even = Odd \<longrightarrow> P)"
  by auto

lemma False_imp_2: "True \<Longrightarrow> (Odd = Even \<longrightarrow> P)"
  by auto

lemma closed_alt_vwalk_bet_decomp_1:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys @ y # zs) v"
  shows
    "\<exists>parity parity' parity''.
    alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y \<and>
    next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y \<and>
    next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v \<and>
    (({# parity,parity',parity'' #} = {# Odd, Odd, Even #}) \<or> 
     ({# parity,parity',parity'' #} = {# Even, Even, Even #}))"
  using assms
  apply -
  apply(erule alt_vwalk_bet_vertex_decompE_1)
  subgoal for parity q r
    apply(cases parity)
    subgoal apply(rule exI[where x = Even])
      apply (simp only: )
      apply(simp only: parity_simps split: parity.splits)
      subgoal
        apply(rule conjI)
        subgoal apply(rule True_imp_2)
          apply(erule alt_vwalk_bet_vertex_decompE_1[where xs = "y # ys", simplified])
            by(((rule conjI)+)?; (simp_all only: parity_simps)?; (split parity.splits)?; metis add_mset_commute parity.simps)+
        subgoal by force
        done
      subgoal by force
      done
    subgoal apply(rule exI[where x = Odd])
      apply (simp only: )
      apply(simp only: parity_simps split: parity.splits)
      subgoal by force
      subgoal
        apply(rule conjI)
        subgoal apply(rule False_imp_2) by force
        subgoal apply(rule True_imp_2)
          apply(rule conjI)
          subgoal apply(rule False_imp_2) by metis
          subgoal
            apply (rule True_imp_2)
            apply(erule alt_vwalk_bet_vertex_decompE_2[where xs = "y # ys", simplified])
            subgoal for parity' q' r'
              apply(cases parity')
              subgoal apply(rule exI[where x = Even])
                by((simp_all only: parity_simps)?; split parity.splits; metis add_mset_commute parity.simps)+
              subgoal apply(rule exI[where x = Odd])
                by((simp_all only: parity_simps)?; split parity.splits; metis add_mset_commute parity.simps)+
              done
            done
          done
        done
      done
    done
  done

lemma closed_alt_vwalk_bet_decompE_1:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys @ y # zs) v"
  obtains parity parity' parity'' where
    "alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y"
    "next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v"
    "(({# parity,parity',parity'' #} = {# Odd, Odd, Even #}) \<or> 
     ({# parity,parity',parity'' #} = {# Even, Even, Even #}))"
  using closed_alt_vwalk_bet_decomp_1[OF assms]
  by auto

lemma closed_alt_vwalk_bet_decompE_1':
  "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys @ y # zs) v \<Longrightarrow>
   \<lbrakk>\<And>parity parity' parity''.
     \<lbrakk>alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y;
      next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y;
      next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v;
      (({# parity,parity',parity'' #} = {# Odd, Odd, Even #}) \<or> 
       ({# parity,parity',parity'' #} = {# Even, Even, Even #}))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using closed_alt_vwalk_bet_decompE_1
  by metis

lemma three_parity_crunch_1[case_names EEE OOE OEO EOO]:
  "({# parity,parity',parity'' #} = {# Odd, Odd, Even #}) \<or> 
       ({# parity,parity',parity'' #} = {# Even, Even, Even #}) \<Longrightarrow>
       \<lbrakk>\<lbrakk>parity = Even; parity' = Even; parity'' = Even\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Odd; parity' = Odd; parity'' = Even\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Odd; parity' = Even; parity'' = Odd\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Even; parity' = Odd; parity'' = Odd\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (auto simp: add_mset_commute)
  apply (smt (verit, del_insts) add_eq_conv_diff add_mset_remove_trivial parity.exhaust single_eq_single)
  by (metis add_mset_eq_single add_mset_remove_trivial diff_union_swap)

lemma closed_alt_vwalk_bet_decomp_2:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ y # ys @ y # zs) v"
  shows
    "\<exists>parity parity' parity''.
    alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y \<and>
    next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y \<and>
    next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v \<and>
    (({# parity,parity',parity'' #} = {# Odd, Odd, Odd #}) \<or> 
     ({# parity,parity',parity'' #} = {# Even, Odd, Even #}))"
  using assms
  apply -
  apply(erule alt_vwalk_bet_vertex_decompE_2)
  subgoal for parity q r
    apply(cases parity)
    subgoal apply(rule exI[where x = Even])
      apply (simp only: parity_simps)
      apply(split parity.splits)
      apply(rule conjI)
      subgoal apply(rule True_imp)
        apply(split parity.splits)
        apply(rule conjI)
        subgoal apply (rule True_imp)
          apply (simp split: parity.splits)
          apply(erule alt_vwalk_bet_vertex_decompE_2[where xs = "y # ys", simplified])
          by((simp_all only: parity_simps)?; split parity.splits; metis add_mset_commute parity.simps)+
        subgoal by blast
        done
      subgoal by blast
      done
    subgoal apply(rule exI[where x = Odd])
      apply (simp only: parity_simps)
      apply(split parity.splits)
      apply(rule conjI)
      subgoal 
        by((simp_all only: parity_simps)?; split parity.splits; metis add_mset_commute parity.simps)+
      apply(rule True_imp)
      apply(simp)
      apply(erule alt_vwalk_bet_vertex_decompE_1[where xs = "y # ys", simplified])
      subgoal for parity' q' r'
        apply(cases parity')
        subgoal apply(rule exI[where x = Even])
          by((simp_all only: parity_simps)?; split parity.splits; metis add_mset_commute parity.simps)+
        subgoal apply(rule exI[where x = Odd])
          by((simp_all only: parity_simps)?; split parity.splits; metis add_mset_commute parity.simps)+
        done
      done
    done
  done

lemma closed_alt_vwalk_bet_decompE_2:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ y # ys @ y # zs) v"
  obtains parity parity' parity'' where
    "alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y"
    "next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v"
    "(({# parity,parity',parity'' #} = {# Odd, Odd, Odd #}) \<or> 
     ({# parity,parity',parity'' #} = {# Even, Odd, Even #}))"
  using closed_alt_vwalk_bet_decomp_2[OF assms]
  by auto

lemma three_parity_crunch_2[case_names OOO EEO EOE OEE]:
  "({# parity,parity',parity'' #} = {# Odd, Odd, Odd#}) \<or>
   ({#parity,parity',parity'' #} = {# Even, Odd, Even #}) \<Longrightarrow>
       \<lbrakk>\<lbrakk>parity = Odd; parity' = Odd; parity'' = Odd\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Even; parity' = Even; parity'' = Odd\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Even; parity' = Odd; parity'' = Even\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Odd; parity' = Even; parity'' = Even\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (auto simp: add_mset_commute)
  apply (smt (verit, best) add_eq_conv_ex add_mset_eq_singleton_iff parity.exhaust parity.simps(2))
  by (smt (verit, del_insts) add_eq_conv_diff add_mset_remove_trivial parity.exhaust single_eq_single)

locale labelled_alt_dist = alt_dist P1 P2 for P1 P2::"'a labelled_vtx \<times> 'a labelled_vtx \<Rightarrow> bool"
begin

(*lemma split_alt_vwalk:
  "alt_vwalk_bet parity dG v1 (p1 @ v2 # p2) v3 \<Longrightarrow> alt_vwalk_bet parity dG v2 (v2 # p2) v3"
  unfolding vwalk_bet_def
proof (induction p1)
  case (Cons v p1)
  then show ?case 
    by (auto intro: append_vwalk_suff[where ?p1.0 = "v1 # p1"] simp add: vwalk_then_in_dVs vwalk_bet_def)
qed auto*)

definition "labelled p =     
    ((\<forall>v \<in> set p. \<forall>label v'. (v = (Vtx label v') \<and> (label = Odd) \<longrightarrow> (\<forall>(u,v)\<in>set (edges_of_vwalk p). P1 (u,v)))) \<and> 
     (\<forall>v \<in> set p. \<forall>label v'. (v = (Vtx label v') \<and>  (label = Even) \<longrightarrow> (\<forall>(u,v)\<in>set (edges_of_vwalk p). P2 (u,v)))))"

(*lemma labelledE: 
  "labelled p \<Longrightarrow> 
     \<lbrakk>\<And>label v' x. 
         \<lbrakk>(Vtx label v') \<in> set p; (x,(Vtx label v'))\<in>set (edges_of_vwalk p)\<rbrakk> \<Longrightarrow> (label = Odd) \<longleftrightarrow> P1 (x,v) \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (auto simp: labelled_def split: labelled_vtx.splits parity.splits)
  by blast
*)

definition "op_on es = (\<forall>e \<in> set es. P1 e \<longleftrightarrow> \<not> P2 e)"

lemma op_onE: "op_on es \<Longrightarrow> \<lbrakk>\<lbrakk>\<And>e. e \<in> set es \<Longrightarrow> P1 e \<longleftrightarrow> \<not> P2 e\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (auto simp: op_on_def)

lemma labelledE: 
  "labelled p \<Longrightarrow>
     \<lbrakk>\<lbrakk>\<And>label v' x. 
         (\<lbrakk>(Vtx label v') \<in> set p; (x,(Vtx label v'))\<in>set (edges_of_vwalk p); label = Odd\<rbrakk> \<Longrightarrow> P1 (x,(Vtx label v')));
       \<And>label v' x.
         (\<lbrakk>(Vtx label v') \<in> set p; (x,(Vtx label v'))\<in>set (edges_of_vwalk p); (label = Even)\<rbrakk> \<Longrightarrow> P2 (x,(Vtx label v')))\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  by (auto simp: labelled_def elim!: op_onE split: labelled_vtx.splits parity.splits)


lemma labelled_op_works:
  assumes "labelled p" "op_on (edges_of_vwalk p)" 
          "(u,v) \<in> set (edges_of_vwalk p)" 
          "(w,v) \<in> set (edges_of_vwalk p)" "P1 (u,v)"
    shows "\<not> P2 (w,v)"
proof(cases v)
  case (Vtx label vtx_name)
  then show ?thesis
    using assms
    apply(cases label)
    subgoal
      apply(erule labelledE)
      subgoal
        using assms
        apply (auto elim!: op_onE)
      by (meson v_in_edge_in_vwalk(2))
    done
    subgoal
      apply(erule labelledE)
      subgoal
        using assms
        apply (auto elim!: op_onE)
        by (meson v_in_edge_in_vwalk(2))
    done
  done
qed

definition "on_path parity p pre v suff= (p = pre @ (Vtx parity v) # suff)"

lemma on_pathE: "on_path parity p pre v suff \<Longrightarrow> (p = pre @ (Vtx parity v) # suff \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: on_path_def)

lemma on_pathI: "(p = pre @ (Vtx parity v) # suff \<Longrightarrow> on_path parity p pre v suff)"
  by (auto simp: on_path_def)

(*lemma
  assumes "on_path parity' p pre w suff" "labelled p" "alt_vwalk_bet Even G u p v"
  shows "alt_vwalk_bet parity' G u (pre @ [(Vtx parity' w)]) (Vtx parity' w)"
proof(cases parity')
  case Even
  obtain parity'' where parity'': "alt_vwalk_bet parity'' G u (pre @ [Vtx Even w]) (Vtx Even w)"
    using assms
    apply(elim on_pathE)
    by (metis Even alt_vwalk_bet_vertex_decompE_1)
  moreover have "parity'' = Odd"
  proof(rule ccontr, goal_cases)
    case 1
    hence "parity'' = Even"
      using parity.exhaust
      by auto
    hence "odd (length (pre @ [Vtx Even w]))"
      using parity''
      by (auto elim!: alt_vwalk_betE simp: parity_simps)
    hence "even (length (edges_of_vwalk (pre @ [Vtx Even w])))"
      by (simp add: edges_of_vwalk_length)
    moreover have "alt_list P1 P2 (edges_of_vwalk (pre @ [Vtx Even w]))"
      using parity''
      by (auto elim!: alt_vwalk_betE simp: parity_simps)
    moreover have "(edges_of_vwalk (pre @ [Vtx Even w])) \<noteq> []"
    proof(cases pre)
      case Nil
      then show ?thesis
    using assms
    apply(elim on_pathE labelledE alt_vwalk_betE)
    apply simp
    sledgehammer


    next
      case (Cons a list)
      then show ?thesis sorry
    qed
    moreover have "last (edges_of_vwalk (pre @ [Vtx Even w])) = (last pre, Vtx Even w)"
      by (metis One_nat_def Suc_1 calculation(3) edges_of_vwalk.simps(2) edges_of_vwalk.simps(3) 
                edges_of_vwalk_append_3 last_snoc le_add1 list.size(3) list_sing_conv(1) not_less_eq_eq plus_1_eq_Suc)
    ultimately have "P2 (last pre, Vtx Even w)"
      by (metis Alternating_Lists.alternating_list_even_last linorder_not_less list.size(3) pos2)
    then show ?case sorry
  qed
  then show ?thesis
    using assms
    apply(elim on_pathE)
    apply auto
next
  case Odd
  then show ?thesis sorry
qed
*)
end

lemma alt_shortest_path_distinct:
  "\<lbrakk>labelled_alt_dist.op_on P1 P2 (edges_of_vwalk p); labelled_alt_dist.labelled P1 P2 p;
    alt_dist.alt_shortest_path P1 P2 parity G u p v\<rbrakk>
    \<Longrightarrow> distinct p"
  apply(erule alt_dist.alt_shortest_path_props)
  apply(rule ccontr)
  apply(erule not_distinct_props)
proof(goal_cases)
  case (1 x1 x2 xs1 xs2 xs3)
  note alt_vwalk_bet_append_2_simps=last_append list.simps if_False last.simps if_True HOL.refl

  hence "alt_dist.alt_vwalk_bet P1 P2 parity G u (xs1 @ x2 # xs3) v"
  proof(cases parity)
    case Even
    thus ?thesis
      using 1
    proof(simp_all only: parity.simps, elim closed_alt_vwalk_bet_decompE_1 three_parity_crunch_1, goal_cases)
      case EEE: (1 parity parity' parity'')
      then show ?case
        by (fastforce simp: parity_simps parity.simps 
              dest!:
                   alt_vwalk_bet_append_2[where ?p1.0 = "xs1 @ [x2]", simplified alt_vwalk_bet_append_2_simps])
    next
      case OOE: (2 parity parity' parity'')
      hence "P1 (last (xs1), x2)"
        using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (xs1 @ [x2]) x2\<close> \<open>parity = Odd\<close>
        apply(elim alt_dist.alt_vwalk_betE)
        apply(auto simp: parity_simps split: parity.splits)
        by (metis alt_list_split_1 alt_list_step dvd_triv_left edges_of_vwalk.simps(3)
                  edges_of_vwalk_append_3 edges_of_vwalk_length length_greater_0_conv odd_pos
                  odd_two_times_div_two_nat)+
      moreover have "(last (xs1), x1) \<in> set (edges_of_vwalk p)"
        using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (xs1 @ [x2]) x2\<close> \<open>parity = Odd\<close>
        apply(elim alt_dist.alt_vwalk_betE)
        apply(auto simp: parity_simps split: parity.splits)
        by (metis OOE(12) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 in_set_conv_decomp length_greater_0_conv odd_pos)
      moreover have "P2 (last (x2 # xs2), x2)" (is ?g1)
                     "(last (xs2), x1) \<in> set (edges_of_vwalk p)" (is ?g2)
      proof-
        have *:"last (edges_of_vwalk (x2 # xs2 @ [x2])) = (last xs2, x2)" if "xs2 \<noteq> []"
          using that
          apply(auto simp only: neq_Nil_conv)
          by (metis Cons_eq_appendI edges_of_vwalk.simps(2) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 last_snoc that)
        thus ?g1
          using \<open> next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G x2 (x2 # xs2 @ [x2]) x2\<close>
            \<open>parity = Odd\<close>  \<open>parity' = Odd\<close> \<open>x1 = x2\<close>
          apply(auto simp: parity_simps split: parity.splits elim!: )
           apply (metis alt_dist.alt_vwalk_betE alt_list_step edges_of_vwalk.simps(3))
          using Alt_Dist.alternating_list_odd_last by fastforce
        have **: "p = (xs1 @ [x2]) @ xs2 @ x2 # xs3"
          using \<open>p = xs1 @ x2 # xs2 @ x2 # xs3\<close> 
          by auto
        have ***: "x2 # xs2 @ x2 # xs3 = (x2 # xs2 @ [x2]) @ xs3"
          by auto
        show ?g2
          apply(cases xs1)
          subgoal using * \<open>x1 = x2\<close> apply (auto simp: **)
            by (metis Cons_eq_appendI OOE(12) append_Nil calculation(2) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 in_set_conv_decomp last.simps) 
          subgoal
            using * \<open>x1 = x2\<close> 
            apply(subst **)+
            apply (subst edges_of_vwalk_append_3)
             apply simp +
            apply(subst ***)
            apply (subst edges_of_vwalk_append_3)
             apply auto
            (*by (smt (verit) "**" Cons_eq_appendI OOE(2) OOE(3) \<open>P2 (last (x2 # xs2), x2)\<close> 
                            append_eq_Cons_conv append_eq_append_conv2 append_self_conv calculation(1)
                            calculation(2) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 
                            in_set_conv_decomp labelled_alt_dist.labelled_op_works last_ConsL
                            last_in_set last_snoc list.discI)*)
            sorry
          done
      qed
      moreover obtain label vtx_name where "x1 = Vtx label vtx_name"
        by (cases x1)
      ultimately show ?case
        apply (cases label)
        using labelled_alt_dist.labelled_op_works[OF OOE(3,2)] OOE(12,13)
        apply (metis OOE(3) labelled_alt_dist.labelledE v_in_edge_in_vwalk(2))+
        by (smt (verit) Cons_eq_appendI OOE(12) OOE(3) OOE(6) OOE(8) append.assoc append_Nil 
                edges_of_vwalk.simps(3) edges_of_vwalk_append_3 in_set_conv_decomp 
                labelled_alt_dist.labelledE labelled_alt_dist.op_on_def list.discI v_in_edge_in_vwalk(2))
    next
      case OEO: (3 parity parity' parity'')
      then show ?case
        by (fastforce simp: parity_simps parity.simps 
              dest!:
                   alt_vwalk_bet_append_2[where ?p1.0 = "xs1 @ [x2]", simplified alt_vwalk_bet_append_2_simps])
    next
      case EOO: (4 parity parity' parity'')
      hence "P2 (last (xs1), x2)"
        using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (xs1 @ [x2]) x2\<close> \<open>parity = Even\<close>
        apply(elim alt_dist.alt_vwalk_betE)
        apply(auto simp: parity_simps split: parity.splits)
        sorry
      moreover have "(last (xs1), x1) \<in> set (edges_of_vwalk p)"
        using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (xs1 @ [x2]) x2\<close> \<open>parity = Even\<close>
        apply(elim alt_dist.alt_vwalk_betE)
        apply(auto simp: parity_simps split: parity.splits)
        sorry
      moreover have "P1 (last (x2 # xs2), x2)" (is ?g1)
                     "(last (xs2), x1) \<in> set (edges_of_vwalk p)" (is ?g2)
      proof-
        have *:"last (edges_of_vwalk (x2 # xs2 @ [x2])) = (last xs2, x2)" if "xs2 \<noteq> []"
          using that
          apply(auto simp only: neq_Nil_conv)
          by (metis Cons_eq_appendI edges_of_vwalk.simps(2) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 last_snoc that)
        thus ?g1
          using \<open> next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G x2 (x2 # xs2 @ [x2]) x2\<close>
            \<open>parity = Even\<close>  \<open>parity' = Odd\<close> \<open>x1 = x2\<close>
          apply(auto simp: parity_simps split: parity.splits elim!: )
           apply (metis alt_dist.alt_vwalk_betE alt_list_step edges_of_vwalk.simps(3))
          using Alt_Dist.alternating_list_odd_last by fastforce
        have **: "p = (xs1 @ [x2]) @ xs2 @ x2 # xs3"
          using \<open>p = xs1 @ x2 # xs2 @ x2 # xs3\<close> 
          by auto
        have ***: "x2 # xs2 @ x2 # xs3 = (x2 # xs2 @ [x2]) @ xs3"
          by auto
        show ?g2
          apply(cases xs1)
          subgoal using * \<open>x1 = x2\<close> apply (auto simp: **)
            by (metis Cons_eq_appendI EOO(12) append_Nil calculation(2) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 in_set_conv_decomp last.simps) 
          subgoal
            using * \<open>x1 = x2\<close> 
            apply(subst **)+
            apply (subst edges_of_vwalk_append_3)
             apply simp +
            apply(subst ***)
            apply (subst edges_of_vwalk_append_3)
             apply auto
            by (smt (verit) "**" "***" Cons_eq_appendI EOO(2) EOO(3) \<open>P1 (last (x2 # xs2), x2)\<close> 
                            append.assoc append_eq_Cons_conv append_eq_append_conv calculation(1) 
                            calculation(2) diff_Suc_1 edges_of_vwalk.simps(3) edges_of_vwalk_append_3 
                            edges_of_vwalk_length in_set_conv_decomp labelled_alt_dist.labelled_op_works 
                            last_ConsL last_in_set last_snoc length_Cons list.inject list.size(3))
            (*by (smt (verit) "**" Cons_eq_appendI OOE(2) OOE(3) \<open>P2 (last (x2 # xs2), x2)\<close> 
                            append_eq_Cons_conv append_eq_append_conv2 append_self_conv calculation(1)
                            calculation(2) edges_of_vwalk.simps(3) edges_of_vwalk_append_3 
                            in_set_conv_decomp labelled_alt_dist.labelled_op_works last_ConsL
                            last_in_set last_snoc list.discI)*)
          done
      qed
      moreover obtain label vtx_name where "x1 = Vtx label vtx_name"
        by (cases x1)
      ultimately show ?case
        apply (cases label)
        using labelled_alt_dist.labelled_op_works[OF EOO(3,2)] EOO(12,13)
        apply (metis edges_of_vwalk.simps(3) edges_of_vwalk_append_subset last_ConsL last_ConsR list.set_intros(1) self_append_conv2 subsetD)
        by (metis EOO(12) EOO(6) EOO(9) labelled_alt_dist.labelledE v_in_edge_in_vwalk_gen(2)
                   \<open>\<And>w v u. \<lbrakk>(u, v) \<in> set (edges_of_vwalk (xs1 @ x2 # xs2 @ x2 # xs3));
                              (w, v) \<in> set (edges_of_vwalk (xs1 @ x2 # xs2 @ x2 # xs3)); P1 (u, v)\<rbrakk>
                         \<Longrightarrow> \<not> P2 (w, v)\<close>)
    qed
  next
    case Odd
    then show ?thesis sorry
  qed

  hence "alt_dist.alt_distance P1 P2 parity G u v \<le> length (xs1 @ x2 # xs3) - 1"
    using alt_dist.alt_vwalk_bet_alt_dist 
    by force
  moreover have "length (xs1 @ x2 # xs3) < length p"
    by(auto simp: \<open> p = xs1 @ x1 # xs2 @ x2 # xs3\<close>)
  ultimately show ?case
    using \<open>alt_dist.alt_distance P1 P2 parity G u v = enat (length p - 1)\<close>
    by auto
qed

lemma diet_eq': "\<lbrakk>\<And>p. \<lbrakk>alt_dist.alt_shortest_path P1 P2 parity G' u p v\<rbrakk>
                   \<Longrightarrow> alt_dist.alt_shortest_path P1 P2 parity G u (map f p) v\<rbrakk> \<Longrightarrow>
                   alt_dist.alt_distance P1 P2 parity G u v \<le> alt_dist.alt_distance P1 P2 parity G' u v"
  apply(auto simp: alt_dist.alt_shortest_path_def)
  by (metis One_nat_def Orderings.order_eq_iff order.strict_implies_order alt_dist.alt_reachable_dist
            alt_dist.alt_reachable_dist_2 alt_dist.alt_unreachable_dist)

context alt_dist
begin
lemma alt_vwalk_bet_singleton[simp]: "v \<in> dVs G \<Longrightarrow> alt_vwalk_bet Even G v [v] v"
  by (auto intro!: alt_vwalk_betI simp: alt_list_empty parity_simps split: parity.splits)

end

declare alt_dist.alt_vwalk_bet_singleton[simp]

lemma even_alt_distance_0:
  "(u = v \<and> v \<in> dVs G) \<longleftrightarrow> alt_dist.alt_distance P1 P2 Even G u v = 0"
proof(safe, goal_cases)
  case 1
  hence "alt_dist.alt_vwalk_bet P1 P2 Even G v [v] v"
    by auto
  moreover have "length [v] = 1"
    by auto
  ultimately show ?case
    using zero_enat_def
    by(auto dest!: alt_dist.alt_vwalk_bet_alt_dist simp: )
next
  case 2
  hence "alt_dist.alt_distance P1 P2 Even G u v < \<infinity>"
    by auto
  then obtain p where "alt_dist.alt_shortest_path P1 P2 Even G u p v"
    by(erule alt_shortest_path_exists_2)
  hence "length p = 1" "vwalk_bet G u p v"
    using \<open>alt_dist.alt_distance P1 P2 Even G u v = 0\<close>
    apply (auto simp: alt_dist.alt_shortest_path_def)
    apply (metis diff_Suc_Suc diff_zero enat_0_iff(2) alt_dist.hd_of_alt_vwalk_bet length_Cons)
    by(auto elim!: elim!: alt_dist.alt_vwalk_betE)
  then obtain x where "p = [x]"
    by (auto simp: length_Suc_conv)
  then have "x = u" "x = v" "x \<in> dVs G"
    using \<open>vwalk_bet G u p v\<close> hd_of_vwalk_bet last_of_vwalk_bet
    by (fastforce simp: vwalk_bet_in_vertices)+
  then show "u = v"  "v \<in> dVs G"
    by auto
qed

lemma even_alt_distance_neighbourhood':
  assumes "v \<in> neighbourhood G u" "P2 (u,v)" 
  shows "alt_dist.alt_distance P1 P2 Even G x v \<le> 
          alt_dist.alt_distance P1 P2 Odd G x u + 1"
  using assms
proof-
  have "alt_dist.alt_distance P1 P2 Even G x v \<le>
           alt_dist.alt_distance P1 P2 Odd G x u +
             next_alt_list_parity Odd alt_dist.alt_distance P1 P2 Odd G u v"
    by(rule alt_triangle_ineq_2)
  moreover have "alt_dist.alt_distance P2 P1 Odd G u v \<le> 1"
    using assms
    by (auto intro!: odd_alt_distance_neighbourhood simp add: parity_simps)

  ultimately show ?thesis
    using order_subst1 
    by(fastforce simp add: parity_simps split: parity.splits)
qed

lemma odd_alt_distance_neighbourhood':
  assumes "v \<in> neighbourhood G u" "P1 (u,v)" 
  shows "alt_dist.alt_distance P1 P2 Odd G x v \<le> 
          alt_dist.alt_distance P1 P2 Even G x u + 1"
  using assms
proof-
  have "alt_dist.alt_distance P1 P2 Odd G x v \<le>
           alt_dist.alt_distance P1 P2 Even G x u +
             next_alt_list_parity Even alt_dist.alt_distance P1 P2 (other_parity Even) G u v"
    by(rule alt_triangle_ineq_1)
  moreover have "alt_dist.alt_distance P1 P2 Odd G u v \<le> 1"
    using assms
    by (auto intro!: odd_alt_distance_neighbourhood simp add: parity_simps)

  ultimately show ?thesis
    using order_subst1 
    by(fastforce simp add: parity_simps split: parity.splits)
qed

lemma Suc_le_length_iff_2:
  "(Suc n \<le> length xs) = (\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys)"
  by (metis Suc_le_D Suc_le_mono length_Suc_conv_rev)

context alt_dist
begin

lemma alt_vwalk_bet_last[simp]: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v \<Longrightarrow> last p = v"
    apply -
    apply(erule alt_dist.alt_vwalk_betE)
    by auto

lemma alt_vwalk_bet_hd[simp]: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v \<Longrightarrow> hd p = u"
    apply -
    apply(erule alt_dist.alt_vwalk_betE)
    by auto

lemma alt_shortest_path_last[simp]: "alt_shortest_path parity G u p v \<Longrightarrow> last p = v"
    by auto

lemma alt_shortest_path_hd[simp]: "alt_shortest_path parity G u p v \<Longrightarrow> hd p = u"
    by auto
end

declare alt_dist.alt_vwalk_bet_last[simp]
declare alt_dist.alt_vwalk_bet_hd[simp]
declare alt_dist.alt_shortest_path_last[simp]
declare alt_dist.alt_shortest_path_hd[simp]

lemma even_alt_distance_parent: 
 "\<lbrakk>alt_dist.alt_distance P1 P2 Even G u v < \<infinity>; u \<noteq> v\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance P1 P2 Even G u v = alt_dist.alt_distance P1 P2 Odd G u w + 1 \<and>
         v \<in> neighbourhood G w \<and> P2 (w, v)"
proof(goal_cases)
  case 1
  then obtain p where p: "alt_dist.alt_shortest_path P1 P2 Even G u p v"
    by(force dest!: alt_dist.alt_dist_reachable elim!: alt_shortest_path_exists)
  hence "length p \<ge> 2"
    using \<open>u\<noteq>v\<close> 
    by(auto dest!: alt_dist.alt_shortest_path_vwalk 
               simp: Suc_le_length_iff eval_nat_numeral parity_simps 
               elim!: alt_dist.alt_vwalk_betE elim: vwalk_betE split: parity.splits)
  moreover have "last p = v"
    using p
    by auto
  ultimately obtain p' w where "p = p' @ [w, v]"
    by(auto simp: Suc_le_length_iff_2 eval_nat_numeral)

  obtain parity where "alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w"
    using \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close>
    by (auto dest: alt_shortest_path_split_1 simp: \<open>p = p' @ [w, v]\<close> parity_simps split: parity.splits)

  moreover have "parity = Odd"
  proof(rule ccontr, goal_cases)
    case 1
    hence "parity = Even" using parity.exhaust by auto
    hence "odd (length (p' @ [w]))"
      using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w\<close>
      by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
    moreover have "odd (length p)"
      using p 
      by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
    hence "even (length (p' @ [w]))"
      by (auto simp: \<open>p= p' @ [w, v]\<close>)
    ultimately show ?case
      by auto
  qed

  hence "alt_dist.alt_distance P1 P2 (other_parity parity) G u v = alt_dist.alt_distance P1 P2 parity G u w + 1"
    using \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close> \<open>p = p' @ [w,v]\<close>
    apply (auto dest!: alt_dist.alt_shortest_path_dist simp: eSuc_plus_1 parity_simps)
    by (metis alt_dist.alt_shortest_path_dist calculation diff_Suc_1 length_append_singleton)
  moreover have "v \<in> neighbourhood G w"
    using \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close> \<open>p = p' @ [w,v]\<close> vwalk_bet_suffix_is_vwalk_bet
    by(fastforce elim: alt_dist.alt_vwalk_betE
                 simp: \<open>p = p' @ [w,v]\<close> 
                 dest!: alt_dist.alt_shortest_path_vwalk)
  moreover have "P2 (w, v)"
    using \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close> \<open>p = p' @ [w,v]\<close> vwalk_bet_suffix_is_vwalk_bet
    apply(auto elim!: alt_dist.alt_vwalk_betE  alt_dist.alt_shortest_path_props
                 simp: \<open>p = p' @ [w,v]\<close> parity_simps) 
    by (smt (verit, best) alt_list_split_1 alt_list_step dvd_triv_left edges_of_vwalk.simps(3)
                          edges_of_vwalk_append_3 edges_of_vwalk_length length_greater_0_conv odd_pos
                          odd_two_times_div_two_nat) 
  ultimately show ?thesis
    by (auto simp: \<open>parity = Odd\<close> parity_simps)
qed

lemma odd_alt_distance_parent: 
 "\<lbrakk>alt_dist.alt_distance P1 P2 Odd G u v < \<infinity>; u \<noteq> v\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance P1 P2 Odd G u v = alt_dist.alt_distance P1 P2 Even G u w + 1 \<and>
         v \<in> neighbourhood G w \<and> P1 (w, v)"
proof(goal_cases)
  case 1
  then obtain p where p: "alt_dist.alt_shortest_path P1 P2 Odd G u p v"
    by(force dest!: alt_dist.alt_dist_reachable elim!: alt_shortest_path_exists)
  hence "length p \<ge> 2"
    using \<open>u\<noteq>v\<close> 
    by(auto dest!: alt_dist.alt_shortest_path_vwalk 
               simp: Suc_le_length_iff eval_nat_numeral parity_simps 
               elim!: alt_dist.alt_vwalk_betE elim: vwalk_betE split: parity.splits)
  moreover have "last p = v"
    using p
    by auto
  ultimately obtain p' w where "p = p' @ [w, v]"
    by(auto simp: Suc_le_length_iff_2 eval_nat_numeral)

  obtain parity where "alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w"
    using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u p v\<close>
    by (auto dest: alt_shortest_path_split_2 simp: \<open>p = p' @ [w, v]\<close> parity_simps split: parity.splits)

  moreover have "parity = Even"
  proof(rule ccontr, goal_cases)
    case 1
    hence "parity = Odd" using parity.exhaust by auto
    hence "even (length (p' @ [w]))"
      using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w\<close>
      by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
    moreover have "even (length p)"
      using p 
      by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
    hence "odd (length (p' @ [w]))"
      by (auto simp: \<open>p= p' @ [w, v]\<close>)
    ultimately show ?case
      by auto
  qed

  hence "alt_dist.alt_distance P1 P2 (other_parity parity) G u v = alt_dist.alt_distance P1 P2 parity G u w + 1"
    using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u p v\<close> \<open>p = p' @ [w,v]\<close>
    apply (auto dest!: alt_dist.alt_shortest_path_dist simp: eSuc_plus_1 parity_simps)
    by (metis alt_dist.alt_shortest_path_dist calculation diff_Suc_1 length_append_singleton)
  moreover have "v \<in> neighbourhood G w"
    using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u p v\<close> \<open>p = p' @ [w,v]\<close> vwalk_bet_suffix_is_vwalk_bet
    by(fastforce elim: alt_dist.alt_vwalk_betE
                 simp: \<open>p = p' @ [w,v]\<close> 
                 dest!: alt_dist.alt_shortest_path_vwalk)
  moreover have "P1 (w, v)"
    using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u p v\<close> \<open>p = p' @ [w,v]\<close> vwalk_bet_suffix_is_vwalk_bet
    apply(auto elim!: alt_dist.alt_vwalk_betE  alt_dist.alt_shortest_path_props
                 simp: \<open>p = p' @ [w,v]\<close> parity_simps) 
    by (smt (verit) alt_list_split_1 alt_list_step diff_Suc_1 edges_of_vwalk.simps(3) 
                    edges_of_vwalk_append_2 edges_of_vwalk_length length_append_singleton list.discI)
  ultimately show ?thesis
    by (auto simp: \<open>parity = Even\<close> parity_simps)
qed

subsection \<open>Distance from a set of vertices\<close>

context alt_dist
begin

definition "alt_distance_set parity G U v = ( INF u\<in>U. alt_distance parity G u v)"
                                                               
(*TODO: intro rule*)

lemma alt_dist_set_inf: "v \<notin> dVs G \<Longrightarrow> alt_distance_set parity G U v = \<infinity>"
  by(auto simp: alt_distance_set_def INF_eqI alt_dist_inf)

lemma alt_dist_set_mem[intro]: "u \<in> U \<Longrightarrow> alt_distance_set parity G U v \<le> alt_distance parity G u v"
  by (auto simp: alt_distance_set_def wellorder_Inf_le1)
end

lemma even_dist_not_inf'':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Even G U v \<noteq> \<infinity>; u\<in>U; 
    alt_dist.alt_distance P1 P2 Even G u v = alt_dist.alt_distance_set P1 P2 Even G U v\<rbrakk>
    \<Longrightarrow> \<exists>p. alt_dist.alt_vwalk_bet P1 P2 Even G u (u#p) v \<and>
            length p = alt_dist.alt_distance P1 P2 Even G u v \<and>
            (\<forall>p1 w p2. p = p1 @ w # p2 \<and>
                       alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v
                           \<longrightarrow> w \<notin> U)"
proof(goal_cases)
  case main: 1
  then obtain p where "alt_dist.alt_vwalk_bet P1 P2 Even G u (u#p) v"
                      "length p = alt_dist.alt_distance P1 P2 Even G u v"
    by (metis alt_dist.alt_shortest_path_hd alt_dist.alt_reachable_dist alt_dist.alt_shortest_path_dist 
              alt_shortest_path_exists_2 alt_dist.alt_shortest_path_vwalk alt_dist.alt_unreachable_dist 
              append_is_Nil_conv alt_dist.last_of_alt_vwalk_bet' length_tl list.collapse list.discI)

  moreover have "w \<notin> U" if "p = p1 @ w # p2" "alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v" for p1 w p2
  proof(rule ccontr, goal_cases)
    case 1
    have "length (w#p2) < length (u#p)"
      using that
      by auto
    moreover have "alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v"
      using that
      by fastforce
    hence "alt_dist.alt_distance P1 P2 Even G w v \<le> length p2"
      by(auto dest!: alt_dist.alt_vwalk_bet_alt_dist)
    ultimately have "alt_dist.alt_distance_set P1 P2 Even G U v \<le> length p2"
      using 1
      by(auto dest!: alt_dist.alt_dist_set_mem dest: order.trans)
    moreover have "length p \<le> alt_dist.alt_distance_set P1 P2 Even G U v"
      by (simp add: \<open>enat (length p) = alt_dist.alt_distance P1 P2 Even G u v\<close> main(3))
    moreover have " enat (length p2) < eSuc (enat (length p1 + length p2))"
      by auto
    ultimately have False
      using leD
      apply -
      apply(drule dual_order.trans[where c = "enat (length p)"])
      by (fastforce simp: \<open>p = p1 @ w # p2\<close> dest: )+
    then show ?case
      by auto
  qed
  ultimately show ?thesis
    by auto
qed

lemma even_dist_not_inf''':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Even G U v \<noteq> \<infinity>; u\<in>U;
    alt_dist.alt_distance P1 P2 Even G u v = alt_dist.alt_distance_set P1 P2 Even G U v\<rbrakk>
      \<Longrightarrow> \<exists>p. alt_dist.alt_shortest_path P1 P2 Even G u (u#p) v \<and> 
              (\<forall>p1 w p2. p = p1 @ w # p2 \<and> alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v
                           \<longrightarrow> w \<notin> U)"
  apply (simp add: alt_dist.alt_shortest_path_def)
  by (metis even_dist_not_inf'' enat.distinct(1))

lemma odd_dist_not_inf'':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Odd G U v \<noteq> \<infinity>; u\<in>U; 
    alt_dist.alt_distance P1 P2 Odd G u v = alt_dist.alt_distance_set P1 P2 Odd G U v\<rbrakk>
    \<Longrightarrow> \<exists>p. alt_dist.alt_vwalk_bet P1 P2 Odd G u (u#p) v \<and>
            length p = alt_dist.alt_distance P1 P2 Odd G u v \<and>
            (\<forall>p1 w p2. p = p1 @ w # p2 \<and> alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v
                           \<longrightarrow> w \<notin> U)"
proof(goal_cases)
  case main: 1
  then obtain p where "alt_dist.alt_vwalk_bet P1 P2 Odd G u (u#p) v"
                      "length p = alt_dist.alt_distance P1 P2 Odd G u v"
    by (metis alt_dist.alt_shortest_path_hd alt_dist.alt_reachable_dist alt_dist.alt_shortest_path_dist 
              alt_shortest_path_exists_2 alt_dist.alt_shortest_path_vwalk alt_dist.alt_unreachable_dist 
              append_is_Nil_conv alt_dist.last_of_alt_vwalk_bet' length_tl list.collapse list.discI)

  moreover have "w \<notin> U" if "p = p1 @ w # p2" "alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v" for p1 w p2
  proof(rule ccontr, goal_cases)
    case 1
    have "length (w#p2) < length (u#p)"
      using that
      by auto
    moreover have "alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v"
      using that
      by fastforce
    hence "alt_dist.alt_distance P1 P2 Odd G w v \<le> length p2"
      by(auto dest!: alt_dist.alt_vwalk_bet_alt_dist)
    ultimately have "alt_dist.alt_distance_set P1 P2 Odd G U v \<le> length p2"
      using 1
      by(auto dest!: alt_dist.alt_dist_set_mem dest: order.trans)
    moreover have "length p \<le> alt_dist.alt_distance_set P1 P2 Odd G U v"
      by (simp add: \<open>enat (length p) = alt_dist.alt_distance P1 P2 Odd G u v\<close> main(3))
    moreover have " enat (length p2) < eSuc (enat (length p1 + length p2))"
      by auto
    ultimately have False
      using leD
      apply -
      apply(drule dual_order.trans[where c = "enat (length p)"])
      by (fastforce simp: \<open>p = p1 @ w # p2\<close> dest: )+
    then show ?case
      by auto
  qed
  ultimately show ?thesis
    by auto
qed

lemma odd_dist_not_inf''':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Odd G U v \<noteq> \<infinity>; u\<in>U;
    alt_dist.alt_distance P1 P2 Odd G u v = alt_dist.alt_distance_set P1 P2 Odd G U v\<rbrakk>
      \<Longrightarrow> \<exists>p. alt_dist.alt_shortest_path P1 P2 Odd G u (u#p) v \<and> 
              (\<forall>p1 w p2. p = p1 @ w # p2 \<and> alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v
                           \<longrightarrow> w \<notin> U)"
  apply (simp add: alt_dist.alt_shortest_path_def)
  by (metis odd_dist_not_inf'' enat.distinct(1))

(*lemma distance_set_split:
  "\<lbrakk>distance_set G U v \<noteq> \<infinity>; distance_set G U v = distance_set G U w + distance_set G U' v; w \<in> U' \<rbrakk> \<Longrightarrow>
       \<exists>w'\<in>U'. reachable G u w' \<and> distance G u w' = distance G u w \<and>
            reachable G w' v \<and> distance G w' v = distance G w' v"
proof(goal_cases)
  case 1
  hence "distance_set G U' v \<noteq> \<infinity>"
    by (simp add: plus_eq_infty_iff_enat)
  then obtain w' where "w' \<in> U'" "distance_set G U' v = distance G w' v" "reachable G w' v"
    using 1
    by (metis dist_not_inf')
*)

lemma alt_distance_set_union:
  "alt_dist.alt_distance_set P1 P2 parity G (U \<union> V) v \<le> alt_dist.alt_distance_set P1 P2 parity G U v"
  by (simp add: alt_dist.alt_distance_set_def INF_superset_mono)   

lemma lt_lt_infnty: "x < (y::enat) \<Longrightarrow> x < \<infinity>"
  using enat_ord_code(3) order_less_le_trans
  by blast

lemma finite_alt_dist_nempty:
  "alt_dist.alt_distance_set P1 P2 parity G V v \<noteq> \<infinity> \<Longrightarrow> V \<noteq> {}"
  by (auto simp: alt_dist.alt_distance_set_def top_enat_def)

lemma alt_distance_set_wit: 
  assumes "v \<in> V"
  obtains v' where "v' \<in> V" "alt_dist.alt_distance_set P1 P2 parity G V x = alt_dist.alt_distance P1 P2 parity G v' x"
  using assms wellorder_InfI[of "alt_dist.alt_distance P1 P2 parity G v x" "(%v. alt_dist.alt_distance P1 P2 parity G v x) ` V"]
  by (auto simp: alt_dist.alt_distance_set_def image_def dest!: )

lemma alt_distance_set_wit':
  assumes "alt_dist.alt_distance_set P1 P2 parity G V v \<noteq> \<infinity>"
  obtains v' where "v' \<in> V" "alt_dist.alt_distance_set P1 P2 parity G V x = alt_dist.alt_distance P1 P2 parity G v' x"
  using finite_alt_dist_nempty[OF assms]
  by (auto elim: alt_distance_set_wit)

lemma alt_dist_set_not_inf: 
  "alt_dist.alt_distance_set P1 P2 parity G U v \<noteq> \<infinity> 
   \<Longrightarrow> \<exists>u\<in>U. alt_dist.alt_distance P1 P2 parity G u v = alt_dist.alt_distance_set P1 P2 parity G U v"
  using alt_distance_set_wit'
  by metis

lemma alt_dist_not_inf':
  "alt_dist.alt_distance_set P1 P2 parity G U v \<noteq> \<infinity> \<Longrightarrow>
     \<exists>u\<in>U. alt_dist.alt_distance P1 P2 parity G u v = alt_dist.alt_distance_set P1 P2 parity G U v \<and> alt_dist.alt_reachable P1 P2 parity G u v"
  by (metis alt_dist.alt_dist_reachable alt_dist_set_not_inf enat_ord_simps(4))

lemma alt_shortest_path_Parity: 
  "alt_dist.alt_shortest_path P1 P2 parity G u (p1 @[x]) x \<Longrightarrow> of_parity (other_parity parity) (length (p1 @ [x]))"
  by (auto elim!: alt_dist.alt_shortest_path_props alt_dist.alt_vwalk_betE)

lemma alt_distance_on_vwalk:
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 parity G U v = alt_dist.alt_distance P1 P2 parity G u v; u \<in> U;
    alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<rbrakk>
       \<Longrightarrow> \<exists>parity'. alt_dist.alt_distance_set P1 P2 parity' G U x = alt_dist.alt_distance P1 P2 parity' G u x \<and>
                     of_parity (other_parity parity') (length (p1 @ [x]))"
proof(goal_cases)
  case assms: 1
  moreover have 
    "\<exists>parity'. alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance_set P1 P2 parity' G U x \<and>
               of_parity (other_parity parity') (length (p1 @ [x]))"
  proof(rule ccontr, goal_cases)
    case alt_dist_gt: 1

    hence "\<exists>parity'. alt_dist.alt_distance_set P1 P2 parity' G U x \<noteq> \<infinity> \<and>
                     of_parity (other_parity parity') (length (p1 @ [x]))"
      by (metis enat_ord_code(3) of_parity other_parity parity.simps(3) parity.simps(4))

    then obtain u' parity' where 
          "u' \<in> U"
          "alt_dist.alt_distance P1 P2 parity' G u' x < alt_dist.alt_distance P1 P2 parity' G u x"
          "of_parity (other_parity parity') (length (p1 @ [x]))"
      using alt_dist_gt
      by (metis alt_dist_set_not_inf leI) 
    moreover then obtain p' where p': "alt_dist.alt_shortest_path P1 P2 parity' G u' p' x"
      by (fastforce dest: lt_lt_infnty elim!: alt_shortest_path_exists_2)


    have "alt_dist.alt_vwalk_bet P1 P2 parity G u' (p' @ tl ([x] @ p2)) v"
    proof-
      have "alt_list P1 P2 (edges_of_vwalk p')"
        using p'
        by(auto elim!: alt_dist.alt_vwalk_betE dest!: alt_dist.alt_shortest_path_vwalk)

      moreover have "alt_list P1 P2 (edges_of_vwalk (p1 @ x # p2))"
        using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<close>
        by(auto elim!: alt_dist.alt_vwalk_betE dest!: alt_dist.alt_shortest_path_vwalk)

      obtain parity'' where "alt_dist.alt_shortest_path P1 P2 parity'' G u (p1 @[x]) x"
        "parity = Odd \<Longrightarrow> next_alt_list_parity parity'' alt_dist.alt_shortest_path P1 P2 (other_parity parity'') G x (x # p2) v"
        "parity = Even \<Longrightarrow> next_alt_list_parity parity'' alt_dist.alt_shortest_path P1 P2 parity'' G x (x # p2) v"
        using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<close>
        apply (cases parity)
        by (auto dest!: alt_shortest_path_split_1 alt_shortest_path_split_2)
      moreover hence "parity'' = parity'"
        using \<open>of_parity (other_parity parity') (length (p1 @ [x]))\<close>
        by (auto dest!: alt_shortest_path_Parity simp: parity_simps split: parity.splits)
      ultimately have alt_vwalks: 
        "alt_dist.alt_shortest_path P1 P2 parity' G u (p1 @[x]) x"
        "parity = Odd \<Longrightarrow> next_alt_list_parity parity' alt_dist.alt_shortest_path P1 P2 (other_parity parity') G x (x # p2) v"
        "parity = Even \<Longrightarrow> next_alt_list_parity parity' alt_dist.alt_shortest_path P1 P2 parity' G x (x # p2) v"
        by auto

      have "last p' = x"
        using p' by auto
    
      have "alt_dist.alt_vwalk_bet P1 P2 Odd G u' (p' @ tl ([x] @ p2)) v" if "parity = Odd"
        apply(rule alt_vwalk_bet_append_3[where parity = parity'])
        subgoal 
          using p' that
          by(auto elim!: alt_dist.alt_shortest_path_props simp add: \<open>last p' = x\<close>)
        subgoal 
          using p' that alt_vwalks(2,3)
          by(auto elim!: alt_dist.alt_shortest_path_props simp add: parity_simps \<open>last p' = x\<close> split: parity.splits)
        subgoal
          by (metis \<open>alt_dist.alt_vwalk_bet P1 P2 parity' G u' p' (last p')\<close> alt_dist.alt_vwalk_bet_nonempty')
        done

      moreover have "alt_dist.alt_vwalk_bet P1 P2 Even G u' (p' @ tl ([x] @ p2)) v" if "parity = Even"
        apply(rule alt_vwalk_bet_append_2[where parity = parity'])
        subgoal 
          using p' that
          by(auto elim!: alt_dist.alt_shortest_path_props simp add: \<open>last p' = x\<close>)
        subgoal 
          using p' that alt_vwalks(2,3)
          by(auto elim!: alt_dist.alt_shortest_path_props simp add: parity_simps \<open>last p' = x\<close> split: parity.splits)
        subgoal
          by (metis \<open>alt_dist.alt_vwalk_bet P1 P2 parity' G u' p' (last p')\<close> alt_dist.alt_vwalk_bet_nonempty')
        done
      ultimately show ?thesis
        by (cases parity, auto)
    qed


    obtain parity'' where *: "alt_dist.alt_shortest_path P1 P2 parity'' G u (p1 @[x]) x"
      using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<close>
      apply (cases parity)
      by (auto dest!: alt_shortest_path_split_1 alt_shortest_path_split_2)
    moreover hence "parity'' = parity'"
      using \<open>of_parity (other_parity parity') (length (p1 @ [x]))\<close>
      by (auto dest!: alt_shortest_path_Parity simp: parity_simps split: parity.splits)

    ultimately have "length (p' @ tl ([x] @ p2)) - 1 < length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 parity' G u' p' x\<close>
            \<open>alt_dist.alt_distance P1 P2 parity' G u' x < alt_dist.alt_distance P1 P2 parity' G u x\<close>
      by(auto dest!: alt_dist.alt_shortest_path_dist)
    hence "length (p' @ tl ([x] @ p2)) - 1 < alt_dist.alt_distance_set P1 P2 parity G U v"
      using assms(1,3) alt_dist.alt_shortest_path_dist
      by force
    with \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u' (p' @ tl ([x] @ p2)) v\<close> show False
      using alt_dist.alt_dist_set_mem [OF \<open>u' \<in> U\<close>]
      apply -
      apply(drule alt_dist.alt_vwalk_bet_alt_dist)
      by (meson leD order_le_less_trans)
  qed
  ultimately show ?thesis
    using antisym 
    by (metis alt_dist.alt_dist_set_mem assms(2))
qed

lemma even_alt_distance_set_neighbourhood:
  "\<lbrakk>v \<in> neighbourhood G u; vs \<noteq> {}; P2 (u, v)\<rbrakk> \<Longrightarrow>
    alt_dist.alt_distance_set P1 P2 Even G vs v \<le> alt_dist.alt_distance_set P1 P2 Odd G vs u + 1"
proof(goal_cases)
  case assms: 1
  hence "(INF w\<in> vs. alt_dist.alt_distance P1 P2 Even G w v) \<le> (INF w\<in> vs. alt_dist.alt_distance P1 P2 Odd G w u + 1)"
    by (auto simp add: even_alt_distance_neighbourhood' intro!: INF_mono')
  also have "... = (INF w\<in> vs.  alt_dist.alt_distance P1 P2 Odd G w u) + (1::enat)"
    using \<open>vs \<noteq> {}\<close> 
    by (auto simp: INF_plus_enat)
  finally show ?case
    by(simp only: alt_dist.alt_distance_set_def)
qed

lemma odd_alt_distance_set_neighbourhood:
  "\<lbrakk>v \<in> neighbourhood G u; vs \<noteq> {}; P1 (u, v)\<rbrakk> \<Longrightarrow>
    alt_dist.alt_distance_set P1 P2 Odd G vs v \<le> alt_dist.alt_distance_set P1 P2 Even G vs u + 1"
proof(goal_cases)
  case assms: 1
  hence "(INF w\<in> vs. alt_dist.alt_distance P1 P2 Odd G w v) \<le> (INF w\<in> vs. alt_dist.alt_distance P1 P2 Even G w u + 1)"
    by (auto simp add: odd_alt_distance_neighbourhood' intro!: INF_mono')
  also have "... = (INF w\<in> vs.  alt_dist.alt_distance P1 P2 Even G w u) + (1::enat)"
    using \<open>vs \<noteq> {}\<close> 
    by (auto simp: INF_plus_enat)
  finally show ?case
    by(simp only: alt_dist.alt_distance_set_def)
qed

lemma even_alt_distance_set_parent:
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Even G vs v < \<infinity>; vs \<noteq> {}; v \<notin> vs\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance_set P1 P2 Odd G vs w + 1 = alt_dist.alt_distance_set P1 P2 Even G vs v \<and> v \<in> neighbourhood G w \<and> P2 (w, v)"
proof(goal_cases)
  case 1
  moreover hence "alt_dist.alt_distance_set P1 P2 Even G vs v \<noteq> \<infinity>"
    by auto
  ultimately obtain u where \<open>u \<in> vs\<close> \<open>alt_dist.alt_distance_set P1 P2 Even G vs v = alt_dist.alt_distance P1 P2 Even G u v \<close> \<open>u \<noteq> v\<close>
    by(fastforce elim!: alt_distance_set_wit')
  moreover then obtain w where "alt_dist.alt_distance P1 P2 Odd G u w + 1 = alt_dist.alt_distance P1 P2 Even G u v" "v \<in> neighbourhood G w" "P2 (w, v)"
    find_theorems alt_dist.alt_distance name: parent
    using 1 even_alt_distance_parent
    by fastforce
  ultimately show ?thesis
    using \<open>u \<in> vs\<close> even_alt_distance_set_neighbourhood
          alt_dist.alt_dist_set_mem
    by (metis (full_types) "1"(2) add_mono_thms_linordered_semiring(3) antisym)
qed

lemma odd_alt_distance_set_parent:
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Odd G vs v < \<infinity>; vs \<noteq> {}; v \<notin> vs\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance_set P1 P2 Even G vs w + 1 = alt_dist.alt_distance_set P1 P2 Odd G vs v \<and> v \<in> neighbourhood G w \<and> P1 (w, v)"
proof(goal_cases)
  case 1
  moreover hence "alt_dist.alt_distance_set P1 P2 Odd G vs v \<noteq> \<infinity>"
    by auto
  ultimately obtain u where \<open>u \<in> vs\<close> \<open>alt_dist.alt_distance_set P1 P2 Odd G vs v = alt_dist.alt_distance P1 P2 Odd G u v \<close> \<open>u \<noteq> v\<close>
    by(fastforce elim!: alt_distance_set_wit')
  moreover then obtain w where "alt_dist.alt_distance P1 P2 Even G u w + 1 = alt_dist.alt_distance P1 P2 Odd G u v" "v \<in> neighbourhood G w" "P1 (w, v)"
    using 1 odd_alt_distance_parent
    by fastforce
  ultimately show ?thesis
    using \<open>u \<in> vs\<close> odd_alt_distance_set_neighbourhood
          alt_dist.alt_dist_set_mem
    by (metis (full_types) "1"(2) add_mono_thms_linordered_semiring(3) antisym)
qed

lemma even_alt_distance_set_parent':
  "\<lbrakk>0 < alt_dist.alt_distance_set P1 P2 Even G vs v; alt_dist.alt_distance_set P1 P2 Even G vs v < \<infinity>; vs \<noteq> {}\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance_set P1 P2 Odd G vs w + 1 = alt_dist.alt_distance_set P1 P2 Even G vs v \<and> v \<in> neighbourhood G w \<and> P2 (w,v)"
  using even_alt_distance_set_parent
  by (metis antisym_conv2 alt_dist.alt_dist_set_inf even_alt_distance_0 
            alt_dist.alt_distance_set_def less_INF_D order.strict_implies_order)

lemma distance_set_0[simp]: "\<lbrakk>v \<in> dVs G\<rbrakk> \<Longrightarrow> alt_dist.alt_distance_set P1 P2 Even G vs v = 0 \<longleftrightarrow> v \<in> vs"
proof(safe, goal_cases)
  case 2
  moreover have "alt_dist.alt_distance P1 P2 Even G v v = 0"
    by (meson calculation(1) even_alt_distance_0)
  ultimately show ?case
    by (metis alt_dist.alt_dist_set_mem le_zero_eq)
next
  case 1
  thus ?case
    by (metis alt_dist_set_not_inf even_alt_distance_0 infinity_ne_i0)
qed

lemma alt_dist_set_leq: 
  "\<lbrakk>\<And>u. u \<in> vs \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G u v \<le> alt_dist.alt_distance P1 P2 parity G' u v\<rbrakk> \<Longrightarrow> alt_dist.alt_distance_set P1 P2 parity G vs v \<le> alt_dist.alt_distance_set P1 P2 parity G' vs v"
  by(auto simp: alt_dist.alt_distance_set_def INF_superset_mono)             

lemma alt_dist_set_eq: 
  "\<lbrakk>\<And>u. u \<in> vs \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G u v = alt_dist.alt_distance P1 P2 parity G' u v\<rbrakk> \<Longrightarrow> alt_dist.alt_distance_set P1 P2 parity G vs v = alt_dist.alt_distance_set P1 P2 parity G' vs v"
  using alt_dist_set_leq
  by (metis nle_le)

lemma alt_distance_set_subset: "G \<subseteq> G' \<Longrightarrow> alt_dist.alt_distance_set P1 P2 parity G' vs v \<le> alt_dist.alt_distance_set P1 P2 parity G vs v"
  by (simp add: alt_dist_set_leq alt_distance_subset)

lemma alt_vwalk_bet_alt_dist_set:
  "\<lbrakk>alt_dist.alt_vwalk_bet P1 P2 parity G u p v; u \<in> U\<rbrakk> \<Longrightarrow> alt_dist.alt_distance_set P1 P2 parity G U v \<le> length p - 1"
  apply (auto simp: alt_dist.alt_distance_set_def image_def intro!:)
  by (smt (verit, best) Inf_lower2 One_nat_def alt_dist.alt_vwalk_bet_alt_dist mem_Collect_eq)
end