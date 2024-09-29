theory Dist
  imports "../Misc/enat_misc" Vwalk
begin

section \<open>Distances\<close>

subsection \<open>Distance from a vertex\<close>

definition "distance G u v \<equiv> INF p. if Vwalk.vwalk_bet G u p v then length p - 1 else \<infinity>"

lemma vwalk_bet_dist:
  "Vwalk.vwalk_bet G u p v \<Longrightarrow> distance G u v \<le> length p - 1"
  by (auto simp: distance_def image_def intro!: complete_lattice_class.Inf_lower enat_ile)

lemma reachable_dist:
  "reachable G u v \<Longrightarrow> distance G u v < \<infinity>"
  apply(clarsimp simp add: reachable_vwalk_bet_iff)
  by (auto simp: distance_def image_def intro!: complete_lattice_class.Inf_lower enat_ile)

lemma unreachable_dist:
  "\<not>reachable G u v \<Longrightarrow> distance G u v = \<infinity>"
  apply(clarsimp simp add: reachable_vwalk_bet_iff)
  by (auto simp: distance_def image_def intro!: complete_lattice_class.Inf_lower enat_ile)

lemma dist_reachable:
  "distance G u v < \<infinity> \<Longrightarrow> reachable G u v"
  using wellorder_InfI       
  by(fastforce simp: distance_def image_def reachable_vwalk_bet_iff)    

lemma reachable_dist_2:
  assumes "reachable G u v"
  obtains p where "Vwalk.vwalk_bet G u p v" "distance G u v = length p - 1"
  using assms
  apply(clarsimp simp add: reachable_vwalk_bet_iff distance_def image_def)
  by (smt (verit, del_insts) Collect_disj_eq Inf_lower enat_ile mem_Collect_eq not_infinity_eq wellorder_InfI)

lemma triangle_ineq_reachable: 
  assumes "reachable G u v" "reachable G v w"
  shows "distance G u w \<le> distance G u v + distance G v w"
proof-
  obtain p q
    where p_q: "vwalk_bet G u p v" "distance G u v = length p - 1"
          "vwalk_bet G v q w" "distance G v w = length q - 1"
    using assms 
    by (auto elim!: reachable_dist_2)
  hence "vwalk_bet G u (p @ tl q) w"
    by(auto intro!: vwalk_bet_transitive)
  hence "distance G u w \<le> length (p @ tl q) - 1"
    by (auto dest!: vwalk_bet_dist)
  moreover have "length (p @ tl q) = length p + (length q - 1)"
    using \<open>vwalk_bet G v q w\<close>
    by (cases q; auto)
  ultimately have "distance G u w \<le> length p + (length q - 1) - 1"
    by (auto simp: eval_nat_numeral)
  thus ?thesis
    using p_q(1)
    by(cases p; auto simp add: p_q(2,4) eval_nat_numeral)
qed

lemma triangle_ineq:
  "distance G u w \<le> distance G u v + distance G v w"
proof(cases "reachable G u v")
  case reach_u_v: True
  then show ?thesis
  proof(cases "reachable G v w")
    case reach_v_w: True
    then show ?thesis
      using triangle_ineq_reachable reach_u_v reach_v_w
      by auto
  next
    case not_reach_v_w: False
    hence "distance G v w = \<infinity>"
      by (simp add: unreachable_dist) 
    then show ?thesis
      by simp
  qed
next
  case not_reach_u_v: False
  hence "distance G u v = \<infinity>"
    by (simp add: unreachable_dist) 
  then show ?thesis
    by simp
qed


lemma distance_split:
  "\<lbrakk>distance G u v \<noteq> \<infinity>; distance G u v = distance G u w + distance G w v \<rbrakk> \<Longrightarrow>
       \<exists>w'. reachable G u w' \<and> distance G u w' = distance G u w \<and>
            reachable G w' v \<and> distance G w' v = distance G w' v"
  by (metis dist_reachable enat_ord_simps(4) plus_eq_infty_iff_enat)

lemma dist_inf: "v \<notin> dVs G \<Longrightarrow> distance G u v = \<infinity>"
proof(rule ccontr, goal_cases)
  case 1
  hence "reachable G u v"
    by(auto intro!: dist_reachable)
  hence "v \<in>dVs G"
    by (simp add: reachable_in_dVs(2))
  then show ?case
    using 1
    by auto
qed

lemma dist_inf_2: "v \<notin> dVs G \<Longrightarrow> distance G v u = \<infinity>"
proof(rule ccontr, goal_cases)
  case 1
  hence "reachable G v u"
    by(auto intro!: dist_reachable)
  hence "v \<in>dVs G"
    by (simp add: reachable_in_dVs(1))
  then show ?case
    using 1
    by auto
qed

lemma dist_eq: "\<lbrakk>\<And>p. Vwalk.vwalk_bet G' u p v \<Longrightarrow> Vwalk.vwalk_bet G u (map f p) v\<rbrakk> \<Longrightarrow>
                   distance G u v \<le> distance G' u v"
  apply(auto simp: distance_def image_def intro!: Inf_lower)
  apply (smt (verit, ccfv_threshold) Un_iff length_map mem_Collect_eq wellorder_InfI)
  by (meson vwalk_bet_nonempty')

lemma distance_subset: "G \<subseteq> G' \<Longrightarrow> distance G' u v \<le> distance G u v"
  by (metis enat_ord_simps(3) reachable_dist_2 unreachable_dist vwalk_bet_dist vwalk_bet_subset)


lemma distance_neighbourhood:
  "\<lbrakk>v \<in> neighbourhood G u\<rbrakk> \<Longrightarrow> distance G u v \<le> 1"
proof(goal_cases)
  case 1
  hence "vwalk_bet G u [u,v] v"
    by auto
  moreover have "length [u,v] = 2"
    by auto
  ultimately show ?case
    by(force dest!: vwalk_bet_dist simp: one_enat_def)
qed

subsection \<open>Shortest Paths\<close>

definition "shortest_path G u p v \<equiv> distance G u v = length p -1 \<and> vwalk_bet G u p v"

lemma shortest_path_props[elim]:
  "shortest_path G u p v \<Longrightarrow> (\<lbrakk>distance G u v = length p -1; vwalk_bet G u p v\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: shortest_path_def)

lemma shortest_path_intro:
  "\<lbrakk>distance G u v = length p -1; vwalk_bet G u p v\<rbrakk> \<Longrightarrow> shortest_path G u p v"
  by (auto simp: shortest_path_def)

lemma shortest_path_vwalk: "shortest_path G u p v \<Longrightarrow> vwalk_bet G u p v"
  by(auto simp: shortest_path_def)

lemma shortest_path_dist: "shortest_path G u p v \<Longrightarrow> distance G u v = length p - 1"
  by(auto simp: shortest_path_def)

lemma shortest_path_split_1:
  "\<lbrakk>shortest_path G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow> shortest_path G x (x # p2) v"
proof(goal_cases)
  case 1
  hence "vwalk_bet G u (p1 @ [x]) x" "vwalk_bet G x (x # p2) v"
    by (auto dest!: shortest_path_vwalk simp: split_vwalk vwalk_bet_pref)

  hence "reachable G x v" "reachable G u x"
    by (auto dest: reachable_vwalk_betD) 


  have "distance G x v \<ge> length (x # p2) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>reachable G x v\<close>
    obtain p where "vwalk_bet G x p v" "distance G x v = enat (length p - 1)"
      by (rule reachable_dist_2)
    ultimately have "length p - 1 < length (x # p2) - 1"
      by auto 
    hence "length (p1 @ p) - 1 < length (p1 @ x # p2) - 1"
      by auto

    have "vwalk_bet G u ((p1 @ [x]) @ (tl p)) v"
      using \<open>vwalk_bet G u (p1 @ [x]) x\<close> \<open>vwalk_bet G x p v\<close> 
      by (fastforce intro: vwalk_bet_transitive)
    moreover have "p = x # (tl p)"
      using \<open>vwalk_bet G x p v\<close> 
      by (fastforce dest: hd_of_vwalk_bet)
    ultimately have "distance G u v \<le> length (p1 @ p) -1"
      using vwalk_bet_dist
      by fastforce
    moreover have "distance G u v = length (p1 @ x # p2) - 1"
      using \<open>shortest_path G u (p1 @ x # p2) v\<close>
      by (rule shortest_path_dist)
    ultimately show ?case
      using \<open>length (p1 @ p) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "distance G x v \<le> length (x # p2) - 1"
    using \<open>vwalk_bet G x (x # p2) v\<close>
    by (force intro!: vwalk_bet_dist)

  ultimately show ?case
    using \<open>vwalk_bet G x (x # p2) v\<close>
    by (auto simp: shortest_path_def)
qed

lemma shortest_path_split_2:
  "\<lbrakk>shortest_path G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow> shortest_path G u (p1 @ [x]) x"
proof(goal_cases)
  case 1
  hence "vwalk_bet G u (p1 @ [x]) x" "vwalk_bet G x (x # p2) v"
    by (auto dest!: shortest_path_vwalk simp: split_vwalk vwalk_bet_pref)

  hence "reachable G x v" "reachable G u x"
    by (auto dest: reachable_vwalk_betD) 

  have "distance G u x \<ge> length (p1 @ [x]) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>reachable G u x\<close>
    obtain p where "vwalk_bet G u p x" "distance G u x = enat (length p - 1)"
      by (rule reachable_dist_2)
    ultimately have "length p - 1 < length (p1 @ [x]) - 1"
      by auto 
    hence "length (p @ p2) - 1 < length (p1 @ x # p2) - 1"
      by auto
    have "vwalk_bet G u (butlast p @ x # p2) v"
      using \<open>vwalk_bet G u p x\<close> \<open>vwalk_bet G x (x # p2) v\<close> 
      by (simp add: vwalk_bet_transitive_2)
    moreover have "p = (butlast p) @ [x]"
      using \<open>vwalk_bet G u p x\<close> 
      by (fastforce dest: last_of_vwalk_bet')
    moreover have "length p > 0"
      using \<open>vwalk_bet G u p x\<close>
      by force
    ultimately have "distance G u v \<le> length (p @ p2) -1"
      by (auto dest!: vwalk_bet_dist simp: neq_Nil_conv)
    moreover have "distance G u v = length (p1 @ x # p2) - 1"
      using \<open>shortest_path G u (p1 @ x # p2) v\<close>
      by (rule shortest_path_dist)
    ultimately show ?case
      using \<open>length (p @ p2) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "distance G u x \<le> length (p1 @ [x]) - 1"
    using \<open>vwalk_bet G u (p1 @ [x]) x\<close>
    by (force intro!: vwalk_bet_dist)

  ultimately show ?case
    using \<open>vwalk_bet G u (p1 @ [x]) x\<close>
    by (auto simp: shortest_path_def)
qed

lemma shortest_path_split_distance:
  "\<lbrakk>shortest_path G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow> distance G u x \<le> distance G u v"
  using shortest_path_split_2 shortest_path_dist
  by fastforce

lemma shortest_path_split_distance':
  "\<lbrakk>x \<in> set p; shortest_path G u p v\<rbrakk> \<Longrightarrow> distance G u x \<le> distance G u v"
  apply(subst (asm) in_set_conv_decomp_last)
  using shortest_path_split_distance
  by auto 

lemma shortest_path_exists:
  assumes "reachable G u v"
  obtains p where "shortest_path G u p v"
  using assms 
  by (force elim!: reachable_dist_2 simp: shortest_path_def)

lemma shortest_path_exists_2:
  assumes "distance G u v < \<infinity>"
  obtains p where "shortest_path G u p v"
  using assms 
  by (force dest!: dist_reachable elim!: shortest_path_exists simp: shortest_path_def)

lemma not_distinct_props: 
  "\<not>distinct xs \<Longrightarrow> (\<And>x1 x2 xs1 xs2 xs3. \<lbrakk>xs = xs1 @ x1# xs2 @ x2 # xs3; x1 = x2\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  using not_distinct_decomp
  by fastforce

lemma shortest_path_distinct:
  "shortest_path G u p v \<Longrightarrow> distinct p"
  apply(erule shortest_path_props)
  apply(rule ccontr)
  apply(erule not_distinct_props)
proof(goal_cases)
  case (1 x1 x2 xs1 xs2 xs3)
  hence "Vwalk.vwalk_bet G u (xs1 @ x2 # xs3) v"
    using vwalk_bet_transitive_2 closed_vwalk_bet_decompE
    by (smt (verit, best) butlast_snoc)
  hence "distance G u v \<le> length (xs1 @ x2 # xs3) - 1"
    using vwalk_bet_dist
    by force
  moreover have "length (xs1 @ x2 # xs3) < length p"
    by(auto simp: \<open> p = xs1 @ x1 # xs2 @ x2 # xs3\<close>)
  ultimately show ?case
    using \<open>distance G u v = enat (length p - 1)\<close>
    by auto
qed

lemma diet_eq': "\<lbrakk>\<And>p. shortest_path G' u p v \<Longrightarrow> shortest_path G u (map f p) v\<rbrakk> \<Longrightarrow>
                   distance G u v \<le> distance G' u v"
  apply(auto simp: shortest_path_def)
  by (metis One_nat_def Orderings.order_eq_iff order.strict_implies_order reachable_dist
            reachable_dist_2 unreachable_dist)

lemma distance_0:
  "(u = v \<and> v \<in> dVs G) \<longleftrightarrow> distance G u v = 0"
proof(safe, goal_cases)
  case 1
  hence "vwalk_bet G v [v] v"
    by auto
  moreover have "length [v] = 1"
    by auto
  ultimately show ?case
    using zero_enat_def
    by(auto dest!: vwalk_bet_dist simp: )
next
  case 2
  hence "distance G u v < \<infinity>"
    by auto
  then obtain p where "shortest_path G u p v"
    by(erule shortest_path_exists_2)
  hence "length p = 1" "vwalk_bet G u p v"
    using \<open>distance G u v = 0\<close>
    apply (auto simp: shortest_path_def)
    by (metis diff_Suc_Suc diff_zero enat_0_iff(2) hd_of_vwalk_bet length_Cons)
  then obtain x where "p = [x]"
    by (auto simp: length_Suc_conv)
  then have "x = u" "x = v" "x \<in> dVs G"
    using \<open>vwalk_bet G u p v\<close> hd_of_vwalk_bet last_of_vwalk_bet
    by (fastforce simp: vwalk_bet_in_vertices)+
  then show "u = v"  "v \<in> dVs G"
    by auto
qed

lemma distance_neighbourhood':
  "\<lbrakk>v \<in> neighbourhood G u\<rbrakk> \<Longrightarrow> distance G x v \<le> distance G x u + 1"
  using triangle_ineq distance_neighbourhood
  by (metis add.commute add_mono_thms_linordered_semiring(3) order_trans)



lemma Suc_le_length_iff_2:
  "(Suc n \<le> length xs) = (\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys)"
  by (metis Suc_le_D Suc_le_mono length_Suc_conv_rev)

lemma distance_parent: 
  "\<lbrakk>distance G u v < \<infinity>; u \<noteq> v\<rbrakk> \<Longrightarrow> 
     \<exists>w. distance G u w + 1 = distance G u v \<and> v \<in> neighbourhood G w"
proof(goal_cases)
  case 1
  then obtain p where "shortest_path G u p v"
    by(force dest!: dist_reachable elim!: shortest_path_exists)
  hence "length p \<ge> 2"
    using \<open>u\<noteq>v\<close> 
    by(auto dest!: shortest_path_vwalk simp: Suc_le_length_iff eval_nat_numeral elim: vwalk_betE)
  then obtain p' x y where "p = p' @ [x, y]"
    by(auto simp: Suc_le_length_iff_2 eval_nat_numeral)

  hence "shortest_path G u (p' @ [x]) x"
    using \<open>shortest_path G u p v\<close> 
    by (fastforce dest: shortest_path_split_2)

  hence "distance G u x + 1 = distance G u v"
    using \<open>shortest_path G u p v\<close> \<open>p = p' @ [x,y]\<close>
    by (auto dest!: shortest_path_dist simp: eSuc_plus_1)
  moreover have "y = v"
    using \<open>shortest_path G u p v\<close> \<open>p = p' @ [x,y]\<close> 
    by(force simp: \<open>p = p' @ [x,y]\<close> dest!: shortest_path_vwalk intro!: vwalk_bet_snoc[where p = "p' @ [x]"])
  moreover have "y \<in> neighbourhood G x"
    using \<open>shortest_path G u p v\<close> \<open>p = p' @ [x,y]\<close> vwalk_bet_suffix_is_vwalk_bet
    by(fastforce simp: \<open>p = p' @ [x,y]\<close> dest!: shortest_path_vwalk)
  ultimately show ?thesis
    by auto
qed

subsection \<open>Distance from a set of vertices\<close>

definition "distance_set G U v \<equiv> INF u\<in>U. distance G u v"

(*TODO: intro rule*)

lemma dist_set_inf: "v \<notin> dVs G \<Longrightarrow> distance_set G U v = \<infinity>"
  by(auto simp: distance_set_def INF_eqI dist_inf)

lemma dist_set_mem[intro]: "u \<in> U \<Longrightarrow> distance_set G U v \<le> distance G u v"
  by (auto simp: distance_set_def wellorder_Inf_le1)

lemma dist_not_inf'': "\<lbrakk>distance_set G U v \<noteq> \<infinity>; u\<in>U; distance G u v = distance_set G U v\<rbrakk>
                       \<Longrightarrow> \<exists>p. vwalk_bet G u (u#p) v \<and> length p = distance G u v \<and>
                               set p \<inter> U = {}"
proof(goal_cases)
  case main: 1
  then obtain p where "vwalk_bet G u (u#p) v" "length p = distance G u v"
    by (metis dist_reachable enat_ord_simps(4) hd_of_vwalk_bet length_tl list.sel(3) reachable_dist_2)
  moreover have "set p \<inter> U = {}"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain p1 w p2 where "p = p1 @ w # p2" "w \<in> U"
      by (auto dest!: split_list)
    hence "length (w#p2) < length (u#p)"
      by auto
    moreover have "vwalk_bet G w (w#p2) v"
      using \<open>p = p1 @ w # p2\<close> \<open>vwalk_bet G u (u # p) v\<close>
            split_vwalk vwalk_bet_cons
      by fastforce
    hence "distance G w v \<le> length p2"
      by(auto dest!: vwalk_bet_dist) 
    ultimately have "distance_set G U v \<le> length p2"
      using \<open>w \<in> U\<close> 
      by(auto dest!: dist_set_mem dest: order.trans)
    moreover have "length p \<le> distance_set G U v"
      by (simp add: \<open>enat (length p) = distance G u v\<close> main(3))
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

lemma dist_not_inf''':
  "\<lbrakk>distance_set G U v \<noteq> \<infinity>; u\<in>U; distance G u v = distance_set G U v\<rbrakk>
      \<Longrightarrow> \<exists>p. shortest_path G u (u#p) v \<and> set p \<inter> U = {}"
  apply (simp add: shortest_path_def)
  by (metis dist_not_inf'' enat.distinct(1))

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

lemma distance_set_union:
  "distance_set G (U \<union> V) v \<le> distance_set G U v"
  by (simp add: distance_set_def INF_superset_mono)   

lemma lt_lt_infnty: "x < (y::enat) \<Longrightarrow> x < \<infinity>"
  using enat_ord_code(3) order_less_le_trans
  by blast

lemma finite_dist_nempty:
  "distance_set G V v \<noteq> \<infinity> \<Longrightarrow> V \<noteq> {}"
  by (auto simp: distance_set_def top_enat_def)

lemma distance_set_wit: 
  assumes "v \<in> V"
  obtains v' where "v' \<in> V" "distance_set G V x = distance G v' x"
  using assms wellorder_InfI[of "distance G v x" "(%v. distance G v x) ` V"]
  by (auto simp: distance_set_def image_def dest!: )

lemma distance_set_wit':
  assumes "distance_set G V v \<noteq> \<infinity>"
  obtains v' where "v' \<in> V" "distance_set G V x = distance G v' x"
  using finite_dist_nempty[OF assms]
  by (auto elim: distance_set_wit)

lemma dist_set_not_inf: "distance_set G U v \<noteq> \<infinity> \<Longrightarrow> \<exists>u\<in>U. distance G u v = distance_set G U v"
  using distance_set_wit'
  by metis

lemma dist_not_inf': "distance_set G U v \<noteq> \<infinity> \<Longrightarrow>
                        \<exists>u\<in>U. distance G u v = distance_set G U v \<and> reachable G u v"
  by (metis dist_reachable dist_set_not_inf enat_ord_simps(4))

lemma distance_on_vwalk:
  "\<lbrakk>distance_set G U v = distance G u v; u \<in> U; shortest_path G u p v; x \<in> set p\<rbrakk>
       \<Longrightarrow> distance_set G U x = distance G u x"
proof(goal_cases)
  case assms: 1
  hence "distance_set G U x \<le> distance G u x"
    by (auto intro: dist_set_mem)
  moreover have "distance G u x \<le> distance_set G U x"
  proof(rule ccontr, goal_cases)
    case dist_gt: 1
    hence "distance_set G U x \<noteq> \<infinity>"
      using lt_lt_infnty
      by (auto simp: linorder_class.not_le)
    then obtain u' where "u' \<in> U" "distance G u' x < distance G u x"
      using dist_gt 
      by (fastforce dest!: dist_set_not_inf)
    moreover then obtain p' where "shortest_path G u' p' x"
      by (fastforce dest: lt_lt_infnty elim!: shortest_path_exists_2)
    moreover obtain p1 p2 where "p = p1 @ [x] @ p2"
      using \<open>x \<in> set p\<close>              
      by(fastforce dest: iffD1[OF in_set_conv_decomp_first])
    ultimately have "vwalk_bet G u' (p' @ tl ([x] @ p2)) v"
      using \<open>shortest_path G u p v\<close> 
      apply -
      apply (rule vwalk_bet_transitive)
      by(auto dest!: shortest_path_vwalk shortest_path_split_1)+
    moreover have "shortest_path G u (p1 @[x]) x"
      using \<open>shortest_path G u p v\<close>
      by(auto dest!: shortest_path_split_2 simp: \<open>p = p1 @ [x] @ p2\<close>) 
    hence "length (p' @ tl ([x] @ p2)) - 1 < length p - 1"
      using \<open>shortest_path G u' p' x\<close> \<open>distance G u' x < distance G u x\<close>
      by(auto dest!: shortest_path_dist simp: \<open>p = p1 @ [x] @ p2\<close>)
    hence "length (p' @ tl ([x] @ p2)) - 1 < distance_set G U v"
      using assms(1,3) shortest_path_dist
      by force
    ultimately show False
      using dist_set_mem [OF \<open>u' \<in> U\<close>]
      apply -
      apply(drule vwalk_bet_dist)
      by (meson leD order_le_less_trans)
  qed
  ultimately show ?thesis
    by auto
qed

lemma diff_le_self_enat: "m - n \<le> (m::enat)"
  by (metis diff_le_self enat.exhaust enat_ord_code(1) idiff_enat_enat idiff_infinity idiff_infinity_right order_refl zero_le)

lemma shortest_path_dist_set_union:
  "\<lbrakk>distance_set G U v = distance G u v; u \<in> U; shortest_path G u (p1 @ x # p2) v;
     x \<in> V; \<And>v'. v' \<in> V \<Longrightarrow> distance_set G U v' = distance G u x\<rbrakk>
       \<Longrightarrow> distance_set G (U \<union> V) v = distance_set G U v - distance G u x"
proof(goal_cases)
  case assms: 1
  define k where "k \<equiv> distance G u x"
  have "distance_set G (U \<union> V) v \<le> distance_set G U v - k"
  proof-
    have "vwalk_bet G x (x#p2) v"
      using \<open>shortest_path G u (p1 @ x # p2) v\<close>
      by(auto dest: shortest_path_vwalk split_vwalk)
    moreover have \<open>x \<in> U \<union> V\<close>
      using \<open>x \<in> V\<close>
      by auto
    ultimately have "distance_set G (U \<union> V) v \<le> length (x # p2) - 1"
      by(auto simp only: dest!: vwalk_bet_dist dist_set_mem dest: order_trans) 
    moreover have "length p1 = k"
    proof-
      have "shortest_path G u (p1 @ [x]) x"
        using \<open>shortest_path G u (p1 @ x # p2) v\<close>
        by(auto intro: shortest_path_split_2)
      moreover have "distance_set G U x = k"
        using assms
        by (auto simp: k_def)
      ultimately have "length (p1 @ [x]) - 1 = k"
        using assms(1,2,3) distance_on_vwalk shortest_path_dist
        by fastforce        
      thus ?thesis
        by auto
    qed
    hence "(distance_set G U v) - k = length (x#p2) - 1"
      using \<open>shortest_path G u (p1 @ x # p2) v\<close>
      by(auto dest!: shortest_path_dist simp: \<open>distance_set G U v = distance G u v\<close>)
    ultimately show ?thesis
      by auto
  qed
  moreover have "distance_set G (U \<union> V) v \<ge> distance_set G U v - k"
  proof(rule ccontr, goal_cases)
    case dist_lt: 1
    hence "distance_set G (U \<union> V) v \<noteq> \<infinity>"
      using lt_lt_infnty
      by (auto simp: linorder_class.not_le)
    then obtain u' where "u' \<in> U \<union> V" "distance G u' v < distance_set G U v - k"
      using dist_lt
      by (fastforce dest!: dist_set_not_inf)
    then consider "u' \<in> U" | "u' \<in> V"
      by auto
    then show ?case
    proof(cases)
      case 1
      moreover from \<open>distance G u' v < distance_set G U v - k\<close>
      have \<open>distance G u' v < distance_set G U v\<close>
        using diff_le_self_enat order_less_le_trans
        by blast
      ultimately show ?thesis
        by(auto simp: dist_set_mem leD)
    next
      case 2
      moreover from \<open>distance G u' v < distance_set G U v - k\<close>
      obtain p2 where "shortest_path G u' p2 v"
        by(auto elim!: shortest_path_exists_2 dest: lt_lt_infnty)
      have "distance_set G U u' = k"
        using assms 2
        by (auto simp: k_def)
      moreover have \<open>k \<noteq> \<infinity>\<close>
        using assms 
        by (fastforce simp: k_def dest: shortest_path_split_2 shortest_path_dist )
      ultimately obtain u where "u \<in> U" "distance G u u' = k"
        by(fastforce dest!: dist_set_not_inf)
      moreover have "distance G u v \<le> distance G u u' + distance G u' v"
        using \<open>k \<noteq> \<infinity>\<close> lt_lt_infnty[OF \<open>distance G u' v < distance_set G U v - k\<close>] \<open>distance G u u' = k\<close>
        by(auto intro!: triangle_ineq simp: dist_reachable)
      ultimately have "distance G u v \<le> k + distance G u' v"
        by auto
      hence "distance G u v < k + (distance_set G U v - k)"
        using \<open>distance G u' v < distance_set G U v - k\<close>
        by (meson \<open>k \<noteq> \<infinity>\<close> dual_order.strict_trans2 enat_add_left_cancel_less)
      moreover have "k \<le> distance_set G U v"
        using assms(1,3) shortest_path_split_distance
        by (fastforce simp: k_def)
      hence "k + (distance_set G U v - k) \<le> distance_set G U v"
        by (simp add: \<open>k \<noteq> \<infinity>\<close> add_diff_assoc_enat)
      ultimately have "distance G u v < distance_set G U v "
        by auto
      then show ?thesis
        using \<open>u \<in> U\<close>
        by (simp add: dist_set_mem leD)
    qed
  qed
  ultimately show ?case
    by (auto simp: k_def)
qed
                   
lemma Inf_enat_def1:
  fixes K::"enat set"
  assumes "K \<noteq> {}"
  shows "Inf K \<in> K"
  using assms
  by (auto simp add: Min_def Inf_enat_def) (meson LeastI)

lemma INF_plus_enat:
  "V \<noteq> {} \<Longrightarrow> (INF v\<in>V. (f::'a \<Rightarrow> enat) v) + (x::enat) = (INF v\<in>V. f v + x)"
proof(goal_cases)
  case assms: 1
  have "(INF v\<in>V. (f::'a \<Rightarrow> enat) v) + (x::enat) \<le> f_v" if "f_v \<in> {f v + x | v . v\<in>V}" for f_v
    using that
    apply(auto simp: image_def)
    by (metis (mono_tags, lifting) Inf_lower mem_Collect_eq)
  moreover have "(INF v\<in>V. (f::'a \<Rightarrow> enat) v) + (x::enat) \<in> {f v + x | v . v\<in>V}"
  proof-
    have "Inf {f v | v. v \<in> V} \<in> {f v | v. v \<in> V}"
      apply (rule Inf_enat_def1)
      using assms
      by simp

    then obtain v where "v \<in> V" "Inf {f v | v. v \<in> V} = f v"
      using assms
      by auto
    hence "f v + 1 \<in> {f v + 1 | v. v \<in> V}"
      by auto
    hence "Inf {f v | v. v \<in> V} + x \<in> {f v + x | v. v \<in> V}"
      apply(subst \<open>Inf {f v | v. v \<in> V} = f v\<close>)
      by auto
    thus ?thesis
      by (simp add: Setcompr_eq_image)
  qed
  ultimately show ?case
    by (simp add: Inf_lower Setcompr_eq_image order_antisym wellorder_InfI)
qed

lemma distance_set_neighbourhood:
  "\<lbrakk>v \<in> neighbourhood G u; Vs \<noteq> {}\<rbrakk> \<Longrightarrow> distance_set G Vs v \<le> distance_set G Vs u + 1"
proof(goal_cases)
  case assms: 1
  hence "(INF w\<in> Vs. distance G w v) \<le> (INF w\<in> Vs. distance G w u + 1)"
    by (auto simp add: distance_neighbourhood' intro!: INF_mono')
  also have "... = (INF w\<in> Vs. distance G w u) + (1::enat)"
    using \<open>Vs \<noteq> {}\<close> 
    by (auto simp: INF_plus_enat)
  finally show ?case
    by(simp only: distance_set_def)
qed

lemma distance_set_parent: 
  "\<lbrakk>distance_set G Vs v < \<infinity>; Vs \<noteq> {}; v \<notin> Vs\<rbrakk> \<Longrightarrow> 
     \<exists>w. distance_set G Vs w + 1 = distance_set G Vs v \<and> v \<in> neighbourhood G w"
proof(goal_cases)
  case 1
  moreover hence "distance_set G Vs v \<noteq> \<infinity>"
    by auto
  ultimately obtain u where \<open>u \<in> Vs\<close> \<open>distance_set G Vs v = distance G u v \<close> \<open>u \<noteq> v\<close>
    by(fastforce elim!: distance_set_wit')
  then obtain w where "distance G u w + 1 = distance G u v" "v \<in> neighbourhood G w"
    using 1 distance_parent
    by fastforce
  thus ?thesis
    by (metis "1"(2) \<open>distance_set G Vs v = distance G u v\<close> \<open>u \<in> Vs\<close> 
              add_mono_thms_linordered_semiring(3) dist_set_mem
              distance_set_neighbourhood nle_le)
qed

lemma distance_set_parent':
  "\<lbrakk>0 < distance_set G Vs v; distance_set G Vs v < \<infinity>; Vs \<noteq> {}\<rbrakk> \<Longrightarrow> 
     \<exists>w. distance_set G Vs w + 1 = distance_set G Vs v \<and> v \<in> neighbourhood G w"
  using distance_set_parent
  by (metis antisym_conv2 dist_set_inf distance_0 distance_set_def less_INF_D order.strict_implies_order)

lemma distance_set_0[simp]: "\<lbrakk>v \<in> dVs G\<rbrakk> \<Longrightarrow> distance_set G Vs v = 0 \<longleftrightarrow> v \<in> Vs"
proof(safe, goal_cases)
  case 2
  moreover have "distance G v v = 0"
    by (meson calculation(1) distance_0)
  ultimately show ?case
    by (metis dist_set_mem le_zero_eq)
next
  case 1
  thus ?case
    by (metis dist_set_not_inf distance_0 infinity_ne_i0)
qed

lemma dist_set_leq: 
  "\<lbrakk>\<And>u. u \<in> Vs \<Longrightarrow> distance G u v \<le> distance G' u v\<rbrakk> \<Longrightarrow> distance_set G Vs v \<le> distance_set G' Vs v"
  by(auto simp: distance_set_def INF_superset_mono)             

lemma dist_set_eq: 
  "\<lbrakk>\<And>u. u \<in> Vs \<Longrightarrow> distance G u v = distance G' u v\<rbrakk> \<Longrightarrow> distance_set G Vs v = distance_set G' Vs v"
  using dist_set_leq
  by (metis nle_le)

lemma distance_set_subset: "G \<subseteq> G' \<Longrightarrow> distance_set G' Vs v \<le> distance_set G Vs v"
  by (simp add: dist_set_leq distance_subset)

lemma vwalk_bet_dist_set:
  "\<lbrakk>Vwalk.vwalk_bet G u p v; u \<in> U\<rbrakk> \<Longrightarrow> distance_set G U v \<le> length p - 1"
  apply (auto simp: distance_set_def image_def intro!:)
  by (metis (mono_tags, lifting) Inf_lower One_nat_def dual_order.trans mem_Collect_eq vwalk_bet_dist)
(*
section \<open>Forests\<close>

definition "forest G \<equiv> (\<forall>u v p p'. Vwalk.vwalk_bet G u p v \<and> Vwalk.vwalk_bet G u p' v \<longrightarrow> p = p')"

lemma forest_props[elim]:
"forest G \<Longrightarrow> (\<lbrakk> \<And>u v p p'. \<lbrakk>Vwalk.vwalk_bet G u p v; Vwalk.vwalk_bet G u p' v\<rbrakk> \<Longrightarrow> p = p'\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: forest_def)

lemma forest_intro:
"\<lbrakk> \<And>u v p p'. \<lbrakk>Vwalk.vwalk_bet G u p v; Vwalk.vwalk_bet G u p' v\<rbrakk> \<Longrightarrow> p = p'\<rbrakk> \<Longrightarrow> forest G"
  by (auto simp: forest_def)

lemma forest_subset: "\<lbrakk>forest G'; G \<subseteq> G'\<rbrakk> \<Longrightarrow> forest G"
  by(auto simp: forest_def intro!: vwalk_bet_subset)

lemma distance_forest: "\<lbrakk>reachable G u v; G \<subseteq> G'; forest G'\<rbrakk> \<Longrightarrow> distance G u v = distance G' u v"
proof(goal_cases)
  case 1
  have "distance G' u v \<le> distance G u v"
    using \<open>G \<subseteq> G'\<close>
    by(auto simp: distance_subset)
  moreover  have "distance G u v \<le> distance G' u v"
    using 1 
    apply(auto simp: elim!: forest_props intro!: dist_eq[where f = id])
    by (metis reachable_dist_2 vwalk_bet_subset)
  ultimately show ?thesis
    by auto
qed

lemma forest_shortest_path:
  "\<lbrakk>forest G; Vwalk.vwalk_bet G u p v\<rbrakk> \<Longrightarrow> shortest_path G u p v"
  apply(auto elim!: forest_props intro!: shortest_path_intro)
  by (metis One_nat_def reachable_dist_2 reachable_vwalk_bet_iff)

lemma forest_insert: "\<lbrakk>forest G; v \<notin> dVs G\<rbrakk> \<Longrightarrow> forest (insert (u,v) G)"
proof(intro forest_intro, goal_cases)
  case (1 u v p p')
  then show ?case sorry
qed

lemma forest_union: "\<lbrakk>forest G\<rbrakk> \<Longrightarrow> forest (G \<union> {(u,v). u \<in> dVs G \<and> v \<notin> dVs G})"
  using forest_subset forest_insert
  apply auto
  sorry

section \<open>Rooted Forest\<close>



lemma distance_set_forest:
  "\<lbrakk>u \<in> Vs; reachable G u v; G \<subseteq> G'; forest G'\<rbrakk> \<Longrightarrow> distance_set G Vs v = distance_set G' Vs v"
proof(goal_cases)
  case 1
  then obtain p where "Vwalk.vwalk_bet G u p v"
    by (meson reachable_vwalk_bet_iff)
  hence "shortest_path G u p v"
    using \<open>forest G'\<close>  \<open>G \<subseteq> G'\<close> 
    by(auto dest: forest_subset intro!: forest_shortest_path)
  then show ?case
    by (metis (no_types, lifting) "1"(1) "1"(2) "1"(3) \<open>vwalk_bet G u p v\<close> distance_set_0 distance_set_shortest_path reachable_in_dVs(1) vwalk_bet_endpoints(2) vwalk_bet_subset)
qed*)
  
end