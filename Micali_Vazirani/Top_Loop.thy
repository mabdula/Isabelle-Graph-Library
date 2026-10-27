theory Top_Loop
  imports Alt_BFS Layered_Digraph
begin

text \<open>The Micali-Vazirani top loop. Milestone 1: the output of alternating
BFS, read on parity-labelled vertex copies and reversed, is a layered digraph
in the sense required by DDFS.\<close>

fun copies_of :: "parity \<Rightarrow> 'a list \<Rightarrow> 'a labelled_vtx list" where
  "copies_of parity [] = []"
| "copies_of parity (x # xs) = Vtx parity x # copies_of (other_parity parity) xs"

lemma copies_of_hd_tl:
  "xs \<noteq> [] \<Longrightarrow>
     copies_of parity xs = Vtx parity (hd xs) # copies_of (other_parity parity) (tl xs)"
  by (cases xs) auto

context BFS
begin

definition "copies_dag dT =
  {(Vtx Odd v, Vtx Even u) | u v.
     (u, v) \<in> dT \<and> (u, v) \<in> Graph.digraph_abs unmatching} \<union>
  {(Vtx Even v, Vtx Odd u) | u v.
     (u, v) \<in> dT \<and> (u, v) \<in> Graph.digraph_abs matching}"

definition "copies_lev w = the_enat (altd_G (label w) (vtx w))"

context
  includes Graph.adjmap.automation and Graph.vset.set.automation
       and set_ops.automation2
  assumes BFS_axiom
begin

lemma BFS_axiom_ctxt: "BFS_axiom"
  using \<open>BFS_axiom\<close> .

subsection \<open>alpha-1: the infinity-witness bridge\<close>

lemma altd_set_witness:
  assumes "alt_distance_set H parity v \<noteq> \<infinity>"
  obtains u p where "u \<in> t_set srcs" "alt_walk parity H u p v"
proof -
  have h: "alt_dist.alt_distance_set unmatched_edge matched_edge parity H (t_set srcs) v \<noteq> \<infinity>"
    using assms by (simp add: alt_distance_set_def)
  from alt_dist_set_not_inf[OF h] obtain u where
    u: "u \<in> t_set srcs" and
    ud: "alt_dist.alt_distance unmatched_edge matched_edge parity H u v =
         alt_dist.alt_distance_set unmatched_edge matched_edge parity H (t_set srcs) v"
    by blast
  have ult: "alt_dist.alt_distance unmatched_edge matched_edge parity H u v < \<infinity>"
    using ud h by (simp add: less_le)
  from alt_dist.alt_dist_reachable[OF ult] obtain p where
    p: "alt_walk parity H u p v"
    by (auto simp: alt_dist.alt_reachable_def)
  show thesis by (rule that[OF u p])
qed

lemma altd_G_srcs_Even_0:
  assumes "s \<in> t_set srcs"
  shows "altd_G Even s = 0"
proof -
  have sG: "s \<in> dVs G"
    using assms srcs_in_G[OF BFS_axiom_ctxt] by (fastforce simp: G_def intro: dVs_subset)
  show ?thesis using assms sG by (auto simp: alt_distance_set_def)
qed

subsection \<open>alpha-2: edge tightness (derived, per TL-D5)\<close>

lemma valid_DAG_tight_unmatched:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and uv: "(u, v) \<in> Graph.digraph_abs T"
              "(u, v) \<in> Graph.digraph_abs unmatching"
  shows "altd_G Odd v = altd_G Even u + 1"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_ctxt V]
  have uT: "u \<in> dVs (Graph.digraph_abs T)" using uv(1) by (auto simp: dVs_def)
  have uE: "u \<in> t_set VisE"
    using P(3)[OF uv(1)] uv(2) matching_unmatching_disjoint[OF BFS_axiom_ctxt] by blast
  obtain s p where sp: "s \<in> t_set srcs" "alt_walk Even (Graph.digraph_abs T) s p u"
  proof (cases "u \<in> t_set srcs")
    case True
    have single: "alt_walk Even (Graph.digraph_abs T) u [u] u"
      using uT by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps alt_list_empty)
    show thesis by (rule that[OF True single])
  next
    case False
    have ne: "alt_distance_set (Graph.digraph_abs T) Even u \<noteq> \<infinity>"
      using P(11)[OF uE False] P(5)[OF uE] by simp
    show thesis using altd_set_witness[OF ne] that by blast
  qed
  have p_ne: "p \<noteq> []" using sp(2) by (auto simp: alt_dist.alt_vwalk_bet_def)
  have last_p: "last p = u"
    using sp(2) by (auto simp: alt_dist.alt_vwalk_bet_def dest: last_of_vwalk_bet)
  have step2: "alt_walk Odd (Graph.digraph_abs T) u [u, v] v"
    using uv by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps unmatched_edge_def
                           alt_list_empty alt_list_step edge_iff_vwalk_bet[symmetric])
  have w1: "alt_walk Even (Graph.digraph_abs T) s p (last p)" using sp(2) last_p by simp
  have w2: "next_alt_list_parity Even alt_dist.alt_vwalk_bet unmatched_edge matched_edge
              (other_parity Even) (Graph.digraph_abs T) (last p) (last p # [v]) v"
    using step2 last_p by (simp add: parity_simps)
  have pv: "alt_walk Odd (Graph.digraph_abs T) s (p @ [v]) v"
    by (rule alt_vwalk_bet_append_3[where parity = Even, OF w1 w2 p_ne])
  have l1: "enat (length (p @ [v]) - 1) = altd_G Odd v" using P(12)[OF sp(1) pv] .
  have l2: "enat (length p - 1) = altd_G Even u" using P(12)[OF sp(1) sp(2)] .
  have arith: "enat (length p) = enat (length p - 1) + 1"
    using p_ne by (cases p) (auto simp only: enat_simps diff_Suc_1 list.size)
  show ?thesis using l1 l2 arith by simp
qed

lemma valid_DAG_tight_matched:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and uv: "(u, v) \<in> Graph.digraph_abs T"
              "(u, v) \<in> Graph.digraph_abs matching"
  shows "altd_G Even v = altd_G Odd u + 1"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_ctxt V]
  have uO: "u \<in> t_set VisO"
    using P(3)[OF uv(1)] uv(2) matching_unmatching_disjoint[OF BFS_axiom_ctxt] by blast
  have ne: "alt_distance_set (Graph.digraph_abs T) Odd u \<noteq> \<infinity>"
    using P(10)[OF uO] P(4)[OF uO] by simp
  obtain s p where sp: "s \<in> t_set srcs" "alt_walk Odd (Graph.digraph_abs T) s p u"
    using altd_set_witness[OF ne] by blast
  have p_ne: "p \<noteq> []" using sp(2) by (auto simp: alt_dist.alt_vwalk_bet_def)
  have last_p: "last p = u"
    using sp(2) by (auto simp: alt_dist.alt_vwalk_bet_def dest: last_of_vwalk_bet)
  have step2: "alt_dist.alt_vwalk_bet matched_edge unmatched_edge Odd (Graph.digraph_abs T) u [u, v] v"
    using uv by (auto simp: alt_dist.alt_vwalk_bet_def parity_simps matched_edge_def
                           alt_list_empty alt_list_step edge_iff_vwalk_bet[symmetric])
  have w1: "alt_walk Odd (Graph.digraph_abs T) s p (last p)" using sp(2) last_p by simp
  have w2: "next_alt_list_parity Odd alt_dist.alt_vwalk_bet unmatched_edge matched_edge
              Odd (Graph.digraph_abs T) (last p) (last p # [v]) v"
    using step2 last_p by (simp add: parity_simps)
  have pv: "alt_walk Even (Graph.digraph_abs T) s (p @ [v]) v"
    by (rule alt_vwalk_bet_append_2[where parity = Odd, OF w1 w2 p_ne])
  have l1: "enat (length (p @ [v]) - 1) = altd_G Even v" using P(12)[OF sp(1) pv] .
  have l2: "enat (length p - 1) = altd_G Odd u" using P(12)[OF sp(1) sp(2)] .
  have arith: "enat (length p) = enat (length p - 1) + 1"
    using p_ne by (cases p) (auto simp only: enat_simps diff_Suc_1 list.size)
  show ?thesis using l1 l2 arith by simp
qed

subsection \<open>alpha-3: copies edges + level decrease\<close>

lemma copies_dagE:
  assumes "(w, w') \<in> copies_dag (Graph.digraph_abs T)"
  obtains u v where "w = Vtx Odd v" "w' = Vtx Even u"
      "(u, v) \<in> Graph.digraph_abs T" "(u, v) \<in> Graph.digraph_abs unmatching"
    | u v where "w = Vtx Even v" "w' = Vtx Odd u"
      "(u, v) \<in> Graph.digraph_abs T" "(u, v) \<in> Graph.digraph_abs matching"
  using assms by (auto simp: copies_dag_def)

lemma copies_lev_decrease:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and e: "(w, w') \<in> copies_dag (Graph.digraph_abs T)"
  shows "copies_lev w' < copies_lev w"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_ctxt V]
  from e show ?thesis
  proof (cases rule: copies_dagE)
    case (1 u v)
    have tight: "altd_G Odd v = altd_G Even u + 1"
      by (rule valid_DAG_tight_unmatched[OF V 1(3) 1(4)])
    have fin: "altd_G Even u \<noteq> \<infinity>"
      using P(5) P(3)[OF 1(3)] 1(4) matching_unmatching_disjoint[OF BFS_axiom_ctxt] by blast
    obtain n where n: "altd_G Even u = enat n" using fin by (cases "altd_G Even u") auto
    have vn: "altd_G Odd v = enat (n + 1)"
      using tight n by (simp only: enat_simps)
    have lw': "copies_lev (Vtx Even u) = n"
      using n by (simp only: copies_lev_def labelled_vtx.sel the_enat.simps)
    have lw: "copies_lev (Vtx Odd v) = n + 1"
      using vn by (simp only: copies_lev_def labelled_vtx.sel the_enat.simps)
    show ?thesis using 1(1) 1(2) lw lw' by simp
  next
    case (2 u v)
    have tight: "altd_G Even v = altd_G Odd u + 1"
      by (rule valid_DAG_tight_matched[OF V 2(3) 2(4)])
    have fin: "altd_G Odd u \<noteq> \<infinity>"
      using P(4) P(3)[OF 2(3)] 2(4) matching_unmatching_disjoint[OF BFS_axiom_ctxt] by blast
    obtain n where n: "altd_G Odd u = enat n" using fin by (cases "altd_G Odd u") auto
    have vn: "altd_G Even v = enat (n + 1)"
      using tight n by (simp only: enat_simps)
    have lw': "copies_lev (Vtx Odd u) = n"
      using n by (simp only: copies_lev_def labelled_vtx.sel the_enat.simps)
    have lw: "copies_lev (Vtx Even v) = n + 1"
      using vn by (simp only: copies_lev_def labelled_vtx.sel the_enat.simps)
    show ?thesis using 2(1) 2(2) lw lw' by simp
  qed
qed

subsection \<open>alpha-4: vertices + finiteness\<close>

lemma copies_dag_dVs:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
  shows "dVs (copies_dag (Graph.digraph_abs T))
           \<subseteq> Vtx Even ` t_set VisE \<union> Vtx Odd ` t_set VisO"
proof (rule subsetI)
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_ctxt V]
  fix x assume "x \<in> dVs (copies_dag (Graph.digraph_abs T))"
  then obtain a b where ab: "(a, b) \<in> copies_dag (Graph.digraph_abs T)" "x = a \<or> x = b"
    by (force simp: dVs_eq)
  from ab(1) show "x \<in> Vtx Even ` t_set VisE \<union> Vtx Odd ` t_set VisO"
  proof (cases rule: copies_dagE)
    case (1 u v)
    have "u \<in> t_set VisE" and "v \<in> t_set VisO"
      using P(3)[OF 1(3)] 1(4) matching_unmatching_disjoint[OF BFS_axiom_ctxt] by blast+
    thus ?thesis using ab(2) 1(1) 1(2) by auto
  next
    case (2 u v)
    have "u \<in> t_set VisO" and "v \<in> t_set VisE"
      using P(3)[OF 2(3)] 2(4) matching_unmatching_disjoint[OF BFS_axiom_ctxt] by blast+
    thus ?thesis using ab(2) 2(1) 2(2) by auto
  qed
qed

lemma copies_dag_finite:
  assumes V: "valid_alt_BFS_DAG_impl T dists VisE VisO"
  shows "finite (dVs (copies_dag (Graph.digraph_abs T)))"
proof -
  note P = valid_alt_BFS_DAG_impl_props[OF BFS_axiom_ctxt V]
  have fin: "finite (Vtx Even ` t_set VisE \<union> Vtx Odd ` t_set VisO)"
    using P(5) P(6) by simp
  show ?thesis by (rule finite_subset[OF copies_dag_dVs[OF P(7)] fin])
qed

subsection \<open>alpha-5: walk reversal to a copies path\<close>

lemma alt_walk_copies_path:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and s: "s \<in> t_set srcs"
      and w: "alt_walk parity (Graph.digraph_abs T) s p v"
      and mem: "Vtx parity v \<in> dVs (copies_dag (Graph.digraph_abs T))"
  shows "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T))
           (Vtx parity v) (copies_of parity (rev p)) (Vtx Even s)"
proof -
  from w mem show ?thesis
  proof (induction p arbitrary: parity v rule: rev_induct)
    case Nil
    then show ?case by (auto simp: alt_dist.alt_vwalk_bet_def)
  next
    case (snoc x xs)
    note IH = snoc(1) and wlk = snoc(2) and memb = snoc(3)
    have xv: "x = v" using wlk by (auto simp: alt_dist.alt_vwalk_bet_def dest: vwalk_bet_snoc)
    show ?case
    proof (cases "xs = []")
      case True
      have vb: "Vwalk.vwalk_bet (Graph.digraph_abs T) s [v] v"
        using wlk True xv by (auto simp: alt_dist.alt_vwalk_bet_def)
      have sv: "s = v" using hd_of_vwalk_bet'[OF vb] by simp
      have lenpar: "of_parity (other_parity parity) (length [v])"
        using wlk True xv by (auto simp: alt_dist.alt_vwalk_bet_def)
      have pe: "parity = Even" using lenpar by (cases parity) (simp_all add: parity_simps)
      have base: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T))
                    (Vtx Even v) [Vtx Even v] (Vtx Even v)"
        by (rule vwalk_bet_reflexive) (use memb pe in simp)
      show ?thesis using base sv pe True xv by simp
    next
      case False
      have len: "1 < length (xs @ [x])" using False by (cases xs) auto
      obtain q y where sn: "xs @ [x] = q @ [v]" "q \<noteq> []" "y = last q"
        "alt_walk (other_parity parity) (Graph.digraph_abs T) s q y"
        "(y, v) \<in> Graph.digraph_abs T"
        "case parity of Odd \<Rightarrow> unmatched_edge (y, v) | Even \<Rightarrow> matched_edge (y, v)"
        by (rule alt_walk_snocE[OF BFS_axiom_ctxt wlk len])
      have q_eq: "q = xs" using sn(1) xv by auto
      have edge: "(Vtx parity v, Vtx (other_parity parity) y) \<in> copies_dag (Graph.digraph_abs T)"
        using sn(5) sn(6)
        by (cases parity) (auto simp: copies_dag_def parity_simps unmatched_edge_def matched_edge_def)
      have memy: "Vtx (other_parity parity) y \<in> dVs (copies_dag (Graph.digraph_abs T))"
        using edge by (force simp: dVs_eq)
      have ihw: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx (other_parity parity) y)
                   (copies_of (other_parity parity) (rev xs)) (Vtx Even s)"
        using IH[OF sn(4)[unfolded q_eq] memy] .
      have two: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx parity v)
                   [Vtx parity v, Vtx (other_parity parity) y] (Vtx (other_parity parity) y)"
        by (rule iffD1[OF edge_iff_vwalk_bet edge])
      have y_eq: "hd (rev xs) = y" using sn(3) q_eq False by (simp add: hd_rev)
      have hd_eq: "copies_of (other_parity parity) (rev xs)
                     = Vtx (other_parity parity) y
                       # copies_of (other_parity (other_parity parity)) (tl (rev xs))"
        using copies_of_hd_tl[of "rev xs" "other_parity parity"] False y_eq by simp
      have res: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) (Vtx parity v)
                   ([Vtx parity v, Vtx (other_parity parity) y]
                      @ tl (copies_of (other_parity parity) (rev xs))) (Vtx Even s)"
        using vwalk_bet_transitive[OF two ihw] .
      show ?thesis using res hd_eq xv by simp
    qed
  qed
qed

subsection \<open>alpha-6: reaching level 0, and the main theorem\<close>

lemma copies_reach_zero:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and mem: "w \<in> dVs (copies_dag (Graph.digraph_abs T))"
  obtains p z where
    "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w p z" "copies_lev z = 0"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_ctxt V]
  have wmem: "w \<in> Vtx Even ` t_set VisE \<union> Vtx Odd ` t_set VisO"
    using copies_dag_dVs[OF V] mem by blast
  then consider (Ev) x where "w = Vtx Even x" "x \<in> t_set VisE"
              | (Od) x where "w = Vtx Odd x" "x \<in> t_set VisO"
    by blast
  then show thesis
  proof cases
    case (Ev x)
    show thesis
    proof (cases "x \<in> t_set srcs")
      case True
      have "copies_lev w = the_enat (altd_G Even x)"
        using Ev(1) by (simp only: copies_lev_def labelled_vtx.sel)
      also have "... = 0" using altd_G_srcs_Even_0[OF True] by (simp add: zero_enat_def)
      finally have l0: "copies_lev w = 0" .
      have base: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w [w] w"
        by (rule vwalk_bet_reflexive[OF mem])
      show thesis by (rule that[OF base l0])
    next
      case False
      have ne: "alt_distance_set (Graph.digraph_abs T) Even x \<noteq> \<infinity>"
        using P(11)[OF Ev(2) False] P(5)[OF Ev(2)] by simp
      obtain s p where sp: "s \<in> t_set srcs" "alt_walk Even (Graph.digraph_abs T) s p x"
        using altd_set_witness[OF ne] by blast
      have walk: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w
                    (copies_of Even (rev p)) (Vtx Even s)"
        using alt_walk_copies_path[OF V sp(1) sp(2)] mem Ev(1) by simp
      have l0: "copies_lev (Vtx Even s) = 0"
        using altd_G_srcs_Even_0[OF sp(1)]
        by (simp only: copies_lev_def labelled_vtx.sel) (simp add: zero_enat_def)
      show thesis by (rule that[OF walk l0])
    qed
  next
    case (Od x)
    have ne: "alt_distance_set (Graph.digraph_abs T) Odd x \<noteq> \<infinity>"
      using P(10)[OF Od(2)] P(4)[OF Od(2)] by simp
    obtain s p where sp: "s \<in> t_set srcs" "alt_walk Odd (Graph.digraph_abs T) s p x"
      using altd_set_witness[OF ne] by blast
    have walk: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) w
                  (copies_of Odd (rev p)) (Vtx Even s)"
      using alt_walk_copies_path[OF V sp(1) sp(2)] mem Od(1) by simp
    have l0: "copies_lev (Vtx Even s) = 0"
      using altd_G_srcs_Even_0[OF sp(1)]
      by (simp only: copies_lev_def labelled_vtx.sel) (simp add: zero_enat_def)
    show thesis by (rule that[OF walk l0])
  qed
qed

theorem valid_DAG_layered:
  assumes V: "valid_alt_BFS_DAG_impl T dists VisE VisO"
  shows "layered_dgraph (copies_dag (Graph.digraph_abs T)) copies_lev"
proof -
  note V' = valid_alt_BFS_DAG_impl_props(7)[OF BFS_axiom_ctxt V]
  show ?thesis
  proof (rule layered_dgraphI, goal_cases)
    case 1
    show ?case by (rule copies_dag_finite[OF V])
  next
    case (2 v v')
    show ?case by (rule copies_lev_decrease[OF V' 2])
  next
    case (3 v)
    obtain p z where pz: "Vwalk.vwalk_bet (copies_dag (Graph.digraph_abs T)) v p z"
      "copies_lev z = 0"
      by (rule copies_reach_zero[OF V' 3])
    show ?case using pz by blast
  qed
qed

corollary BFS_output_layered:
  "layered_dgraph (copies_dag (Graph.digraph_abs (parents (BFS initial_state)))) copies_lev"
  using valid_DAG_layered[OF BFS_valid_DAG_impl[OF BFS_axiom_ctxt]] .

subsection \<open>Milestone-2 down-payment: the level function from the distance map\<close>

lemma copies_lev_by_lookup:
  assumes V: "valid_alt_BFS_DAG T dists VisE VisO"
      and mem: "w \<in> dVs (copies_dag (Graph.digraph_abs T))"
  shows "copies_lev w = the_enat (the (lookup_dist dists w))"
proof -
  note P = valid_alt_BFS_DAG_props[OF BFS_axiom_ctxt V]
  have wmem: "w \<in> Vtx Even ` t_set VisE \<union> Vtx Odd ` t_set VisO"
    using copies_dag_dVs[OF V] mem by blast
  then consider (Ev) x where "w = Vtx Even x" "x \<in> t_set VisE"
              | (Od) x where "w = Vtx Odd x" "x \<in> t_set VisO"
    by blast
  then show ?thesis
  proof cases
    case (Ev x)
    have lk: "lookup_dist dists (Vtx Even x) = Some (altd_G Even x)" using P(9)[OF Ev(2)] .
    show ?thesis using lk Ev(1) by (simp add: copies_lev_def)
  next
    case (Od x)
    have lk: "lookup_dist dists (Vtx Odd x) = Some (altd_G Odd x)" using P(8)[OF Od(2)] .
    show ?thesis using lk Od(1) by (simp add: copies_lev_def)
  qed
qed

end \<comment> \<open>BFS_axiom context\<close>

end \<comment> \<open>locale BFS\<close>

end
