theory Awalk
  imports 
    "Adaptors/Pair_Graph_Library_Awalk_Adaptor"
    Vwalk               
begin

no_notation Digraph.dominates ("_ \<rightarrow>\<index> _")
no_notation Digraph.reachable1 ("_ \<rightarrow>\<^sup>+\<index> _")
no_notation Digraph.reachable ("_ \<rightarrow>\<^sup>*\<index> _")

lemma cas_simp:
  assumes "es \<noteq> []"
  shows "cas u es v \<longleftrightarrow> fst (hd es) = u \<and> cas (snd (hd es)) (tl es) v"
  using assms by (cases es) auto

lemma awalk_verts_conv:
  "awalk_verts u p = (if p = [] then [u] else map fst p @ [snd (last p)])"
  by (induction p arbitrary: u) auto

lemma awalk_verts_conv':
  assumes "cas u p v"
  shows "awalk_verts u p = (if p = [] then [u] else fst (hd p) # map snd p)"
  using assms by (induction u p v rule: cas.induct) (auto simp: cas_simp)

lemma awalk_verts_non_Nil[simp]:
  "awalk_verts u p \<noteq> []"
  by (simp add: awalk_verts_conv)

lemma
  assumes "cas u p v"
  shows awhd_if_cas: "awhd u p = u" and awlast_if_cas: "awlast u p = v"
  using assms by (induction p arbitrary: u) auto

lemma awalk_verts_in_verts:
  assumes "u \<in> dVs E" "set p \<subseteq> E" "v \<in> set (awalk_verts u p)"
  shows "v \<in> dVs E"
  using assms
  by (induction p arbitrary: u) (auto simp: dVsI, auto dest: dVsI(2))

lemma
  assumes "u \<in> dVs E" "set p \<subseteq> E"
  shows awhd_in_verts: "awhd u p \<in> dVs E"
    and awlast_in_verts: "awlast u p \<in> dVs E"
  using assms by (auto elim: awalk_verts_in_verts)

lemma awalk_conv:
  "awalk E u p v = (set (awalk_verts u p) \<subseteq> dVs E
    \<and> set p \<subseteq> E
    \<and> awhd u p = u \<and> awlast u p = v \<and> cas u p v)"
  unfolding awalk_def using hd_in_set[OF awalk_verts_non_Nil, of u p]
  by (auto intro: awalk_verts_in_verts awhd_if_cas awlast_if_cas simp del: hd_in_set)

lemma awalkI:
  assumes "set (awalk_verts u p) \<subseteq> dVs E" "set p \<subseteq> E" "cas u p v"
  shows "awalk E u p v"
  using assms by (auto simp: awalk_conv awhd_if_cas awlast_if_cas)

lemma awalkE[elim]:
  assumes "awalk E u p v"
  obtains "set (awalk_verts u p) \<subseteq> dVs E" "set p \<subseteq> E" "cas u p  v"
    "awhd u p = u" "awlast u p = v"
  using assms by (auto simp: awalk_conv)

lemma awalk_Nil_iff:
  "awalk E u [] v \<longleftrightarrow> u = v \<and> u \<in> dVs E"
  unfolding awalk_def by auto

lemma hd_in_awalk_verts:
  "awalk E u p v \<Longrightarrow> u \<in> set (awalk_verts u p)"
  by (cases p) auto

lemma awalk_Cons_iff:
  shows "awalk E u (e # es) w \<longleftrightarrow> e \<in> E \<and> fst e = u \<and> awalk E (snd e) es w"
  by (auto simp: awalk_def cas_simp dVsI')

lemmas awalk_simps = awalk_Nil_iff awalk_Cons_iff

lemma arc_implies_awalk:
  "e \<in> E \<Longrightarrow> e = (u, v) \<Longrightarrow> awalk E u [e] v"
  by (simp add: awalk_simps dVsI)

lemma awalkI_apath:
  assumes "apath E u p v" shows "awalk E u p v"
  using assms by (simp add: apath_def)

lemma set_awalk_verts_cas:
  assumes "cas u p v"
  shows "set (awalk_verts u p) = {u} \<union> set (map fst p) \<union> set (map snd p)"
  using assms
  by (induction p arbitrary: u) (fastforce simp: image_iff)+

lemma set_awalk_verts_not_Nil_cas:
  assumes "cas u p v" "p \<noteq> []"
  shows "set (awalk_verts u p) = set (map fst p) \<union> set (map snd p)"
proof -
  have "u \<in> set (map fst p)" using assms by (cases p) auto
  with assms show ?thesis by (auto simp: set_awalk_verts_cas)
qed

lemma set_awalk_verts:
  assumes "awalk E u p v"
  shows "set (awalk_verts u p) = {u} \<union> set (map fst p) \<union> set (map snd p)"
  using assms by (intro set_awalk_verts_cas) blast

lemma set_awalk_verts_not_Nil:
  assumes "awalk E u p v" "p \<noteq> []"
  shows "set (awalk_verts u p) = set (map fst p) \<union> set (map snd p)"
  using assms by (intro set_awalk_verts_not_Nil_cas) blast

lemma
  awhd_of_awalk: "awalk E u p v \<Longrightarrow> awhd u p = u" and
  awlast_of_awalk: "awalk E u p v \<Longrightarrow> NOMATCH (awlast u p) v \<Longrightarrow> awlast u p = v"
  unfolding NOMATCH_def
  by auto
lemmas awends_of_awalk[simp] = awhd_of_awalk awlast_of_awalk

lemma cas_append_iff[simp]:
  "cas u (p @ q) v \<longleftrightarrow> cas u p (awlast u p) \<and> cas (awlast u p) q v"
  by (induction u p v rule: cas.induct) auto

lemma cas_ends:
  assumes "cas u p v" "cas u' p v'"
  shows "(p \<noteq> [] \<and> u = u' \<and> v = v') \<or> (p = [] \<and> u = v \<and> u' = v')"
  using assms by (induction u p v arbitrary: u u' rule: cas.induct) auto

lemma awalk_ends:
  assumes "awalk E u p v" "awalk E u' p v'"
  shows "(p \<noteq> [] \<and> u = u' \<and> v = v') \<or> (p = [] \<and> u = v \<and> u' = v')"
  using assms by (simp add: awalk_def cas_ends)

lemma awalk_ends_eqD:
  assumes "awalk E u p u" "awalk E v p w"
  shows "v = w"
  using awalk_ends[OF assms] by auto

lemma awalk_append_iff[simp]:
  "awalk E u (p @ q) v \<longleftrightarrow> awalk E u p (awlast u p) \<and> awalk E (awlast u p) q v"
  by (auto simp: awalk_def intro: awlast_in_verts)

declare awalkE[rule del]

lemma awalkE'[elim]:
  assumes "awalk E u p v"
  obtains "set (awalk_verts u p) \<subseteq> dVs E" "set p \<subseteq> E" "cas u p v"
    "awhd u p = u" "awlast u p = v" "u \<in> dVs E" "v \<in> dVs E"
  using assms
  by (auto elim!: awalkE simp: awlast_in_verts, auto simp: awalk_def)

lemma awalk_appendI:
  assumes "awalk E u p v"
  assumes "awalk E v q w"
  shows "awalk E u (p @ q) w"
  using assms by auto

lemma cas_takeI:
  assumes "cas u p v" "awlast u (take n p) = v'"
  shows "cas u (take n p) v'"
proof -
  from assms have "cas u (take n p @ drop n p) v" by simp
  with assms show ?thesis unfolding cas_append_iff by simp
qed

lemma awalk_verts_take_conv:
  assumes "cas u p v"
  shows "awalk_verts u (take n p) = take (Suc n) (awalk_verts u p)"
proof -
  from assms have "cas u (take n p) (awlast u (take n p))" by (auto intro: cas_takeI)
  with assms show ?thesis
    by (cases n p rule: nat.exhaust[case_product list.exhaust])
       (auto simp: awalk_verts_conv' take_map simp del: awalk_verts.simps)
qed

lemma awalk_verts_drop_conv:
  assumes "cas u p v"
  shows "awalk_verts u' (drop n p) = (if n < length p then drop n (awalk_verts u p) else [u'])"
  using assms by (auto simp: awalk_verts_conv drop_map)

lemma awalk_decomp_verts:
  assumes cas: "cas u p v" and ev_decomp: "awalk_verts u p = xs @ y  # ys"
  obtains q r where "cas u q y" "cas y r v" "p = q @ r" "awalk_verts u q = xs @ [y]"
    "awalk_verts y r = y # ys"
proof -
  define q r where "q = take (length xs) p" and "r = drop (length xs) p"
  then have p: "p = q @ r" by simp
  moreover from p have "cas u q (awlast u q)" "cas (awlast u q) r v"
    using \<open>cas u p v\<close> by auto
  moreover have "awlast u q = y"
    using q_def and assms by (auto simp: awalk_verts_take_conv)
  moreover have *:"awalk_verts u q = xs @ [awlast u q]"
    using assms q_def by (auto simp: awalk_verts_take_conv)
  moreover from * have "awalk_verts y r = y # ys"
    unfolding q_def r_def using assms by (auto simp: awalk_verts_drop_conv not_less)
  ultimately show ?thesis by (intro that) auto
qed

lemma awalk_decomp:
  assumes "awalk E u p v"
    and "w \<in> set (awalk_verts u p)"
  shows "\<exists>q r. p = q @ r \<and> awalk E u q w \<and> awalk E w r v"
proof -
  from assms have "cas u p v" by auto
  moreover from assms obtain xs ys where
    "awalk_verts u p = xs @ w # ys" by (auto simp: in_set_conv_decomp)
  ultimately
  obtain q r where "cas u q w" "cas w r v" "p = q @ r" "awalk_verts u q = xs @ [w]"
    by (auto intro: awalk_decomp_verts)
  with assms show ?thesis by auto
qed

lemma awalk_not_distinct_decomp:
  assumes "awalk E u p v"
  assumes "\<not>distinct (awalk_verts u p)"
  obtains q r s w where "p = q @ r @ s" 
    "distinct (awalk_verts u q)"
    "0 < length r"
    "awalk E u q w" "awalk E w r w" "awalk E w s v"
proof -
  from assms
  obtain xs ys zs y where
    pv_decomp: "awalk_verts u p = xs @ y # ys @ y # zs"
    and xs_y_props: "distinct xs" "y \<notin> set xs" "y \<notin> set ys"
    using not_distinct_decomp_min_prefix by blast

  obtain q p' where "cas u q y" "p = q @ p'" "awalk_verts u q = xs @ [y]"
    and p'_props: "cas y p' v" "awalk_verts y p' = (y # ys) @ y # zs"
    using assms pv_decomp by - (rule awalk_decomp_verts, auto)
  obtain r s where "cas y r y" "cas y s v" "p' = r @ s"
    "awalk_verts y r = y # ys @ [y]" "awalk_verts y s = y # zs"
    using p'_props by (rule awalk_decomp_verts) auto

  have "p =  q @ r @ s" using \<open>p = q @ p'\<close> \<open>p' = r @ s\<close> by simp
  moreover
  have "distinct (awalk_verts u q)" using \<open>awalk_verts u q = xs @ [y]\<close> xs_y_props by simp
  moreover
  have "0 < length r" using \<open>awalk_verts y r = y # ys @ [y]\<close> by auto
  moreover
  from pv_decomp assms have "y \<in> dVs E" by auto
  then have "awalk E u q y" "awalk E y r y" "awalk E y s v"
    using \<open>awalk E u p v\<close> \<open>cas u q y\<close> \<open>cas y r y\<close> \<open>cas y s v\<close> unfolding \<open>p = q @ r @ s\<close>
    by (auto simp: awalk_def)
  ultimately show ?thesis using that by blast
qed

lemma awalk_cyc_decomp_has_prop:
  assumes "awalk E u p v" and "\<not>distinct (awalk_verts u p)"
  shows "is_awalk_cyc_decomp E p (awalk_cyc_decomp E p)"
proof -
  obtain q r s w where "p = q @ r @ s" "distinct (awalk_verts u q)"
      "0 < length r" "awalk E u q w" "awalk E w r w" "awalk E w s v"
    by (auto intro: awalk_not_distinct_decomp[OF assms])
  then have "\<exists>x. is_awalk_cyc_decomp E p x"
    by (auto intro: exI[where x="(q,r,s)"]) blast
  then show ?thesis unfolding awalk_cyc_decomp_def ..
qed

lemma awalk_cyc_decompE:
  assumes dec: "awalk_cyc_decomp E p = (q,r,s)"
  assumes p_props: "awalk E u p v" "\<not>distinct (awalk_verts u p)"
  obtains "p = q @ r @ s" "distinct (awalk_verts u q)" 
    "\<exists>w. awalk E u q w \<and> awalk E w r w \<and> awalk E w s v" "closed_w E r"
proof
  show "p = q @ r @ s" "distinct (awalk_verts u q)" "closed_w E r"
    using awalk_cyc_decomp_has_prop[OF p_props] and dec
      imageI[of "(snd (last q), _)" "set q" fst]
    by (auto simp: closed_w_def awalk_verts_conv)
  then have "p \<noteq> []" by (auto simp: closed_w_def)

  obtain u' w' v' where obt_awalk: "awalk E u' q w'" "awalk E w' r w'" "awalk E w' s v'"
    using awalk_cyc_decomp_has_prop[OF p_props] and dec by auto
  then have "awalk E u' p v'" 
    using \<open>p = q @ r @ s\<close> by simp
  then have "u = u'" and "v = v'" using \<open>p \<noteq> []\<close> \<open>awalk E u p v\<close> by (auto dest: awalk_ends)
  then have "awalk E u q w'" "awalk E w' r w'" "awalk E w' s v"
    using obt_awalk by auto
  then show "\<exists>w. awalk E u q w \<and> awalk E w r w \<and> awalk E w s v" by auto
qed

lemma awalk_to_apath_induct[consumes 1, case_names path decomp]:
  assumes awalk: "awalk E u p v"
  assumes dist: "\<And>p. awalk E u p v \<Longrightarrow> distinct (awalk_verts u p) \<Longrightarrow> P p"
  assumes dec: "\<And>p q r s. \<lbrakk>awalk E u p v; awalk_cyc_decomp E p = (q, r, s);
    \<not>distinct (awalk_verts u p); P (q @ s)\<rbrakk> \<Longrightarrow> P p"
  shows "P p"
  using awalk
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  then show ?case
  proof (cases "distinct (awalk_verts u p)")
    case True
    then show ?thesis by (auto intro: dist less.prems)
  next
    case False
    obtain q r s where p_cdecomp: "awalk_cyc_decomp E p = (q, r, s)"
      by (cases "awalk_cyc_decomp E p") auto
    then have "is_awalk_cyc_decomp E p (q, r, s)" "p = q @ r @ s"
      using awalk_cyc_decomp_has_prop[OF less.prems(1) False] by auto
    then have "length (q @ s) < length p" "awalk E u (q @ s) v"
      using less.prems by (auto dest!: awalk_ends_eqD)
    then have "P (q @ s)" by (auto intro: less)

    with p_cdecomp False show ?thesis by (auto intro: dec less.prems)
  qed
qed

lemma step_awalk_to_apath:
  assumes awalk: "awalk E u p v"
    and decomp: "awalk_cyc_decomp E p = (q, r, s)"
    and dist: "\<not>distinct (awalk_verts u p)"
  shows "awalk_to_apath E p = awalk_to_apath E (q @ s)"
proof -
  from dist have "\<not>(\<exists>u. distinct (awalk_verts u p))"
    by (auto simp: awalk_verts_conv)
  with awalk and decomp show "awalk_to_apath E p = awalk_to_apath E (q @ s)"
    by (auto simp: awalk_to_apath.simps)
qed

lemma apath_awalk_to_apath:
  assumes "awalk E u p v"
  shows "apath E u (awalk_to_apath E p) v"
  using assms
proof (induction rule: awalk_to_apath_induct)
  case (path p)
  then have "awalk_to_apath E p = p" by (auto simp: awalk_to_apath.simps)
  then show ?case using path by (auto simp: apath_def)
next
  case (decomp p q r s)
  then show ?case using step_awalk_to_apath[of _ _ p _ q r s] by simp
qed

lemma reachable1_awalk:
  "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. awalk E u p v \<and> p \<noteq> [])"
proof
  assume "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v" then show "\<exists>p. awalk E u p v \<and> p \<noteq> []"
    by (induct rule: converse_trancl_induct)
       (auto intro: arc_implies_awalk awalk_appendI)
next
  assume "\<exists>p. awalk E u p v \<and> p \<noteq> []" then obtain p where "awalk E u p v" "p \<noteq> []" by auto
  thus "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  proof (induct p arbitrary: u)
    case (Cons a p)
    then show ?case 
      by (cases "p = []") 
         (auto simp: awalk_simps trancl_into_trancl2 simp del: prod.collapse dest: arc_implies_dominates)
  qed simp
qed

lemma reachable_awalk:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. awalk E u p v)"
proof cases
  assume "u = v"
  have "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> u \<longleftrightarrow> awalk E u [] u" by (auto simp: awalk_Nil_iff reachable_in_dVs)
  then show ?thesis using \<open>u = v\<close> by auto                 
next
  assume "u \<noteq> v"
  then have "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>p. awalk E u p v)" 
    using \<open>u \<noteq> v\<close> unfolding reachable1_awalk by force
  finally show ?thesis .
qed

lemma awalk_verts_reachable_from:
  assumes "awalk E u p v" "w \<in> set (awalk_verts u p)" shows "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
proof -
  obtain s where "awalk E u s w" using awalk_decomp[OF assms] by blast
  then show ?thesis by (auto simp: reachable_awalk)
qed

lemma awalk_verts_reachable_to:
  assumes "awalk E u p v" "w \<in> set (awalk_verts u p)" shows "w \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
proof -
  obtain s where "awalk E w s v" using awalk_decomp[OF assms] by blast
  then show ?thesis by (auto simp: reachable_awalk)
qed

subsection \<open>Vertex walks\<close>
lemma awalk_imp_vwalk:
  assumes "awalk E u p v" shows "vwalk_bet E u (awalk_verts u p) v"
  using assms
  by (induction p arbitrary: u rule: edges_of_vwalk.induct)
     (auto simp: awalk_simps vwalk_bet_reflexive edges_are_vwalk_bet vwalk_bet_def)

lemma awalkE_vwalk:
  assumes "awalk E u p v"
  obtains p' where "p' = awalk_verts u p" "vwalk_bet E u p' v"
  using assms
  by (auto dest: awalk_imp_vwalk)

lemma vwalk_imp_awalk:
  "vwalk_bet E u p v \<Longrightarrow> awalk E u (edges_of_vwalk p) v"
  unfolding vwalk_bet_def
  by (induction p arbitrary: u rule: edges_of_vwalk.induct)
     (auto simp: awalk_Nil_iff arc_implies_awalk awalk_Cons_iff)

lemma vwalkE_awalk:
  assumes "vwalk_bet E u p v"
  obtains p' where "p' = edges_of_vwalk p" "awalk E u p' v"
  using assms
  by (auto dest: vwalk_imp_awalk)

end