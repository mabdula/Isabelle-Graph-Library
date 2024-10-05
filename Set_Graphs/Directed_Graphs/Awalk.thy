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

lemma awalk_to_apath_subset:
  "awalk E u p v \<Longrightarrow> set (awalk_to_apath E p) \<subseteq> set p"
proof (induction p arbitrary: u v rule: awalk_to_apath_induct)
  case (path p)
  then have "awalk_to_apath E p = p"
    by (meson awalk_to_apath.simps)
  then show ?case by simp
next
  case (decomp p q r s)
  with step_awalk_to_apath
    have "awalk_to_apath E p = awalk_to_apath E (q @ s)" by force
  moreover have "set (q @ s) \<subseteq> set p"
    using awalk_cyc_decomp_def awalk_cyc_decomp_has_prop[OF \<open>awalk E u p v\<close> \<open>\<not> distinct (awalk_verts u p)\<close>]
     using decomp.hyps(2) by auto
  ultimately show ?case
    using \<open>set (awalk_to_apath E (q @ s)) \<subseteq> set (q @ s)\<close> by auto
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


subsection \<open>Additional lemmas (TODO maybe change section name)\<close>

(* These theorems are relevant for the instantiation of the greedy algorithm as Kruskal's algorithm *)
(* TODO maybe simplify proofs of these lemmas *)


lemma vwalk_other_edge_set:
  "Vwalk.vwalk E p \<Longrightarrow> \<forall>x \<in> dVs (E - E'). x \<notin> set p \<Longrightarrow> Vwalk.vwalk E' p"
  apply (induction rule: Vwalk.vwalk.induct)
  apply simp
  apply (meson DiffI in_dVsE(1) in_dVsE(2) list.set_intros(1) vwalk1)
  by auto

lemma vwalk_bet_other_edge_set:
  "Vwalk.vwalk_bet E u p v \<Longrightarrow> \<not>Vwalk.vwalk_bet E' u p v \<Longrightarrow> \<exists>x \<in> dVs (E - E'). x \<in> set p"
  using vwalk_bet_def vwalk_other_edge_set by metis 

lemma awalk_other_edge_set:
  "u \<noteq> v \<Longrightarrow> awalk E u p v \<Longrightarrow> \<not>awalk E' u p v \<Longrightarrow> \<exists>e. e \<in> (E - E') \<and> e \<in> set p"
  by (metis (no_types, lifting) DiffI awalk_def awalk_ends cas_simp dVsI'(1) list.set_sel(1) subset_code(1))

lemma awalk_hd_in_set:
  "awalk G u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> set p \<subseteq> X \<Longrightarrow> u \<in> dVs X"
  by (metis (mono_tags, lifting) awalkE' cas_simp dVsI'(1) in_mono list.set_sel(1))


lemma edges_of_vwalk_length_geq_2:
  "length p \<ge> 3 \<Longrightarrow> length (edges_of_vwalk p) \<ge> 2"
  apply (induction p rule: edges_of_vwalk.induct)
  by (simp add: edges_of_vwalk_length)+

lemma awalk_vwalk_id:
  "p \<noteq> [] \<Longrightarrow> hd p = x \<Longrightarrow> awalk_verts x (edges_of_vwalk p) = p"
  apply (induction p arbitrary: x)
  apply simp
  by (smt (verit) Pair_inject awalk_verts.elims edges_of_vwalk.elims list.sel(1) list.sel(3) list.simps(3))
  
lemma vwalk_rev:
  "\<forall>(x, y) \<in> E. (y, x) \<in> E \<Longrightarrow> Vwalk.vwalk E p \<Longrightarrow> Vwalk.vwalk E (rev p)"
  apply (induction p)
  apply simp
  by (metis append_Nil case_prod_conv last_rev rev.simps(2) rev_is_Nil_conv vwalk_ConsE vwalk_append_single)
  
lemma awalk_verts_cons:
  "awalk E u ([(x, y)] @ xs) v \<Longrightarrow> awalk_verts u ([(x, y)] @ xs) = [x, y] @ tl (awalk_verts u xs)"
  by (smt (verit, best) append.left_neutral append_Cons awalkE awalk_verts.elims awalk_verts.simps(2)
  cas.simps(2) list.sel(3))

lemma awalk_verts_snoc:
  "l = xs @ [(x, y)] \<Longrightarrow> \<exists>ys. awalk_verts u l = ys @ [x, y]"
  apply (induction l arbitrary: xs x y u)
  apply blast
  by (smt (z3) append.left_neutral append_Cons awalk_verts.simps(1) awalk_verts.simps(2) list.exhaust
  list.inject old.prod.exhaust)

lemma awalk_verts_length:
  "awalk E u p v \<Longrightarrow> length (awalk_verts u p) = length p + 1"
  by (metis Suc_eq_plus1 awalk_def awalk_verts_conv' length_Cons length_map list.size(3))

lemma cas_rev:
  "cas u p v \<Longrightarrow> cas v (rev (map prod.swap p)) u"
  apply (induction p arbitrary: u v)
  apply simp
  by (smt (verit, best) awlast_if_cas cas.elims(2) cas.simps(1) cas.simps(2) cas_append_iff
     list.distinct(1) list.sel(3) list.simps(9) rev.simps(2) swap_simp)

lemma awalk_rev:
  "\<forall>e \<in> G. prod.swap e \<in> G \<Longrightarrow> awalk G u p v \<Longrightarrow> awalk G v (rev (map prod.swap p)) u"
proof-
  assume "\<forall>e \<in> G. prod.swap e \<in> G" "awalk G u p v"
  then have "cas u p v" by auto

  from \<open>awalk G u p v\<close> have 1: "v \<in> dVs G" by blast
  from \<open>awalk G u p v\<close> \<open>\<forall>e \<in> G. prod.swap e \<in> G\<close>
    have 2: "set (rev (map prod.swap p)) \<subseteq> G" by fastforce
  from cas_rev[OF \<open>cas u p v\<close>] have 3: "cas v (rev (map prod.swap p)) u" .
  from 1 2 3 show "awalk G v (rev (map prod.swap p)) u" unfolding awalk_def by blast
qed





lemma cycle'_edges_subset:
  "cycle' E p \<Longrightarrow> set p \<subseteq> E"
  unfolding cycle'_def Awalk_Defs.cycle_def Awalk_Defs.awalk_def by blast

lemma cycle'_imp_awalk:
  "cycle' E p \<Longrightarrow> \<exists>u. awalk E u p u"
  unfolding cycle'_def Awalk_Defs.cycle_def by blast

lemma cycle'_imp_length_greater_2:
  "cycle' E p \<Longrightarrow> length p > 2"
  unfolding cycle'_def by blast

lemma cycle'_imp_awalk_verts_distinct:
  "cycle' E p \<Longrightarrow> awalk E u p u \<Longrightarrow> distinct (butlast (awalk_verts u p))"
proof-
  assume "cycle' E p" "awalk E u p u"
  from cycle'_imp_length_greater_2[OF \<open>cycle' E p\<close>] awalk_verts_length[OF \<open>awalk E u p u\<close>]
    have "\<exists>xs. awalk_verts u p = [fst (hd p)] @ xs @ [snd (last p)]"    
    by (smt (verit) \<open>cycle' E p\<close> append_Cons append_Nil awalk_verts.elims awalk_verts_conv cycle'_def
      cycle_def fst_conv list.sel(1) list.sel(3) tl_append2)
  with \<open>awalk E u p u\<close>
    have "\<exists>xs. awalk_verts u p = [u] @ xs @ [u]" by auto
  then obtain xs where "awalk_verts u p = [u] @ xs @ [u]" by blast
  moreover have "distinct (tl (awalk_verts u p))"
    using \<open>cycle' E p\<close> cycle'_def cycle_def \<open>awalk E u p u\<close>
    by (metis awalk_verts_conv)
  ultimately show
    "distinct (butlast (awalk_verts u p))" by simp
qed


lemma cycle'_adj_edge1:
  "cycle' E p \<Longrightarrow> v \<noteq> w \<Longrightarrow> (v, w) \<in> set p \<Longrightarrow> (\<exists>z. (w, z) \<in> set p \<and> z \<noteq> v)"
proof (cases "(v, w) = last p")
  case True
  assume "cycle' E p" "v \<noteq> w" "(v, w) \<in> set p"
  from cycle'_imp_awalk[OF `cycle' E p`]
    obtain u where "awalk E u p u" by blast
  then have "awlast u p = u"
    by simp
  moreover have "awlast u p = w"
    using \<open>awalk E u p u\<close> \<open>(v, w) = last p\<close> awalk_verts_conv
    by (metis \<open>(v, w) \<in> set p\<close> empty_iff empty_set last_snoc snd_conv)
  ultimately have "u = w" by auto

  from \<open>awalk E u p u\<close>
    have "awhd u p = u" by blast
  then have "fst (hd p) = u" 
    by (metis \<open>awalk E u p u\<close> \<open>cycle' E p\<close> awalkE' cas_simp cycle'_def cycle_def)

  from \<open>v \<noteq> w\<close> \<open>fst (hd p) = u\<close> \<open>u = w\<close>
    have "(hd p) \<noteq> (v, w)"
    by (metis fst_conv)

  from \<open>(v, w) = last p\<close> \<open>(hd p) \<noteq> (v, w)\<close>
    have "\<exists>xs. p = [hd p] @ xs @ [(v, w)]" 
    by (metis (no_types, opaque_lifting) \<open>(v, w) \<in> set p\<close> append.left_neutral append_Cons
    append_butlast_last_id last_snoc list.distinct(1) list.exhaust_sel split_list)
  then obtain xs where "p = [(fst (hd p), snd (hd p))] @ xs @ [(v, w)]" by auto
  with awalk_verts_cons \<open>awalk E u p u\<close>
    have awalk_verts_p: "awalk_verts u ([(fst (hd p), snd (hd p))] @ (xs @ [(v, w)])) =
      [fst (hd p), snd (hd p)] @ tl (awalk_verts u (xs @ [(v, w)]))"
    by metis
  from awalk_verts_snoc
    obtain ys where "awalk_verts u (xs @ [(v, w)]) = ys @ [v, w]" by fastforce
  with awalk_verts_p \<open>p = [(fst (hd p), snd (hd p))] @ xs @ [(v, w)]\<close>
    have "awalk_verts u p = [fst (hd p), snd (hd p)] @ tl (ys @ [v, w])" by auto
  moreover have "ys \<noteq> []"
    by (metis One_nat_def Suc_eq_plus1 cycle'_imp_length_greater_2[OF \<open>cycle' E p\<close>] awalk_verts_conv butlast_snoc
    \<open>awalk_verts u p = [fst (hd p), snd (hd p)] @ tl (ys @ [v, w])\<close>
    length_map linorder_neq_iff list.sel(3) list.size(3) list.size(4) nat_1_add_1 self_append_conv2)
  ultimately have "awalk_verts u p = [fst (hd p), snd (hd p)] @ tl ys @ [v, w]"
    by auto
  then have "tl (awalk_verts u p) = [snd (hd p)] @ tl ys @ [v, w]" by simp 
  moreover have "distinct (tl (awalk_verts u p))"
    using \<open>cycle' E p\<close> cycle'_def cycle_def
    by (metis \<open>awalk E u p u\<close> awalk_ends)
  ultimately have "snd (hd p) \<noteq> v" by simp

  from \<open>fst (hd p) = u\<close> \<open>u = w\<close> \<open>snd (hd p) \<noteq> v\<close>
    show ?thesis
    by (metis \<open>(v, w) \<in> set p\<close> list.set_cases list.set_sel(1) list.simps(3) prod.collapse)
next
  case False
  assume "cycle' E p" "v \<noteq> w" "(v, w) \<in> set p"
  from cycle'_imp_awalk[OF `cycle' E p`]
    obtain u where "awalk E u p u" by blast

  have "\<exists>xs ys. p = xs @ [(v, w)] @ ys"
    by (metis \<open>(v, w) \<in> set p\<close> append_Cons append_Nil in_set_conv_decomp_first)
  then obtain xs ys where "p = xs @ [(v, w)] @ ys" by blast
  from cycle'_imp_length_greater_2[OF \<open>cycle' E p\<close>] False this
    have "ys \<noteq> []" by auto
  with \<open>p = xs @ [(v, w)] @ ys\<close>
    obtain x y where "p = xs @ [(v, w), (x, y)] @ tl ys"
    by (metis append_Cons append_Nil list.collapse prod.collapse)
  with \<open>awalk E u p u\<close> awalk_def
    have "cas u (xs @ [(v, w), (x, y)] @ tl ys) u" by blast
  then have "w = x" by simp

  have "distinct (tl (awalk_verts u p))"
    using \<open>cycle' E p\<close> cycle'_def cycle_def
    by (metis \<open>awalk E u p u\<close> awalk_ends)

  have "y \<noteq> v"
  proof (cases "tl ys")
    case Nil
    with cycle'_imp_length_greater_2[OF \<open>cycle' E p\<close>] \<open>p = xs @ [(v, w), (x, y)] @ tl ys\<close>
      have "xs \<noteq> []" by simp
    with \<open>p = xs @ [(v, w), (x, y)] @ tl ys\<close> Nil
      have "p = butlast xs @ [last xs, (v, w), (x, y)]"
      by auto
    with awalk_verts_conv[of "u" "p"] map_append
      have "awalk_verts u p = (map fst (butlast xs)) @ [fst (last xs), v, x, y]"
      by auto
    then have "\<exists>zs. tl (awalk_verts u p) = zs @ [v, x, y]"
      by (metis append.assoc append_Cons append_Nil list.sel(3) tl_append2)
    with \<open>distinct (tl (awalk_verts u p))\<close>
      show ?thesis by auto
  next
    case (Cons hd_tl_ys zs)
    with \<open>p = xs @ [(v, w), (x, y)] @ tl ys\<close>
      have "p = xs @ [(v, w), (x, y), hd_tl_ys] @ zs" by simp
    with \<open>awalk E u p u\<close> awalk_def
      have "cas u (xs @ [(v, w), (x, y), hd_tl_ys] @ zs) u" by blast
    with \<open>p = xs @ [(v, w), (x, y), hd_tl_ys] @ zs\<close> append_assoc
      have "y = fst hd_tl_ys" 
      by (smt (verit, best) cas.simps(2) cas_append_iff prod.collapse)
    with \<open>p = xs @ [(v, w), (x, y), hd_tl_ys] @ zs\<close>
      have "p = xs @ [(v, w), (x, y), (y, snd hd_tl_ys)] @ zs" by simp
    show ?thesis
    proof (cases xs)
      case Nil
      with \<open>p = xs @ [(v, w), (x, y), (y, snd hd_tl_ys)] @ zs\<close>
        have "v = awhd u p" by simp
      with \<open>awalk E u p u\<close> have "snd (last p) = v"
        by (metis \<open>(v, w) \<in> set p\<close> awalkE' awalk_verts_conv empty_iff empty_set last_snoc)
      with \<open>p = xs @ [(v, w), (x, y), (y, snd hd_tl_ys)] @ zs\<close> awalk_verts_conv Nil
        have "awalk_verts u p = [v, x, y] @ (map fst zs) @ [v]"
        by (metis (no_types, lifting) append_Cons append_Nil fst_conv list.simps(3) list.simps(9))
      then have "tl (awalk_verts u p) = [x, y] @ (map fst zs) @ [v]" by simp
      with \<open>distinct (tl (awalk_verts u p))\<close>
        show ?thesis by auto
    next
      case (Cons hd_xs tl_xs)
      with \<open>p = xs @ [(v, w), (x, y), (y, snd hd_tl_ys)] @ zs\<close>
        have "p = butlast xs @ [last xs, (v, w), (x, y), (y, snd hd_tl_ys)] @ zs"
        by auto
      with awalk_verts_conv[of "u" "p"] map_append
        have "awalk_verts u p = (map fst (butlast xs)) @ [fst (last xs), v, x, y] @ (map fst zs) @ [(snd (last p))]"
        by auto
      then have "\<exists>as. tl (awalk_verts u p) = as @ [v, x, y] @ (map fst zs) @ [(snd (last p))]"
        by (metis append.assoc append_Cons append_Nil list.sel(3) tl_append2)
      with \<open>distinct (tl (awalk_verts u p))\<close>
        show ?thesis by auto
    qed
  qed
    
  from \<open>p = xs @ [(v, w), (x, y)] @ tl ys\<close> \<open>w = x\<close> \<open>y \<noteq> v\<close>
    show ?thesis by auto
qed

lemma cycle'_adj_edge2:
  "cycle' E p \<Longrightarrow> v \<noteq> w \<Longrightarrow> (w, v) \<in> set p \<Longrightarrow> (\<exists>z. (z, w) \<in> set p \<and> z \<noteq> v)"
proof (cases "(w, v) = hd p")
  case True
  assume "cycle' E p" "v \<noteq> w" "(w, v) \<in> set p"
  from cycle'_imp_awalk[OF `cycle' E p`]
    obtain u where "awalk E u p u" by blast
  then have "awhd u p = u"
    by simp
  moreover have "awhd u p = w"
    using \<open>awalk E u p u\<close> \<open>(w, v) = hd p\<close>
    by (metis \<open>(w, v) \<in> set p\<close> awalk_Cons_iff calculation fst_eqD hd_Cons_tl list.distinct(1) list.set_cases)
  ultimately have "u = w" by auto

  from \<open>awalk E u p u\<close>
    have "awlast u p = u" by blast
  then have "snd (last p) = u" 
    by (metis \<open>(w, v) \<in> set p\<close> awalk_verts_conv last_snoc length_greater_0_conv length_pos_if_in_set)

  from \<open>v \<noteq> w\<close> \<open>snd (last p) = u\<close> \<open>u = w\<close>
    have "(last p) \<noteq> (w, v)"
    by (metis snd_conv)

  from \<open>(w, v) = hd p\<close> \<open>(last p) \<noteq> (w, v)\<close>
    have "\<exists>xs. p = [(w, v)] @ xs @ [last p]" 
    by (metis (no_types, opaque_lifting) \<open>(w, v) \<in> set p\<close> append.left_neutral append_Cons
    append_butlast_last_id last_snoc list.distinct(1) list.exhaust_sel split_list)
  then obtain xs where "p = [(w, v)] @ xs @ [(fst (last p), snd (last p))]" by auto
  with awalk_verts_cons \<open>awalk E u p u\<close>
    have awalk_verts_p: "awalk_verts u ([(w, v)] @ (xs @ [(fst (last p), snd (last p))])) =
      [w, v] @ tl (awalk_verts u (xs @ [(fst (last p), snd (last p))]))"
    by metis
  from awalk_verts_snoc
    obtain ys where "awalk_verts u (xs @ [(fst (last p), snd (last p))]) = ys @ [fst (last p), snd (last p)]" by metis
  with awalk_verts_p \<open>p = [(w, v)] @ xs @ [(fst (last p), snd (last p))]\<close>
    have "awalk_verts u p = [w, v] @ tl (ys @ [fst (last p), snd (last p)])" by argo
  moreover have "ys \<noteq> []"
    by (metis One_nat_def Suc_eq_plus1 cycle'_imp_length_greater_2[OF \<open>cycle' E p\<close>] awalk_verts_conv butlast_snoc
    \<open>awalk_verts u p = [w, v] @ tl (ys @ [fst (last p), snd (last p)])\<close>
    length_map linorder_neq_iff list.sel(3) list.size(3) list.size(4) nat_1_add_1 self_append_conv2)
  ultimately have "awalk_verts u p = [w, v] @ tl ys @ [fst (last p), snd (last p)]"
    by auto
  then have "tl (awalk_verts u p) = [v] @ tl ys @ [fst (last p), snd (last p)]" by simp 
  moreover have "distinct (tl (awalk_verts u p))"
    using \<open>cycle' E p\<close> cycle'_def cycle_def
    by (metis \<open>awalk E u p u\<close> awalk_ends)
  ultimately have "fst (last p) \<noteq> v" by auto

  from \<open>snd (last p) = u\<close> \<open>u = w\<close> \<open>fst (last p) \<noteq> v\<close>
    show ?thesis
    by (metis True \<open>last p \<noteq> (w, v)\<close> hd_Nil_eq_last last_in_set prod.collapse)
next
  case False
  assume "cycle' E p" "v \<noteq> w" "(w, v) \<in> set p"
  from cycle'_imp_awalk[OF `cycle' E p`]
    obtain u where "awalk E u p u" by blast
  then have "cas u p u" unfolding awalk_def by auto

  have "\<exists>xs ys. p = xs @ [(w, v)] @ ys"
    by (metis \<open>(w, v) \<in> set p\<close> append_Cons append_Nil in_set_conv_decomp_first)
  then obtain xs ys where "p = xs @ [(w, v)] @ ys" by blast
  from cycle'_imp_length_greater_2[OF \<open>cycle' E p\<close>] False this
    have "xs \<noteq> []" by auto
  with \<open>p = xs @ [(w, v)] @ ys\<close>
    obtain x y where "p = butlast xs @ [(x, y), (w, v)] @ ys"
    by (metis append_Cons append_butlast_last_cancel prod.exhaust_sel)
  with \<open>awalk E u p u\<close> awalk_def
    have "cas u (butlast xs @ [(x, y), (w, v)] @ ys) u" by blast
  then have "w = y" by simp

  have "distinct (butlast (awalk_verts u p))"
    using cycle'_imp_awalk_verts_distinct[OF \<open>cycle' E p\<close> \<open>awalk E u p u\<close>]
    by blast

  consider (Nil) "butlast xs = Nil" | (Snoc) "\<exists>zs l_bl_xs. butlast xs = zs @ [l_bl_xs]"
    by (metis append_butlast_last_id)
  then have "x \<noteq> v"
  proof (cases)
    case Nil
    with cycle'_imp_length_greater_2[OF \<open>cycle' E p\<close>] \<open>p = butlast xs @ [(x, y), (w, v)] @ ys\<close>
      have "ys \<noteq> []" by auto
    with \<open>p = butlast xs @ [(x, y), (w, v)] @ ys\<close> Nil
      have "p = [(x, y), (w, v), hd ys] @ tl ys"
      by auto
    with awalk_verts_conv'[of "u" "p", OF \<open>cas u p u\<close>] map_append
      have "awalk_verts u p = [x, y, v, snd (hd ys)] @ (map snd (tl ys))"
      by auto
    then have "\<exists>zs. butlast (awalk_verts u p) = [x, y, v] @ zs"
      by simp
    with \<open>distinct (butlast (awalk_verts u p))\<close>
      show ?thesis by auto
  next
    case Snoc
    then obtain zs l_bl_xs where Cons: "butlast xs = zs @ [l_bl_xs]" by blast
    with \<open>p = butlast xs @ [(x, y), (w, v)] @ ys\<close>
      have "p = zs @ [l_bl_xs, (x, y), (w, v)] @ ys" by simp
    with \<open>awalk E u p u\<close> awalk_def
      have "cas u (zs @ [l_bl_xs, (x, y), (w, v)] @ ys) u" by blast
    with \<open>p = zs @ [l_bl_xs, (x, y), (w, v)] @ ys\<close> append_assoc
      have "x = snd l_bl_xs" 
      by (smt (verit, best) cas.simps(2) cas_append_iff prod.collapse)
    with \<open>p = zs @ [l_bl_xs, (x, y), (w, v)] @ ys\<close>
      have "p = zs @ [(fst l_bl_xs, x), (x, y), (w, v)] @ ys" by simp
    
    show ?thesis
    proof (cases ys)
      case Nil
      with \<open>p = zs @ [(fst l_bl_xs, x), (x, y), (w, v)] @ ys\<close>
        have "v = awlast u p"
        by (simp add: awalk_verts_conv)
      with \<open>awalk E u p u\<close> have "fst (hd p) = v"
        by (metis Nil_is_append_conv \<open>cas u p u\<close> \<open>p = xs @ [(w, v)] @ ys\<close> \<open>xs \<noteq> []\<close> awlast_if_cas cas_simp)
      with \<open>p = zs @ [(fst l_bl_xs, x), (x, y), (w, v)] @ ys\<close> awalk_verts_conv'[OF \<open>cas u p u\<close>] Nil
        have "awalk_verts u p = [v] @ (map snd zs) @ [x, y, v]"
        by force
      then have "butlast (awalk_verts u p) = [v] @ (map snd zs) @ [x, y]"
        by (simp add: butlast_append)
      with \<open>distinct (butlast (awalk_verts u p))\<close>
        show ?thesis by auto
    next
      case (Cons hd_ys tl_ys)
      with \<open>p = zs @ [(fst l_bl_xs, x), (x, y), (w, v)] @ ys\<close>
        have "p = zs @ [(fst l_bl_xs, x), (x, y), (w, v), hd_ys] @ tl_ys"
        by auto
      with awalk_verts_conv'[of "u" "p", OF \<open>cas u p u\<close>] map_append
        have "awalk_verts u p = [(fst (hd p))] @ (map snd zs) @ [x, y, v, snd (hd_ys)] @ (map snd tl_ys)"
        by auto
      then have "\<exists>as. butlast (awalk_verts u p) = [(fst (hd p))] @ (map snd zs) @ [x, y, v] @ as"
        by (simp add: butlast_append)
      with \<open>distinct (butlast (awalk_verts u p))\<close>
        show ?thesis by auto
    qed
  qed

  from \<open>p = butlast xs @ [(x, y), (w, v)] @ ys\<close> \<open>w = y\<close> \<open>x \<noteq> v\<close> 
    show ?thesis by auto
qed

lemma distinct_tl_awalk_verts:
  "u \<noteq> v \<Longrightarrow> distinct (tl (awalk_verts u p)) \<Longrightarrow> distinct (tl (awalk_verts v p))"
  apply (induction p)
  apply simp
  by auto

lemma cycle'_not_subset:
  "cycle' E p \<Longrightarrow> \<not>cycle' E' p \<Longrightarrow> \<not>set p \<subseteq> E'"
proof (rule ccontr, goal_cases)
  case 1
  then have "set p \<subseteq> E'" by blast
  from \<open>cycle' E p\<close> cycle'_def cycle_def
    have "(\<exists>u. awalk E u p u \<and> distinct (tl (awalk_verts u p)) \<and> p \<noteq> []) \<and> length p > 2"
    by fastforce
  then obtain u where "awalk E u p u" "distinct (tl (awalk_verts u p))" "p \<noteq> []" "length p > 2"
    by blast
  with awalk_def 
    have "u \<in> dVs E" "set p \<subseteq> E" "cas u p u" by auto

  from \<open>cas u p u\<close> have "u \<in> dVs (set p)"
    by (metis \<open>p \<noteq> []\<close> cas_simp dVsI'(1) list.set_sel(1))
  with \<open>set p \<subseteq> E'\<close> have "u \<in> dVs E'" unfolding dVs_def by auto
  with \<open>set p \<subseteq> E'\<close> \<open>cas u p u\<close> awalk_def \<open>distinct (tl (awalk_verts u p))\<close> \<open>p \<noteq> []\<close>
    \<open>length p > 2\<close> cycle_def cycle'_def
    have "cycle' E' p" by metis
  with \<open>\<not>cycle' E' p\<close> show ?case by blast
qed







end