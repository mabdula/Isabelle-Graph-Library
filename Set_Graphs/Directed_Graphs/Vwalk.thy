theory Vwalk
  imports Pair_Graph
begin

context fixes G :: "'a dgraph" begin
inductive vwalk where
  vwalk0: "vwalk []" |
  vwalk1: "v \<in> dVs G \<Longrightarrow> vwalk [v]" |
  vwalk2: "(v,v') \<in> G \<Longrightarrow> vwalk (v'#vs) \<Longrightarrow> vwalk (v#v'#vs)"
end
declare vwalk0[simp]

inductive_simps vwalk_1[simp]: "vwalk E [v]"

inductive_simps vwalk_2[simp]: "vwalk E (v # v' # vs)"

definition "vwalk_bet G v p v' = ( vwalk G p \<and> p \<noteq> [] \<and> hd p = v \<and> last p = v')"

lemma vwalk_then_edge: "vwalk_bet dG v p v' \<Longrightarrow> v \<noteq> v' \<Longrightarrow> (\<exists>v''. (v, v'') \<in> dG)"
  by(cases p; auto split: if_splits simp: neq_Nil_conv vwalk_bet_def)

lemma vwalk_then_in_dVs: "vwalk dG p \<Longrightarrow> v \<in> set p \<Longrightarrow> v \<in> dVs dG"
  by(induction rule: vwalk.induct) (auto simp: dVs_def)

lemma vwalk_cons: "vwalk dG (v1#v2#p) \<Longrightarrow> (v1,v2) \<in> dG"
  by simp

lemma hd_of_vwalk_bet:
  "vwalk_bet dG v p v' \<Longrightarrow> \<exists>p'. p = v # p'"
  by(auto simp: neq_Nil_conv vwalk_bet_def)

lemma hd_of_vwalk_bet': 
  "vwalk_bet dG v p v' \<Longrightarrow> v = hd p"
  by(auto simp: neq_Nil_conv vwalk_bet_def)

\<comment> \<open>TODO: intro\<close>

lemma hd_of_vwalk_bet'': "vwalk_bet dG u p v \<Longrightarrow> u \<in> set p"
  using hd_of_vwalk_bet
  by force 

lemma last_of_vwalk_bet: 
  "vwalk_bet dG v p v' \<Longrightarrow> v' = last p"
  by(auto simp: neq_Nil_conv vwalk_bet_def)

lemma last_of_vwalk_bet': 
  "vwalk_bet dG v p v' \<Longrightarrow> \<exists>p'. p = p' @ [v']"
  by(auto simp: vwalk_bet_def dest: append_butlast_last_id[symmetric])

lemma append_vwalk_pref: "vwalk dG (p1 @ p2) \<Longrightarrow> vwalk dG p1"
  by (induction p1) (fastforce intro: vwalk.intros elim: vwalk.cases simp: dVsI)+

lemma append_vwalk_suff: "vwalk dG (p1 @ p2) \<Longrightarrow> vwalk dG p2"
  by (induction p1) (fastforce intro: vwalk.intros elim: vwalk.cases simp:)+

lemma append_vwalk: "vwalk dG p1 \<Longrightarrow> vwalk dG p2 \<Longrightarrow> (p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> (last p1, hd p2) \<in> dG) \<Longrightarrow> vwalk dG (p1 @ p2)"
  by (induction p1) (fastforce intro: vwalk.intros elim: vwalk.cases simp: dVsI)+

\<comment> \<open>TODO: dest\<close>
lemma split_vwalk:
  "vwalk_bet dG v1 (p1 @ v2 # p2) v3 \<Longrightarrow> vwalk_bet dG v2 (v2 # p2) v3"
  unfolding vwalk_bet_def
proof (induction p1)
  case (Cons v p1)
  then show ?case 
    by (auto intro: append_vwalk_suff[where ?p1.0 = "v1 # p1"] simp add: vwalk_then_in_dVs vwalk_bet_def)
qed auto

lemma vwalk_bet_cons:
  "vwalk_bet dG v (v # p) u \<Longrightarrow> p \<noteq> [] \<Longrightarrow> vwalk_bet dG (hd p) p u"
  by(auto simp: neq_Nil_conv vwalk_bet_def)

lemma vwalk_bet_cons_2: 
  "vwalk_bet dG v p v' \<Longrightarrow> p \<noteq> [] \<Longrightarrow> vwalk_bet dG v (v # tl p) v'"
  by(auto simp: neq_Nil_conv vwalk_bet_def)

lemma vwalk_bet_snoc: 
  "vwalk_bet dG v' (p @ [v]) v'' \<Longrightarrow> v = v''"
  by(auto simp: neq_Nil_conv vwalk_bet_def)

lemma vwalk_bet_vwalk:
  "p \<noteq> [] \<Longrightarrow> vwalk_bet dG (hd p) p (last p) \<longleftrightarrow> vwalk dG p"
  by(auto simp: neq_Nil_conv vwalk_bet_def)

lemma vwalk_snoc_edge': "vwalk dG (p @ [v]) \<Longrightarrow> (v, v') \<in> dG \<Longrightarrow> vwalk dG ((p @ [v]) @ [v'])"
  by (rule append_vwalk) (auto simp add: dVs_def)

lemma vwalk_snoc_edge: "vwalk dG (p @ [v]) \<Longrightarrow> (v, v') \<in> dG \<Longrightarrow> vwalk dG (p @ [v, v'])"
  using vwalk_snoc_edge'
  by simp

lemma vwalk_snoc_edge_2: "vwalk dG (p @ [v, v']) \<Longrightarrow> (v, v') \<in> dG"
  using append_vwalk_suff[where ?p2.0 = "[v, v']"]
  by auto

lemma vwalk_append_edge: "vwalk dG (p1 @ p2) \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> (last p1, hd p2) \<in> dG"
  by (induction p1) (auto simp: vwalk_then_in_dVs neq_Nil_conv)

lemma vwalk_transitive_rel:
  assumes "(\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z)" "(\<And>v1 v2. (v1, v2) \<in> dG \<Longrightarrow> R v1 v2)"
  shows "vwalk dG (v#vs) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> R v v'"
proof(induction vs arbitrary: v v')
  case (Cons v'' vs)
  hence "R v v''"
    using assms(2)
    by simp
  thus ?case
  proof(cases "v' = v''")
    case False
    thus ?thesis
      apply(intro assms(1)[OF \<open>R v v''\<close>] Cons)
      using Cons.prems
      by auto
  qed simp
qed auto

lemma vwalk_transitive_rel': 
  assumes "(\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z)" "(\<And>v1 v2. (v1, v2) \<in> dG \<Longrightarrow> R v1 v2)"
  shows "vwalk dG (vs @ [v]) \<Longrightarrow> v' \<in> set vs \<Longrightarrow> R v' v"
proof(induction vs arbitrary: v v' rule: rev_induct)
  case (snoc v'' vs)
  hence "R v'' v"
    by(auto intro: assms vwalk_snoc_edge_2)    
  thus ?case
  proof(cases "v' = v''")
    case True
    then show ?thesis 
      by (simp add: \<open>R v'' v\<close>)
  next
    case False
    thus ?thesis
      apply(intro assms(1)[OF _ \<open>R v'' v\<close>] snoc append_vwalk_pref[where ?p1.0 = "vs @ [v'']"])
      using snoc(2,3)
      by auto
  qed
qed auto

fun edges_of_vwalk where
  "edges_of_vwalk [] = []" |
  "edges_of_vwalk [v] = []" |
  "edges_of_vwalk (v#v'#l) = (v, v') # edges_of_vwalk (v'#l)"

lemma vwalk_ball_edges: "\<lbrakk>vwalk E p; b \<in> set (edges_of_vwalk p)\<rbrakk> \<Longrightarrow> b \<in> E"
  by (induction p rule: edges_of_vwalk.induct, auto)

lemma edges_of_vwalk_index:
  "Suc i < length p \<Longrightarrow> edges_of_vwalk p ! i = (p ! i, p ! Suc i)"
proof (induction i arbitrary: p)
  case (Suc i)
  then obtain u v ps where "p = u#v#ps" by (auto dest!: Suc_leI simp: Suc_le_length_iff)
  hence "edges_of_vwalk (v#ps) ! i = ((v#ps) ! i, (v#ps) ! Suc i)" using Suc.IH Suc.prems by simp
  then show ?case using \<open>p = u#v#ps\<close> by simp
qed (auto dest!: Suc_leI simp: Suc_le_length_iff)

lemma edges_of_vwalk_length: "length (edges_of_vwalk p) = length p - 1"
  by (induction p rule: edges_of_vwalk.induct, auto)

lemma edges_of_vwalk_length': "p \<noteq> [] \<Longrightarrow> length (edges_of_vwalk p) + 1 = length p"
  by (induction p rule: edges_of_vwalk.induct, auto)

text \<open>With the given assumptions we can only obtain an outgoing edge from \<^term>\<open>v\<close>.\<close>
lemma edges_of_vwalk_for_inner:
  assumes "p ! i = v" "Suc i < length p"
  obtains w where "edges_of_vwalk p ! i = (v, w)"
  by (simp add: assms edges_of_vwalk_index)

text \<open>For an incoming edge we need an additional assumption (\<^term>\<open>i > 0\<close>).\<close>
lemma edges_of_vwalk_for_inner':
  assumes "p ! (Suc i) = v" "Suc i < length p"
  obtains u where "(u, v) = edges_of_vwalk p ! i"
  using assms by (simp add: edges_of_vwalk_index)

lemma hd_edges_neq_last:  
  "\<lbrakk>(last p, hd p) \<notin> set (edges_of_vwalk p); hd p \<noteq> last p; p \<noteq> []\<rbrakk> \<Longrightarrow>
   hd (edges_of_vwalk (last p # p)) \<noteq> last (edges_of_vwalk (last p # p))"
  by (induction p) (auto elim: edges_of_vwalk.elims)

lemma v_in_edge_in_vwalk: 
  assumes "(u, v) \<in> set (edges_of_vwalk p)"
  shows "u \<in> set p" "v \<in> set p"
  using assms
  by (induction p rule: edges_of_vwalk.induct) auto

lemma unused_edge_vwalk: 
  "\<lbrakk>Vwalk.vwalk E p; e \<notin> set (edges_of_vwalk p); length p \<ge> 2\<rbrakk> \<Longrightarrow> Vwalk.vwalk(E-{e}) p" 
  apply(induction rule: Vwalk.vwalk.induct[of E p], simp, simp) 
  subgoal for v v' vs
    by(cases vs) auto
  done

lemma unused_edge_vwalk_bet:
  "\<lbrakk>Vwalk.vwalk_bet E u p v; e \<notin> set (edges_of_vwalk p); length p \<ge> 2\<rbrakk>
   \<Longrightarrow> Vwalk.vwalk_bet(E-{e}) u p v"
   by (metis unused_edge_vwalk vwalk_bet_def)

lemma distinct_edges_of_vwalk:
  "distinct p \<Longrightarrow> distinct (edges_of_vwalk p)"
  by (induction p rule: edges_of_vwalk.induct) (auto dest: v_in_edge_in_vwalk)

lemma distinct_no_self_loop_in_edges_of_vwalk:
"distinct p \<Longrightarrow> \<nexists> x. (x,x) \<in> set (edges_of_vwalk p)"
  by(induction p rule: edges_of_vwalk.induct) auto

lemma distinct_edges_of_vwalk_cons:
  "distinct (edges_of_vwalk (v # p)) \<Longrightarrow> distinct (edges_of_vwalk p)"
  by (cases p; simp)

lemma tl_vwalk_is_vwalk: "vwalk E p \<Longrightarrow> vwalk E (tl p)"
  by (induction p rule: vwalk.induct; simp)

lemma vwalk_concat:
  assumes "vwalk E p" "vwalk E q" "q \<noteq> []" "p \<noteq> [] \<Longrightarrow> last p = hd q"
  shows "vwalk E (p @ tl q)"
  using assms
  by (induction p) (simp_all add: tl_vwalk_is_vwalk)

lemma edges_of_vwalk_append_2:
  "p' \<noteq> [] \<Longrightarrow> edges_of_vwalk (p @ p') = edges_of_vwalk (p @ [hd p']) @ edges_of_vwalk p'"
  by (induction p rule: induct_list012) (auto intro: list.exhaust[of p'])

lemma edges_of_vwalk_append: "\<exists>ep. edges_of_vwalk (p @ p') = ep @ edges_of_vwalk p'"
  by (cases "p' = []") (auto dest: edges_of_vwalk_append_2)

lemma append_butlast_last_cancel: "p \<noteq> [] \<Longrightarrow> butlast p @ last p # p' = p @ p'"
  by simp

lemma edges_of_vwalk_append_3:
  assumes "p \<noteq> []"
  shows "edges_of_vwalk (p @ p') = edges_of_vwalk p @ edges_of_vwalk (last p # p')"
  using assms
  by (auto simp flip: append_butlast_last_cancel simp: edges_of_vwalk_append_2)

lemmas edges_of_vwalk_append_two_vertices = edges_of_vwalk_append_3[of "_ @[_]" "[_]", simplified]

lemma vwalk_vertex_has_edge:
  assumes "length p \<ge> 2" "v \<in> set p"
  obtains e u where "e \<in> set (edges_of_vwalk p)" "e = (u, v) \<or> e = (v, u)"
proof -
  obtain i where idef: "p ! i = v" "i < length p" 
    using assms(2) by (auto simp: in_set_conv_nth)
  have eodplength': "Suc (length (edges_of_vwalk p)) = length p"
    using assms(1) by (auto simp: edges_of_vwalk_length)
  hence eodplength: "length (edges_of_vwalk p) \<ge> 1" using assms(1) by simp

  from idef consider (nil) "i = 0" | (gt) "i > 0" "Suc i < length p" | (last) "Suc i = length p"
    by linarith
  thus ?thesis
  proof cases
    case nil
    hence "edges_of_vwalk p ! 0 = (p ! 0, p ! 1)" using edges_of_vwalk_index assms(1) by force
    then show ?thesis using that nil idef eodplength
      by (force simp: in_set_conv_nth)
  next
    case gt
    then obtain w where w: "(v, w) = edges_of_vwalk p ! i"
      by (auto elim: edges_of_vwalk_for_inner[OF idef(1)])
    have "i < length (edges_of_vwalk p)"
      using eodplength' gt(2) by auto
    then show ?thesis using that w[symmetric] nth_mem by blast
  next
    case last
    then obtain w where w: "(w, v) = edges_of_vwalk p ! (i - 1)"
      using edges_of_vwalk_for_inner'[of p "i - 1"] eodplength' eodplength
      by (auto simp: idef)
    have "i - 1 < length (edges_of_vwalk p)"
      using eodplength eodplength' last by linarith
    then show ?thesis using that w[symmetric] nth_mem by blast
  qed
qed

lemma v_in_edge_in_vwalk_inj:
  assumes "e \<in> set (edges_of_vwalk p)"
  obtains u v where "e = (u, v)"
  by fastforce

lemma v_in_edge_in_vwalk_gen:
  assumes "e \<in> set (edges_of_vwalk p)" "e = (u, v)"
  shows "u \<in> set p" "v \<in> set p"
  using assms v_in_edge_in_vwalk by simp_all

lemma edges_of_vwalk_dVs: "dVs (set (edges_of_vwalk p)) \<subseteq> set p"
  by (auto intro: v_in_edge_in_vwalk simp: dVs_def)

lemma last_v_snd_last_e:
  assumes "length p \<ge> 2"
  shows "last p = snd (last (edges_of_vwalk p))" \<comment> \<open>is this the best formulation for this?\<close>
  using assms
  by (induction p rule: induct_list012) 
     (auto split: if_splits elim: edges_of_vwalk.elims simp: Suc_leI)

lemma hd_v_fst_hd_e:
  assumes "length p \<ge> 2"
  shows "hd p = fst (hd (edges_of_vwalk p))"
  using assms
  by (auto dest: Suc_leI simp: Suc_le_length_iff numeral_2_eq_2)

lemma last_in_edge:
   "p \<noteq> [] \<Longrightarrow> \<exists>u. (u, last p) \<in> set (edges_of_vwalk (v # p)) \<and> u \<in> set (v # p)"
  by (induction p arbitrary: v) auto

lemma edges_of_vwalk_append_subset:
  shows "set (edges_of_vwalk p') \<subseteq> set (edges_of_vwalk (p @ p'))"
  by (fastforce intro: exE[OF edges_of_vwalk_append, of p p'])

lemma nonempty_vwalk_vwalk_bet[intro?]:
  assumes "vwalk E p" "p \<noteq> []" "hd p = u" "last p = v"
  shows "vwalk_bet E u p v"
  using assms
  unfolding vwalk_bet_def
  by blast

lemma vwalk_bet_nonempty:
  assumes "vwalk_bet E u p v"
  shows [simp]: "p \<noteq> []"
  using assms 
  unfolding vwalk_bet_def by blast

lemma vwalk_bet_nonempty_vwalk[elim]:
  assumes "vwalk_bet E u p v"
  shows "vwalk E p" "p \<noteq> []" "hd p = u" "last p = v"
  using assms 
  unfolding vwalk_bet_def by blast+

lemma vwalk_bet_reflexive[intro]:
  assumes "w \<in> dVs E"
  shows "vwalk_bet E w [w] w"
  using assms 
  unfolding vwalk_bet_def by simp

lemma vwalk_bet_reflexive_cong: 
"\<lbrakk>w \<in> dVs E;  a = w; b = w\<rbrakk> \<Longrightarrow> vwalk_bet E a [w] b" 
  by (meson vwalk_bet_reflexive)

lemma singleton_hd_last: "q \<noteq> [] \<Longrightarrow> tl q = [] \<Longrightarrow> hd q = last q"
  by (cases q) simp_all

lemma singleton_hd_last': "q \<noteq> [] \<Longrightarrow> butlast q = [] \<Longrightarrow> hd q = last q"
  by (cases q) auto

lemma vwalk_bet_transitive:
  assumes "vwalk_bet E u p v" "vwalk_bet E v q w"
  shows "vwalk_bet E u (p @ tl q) w"
  using assms
  unfolding vwalk_bet_def
  by (auto intro: vwalk_concat simp: last_append singleton_hd_last last_tl)

lemma vwalk_bet_in_dVs:
  assumes "vwalk_bet E a p b"
  shows "set p \<subseteq> dVs E"
  using assms vwalk_then_in_dVs
  unfolding vwalk_bet_def by fast

lemma vwalk_bet_endpoints:
  assumes "vwalk_bet E u p v"
  shows [simp]: "u \<in> dVs E"
  and   [simp]: "v \<in> dVs E"
  using assms vwalk_then_in_dVs
  unfolding vwalk_bet_def by fastforce+

lemma vwalk_bet_pref:
  assumes "vwalk_bet E u (pr @ [x] @ su) v"
  shows "vwalk_bet E u (pr @ [x]) x"
  using assms
  unfolding vwalk_bet_def
  by (auto simp: append_vwalk_pref) (simp add: hd_append)

lemma vwalk_bet_suff:
  assumes "vwalk_bet E u (pr @ [x] @ su) v"
  shows "vwalk_bet E x (x # su) v"
  using append_vwalk_suff assms 
  unfolding vwalk_bet_def by auto

lemma edges_are_vwalk_bet:
  assumes "(v, w) \<in> E"
  shows "vwalk_bet E v [v, w] w"
  unfolding vwalk_bet_def
  using assms
  by (simp add: dVsI)

lemma  edges_are_vwalk_bet_cong: 
 "\<lbrakk>(v,w)\<in> E; a = v;  b = w\<rbrakk> \<Longrightarrow> vwalk_bet E a [v, w] b" for v E w a b
  using edges_are_vwalk_bet by auto

lemma induct_vwalk_bet[case_names path1 path2, consumes 1, induct set: vwalk_bet]:
  assumes "vwalk_bet E a p b"
  assumes Path1: "\<And>v. v \<in> dVs E \<Longrightarrow> P E [v] v v"
  assumes Path2: "\<And>v v' vs b. (v, v') \<in> E \<Longrightarrow> vwalk_bet E v' (v' # vs) b \<Longrightarrow> P E (v' # vs) v' b \<Longrightarrow> P E (v # v' # vs) v b"
  shows "P E p a b"
proof -
  have "vwalk E p" "p \<noteq> []" "hd p = a" "last p = b" using assms(1) by auto
  thus ?thesis
  proof (induction p arbitrary: a b)
    case vwalk0
    then show ?case by simp
  next
    case vwalk1
    then show ?case using Path1 by fastforce
  next
    case (vwalk2 v v' vs a b)
    then have "vwalk_bet E  v' (v' # vs) b"
      by (simp add: vwalk2.hyps(1) vwalk_bet_def)
    then show ?case using vwalk2 Path2
      by auto
  qed
qed

lemma vwalk_append:
  assumes "vwalk E xs" "vwalk E ys" "last xs = hd ys"
  shows "vwalk E (xs @ tl ys)"
  using assms vwalk_concat by fastforce

lemma vwalk_append2:
  assumes "vwalk E (xs @ [x])" "vwalk E (x # ys)"
  shows "vwalk E (xs @ x # ys)"
  using assms by (auto dest: vwalk_append)

lemma vwalk_appendD_last:
  "vwalk E (xs @ [x, y]) \<Longrightarrow> vwalk E (xs @ [x])"
  by (simp add: append_vwalk_pref)

lemma vwalk_ConsD:
  "vwalk E (x # xs) \<Longrightarrow> vwalk E xs"
  by (auto dest: tl_vwalk_is_vwalk)

lemmas vwalkD = vwalk_ConsD append_vwalk_pref append_vwalk_suff

lemma vwalk_alt_induct[consumes 1, case_names Single Snoc]:
  assumes
    "vwalk E p"  "P []" "(\<And>x. P [x])"
    "\<And>y x xs. (y, x) \<in> E \<Longrightarrow> vwalk E (xs @ [y]) \<Longrightarrow> P (xs @ [y]) \<Longrightarrow> P (xs @ [y, x])"
  shows "P p"
  using assms(1)
proof (induction rule: rev_induct)
  case Nil
  then show ?case by (simp add: assms)
next
  case (snoc x xs)
  then show ?case
    by (cases xs rule: rev_cases) (auto intro!: assms simp add: vwalk_snoc_edge_2 append_vwalk_pref)
qed

lemma vwalk_append_single:
  assumes "vwalk E p" "(last p, x) \<in> E"
  shows "vwalk E (p @ [x])"
  using assms
  by (auto intro!: append_vwalk dest: dVsI)

lemmas vwalk_decomp = append_vwalk_pref append_vwalk_suff vwalk_append_edge

lemma vwalk_rotate:
  assumes "vwalk E (x # xs @ y # ys @ [x])"
  shows "vwalk E (y # ys @ x # xs @ [y])"
proof -
  from vwalk_decomp[of E "x # xs" "y # ys @ [x]"] assms have
    "vwalk E (x # xs)" "vwalk E (y # ys @ [x])" "(last (x # xs), y) \<in> E"
    by auto
  then have "vwalk E (x # xs @ [y])"
    by (auto dest: vwalk_append_single)
  from vwalk_append[OF \<open>vwalk E (y # ys @ [x])\<close> this] show ?thesis by auto
qed

lemma vwalk_bet_nonempty'[simp]: "\<not> vwalk_bet E u [] v" 
  unfolding vwalk_bet_def by simp

lemma vwalk_ConsE: 
  assumes "vwalk E (a # p)" "p \<noteq> []"
  obtains e where "e \<in> E" "e = (a, hd p)" "vwalk E p"
  using assms
  by (metis vwalk_2 hd_Cons_tl)

lemma vwalk_reachable:
  "p \<noteq> [] \<Longrightarrow> vwalk E p \<Longrightarrow> hd p \<rightarrow>\<^sup>*\<^bsub>E\<^esub> last p"
  by (induction p rule: list_nonempty_induct)
     (auto elim!: vwalk_ConsE simp: reachable_def converse_rtrancl_on_into_rtrancl_on dVsI)

lemma vwalk_reachable':
  "vwalk E p \<Longrightarrow> p \<noteq> [] \<Longrightarrow> hd p = u \<Longrightarrow> last p = v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  by (auto dest: vwalk_reachable)

lemma vwalkI: "(x, hd p) \<in> E \<Longrightarrow> vwalk E p \<Longrightarrow> vwalk E (x#p)" 
  by (induction p) (auto simp: dVsI)

lemma reachable_vwalk:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  shows "\<exists>p. hd p = u \<and> last p = v \<and> vwalk E p \<and> p \<noteq> []"
  using assms
  apply induction
   apply force
  apply clarsimp
  subgoal for x p
    by (auto intro!: exI[where x="x#p"] vwalkI)
  done

lemma reachable_vwalk_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. hd p = u \<and> last p = v \<and> vwalk E p \<and> p \<noteq> [])"
  by (auto simp: vwalk_reachable reachable_vwalk)

lemma reachable_vwalk_bet_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. vwalk_bet E u p v)"
  by (auto simp: reachable_vwalk_iff vwalk_bet_def)

lemma reachable_vwalk_betD:
  "vwalk_bet E u p v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  using iffD2[OF reachable_vwalk_bet_iff]
  by force

lemma vwalk_reachable1:
  "vwalk E (u # p @ [v]) \<Longrightarrow> u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  by (induction p arbitrary: u) (auto simp add: trancl_into_trancl2)

lemma reachable1_vwalk:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  shows "\<exists>p. vwalk E (u # p @ [v])"
proof -
  from assms obtain w where "(u,w) \<in> E" "w \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    by (meson converse_tranclE reachable1_in_dVs(2) reachable1_reachable reachable_refl)
  from reachable_vwalk[OF this(2)] obtain p where *: "hd p = w" "last p = v" "vwalk E p" "p \<noteq> []"
    by auto
  then obtain p' where [simp]: "p = p' @ [v]"
    by (auto intro!: append_butlast_last_id[symmetric])
  with \<open>(u,w) \<in> E\<close> * show ?thesis
    by (auto intro: vwalkI)
qed

lemma reachable1_vwalk_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v \<longleftrightarrow> (\<exists>p. vwalk E (u # p @ [v]))"
  by (auto simp: vwalk_reachable1 reachable1_vwalk)

lemma reachable_vwalk_iff2:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> (u = v \<and> u \<in> dVs E \<or> (\<exists>p. vwalk E (u # p @ [v])))"
  by (auto dest: reachable1_vwalk simp: reachable_in_dVs vwalk_reachable1 reachable1_reachable)

lemma vwalk_remove_cycleE:
  assumes "vwalk E (u # p @ [v])"
  obtains p' where "vwalk E (u # p' @ [v])" 
    "distinct p'" "u \<notin> set p'" "v \<notin> set p'" "set p' \<subseteq> set p"
  using assms
proof (induction "length p" arbitrary: p rule: less_induct)
  case less
  note prems = less.prems(2) and intro = less.prems(1) and IH = less.hyps
  consider
    "distinct p" "u \<notin> set p" "v \<notin> set p" | "u \<in> set p" | "v \<in> set  p" | "\<not> distinct p" by auto
  then consider (goal) ?case
    | (a) as bs where "p = as @ u # bs" | (b) as bs where "p = as @ v # bs"
    | (between) x as bs cs where "p = as @ x # bs @ x # cs"
    using prems
    by (cases, auto dest: not_distinct_decomp split_list intro: intro)
  then show ?case
  proof cases
    case a
    with prems show ?thesis
      by - (rule IH[where p = "bs"], auto 4 3 intro: intro dest: vwalkD)
  next
    case b
    with prems have "vwalk E (u # as @ v # [] @ (bs @ [v]))" by simp
    then have "vwalk E (u # as @ [v])" by (auto simp: append_vwalk_pref)
    with b show ?thesis
      by - (rule IH[where p = "as"], auto 4 3 intro: intro)
  next
    case between
    with prems have expanded: "vwalk E ((u # as @ x # bs) @ x # cs @ [v])" by simp
    then have xv: "vwalk E (x # cs @ [v])" by (rule append_vwalk_suff)
    have ux: "vwalk E ((u # as) @ [x])" using append_vwalk_pref expanded by force
    with xv have "vwalk E ((u # as) @ x # cs @ [v])"
      using vwalk_append2[OF ux xv] by auto
    with between show ?thesis
      by - (rule IH[where p = "as @ x # cs"], auto 4 3 intro: intro)
  qed
qed

abbreviation closed_vwalk_bet :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a  \<Rightarrow> bool" where
  "closed_vwalk_bet E c v \<equiv> vwalk_bet E v c v \<and> Suc 0 < length c"

lemma edge_iff_vwalk_bet: "(u, v) \<in> E = vwalk_bet E u [u, v] v"
  by (auto simp: edges_are_vwalk_bet vwalk_bet_def dVsI)

lemma vwalk_bet_in_vertices: "vwalk_bet E u p v \<Longrightarrow> w \<in> set p \<Longrightarrow> w \<in> dVs E"
  by (auto intro: vwalk_then_in_dVs)

lemma vwalk_bet_hd_neq_last_implies_edges_nonempty:
  assumes "vwalk_bet E u p v"
  assumes "u \<noteq> v"
  shows "E \<noteq> {}"
  using assms
  by (induction p) (auto dest: vwalk_then_edge)

lemma vwalk_bet_edges_in_edges: "vwalk_bet E u p v \<Longrightarrow> set (edges_of_vwalk p) \<subseteq> E"
  by (auto simp add: vwalk_bet_def intro: vwalk_ball_edges)

lemma vwalk_bet_prefix_is_vwalk_bet:
  assumes "p \<noteq> []"
  assumes "vwalk_bet E u (p @ q) v"
  shows "vwalk_bet E u p (last p)"
  using assms
  by (auto simp: vwalk_bet_def dest: append_vwalk_pref)

lemma vwalk_bet_suffix_is_vwalk_bet:
  assumes "q \<noteq> []"
  assumes "vwalk_bet E u (p @ q) v"
  shows "vwalk_bet E (hd q) q v"
  using assms
  by (auto simp: vwalk_bet_def dest: append_vwalk_suff)

lemma vwalk_bet_append_append_is_vwalk_bet:
  assumes "vwalk_bet E u p v"
  assumes "vwalk_bet E v q w"
  assumes "vwalk_bet E w r x"
  shows "vwalk_bet E u (p @ tl q @ tl r) x"
  using assms
  by (auto dest: vwalk_bet_transitive)

lemma 
  assumes "p \<noteq> []"
  shows "edges_of_vwalk (p @ q) = edges_of_vwalk p @ edges_of_vwalk ([last p] @ q)"
  using assms
  by (simp add: edges_of_vwalk_append_3)

fun is_vwalk_bet_vertex_decomp :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<times> 'a list \<Rightarrow> bool" where
  "is_vwalk_bet_vertex_decomp E p v (q, r) \<longleftrightarrow> p = q @ tl r \<and> (\<exists>u w. vwalk_bet E u q v \<and> vwalk_bet E v r w)"

definition vwalk_bet_vertex_decomp :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<times> 'a list" where
  "vwalk_bet_vertex_decomp E p v = ( SOME qr. is_vwalk_bet_vertex_decomp E p v qr)"


lemma vwalk_bet_vertex_decompE:
  assumes p_vwalk: "vwalk_bet E u p v"
  assumes p_decomp: "p = xs @ y # ys"
  obtains q r where
    "p = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "vwalk_bet E u q y"
    "vwalk_bet E y r v"
  using assms
  by (simp add: vwalk_bet_pref split_vwalk)

lemma vwalk_bet_vertex_decomp_is_vwalk_bet_vertex_decomp:
  assumes p_vwalk: "vwalk_bet E u p w"
  assumes v_in_p: "v \<in> set p"
  shows "is_vwalk_bet_vertex_decomp E p v (vwalk_bet_vertex_decomp E p v)"
proof -
  obtain xs ys where
    "p = xs @ v # ys"
    using v_in_p by (auto simp: in_set_conv_decomp)
  with p_vwalk
  obtain q r where
    "p = q @ tl r"
    "vwalk_bet E u q v"
    "vwalk_bet E v r w"
    by (blast elim: vwalk_bet_vertex_decompE)
  hence "is_vwalk_bet_vertex_decomp E p v (q, r)"
    by (simp add: vwalk_bet_def)
  hence "\<exists>qr. is_vwalk_bet_vertex_decomp E p v qr"
    by blast
  thus ?thesis
    unfolding vwalk_bet_vertex_decomp_def
    ..
qed

lemma vwalk_bet_vertex_decompE_2:
  assumes p_vwalk: "vwalk_bet E u p w"
  assumes v_in_p: "v \<in> set p"
  assumes qr_def: "vwalk_bet_vertex_decomp E p v = (q, r)"
  obtains
    "p = q @ tl r"
    "vwalk_bet E u q v"
    "vwalk_bet E v r w"
proof
  have *: "is_vwalk_bet_vertex_decomp E p v (q, r)"
    using assms by (auto dest: vwalk_bet_vertex_decomp_is_vwalk_bet_vertex_decomp)
  then obtain u' w' where
    p_decomp: "p = q @ tl r" and
    q_vwalk: "vwalk_bet E u' q v" and
    r_vwalk: "vwalk_bet E v r w'"
    by auto
  hence "vwalk_bet E u' p w'" by (simp add: vwalk_bet_transitive)
  hence "u' = u" "w' = w" using p_vwalk by (simp_all add: vwalk_bet_def)
  thus
    "p = q @ tl r"
    "vwalk_bet E u q v"
    "vwalk_bet E v r w"
    using p_decomp q_vwalk r_vwalk by simp_all
qed


definition vtrail :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "vtrail E u p v = ( vwalk_bet E u p v \<and> distinct (edges_of_vwalk p))"

abbreviation closed_vtrail :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "closed_vtrail E c v \<equiv> vtrail E v c v \<and> Suc 0 < length c"

lemma closed_vtrail_implies_Cons:
  assumes "closed_vtrail E c v"
  shows "c = v # tl c"
  using assms
  by (auto simp add: vtrail_def vwalk_bet_def)

lemma tl_non_empty_conv:
  shows "tl l \<noteq> [] \<longleftrightarrow> Suc 0 < length l"
proof -
  have "tl l \<noteq> [] \<longleftrightarrow> 0 < length (tl l)"
    by blast
  also have "... \<longleftrightarrow> Suc 0 < length l"
    by simp
  finally show ?thesis
    .
qed

lemma closed_vtrail_implies_tl_nonempty:
  assumes "closed_vtrail E c v"
  shows "tl c \<noteq> []"
  using assms
  by (simp add: tl_non_empty_conv)

lemma vtrail_in_vertices:
  "vtrail E u p v \<Longrightarrow> w \<in> set p \<Longrightarrow> w \<in> dVs E"
  by (auto simp add: vtrail_def intro: vwalk_bet_in_vertices)

lemma
  assumes "vtrail E u p v"
  shows vtrail_hd_in_vertices: "u \<in> dVs E"
  and vtrail_last_in_vertices: "v \<in> dVs E"
  using assms
  by (auto intro: vwalk_bet_endpoints simp: vtrail_def)

lemma list_set_tl: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
  by (cases xs) auto

lemma closed_vtrail_hd_tl_in_vertices:
  assumes "closed_vtrail E c v"
  shows "hd (tl c) \<in> dVs E"
  using assms
  by (auto intro!: vtrail_in_vertices simp flip: tl_non_empty_conv simp add: list_set_tl)

lemma vtrail_prefix_is_vtrail:
  notes vtrail_def [simp]
  assumes "p \<noteq> []"
  assumes "vtrail E u (p @ q) v"
  shows "vtrail E u p (last p)"
  using assms 
  by (auto simp: vwalk_bet_prefix_is_vwalk_bet edges_of_vwalk_append_3)

lemma vtrail_suffix_is_vtrail:
  notes vtrail_def [simp]
  assumes "q \<noteq> []"
  assumes "vtrail E u (p @ q) v"
  shows "vtrail E (hd q) q v"
  using assms
  by (auto simp: vwalk_bet_suffix_is_vwalk_bet edges_of_vwalk_append_2[OF \<open>q \<noteq> []\<close>])

definition distinct_vwalk_bet :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "distinct_vwalk_bet E u p v = (vwalk_bet E u p v \<and> distinct p)"

lemma distinct_vwalk_betE:
  "distinct_vwalk_bet E u p v \<Longrightarrow> 
  (\<lbrakk>vwalk_bet E u p v;  distinct p\<rbrakk> \<Longrightarrow> P)
  \<Longrightarrow> P"
and distinct_vwalk_betI:
  "(\<lbrakk>vwalk_bet E u p v;  distinct p\<rbrakk> \<Longrightarrow> distinct_vwalk_bet E u p v)"
and distinct_vwalk_betD:
  "distinct_vwalk_bet E u p v \<Longrightarrow> vwalk_bet E u p v"
  "distinct_vwalk_bet E u p v \<Longrightarrow> distinct p"
  by(auto simp add: distinct_vwalk_bet_def)

lemma distinct_vwalk_bet_length_le_card_vertices:
  assumes "distinct_vwalk_bet E u p v"
  assumes "finite E"
  shows "length p \<le> card (dVs E)"
  using assms
  unfolding distinct_vwalk_bet_def
  by (auto dest!: distinct_card[symmetric] intro!: card_mono simp: vwalk_bet_in_vertices finite_vertices_iff)

lemma distinct_vwalk_bet_triples_finite:
  assumes "finite E"
  shows "finite {(p, u, v). distinct_vwalk_bet E u p v}"
proof (rule finite_subset)
  have "\<And>p u v. vwalk_bet E u p v \<Longrightarrow> distinct p \<Longrightarrow> length p \<le> card (dVs E)"
    by (auto intro!: distinct_vwalk_bet_length_le_card_vertices simp: distinct_vwalk_bet_def assms)
  thus "{(p, u, v). distinct_vwalk_bet E u p v} \<subseteq>
    {p. set p \<subseteq> dVs E \<and> length p \<le> card (dVs E)} \<times> dVs E \<times> dVs E"
    by (auto simp: distinct_vwalk_bet_def vwalk_bet_in_vertices)
  show "finite \<dots>"
    by (auto intro!: finite_cartesian_product finite_lists_length_le 
             simp: assms finite_vertices_iff)
qed

lemma distinct_vwalk_bets_finite:
  "finite E \<Longrightarrow> finite {p. distinct_vwalk_bet E u p v}"
  by (rule finite_surj[OF  distinct_vwalk_bet_triples_finite]) auto

section\<open>Vwalks to paths (as opposed to arc walks (\<^term>\<open>awalk_to_apath\<close> before)\<close>
fun is_closed_decomp :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list \<Rightarrow> bool" where
  "is_closed_decomp E p (q, r, s) \<longleftrightarrow>
    p = q @ tl r @ tl s \<and>
    (\<exists>u v w. vwalk_bet E u q v \<and> closed_vwalk_bet E r v \<and> vwalk_bet E v s w) \<and>
    distinct q"

definition closed_vwalk_bet_decomp :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list" where
  "closed_vwalk_bet_decomp E p = ( SOME qrs. is_closed_decomp E p qrs)"

lemma closed_vwalk_bet_decompE:
  assumes p_vwalk: "vwalk_bet E u p v"
  assumes p_decomp: "p = xs @ y # ys @ y # zs"
  obtains q r s where
    "p = q @ tl r @ tl s"
    "q = xs @ [y]"
    "r = y # ys @ [y]"
    "s = y # zs"
    "vwalk_bet E u q y"
    "vwalk_bet E y r y"
    "vwalk_bet E y s v"
  using assms
  by auto (metis Cons_eq_appendI vwalk_bet_vertex_decompE)

lemma closed_vwalk_bet_decomp_is_closed_decomp:
  assumes p_vwalk: "vwalk_bet E u p v"
  assumes p_not_distinct: "\<not> distinct p"
  shows "is_closed_decomp E p (closed_vwalk_bet_decomp E p)"
proof -
  obtain xs y ys zs where
    "p = xs @ y # ys @ y # zs" and
    xs_distinct: "distinct xs" and
    y_not_in_xs: "y \<notin> set xs"
    using p_not_distinct not_distinct_decomp    
    by (smt append.assoc append.simps(2) in_set_conv_decomp_first not_distinct_conv_prefix)
  from p_vwalk this(1)
  obtain q r s where
    "p = q @ tl r @ tl s"
    "q = xs @ [y]"
    "r = y # ys @ [y]"
    "s = y # zs"
    "vwalk_bet E u q y"
    "vwalk_bet E y r y"
    "vwalk_bet E y s v"
    by (erule closed_vwalk_bet_decompE)
  moreover hence
    "distinct q"
    "Suc 0 < length r"
    using xs_distinct y_not_in_xs
    by simp+
  ultimately have
    "\<exists>q r s.
      p = q @ tl r @ tl s \<and>
      (\<exists>u v w. vwalk_bet E u q v \<and> closed_vwalk_bet E r v \<and> vwalk_bet E v s w) \<and>
      distinct q"
    by blast
  hence "\<exists>qrs. is_closed_decomp E p qrs" by simp
  thus ?thesis unfolding closed_vwalk_bet_decomp_def ..
qed

lemma closed_vwalk_bet_decompE_2:
  assumes p_vwalk: "vwalk_bet E u p v"
  assumes p_not_distinct: "\<not> distinct p"
  assumes qrs_def: "closed_vwalk_bet_decomp E p = (q, r, s)"
  obtains
    "p = q @ tl r @ tl s"
    "\<exists>w. vwalk_bet E u q w \<and> closed_vwalk_bet E r w \<and> vwalk_bet E w s v"
    "distinct q"
proof -
  have "is_closed_decomp E p (q, r, s)"
    unfolding qrs_def[symmetric]
    using p_vwalk p_not_distinct
    by (rule closed_vwalk_bet_decomp_is_closed_decomp)
  then obtain u' w' v' where
    p_decomp: "p = q @ tl r @ tl s" and
    q_distinct: "distinct q" and
    vwalks: "vwalk_bet E u' q w'"
    "closed_vwalk_bet E r w'"
    "vwalk_bet E w' s v'"
    by auto
  hence "vwalk_bet E u' p v'"
    by (auto intro: vwalk_bet_append_append_is_vwalk_bet)
  hence "u' = u" "v' = v"
    using p_vwalk
    by (simp_all add: vwalk_bet_def)
  hence "\<exists>w. vwalk_bet E u q w \<and> closed_vwalk_bet E r w \<and> vwalk_bet E w s v"
    using vwalks by blast
  with p_decomp q_distinct that
  show ?thesis by blast
qed

function vwalk_bet_to_distinct :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "vwalk_bet_to_distinct E p =
    (if (\<exists>u v. vwalk_bet E u p v) \<and> \<not> distinct p
     then let (q, r, s) = closed_vwalk_bet_decomp E p in vwalk_bet_to_distinct E (q @ tl s)
     else p)"
  by auto

termination vwalk_bet_to_distinct
proof (relation "measure (length \<circ> snd)")
  fix E p qrs rs q r s
  assume
    p_not_vwalk: "(\<exists>u v. vwalk_bet E u p v) \<and> \<not> distinct p" and
    assms: "qrs = closed_vwalk_bet_decomp E p"
    "(q, rs) = qrs"
    "(r, s) = rs"
  then obtain u v where
    p_vwalk: "vwalk_bet E u p v"
    by blast
  hence "(q, r, s) = closed_vwalk_bet_decomp E p"
    using assms
    by simp
  then obtain
    "p = q @ tl r @ tl s"
    "Suc 0 < length r"
    using p_vwalk p_not_vwalk
    by (elim closed_vwalk_bet_decompE_2) auto
  thus "((E, (q @ tl s)), E, p) \<in> measure (length \<circ> snd)"
    by auto
qed simp

lemma vwalk_bet_to_distinct_induct [consumes 1, case_names path decomp]:
  assumes "vwalk_bet E u p v"
  assumes distinct: "\<And>p. \<lbrakk> vwalk_bet E u p v; distinct p \<rbrakk> \<Longrightarrow> P p"
  assumes
    decomp: "\<And>p q r s. \<lbrakk> vwalk_bet E u p v; \<not> distinct p;
      closed_vwalk_bet_decomp E p = (q, r, s); P (q @ tl s) \<rbrakk> \<Longrightarrow> P p"
  shows "P p"
  using assms(1)
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  show ?case
  proof (cases "distinct p")
    case True
    with less.prems
    show ?thesis
      by (rule distinct)
  next
    case False
    obtain q r s where
      qrs_def: "closed_vwalk_bet_decomp E p = (q, r, s)"
      by (cases "closed_vwalk_bet_decomp E p")
    with less.prems False
    obtain
      "p = q @ tl r @ tl s"
      "\<exists>w. vwalk_bet E u q w \<and> closed_vwalk_bet E r w \<and> vwalk_bet E w s v"
      by (elim closed_vwalk_bet_decompE_2)
    hence
      "length (q @ tl s) < length p"
      "vwalk_bet E u (q @ tl s) v"
      by (auto simp: tl_non_empty_conv intro: vwalk_bet_transitive)
    hence "P (q @ tl s)"
      by (rule less.hyps)
    with less.prems False qrs_def
    show ?thesis
      by (rule decomp)
  qed
qed

lemma vwalk_bet_to_distinct_is_distinct_vwalk_bet:
  assumes "vwalk_bet E u p v"
  shows "distinct_vwalk_bet E u (vwalk_bet_to_distinct E p) v"
  using assms
  by (induction rule: vwalk_bet_to_distinct_induct) (auto simp: distinct_vwalk_bet_def)

lemma vwalk_betE[elim?]:
  assumes "vwalk_bet E u p v"
  assumes singleton: "\<lbrakk> v\<in> dVs E; u = v\<rbrakk> \<Longrightarrow> P"
  assumes
    step: "\<And>p' x. \<lbrakk> p = u#x#p'; (u,x)\<in>E; vwalk_bet E x (x#p') v\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms
  by (induction rule: induct_vwalk_bet) auto

lemma vwalk_subset:
  "\<lbrakk>vwalk G p; G \<subseteq> G'\<rbrakk> \<Longrightarrow> vwalk G' p"
  by (induction p rule: vwalk.induct) (auto simp: dVs_def)

lemma vwalk_bet_subset:
  "\<lbrakk>vwalk_bet G u p v; G \<subseteq> G'\<rbrakk> \<Longrightarrow> vwalk_bet G' u p v"
  using vwalk_subset
  by (auto simp: vwalk_bet_def)

lemma reachable_subset[intro]:
  "\<lbrakk>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v; G \<subseteq> G'\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G'\<^esub> v"
  by(auto simp add: reachable_vwalk_bet_iff dest: vwalk_bet_subset)

lemma reachable_Union_1[intro]:
  "\<lbrakk>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G \<union> G'\<^esub> v"
  "\<lbrakk>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v\<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G' \<union> G\<^esub> v"
  by auto

lemma reachableE[elim?]:
  assumes "reachable E u v"
  assumes singleton: "\<lbrakk> v\<in> dVs E; u = v\<rbrakk> \<Longrightarrow> P"
  assumes
    step: "\<And>x. \<lbrakk> (u,x)\<in>E; reachable E x v\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms
  by (metis converse_tranclE reachable1_reachable reachable_in_dVs(2) reachable_neq_reachable1 reachable_refl)


lemma vwalk_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>vwalk (insert e E) p; 
     (p = [] \<Longrightarrow> P);
     (\<And>u v. p = [v] \<Longrightarrow> e = (u,v) \<Longrightarrow> P);
     (\<And>u v. p = [v] \<Longrightarrow> e = (v,u) \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> dVs E \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>vwalk {e} [v1, v2]; vwalk (insert e E) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>vwalk E [v1,v2]; vwalk (insert e E) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P )\<rbrakk>
    \<Longrightarrow> P"
proof(induction rule: vwalk.induct)
  case vwalk0
  then show ?case 
    by auto
next
  case (vwalk1 v)
  then show ?case
    by (auto simp: dVs_def)
next
  case (vwalk2 v v' vs)
  then show ?case
    apply (auto simp: dVs_def)
    by (metis insertCI)
qed

text \<open>A lemma which allows for case splitting over paths when doing induction on graph edges.\<close>

lemma vwalk_bet_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>vwalk_bet (insert e E) v1 p v2; 
     (\<lbrakk>v1\<in>dVs (insert e E); v1 = v2; p = []\<rbrakk> \<Longrightarrow> P);
     (\<And>u v. p = [u] \<Longrightarrow> e = (u,v) \<Longrightarrow> P);
     (\<And>u v. p = [v] \<Longrightarrow> e = (u,v) \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> dVs E \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>vwalk_bet {e} v1 [v1,v3] v3; vwalk_bet (insert e E) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>vwalk_bet E v1 [v1,v3] v3; vwalk_bet (insert e E) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding vwalk_bet_def
  apply safe
  apply(erule vwalk_insertE)
  by (simp | force)+

lemma vwalk_bet2[simp]:
  "vwalk_bet G u (u # v # vs) b \<longleftrightarrow> ((u,v) \<in> G \<and> vwalk_bet G v (v # vs) b)"
  by(auto simp: vwalk_bet_def)

(*lemma assumes "vwalk_bet G' u p v""G \<subseteq> G'""u \<in> dVs G"
  shows "vwalk_bet G u p v \<or> 
       (\<exists>p1 w p2. vwalk_bet G' u p1 w \<and> w \<in> dVs G \<and> hd p2 \<notin> dVs G \<and> vwalk_bet G' w (w#p2) v)"
  using assms                              
proof(induction rule: induct_vwalk_bet)
  case (path1 v)
  then show ?case 
   by auto
next
  case (path2 u v vs b)
  then show ?case
  proof(cases "(u,v) \<notin> G")
    case T1: True
    then show ?thesis
    proof(cases "v \<notin> dVs G")
      case T2: True
      hence "vwalk_bet G u [u] u \<and> hd (v # vs) \<notin> dVs G \<and> vwalk_bet G' u (u # v # vs) b"
        using path2
        by auto
      then show ?thesis
        by metis
    next
      case F2: False
      hence "v \<in> dVs G"
        by auto
      hence "vwalk_bet G v (v # vs) b \<or> (\<exists>p1 w p2. vwalk_bet G v p1 w \<and> hd p2 \<notin> dVs G \<and> vwalk_bet G' w (w # p2) b)"
        using path2
        by auto
      with path2 show ?thesis
      proof(elim disjE, goal_cases)
        case 1
        then show ?case
          by auto
      next
        case 2
        then show ?case sorry
      qed

    qed
    
  next
    case False
    then show ?thesis sorry
  qed
qed

*)

lemma butlast_vwalk_is_vwalk: "vwalk E p \<Longrightarrow> vwalk E (butlast p)"
  by (induction p rule: vwalk.induct, auto)


lemma vwalk_concat_2:
  assumes "vwalk E p" "vwalk E q" "q \<noteq> []" "p \<noteq> [] \<Longrightarrow> last p = hd q"
  shows "vwalk E (butlast p @ q)"
  using assms
  by (induction rule: vwalk.induct) (auto simp add: butlast_vwalk_is_vwalk neq_Nil_conv)

lemma vwalk_bet_transitive_2:
  assumes "vwalk_bet E u p v" "vwalk_bet E v q w"
  shows "vwalk_bet E u (butlast p @ q) w"
  using assms
  unfolding vwalk_bet_def
  by (auto intro!: vwalk_concat_2 simp: last_append singleton_hd_last' neq_Nil_conv)

 lemma vwalk_not_vwalk: 
   "\<lbrakk>vwalk G p; \<not>vwalk G' p\<rbrakk> \<Longrightarrow> 
          (\<exists>(u,v) \<in> set (edges_of_vwalk p). (u,v) \<in> (G - G')) \<or> 
          (\<exists>v\<in>set p. v \<in> (dVs G - dVs G'))"
  by(induction rule: vwalk.induct) (auto simp: dVs_def)


 lemma vwalk_not_vwalk_2: 
   "\<lbrakk>vwalk G p; \<not>vwalk G' p; length p \<ge> 2\<rbrakk> \<Longrightarrow> 
          (\<exists>(u,v) \<in> set (edges_of_vwalk p). (u,v) \<in> (G - G'))"
   apply (induction rule: vwalk.induct) 
   apply (auto simp: dVs_def)
   by (metis Suc_leI dVsI(2) length_greater_0_conv vwalk_1)

 lemma vwalk_not_vwalk_elim: 
   "\<lbrakk>vwalk G p; \<not>vwalk G' p\<rbrakk> \<Longrightarrow> 
          \<lbrakk>\<And>u v. \<lbrakk>(u,v) \<in> set (edges_of_vwalk p); (u,v) \<in> (G - G')\<rbrakk> \<Longrightarrow> P; 
          \<And>v. \<lbrakk>v\<in>set p; v \<in> (dVs G - dVs G')\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
   using vwalk_not_vwalk
   by blast

 lemma vwalk_not_vwalk_elim_2: 
   "\<lbrakk>vwalk G p; \<not>vwalk G' p; length p \<ge> 2\<rbrakk> \<Longrightarrow> 
          \<lbrakk>\<And>u v. \<lbrakk>(u,v) \<in> set (edges_of_vwalk p); (u,v) \<in> (G - G')\<rbrakk> \<Longrightarrow> P 
          \<rbrakk> \<Longrightarrow> P"
   using vwalk_not_vwalk_2
   by blast


 lemma vwalk_bet_not_vwalk_bet: 
   "\<lbrakk>vwalk_bet G u p v; \<not>vwalk_bet G' u p v\<rbrakk> \<Longrightarrow> 
          (\<exists>(u,v) \<in> set (edges_of_vwalk p). (u,v) \<in> (G - G')) \<or> 
          (\<exists>v\<in>set p. v \<in> (dVs G - dVs G'))"
   using vwalk_not_vwalk
   by (auto simp: vwalk_bet_def)

 lemma vwalk_bet_not_vwalk_bet_elim: 
   "\<lbrakk>vwalk_bet G u p v; \<not>vwalk_bet G' u p v\<rbrakk> \<Longrightarrow> 
          \<lbrakk>\<And>u v. \<lbrakk>(u,v) \<in> set (edges_of_vwalk p); (u,v) \<in> (G - G')\<rbrakk> \<Longrightarrow> P; 
          \<And>v. \<lbrakk>v\<in>set p; v \<in> (dVs G - dVs G')\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
   using vwalk_not_vwalk_elim
   apply (auto simp: vwalk_bet_def)
   by blast

 lemma vwalk_bet_not_vwalk_bet_elim_2: 
   "\<lbrakk>vwalk_bet G u p v; \<not>vwalk_bet G' u p v; length p \<ge> 2\<rbrakk> \<Longrightarrow> 
          \<lbrakk>\<And>u v. \<lbrakk>(u,v) \<in> set (edges_of_vwalk p); (u,v) \<in> (G - G')\<rbrakk> \<Longrightarrow> P 
          \<rbrakk> \<Longrightarrow> P"
   using vwalk_not_vwalk_elim_2
   apply (auto simp: vwalk_bet_def)
   by blast

lemma vwalk_bet_props:
  "vwalk_bet G u p v \<Longrightarrow> (\<lbrakk>vwalk G p; p\<noteq>[]; hd p = u; last p = v\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: vwalk_bet_def)

lemma no_outgoing_last:
  "\<lbrakk>vwalk G p; \<And>v. (u,v) \<notin> G; u \<in> set p\<rbrakk> \<Longrightarrow> last p = u"
  by(induction rule: vwalk.induct) (auto simp: dVs_def)

lemma not_vwalk_bet_empty: "\<not> Vwalk.vwalk_bet {} u p v"
  by (auto simp: vwalk_bet_def neq_Nil_conv split: if_splits)

lemma edges_in_vwalk_split:
     "(u, v) \<in> set (edges_of_vwalk p) \<Longrightarrow> \<exists> p1 p2. p = p1 @[u,v]@p2" 
proof(induction p rule: edges_of_vwalk.induct)
  case (3 a b p)
  show ?case 
  proof(cases "(a, b) = (u, v)")
    case True
    hence "a # b # p = [u, v] @ p" by auto
    then show ?thesis by auto
  next
    case False
    hence "(u, v) \<in> set (edges_of_vwalk (b # p))"
      using 3(2) by auto
    then obtain p1 p2 where "b # p = p1 @ [u, v] @ p2"
      using 3(1) by auto
    hence "a#b # p = (a#p1) @ [u, v] @ p2" by auto
    then show ?thesis by fast
  qed
qed simp+

lemma vwalk_in_its_own_edges: "Vwalk.vwalk E  p 
  \<Longrightarrow> length p \<ge> 2 \<Longrightarrow> Vwalk.vwalk (set (edges_of_vwalk p)) p "
  using vwalk_not_vwalk_elim_2 by fastforce

lemma vwalk_bet_in_its_own_edges: "Vwalk.vwalk_bet E u p  v
  \<Longrightarrow> length p \<ge> 2 \<Longrightarrow> Vwalk.vwalk_bet (set (edges_of_vwalk p)) u p v" 
  using  vwalk_in_its_own_edges by(auto simp add: vwalk_bet_def)

lemma vwalk_bet_cycle_delete: "vwalk_bet Y x ( xs@[a]@ys@[a]@zs) y \<Longrightarrow> vwalk_bet Y x ( xs@[a]@zs) y"
  by(auto intro!: vwalk_bet_transitive[of Y x "xs@[a]" a "[a]@zs" y, simplified]
           intro: vwalk_bet_pref vwalk_bet_suff[of Y x "xs@a#ys" a zs y])

lemma edges_of_vwalk_rev: "edges_of_vwalk (rev xs) = map prod.swap (rev (edges_of_vwalk  xs))"
  by(induction xs rule: edges_of_vwalk.induct)
    (simp | subst edges_of_vwalk_append_2)+

lemma shortest_vwalk_bet_distinct: 
  assumes "vwalk_bet Y x p y"  "\<nexists> q. vwalk_bet Y x q y \<and> length q < length p"
  shows "distinct p"
proof(rule ccontr, goal_cases)
  case 1
  then obtain xs a ys zs where p_is:"p = xs@[a]@ys@[a]@zs" 
    using not_distinct_decomp by blast
  hence "vwalk_bet Y x (xs@[a]@zs) y" 
    using  vwalk_bet_cycle_delete[OF assms(1)[simplified p_is]] by simp
  moreover have "length (xs@[a]@zs) < length p" 
    using p_is by simp
  ultimately show ?case 
    using assms(2) by auto
qed

lemma vwalk_append_intermediate_edge:"vwalk_bet A x p y \<Longrightarrow> (y, x') \<in> A \<Longrightarrow> vwalk_bet A x' p' y' \<Longrightarrow> vwalk_bet A x (p@p') y'"
  by (simp add: append_vwalk vwalk_bet_def)

lemma vwalk_bet_diff_verts_length_geq_2:"vwalk_bet E s  p t\<Longrightarrow> s \<noteq> t \<Longrightarrow> length p \<ge> 2"
  by(cases p rule: edges_of_vwalk.cases) (auto simp add: vwalk_bet_def)

definition "dir_acyc G = (\<nexists> p u. vwalk_bet G u p u \<and> length p \<ge> 2)"

lemma dir_acycI: "(\<And> u p. vwalk_bet G u p u \<Longrightarrow> length p \<ge> 2 \<Longrightarrow> False) \<Longrightarrow> dir_acyc G"
  by(auto simp add: dir_acyc_def)

lemma dir_acycE: "dir_acyc G \<Longrightarrow>
((\<And> u p. vwalk_bet G u p u \<Longrightarrow> length p \<ge> 2 \<Longrightarrow> False) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: dir_acyc_def)
end
