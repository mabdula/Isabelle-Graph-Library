(*Authors: Mohammad Abdulaziz, Thomas Ammer, Christoph Madlener, Adem Rimpapa,*)
theory Paths
  imports Undirected_Set_Graphs
begin

section\<open>Paths\<close>

subsection \<open>Paths over Vertices\<close>

context fixes X :: "'a set set" begin
inductive path where
  path0: "path []" |
  path1: "v \<in> Vs X \<Longrightarrow> path [v]" |
  path2: "{v,v'} \<in> X \<Longrightarrow> path (v'#vs) \<Longrightarrow> path (v#v'#vs)"
end

declare path0

inductive_simps path_1: "path X [v]"

inductive_simps path_2: "path X (v # v' # vs)"

lemmas path_simps[simp] = path0 path_1 path_2

lemma tl_path_is_path: "path G p \<Longrightarrow> path G (tl p)"
  by (induction p rule: path.induct) (simp_all)

lemma path_concat:
  "\<lbrakk>path G p; path G q; q \<noteq> []; p \<noteq> [] \<Longrightarrow> last p = hd q\<rbrakk> \<Longrightarrow> path G (p @ tl q)"
  by (induction rule: path.induct) (simp_all add: tl_path_is_path)

lemma path_concat_2:
  assumes "path G p" "path G q" "p \<noteq> []" "q \<noteq> []" "last p = hd q"
  shows "path G (butlast p @ q)" 
  apply(rule forw_subst[of "butlast p @ q" "p @ tl q"])
  apply(cases p, all \<open> cases q\<close>)
  using assms path_concat 
  by force+

lemma path_append:
  "\<lbrakk>path G p1; path G p2; \<lbrakk>p1 \<noteq> []; p2 \<noteq> []\<rbrakk> \<Longrightarrow> {last p1, hd p2} \<in> G\<rbrakk> \<Longrightarrow> path G (p1 @ p2)"
  by (induction rule: path.induct) (auto simp add: neq_Nil_conv elim: path.cases)

lemma mem_path_Vs: 
  "\<lbrakk>path G p; a\<in>set p\<rbrakk> \<Longrightarrow> a \<in> Vs G"
  by (induction rule: path.induct) (simp; blast)+

lemma subset_path_Vs: 
  "\<lbrakk>path G p\<rbrakk> \<Longrightarrow> set p \<subseteq> Vs G"
  by (induction rule: path.induct) (simp; blast)+

lemma path_suff:
  assumes "path G (p1 @ p2)"
  shows "path G p2"
  using assms
proof(induction p1)
  case (Cons a p1)
  then show ?case using Cons tl_path_is_path by force
qed simp

lemma path_pref:
  assumes "path G (p1 @ p2)"
  shows "path G p1"
  using assms
proof(induction p1)
  case (Cons a p1)
  then show ?case using Cons by (cases p1; auto simp add: mem_path_Vs)
qed simp

lemma rev_path_is_path:
  assumes "path G p"
  shows "path G (rev p)"
  using assms
proof(induction)
  case (path2 v v' vs)
  moreover hence "{last (rev vs @ [v']), hd [v]} \<in> G"
    by (simp add: insert_commute)
  ultimately show ?case 
    using path_append edges_are_Vs
    by force
qed simp_all

lemma rev_path_is_path_iff:
  "path G (rev p) \<longleftrightarrow> path G p"
  using rev_path_is_path
  by force

lemma path_subset:
  assumes "path G p" "G \<subseteq> G'"
  shows "path G' p"
  using assms Vs_subset
  by (induction, auto)

lemma path_Cons_hd:
  "\<lbrakk>path G vs; hd vs = v; {u,v} \<in> G\<rbrakk> \<Longrightarrow> path G (u#vs)"
  by (cases vs) auto

definition "walk_betw G u p v = (p \<noteq> [] \<and> path G p \<and> hd p = u \<and> last p = v)"

lemma nonempty_path_walk_between:
  "\<lbrakk>path G p; p \<noteq> []; hd p = u; last p = v\<rbrakk> \<Longrightarrow> walk_betw G u p v"
  by (simp add: walk_betw_def)

lemma nonempty_path_walk_betweenE:
  assumes "path G p" "p \<noteq> []" "hd p = u" "last p = v"
  obtains p where "walk_betw G u p v"
  using assms
  by (simp add: walk_betw_def)

lemma walk_nonempty:
  assumes "walk_betw G u p v"
  shows [simp]: "p \<noteq> []"
  using assms walk_betw_def by fastforce

lemma walk_between_nonempty_pathD:
  assumes "walk_betw G u p v"
  shows "path G p" "p \<noteq> []" "hd p = u" "last p = v"
  using assms unfolding walk_betw_def by simp_all

lemma walk_reflexive:
  "w \<in> Vs G \<Longrightarrow> walk_betw G w [w] w"
  by (simp add: nonempty_path_walk_between)

lemma walk_reflexive_cong: 
  "\<lbrakk>w \<in> Vs E;  a = w;  b = w\<rbrakk> \<Longrightarrow>  walk_betw E a [w] b"
  using walk_reflexive by simp

lemma walk_reflexive_cong2: "\<lbrakk>u \<in> Vs G; u = u'; u' = u''\<rbrakk> \<Longrightarrow> walk_betw G u [u'] u''"
  using walk_reflexive by simp

lemma walk_symmetric:
  "walk_betw G u p v \<Longrightarrow> walk_betw G v (rev p) u"
  by (auto simp add: hd_rev last_rev walk_betw_def intro: rev_path_is_path)

lemma walk_transitive:
   "\<lbrakk>walk_betw G u p v; walk_betw G v q w\<rbrakk> \<Longrightarrow> walk_betw G u (p @ tl q) w"
  by (auto simp add: walk_betw_def intro: path_concat elim: path.cases)

lemma walk_transitive_2:
  "\<lbrakk>walk_betw G v q w; walk_betw G u p v\<rbrakk> \<Longrightarrow> walk_betw G u (p @ tl q) w"
  by (auto simp add: walk_betw_def intro: path_concat elim: path.cases)

lemma walk_transitive_3:
  "\<lbrakk>walk_betw G v q w; walk_betw G u p v\<rbrakk> \<Longrightarrow> walk_betw G u (butlast p @ q) w"
  by(auto simp add: walk_betw_def intro!: path_concat_2[of G p q], (cases p)?)+

lemma walk_in_Vs:
  "walk_betw G a p b \<Longrightarrow> set p \<subseteq> Vs G"
  by (simp add: subset_path_Vs walk_betw_def)

lemma walk_endpoints:
  assumes "walk_betw G u p v"
  shows [simp]: "u \<in> Vs G"
  and   [simp]: "v \<in> Vs G"
  using assms mem_path_Vs walk_betw_def
  by fastforce+

lemma walk_pref:
  "walk_betw G u (pr @ [x] @ su) v \<Longrightarrow> walk_betw G u (pr @ [x]) x"
proof(rule nonempty_path_walk_between, goal_cases)
  case 1
  hence "walk_betw G u ((pr @ [x]) @ su) v"
    by auto
  thus ?case
    by (fastforce dest!: walk_between_nonempty_pathD(1) path_pref)
next
  case 3
  then show ?case
    by(cases pr) (auto simp: walk_betw_def)
qed auto

lemma walk_suff:
   "walk_betw G u (pr @ [x] @ su) v \<Longrightarrow> walk_betw G x (x # su) v"
  by (fastforce simp: path_suff walk_betw_def)

lemma edges_are_walks:
  "{v, w} \<in> G \<Longrightarrow> walk_betw G v [v, w] w"
  using edges_are_Vs insert_commute
  by (auto 4 3 intro!: nonempty_path_walk_between)

lemma edges_are_walks_cong:
  "\<lbrakk>{v, w} \<in> E;  a = v; w = b\<rbrakk> \<Longrightarrow> walk_betw E a [v, w] b"
  using edges_are_walks by fast

lemma walk_subset:
  "\<lbrakk>walk_betw G u p v; G \<subseteq> G'\<rbrakk> \<Longrightarrow> walk_betw G' u p v"
  using path_subset
  by (auto simp: walk_betw_def)

lemma induct_walk_betw[case_names path1 path2, consumes 1, induct set: walk_betw]:
  assumes "walk_betw G a p b"
  assumes Path1: "\<And>v. v \<in> Vs G \<Longrightarrow> P v [v] v"
  assumes Path2: "\<And>v v' vs b. {v, v'} \<in> G \<Longrightarrow> walk_betw G v' (v' # vs) b \<Longrightarrow> P v' (v' # vs) b \<Longrightarrow> P v (v # v' # vs) b"
  shows "P a p b"
proof-
  have "path G p" "p \<noteq> []" "hd p = a" "last p = b"
    using assms(1)
    by (auto dest: walk_between_nonempty_pathD)
  thus ?thesis
    by (induction arbitrary: a b rule: path.induct) (auto simp: nonempty_path_walk_between assms(2,3))
qed

lemma walk_betw_length:"\<lbrakk>a \<noteq> b; walk_betw E a p b\<rbrakk> \<Longrightarrow> length p \<ge> 2"
  by(cases p rule: list_cases3)(auto simp add: walk_betw_def)

lemma walk_betw_different_verts_to_ditinct: 
  assumes "walk_betw G u p v" "u \<noteq> v" "length p = l"
  shows " \<exists> q. walk_betw G u q v \<and> distinct q \<and> set q \<subseteq> set p"
  using assms
proof(induction l arbitrary: u p v rule: less_induct)
  case (less l)
  show ?case
  proof(cases "distinct p")
    case True
    then show ?thesis 
      using less(2) by auto
  next
    case False
    then obtain x p1 p2 p3 where p_split:"p = p1@[x]@p2@[x]@p3"
      using not_distinct_decomp by blast
    have new_walk:"walk_betw G u (p1@[x]@p3) v" 
    proof(cases p1)
      case Nil
      hence "u =x"
        using less.prems(1) p_split walk_between_nonempty_pathD(3) by fastforce
      then show ?thesis 
        using less.prems(1) local.Nil p_split path_suff walk_betw_def by fastforce
    next
      case (Cons a list)
      then show ?thesis 
        using  append.assoc less.prems(1) list.sel(3) walk_pref walk_suff[of G u "p1@[x]@p2" x p3 v]
          walk_transitive[of G u "p1@[x]" x]
        by(unfold p_split) fastforce
    qed
    have "length (p1 @ [x] @ p3) < l"
      using p_split less(4) by simp
    then obtain q where q_prop: " walk_betw G u q v" "distinct q" "set q \<subseteq> set (p1 @ [x] @ p3)"
      using less(1)[OF _ new_walk less(3) refl] by auto
    show ?thesis
      using q_prop by(auto intro!: exI[of _ q] simp add: p_split)
  qed
qed

lemma walk_betw_Cons_first:
  "\<lbrakk>walk_betw G v p w; {u, v} \<in> G\<rbrakk> \<Longrightarrow> walk_betw G u (u#p) w"
  by (metis last_ConsR list.collapse list.distinct(1) list.sel(1) path_2 walk_betw_def)

lemma walk_betw_length_2_is: 
  "\<lbrakk>walk_betw G v p u; length p = 2\<rbrakk> \<Longrightarrow> p = [v, u]"
proof(cases p, goal_cases)
  case (2 a p)
  thus ?thesis
    by(cases p)(simp add: walk_betw_def)+
qed simp

lemma walk_betw_split_off_first:
  "walk_betw G u p v \<Longrightarrow> \<exists> pp. p = u # pp"
  by(cases p)(auto simp add: walk_betw_def)

lemma walk_betw_split_off_last:
  "walk_betw G u p v \<Longrightarrow> \<exists> pp. p = pp @[v]"
  by(cases p rule: rev_cases)(auto simp add: walk_betw_def)

lemma path_singletonD: 
  "\<lbrakk>path {{v1::'a,v2}} p; p \<noteq> []\<rbrakk>
   \<Longrightarrow> (hd p = v1 \<or> hd p = v2) \<and> (last p = v1 \<or> last p = v2)"
  by (induction rule: path.induct) (auto simp: Vs_def)

lemma walk_betw_singletonD:
  "\<lbrakk>walk_betw {{v1::'a,v2}} u p v; p \<noteq> []\<rbrakk>
   \<Longrightarrow> (hd p = v1 \<or> hd p = v2) \<and> (last p = v1 \<or> last p = v2) \<and> hd p = u \<and> last p = v"
  by (fastforce simp: walk_betw_def dest: path_singletonD)

lemma path_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>path (insert e G) p; 
     (p = [] \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> e \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs G \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path {e} [v1, v2]; path (insert e G) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path G [v1,v2]; path (insert e G) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P )\<rbrakk>
    \<Longrightarrow> P"
proof(induction rule: path.induct)
  case path0
  then show ?case 
    by auto
next
  case (path1 v)
  then show ?case
    by (auto elim!: in_Vs_insertE)
next
  case (path2 v v' vs)
  then show ?case
    apply (auto simp: vs_member)
    by blast
qed

lemma walk_betw_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>walk_betw (insert e G) v1 p v2; 
     (\<lbrakk>v1\<in>Vs (insert e G); v1 = v2; p = []\<rbrakk> \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> e \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs G \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw {e} v1 [v1,v3] v3; walk_betw (insert e G) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw G v1 [v1,v3] v3; walk_betw (insert e G) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding walk_betw_def
  apply safe
  apply(erule path_insertE)
  by (simp | force)+
  
lemma vwalk_betw_can_be_split_2:
  assumes "walk_betw (insert {w, x} G) u p v" "w \<in> Vs G" "x \<notin> Vs G"
  shows "(\<exists>p'. walk_betw G u p' v) \<or>
         (\<exists>p'. walk_betw G u p' w \<and> v = x) \<or>
         (\<exists>p'. walk_betw G w p' v \<and> u = x) \<or>
         (u = x \<and> v = x)"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule walk_betw_insertE, goal_cases)
    case (4 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (auto dest: walk_endpoints(1) walk_reflexive)
  next
    case (5 p' v3)
    then show ?case
     (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw G u [u, v3] v3\<close>] walk_endpoints(2)
      by (metis list.sel(3))
  qed (auto dest: walk_reflexive)+
qed

lemma walk_betw_cons:
  "walk_betw G v1 (v2 # v3 # p) v4 \<longleftrightarrow> 
    (walk_betw G v3 (v3 # p) v4 \<and> walk_betw G v1 [v2, v3] v3)"
  by(auto simp: walk_betw_def)

lemma vwalk_betw_can_be_split_3:
  assumes "walk_betw (insert {w, x} G) u p v" "w \<notin> Vs G" "x \<notin> Vs G"
  shows "walk_betw G u p v \<or> walk_betw {{w, x}} u p v"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule walk_betw_insertE, goal_cases)
    case (4 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (simp, metis walk_betw_cons walk_endpoints(1))
  next
    case (5 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw G u [u, v3] v3\<close>] walk_betw_singletonD
      by fastforce
  qed (auto simp add: Vs_def walk_reflexive)
qed

lemma path_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>path (G1 \<union> G2) p; 
     (p = [] \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs G1 \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v \<in> Vs G2 \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path G1 [v1, v2]; path (G1 \<union> G2) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v1 v2. \<lbrakk>path G2 [v1,v2]; path (G1 \<union> G2) (v2 # p'); p = v1 # v2 # p'\<rbrakk> \<Longrightarrow> P )\<rbrakk>
    \<Longrightarrow> P"
proof(induction rule: path.induct)
  case path0
  then show ?case 
    by auto
next
  case (path1 v)
  then show ?case
    by (auto elim!: in_Vs_unionE)
next
  case (path2 v v' vs)
  then show ?case
    by (simp add: vs_member) blast+
qed

lemma walk_betw_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>walk_betw (G1 \<union> G2) v1 p v2; 
     (\<lbrakk>v1\<in>Vs (G1 \<union> G2); v1 = v2; p = []\<rbrakk> \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs G1 \<Longrightarrow> P);
     (\<And>v. p = [v] \<Longrightarrow> v = v1 \<Longrightarrow> v = v2 \<Longrightarrow> v \<in> Vs G2 \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw G1 v1 [v1,v3] v3; walk_betw (G1 \<union> G2) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>walk_betw G2 v1 [v1,v3] v3; walk_betw (G1 \<union> G2) v3 (v3 # p') v2; p = v1 # v3 # p'\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding walk_betw_def
  apply safe
  apply(erule path_unionE)
  by (simp | force)+

lemma singleton_subset: "path {e} p \<Longrightarrow> set p \<subseteq> e"
  by (induction rule: path.induct) (auto simp: Vs_def)

lemma edge_mid_path:
  "path G (p1 @ [v1,v2] @ p2) \<Longrightarrow> {v1,v2} \<in> G"
  using path_suff
  by fastforce

lemma walk_betw_repl_edge:
  assumes "path (insert {w, x} G) p" "p \<noteq> []" "walk_betw G w puv x"
  shows "\<exists>p'. walk_betw G (hd p) p' (last p)"
  using assms
proof(induction rule: induct_list012)
  case nil
  then show ?case
    by auto
next
  case (single x)
  then show ?case
    using walk_reflexive
    by (fastforce elim!: in_Vs_insertE dest: walk_endpoints)+
next
  case (sucsuc x y zs)
  then show ?case
    apply -
  proof(erule path_insertE, goal_cases)
    case (4 p' v1 v2)
    then show ?case
      using walk_symmetric walk_transitive
      by(fastforce simp del: path_simps dest!: path_singletonD)
  next
    case (5 p' v1 v2)
    then show ?case
      using walk_transitive
      by (fastforce simp del: path_simps elim!: nonempty_path_walk_betweenE)
  qed auto
qed

lemma vwalk_betw_can_be_split:
  assumes "walk_betw (insert {w, x} G) u p v" "w \<in> Vs G" "x \<in> Vs G"
  shows "(\<exists>p. walk_betw G u p v) \<or>
         (\<exists>p1 p2. walk_betw G u p1 w \<and> walk_betw G x p2 v) \<or>
         (\<exists>p1 p2. walk_betw G u p1 x \<and> walk_betw G w p2 v)"
  using assms
proof(induction p arbitrary: u v)
  case Nil
  then show ?case
    by (auto simp: walk_betw_def)
next
  case (Cons a zs)
  then show ?case
    apply -
  proof(erule walk_betw_insertE, goal_cases)
    case (4 p' v3)
    (*TODO: Lukas*)
      then show ?case
      apply simp
      using walk_between_nonempty_pathD(4)[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
            walk_betw_singletonD[OF \<open>walk_betw {{w, x}} u [u, v3] v3\<close>]
      by (auto dest: walk_reflexive)
  next
    case (5 p' v3)
    then show ?case
      (*TODO: Lukas*)
      using walk_transitive[OF \<open>walk_betw G u [u, v3] v3\<close>]
      by blast
  qed (insert walk_reflexive, fastforce)+
qed

lemma path_repl_edge:
  assumes "path G' p" "p \<noteq> []" "G' = (insert {w,x} G)" "path G puv" "hd puv = w" "last puv = x" "puv \<noteq> []"
  shows "\<exists>p'. p' \<noteq> [] \<and> path G p' \<and> hd p' = hd p \<and> last p' = last p"
  using assms
  by (metis walk_betw_repl_edge walk_betw_def)

lemma path_can_be_split:
  assumes "path G' p" "G' = insert {w,x} G" "{w,x} \<subseteq> Vs G" "p \<noteq> []"
  shows "(\<exists>p'. p' \<noteq> [] \<and> path G p' \<and> hd p' = hd p \<and> last p' = last p) \<or>
         (\<exists>p1 p2. p1 \<noteq> [] \<and> p2 \<noteq> [] \<and> path G p1 \<and> path G p2 \<and>
                             ((last p1 = w \<and> hd p2 = x) \<or> (last p1 = x \<and> hd p2 = w)) \<and>
                             hd p1 = hd p \<and> last p2 = last p)"
  using assms
  using vwalk_betw_can_be_split[OF _ , simplified walk_betw_def, where p = p and u = "hd p" and v = "last p"]
  apply simp
  by (smt (verit, ccfv_SIG))

lemma path_can_be_split_2:
  assumes "path (insert {w,x} G) p" "w \<in> Vs G" "x \<notin> Vs G" "p \<noteq> []"
  shows "(\<exists>p'. p' \<noteq> [] \<and> path G p' \<and> hd p' = hd p \<and> last p' = last p) \<or>
         (\<exists>p'. path G p' \<and> (p' \<noteq> [] \<longrightarrow> hd p' = w) \<and> ((hd p = last (x # p') \<and> last p = x) \<or> (hd p = x \<and> last p = last (x # p'))))"
  using vwalk_betw_can_be_split_2[OF _ \<open>w \<in> Vs G\<close> \<open>x \<notin> Vs G\<close>, simplified walk_betw_def, where p = p and u = "hd p" and v = "last p"]
  using assms
  apply simp
  by (smt (verit, del_insts) hd_rev last.simps last_rev path_simps(1) rev_is_Nil_conv rev_path_is_path_iff) 

lemma path_can_be_split_3:
  assumes "path G' p" "G' = insert {w,x} G" "w \<notin> Vs G" "x \<notin> Vs G" "p \<noteq> []"
  shows "path G p \<or> path {{w, x}} p"
  using assms
proof(induction)
  case (path2 v v' vs)
  show ?case
  proof(cases "path G (v' #  vs)")
    case True
    then have "path G (v # v' # vs)"
      using path2
      by (force simp: doubleton_eq_iff mem_path_Vs)
    then show ?thesis
      by auto
  next
    case False
    then have path: "path {{w,x}} (v' # vs)"
      using path2
      by auto
    then have "v' = w \<or> v' = x"
      by (cases "vs"; auto simp add: doubleton_eq_iff Vs_def)
    then have "path {{w,x}} (v # v' # vs)"
      using path path2
      by (auto simp: edges_are_Vs)
    then show ?thesis
      by auto
  qed
qed (auto simp add: Vs_def)

lemma v_in_apath_in_Vs_append:
  "path G (p1 @ v # p2) \<Longrightarrow> v \<in> Vs G"
  by (simp add: mem_path_Vs)

lemma edge_between_pref_suff:
  "\<lbrakk>p1 \<noteq> []; p2 \<noteq> []; path G (p1 @ p2)\<rbrakk>
    \<Longrightarrow> {last p1, hd p2} \<in> G"
  by(induction p1) (auto simp: neq_Nil_conv)+

lemma construct_path:
 "\<lbrakk>path G p1; path G p2; {hd p1, hd p2} \<in> G\<rbrakk>
   \<Longrightarrow> path G ((rev p1) @ p2)"
  by (simp add: last_rev path_append rev_path_is_path)

text \<open>A function to remove a cycle from a path\<close>

fun remove_cycle_pfx where
"remove_cycle_pfx a [] = []" |
"remove_cycle_pfx a (b#l) = (if (a = b) then (remove_cycle_pfx a l) else (b#l))"

lemma remove_cycle_pfx_works:
 "\<exists>pfx. (l = pfx @ (remove_cycle_pfx h l) \<and> (\<forall>x\<in>set pfx. x = h))"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then obtain pfx where "l = pfx @ remove_cycle_pfx h l \<and> (\<forall>x\<in>set pfx. x = h)"
    by blast
  then have *: "a # l = (a # pfx) @ remove_cycle_pfx a l \<and> (\<forall>x\<in>set pfx. x = a)" if "h = a"
    using append_Cons that by auto
  show ?case
   by (fastforce dest: *)
qed

lemma remove_cycle_pfx_works_card_ge_2:
 "card (set l) \<ge> 2 \<Longrightarrow> (hd (remove_cycle_pfx (last l) l) \<noteq> last (remove_cycle_pfx (last l) l) 
                       \<and> (set (remove_cycle_pfx (last l) l) = set l))"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  show ?case
  proof(cases "card (set l) < 2")
    case True
    then show ?thesis
      using Cons(2)
      by (auto simp: insert_absorb)
  next
    case False
    then have *: "card (set l) \<ge> 2"
      by simp
    show ?thesis
      using Cons(1)[OF *]
      using "*" by force
  qed
qed

subsection \<open>Paths over Edges\<close>

fun epath :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "epath G u [] v = (u = v)"
| "epath G u (x#xs) v \<longleftrightarrow> (\<exists>w. u \<noteq> w \<and> {u, w} = x \<and> epath G w xs v) \<and> x \<in> G"

lemma epath_empty:
  assumes "epath {} u p v"
  shows "u = v" and "p = []"
  using assms
  by (auto elim: epath.elims)

lemma epath_last:
  "\<lbrakk>p \<noteq> []; epath G u p v\<rbrakk> \<Longrightarrow> v \<in> last p"
  apply (induction p arbitrary: u v)
  by auto

lemma epath_edges_subset:
  "epath G v p w \<Longrightarrow> set p \<subseteq> G"
  apply (induction p arbitrary: v w)
  apply simp
  by auto

lemma epath_subset:
  "\<lbrakk>epath G v p w; G \<subseteq> G'\<rbrakk> \<Longrightarrow> epath G' v p w"
  apply (induction p arbitrary: v w)
  apply simp
  by auto

lemma epath_subset_other_set:
  "\<lbrakk>epath G u p v; set p \<subseteq> G'\<rbrakk> \<Longrightarrow> epath G' u p v"
  apply (induction p arbitrary: u v)
  apply simp
  by auto

lemma epath_single: "\<lbrakk>e \<in> G; e= {x, y}; x \<noteq> y\<rbrakk> \<Longrightarrow> epath G x [e] y"
  by auto

lemma epath_non_empty: "\<lbrakk>epath G u p v; u \<noteq> v\<rbrakk> \<Longrightarrow> length p \<ge> 1"
  by (cases p) auto

lemma epath_find_splitter:
  "epath X u (P@[e,d]@Q) v \<Longrightarrow> \<exists> x. epath X u (P@[e]) x \<and> epath X x ([d]@Q) v \<and> x \<in> e \<inter> d"
proof(induction P arbitrary: u)
  case Nil
  then show ?case by auto
next
  case (Cons ee P)
  obtain w where w_prop:"u \<noteq> w" "{u, w} = ee" "epath X w (P @ [e, d]@Q) v" " ee \<in> X" 
    using Cons(2) by auto
  obtain x where "epath X w (P @ [e]) x" "epath X x ([d] @ Q) v \<and> x \<in> e \<inter> d" 
    using Cons(1)[OF w_prop(3)] by auto
  hence "epath X u ((ee#P) @ [e]) x" "epath X x ([d] @ Q) v \<and> x \<in> e \<inter> d"
    using w_prop by auto
  then show ?case by blast
qed

lemma epath_find_splitter_advanced:
  "epath X u (P@[e1, e2, e3]@Q) v \<Longrightarrow> \<exists> x y.  e2 = {x, y} \<and> x \<noteq> y \<and> epath X u (P@[e1]) x \<and>
                                      epath X y ([e3]@Q) v \<and> x \<in> e1 \<inter> e2 \<and> y \<in> e2 \<inter> e3"
proof(induction P arbitrary: u)
  case Nil
  then show ?case by auto
next
  case (Cons ee P)
  obtain w where w_prop:"u \<noteq> w" "{u, w} = ee" "epath X w (P @ [e1 ,e2 ,e3 ]@ Q) v" "ee \<in> X"
    using Cons(2) by auto
  obtain x y where xy_prop:"e2 = {x, y}"
          "x \<noteq> y" "epath X w (P @ [e1]) x" "epath X y ([e3] @ Q) v" "x \<in> e1 \<inter> e2" "y \<in> e2 \<inter> e3"
    using Cons(1)[OF w_prop(3)] by blast
  hence "epath X u ((ee # P) @ [e1]) x"
    using w_prop by auto
  then show ?case 
    using xy_prop by blast
qed

lemma epath_distinct_epath:
"\<lbrakk>epath G u p v; l = length p\<rbrakk> \<Longrightarrow> \<exists> q. epath G u q v \<and> set q \<subseteq> set p \<and> distinct q" 
proof(induction l arbitrary: u p v rule: less_induct)
  case (less l)
  show ?case
  proof(cases l)
    case 0
    then show ?thesis 
      using less.prems by force
  next
    case (Suc nat)
    note Suc = less Suc
  then obtain e p' where ep':"p = e#p'" by(cases p) auto
  show ?thesis
  proof(cases "e \<in> set p'")
    case True
    then obtain p1 p2 where p1p2:"p' = p1 @[e]@p2"
      by (metis append_Cons append_self_conv2 in_set_conv_decomp_first)
    have bulast_p1_subst:"butlast (e # p1) @ [last (e # p1)] = e#p1"
      by simp
    have epath_verbose:"epath G u (butlast (e # p1) @ [last (e # p1), e] @ p2) v"
      by (metis append.assoc append_Cons append_Nil bulast_p1_subst ep' less.prems(1) p1p2)
    obtain x where x_prop:"epath G u (e#p1) x" 
         "epath G x ([e] @ p2) v" "x \<in> last (e # p1) \<inter> e"
      using epath_find_splitter[OF epath_verbose] by (subst (asm) bulast_p1_subst[symmetric])auto
    show ?thesis 
    proof(cases p1)
      case Nil
      hence epath_p2:"epath G u p2 v"
        using x_prop(2) Suc(2) p1p2 ep' by auto
      have  "\<exists>q. epath G u q v \<and> set q \<subseteq> set p2 \<and> distinct q"
        using p1p2 ep' Suc(3)  by(intro Suc(1)[OF _ epath_p2 refl]) simp
      then obtain q where "epath G u q v" "set q \<subseteq> set p2"  "distinct q"
        by auto
      then show ?thesis
        using ep' p1p2 by auto
    next
      case (Cons a list)
      obtain a where e_endpoints:" e = {a, u}" "a \<noteq> u" 
        using x_prop(1) by auto
      hence x_is:"x = u \<or> x = a"
        using x_prop(3) by blast
      show ?thesis 
      proof(cases rule: disjE[OF x_is])
        case 1
        hence  u_v_path:"epath G u ([e] @ p2) v" 
          using x_prop(2) by force
        obtain q where "epath G u q v" "set q \<subseteq> set ([e] @ p2)" "distinct q" 
          using Suc(1)[OF _ u_v_path refl] Suc(3) ep' p1p2  by auto
        then show ?thesis
          using ep' p1p2 by auto
      next
        case 2
        hence  u_v_path:"epath G u ([e, e] @ p2) v" 
          using e_endpoints x_prop(2) by fastforce
        obtain q where "epath G u q v" "set q \<subseteq> set ([e,e] @ p2)" "distinct q" 
          using Suc(1)[OF _ u_v_path refl] Suc(3) ep' p1p2 Cons  by auto         
        then show ?thesis
          using ep' p1p2 by auto
      qed
    qed
  next
    case False
    then obtain w where w_prop:"u \<noteq> w" "{u, w} = e" "epath G w p' v" "e \<in> G"
      using ep' less.prems(1) by auto
    obtain q where "epath G w q v" "set q \<subseteq> set p'" "distinct q"
      using  Suc(1)[OF _ w_prop(3) refl] ep' Suc(3) by auto
    moreover hence "epath G u (e#q) v"
      using w_prop(1,2,4) by auto
    ultimately show ?thesis 
      using False ep' by(intro exI[of _ "e#q"]) auto
  qed
qed
qed

lemma epath_append: "\<lbrakk>epath X x P y; epath X y Q z\<rbrakk> \<Longrightarrow> epath X x (P@Q) z"
  by(induction X x P y rule: epath.induct) auto

lemma epath_one_split: 
 "\<lbrakk>epath G u p v; {x, y} \<in> set p; x \<noteq> y\<rbrakk>
  \<Longrightarrow> \<exists> p1 p2. p = p1@[{x,y}]@p2 \<and> ((epath G u p1 x \<and> epath G y p2 v) \<or>
                                     (epath G u p1 y \<and> epath G x p2 v))"
proof(induction p arbitrary: u )
  case Nil
  then show ?case by simp
next
  case (Cons e p)
  show ?case 
  proof(cases "{x,y} = e")
    case True
    show ?thesis 
      apply(rule exI[of _ Nil])
      apply(rule exI[of _ p])
      using Cons True by fastforce
  next
    case False
    obtain w where w_prop: "u \<noteq> w" "{u, w} = e" "epath G w p v" "e \<in> G"
      using  Cons(2)[simplified] by auto
    hence xy_in_p:"{x, y} \<in> set p"
      using Cons.prems(2) False by auto
    obtain p1 p2 where p1p2:"p = p1 @ [{x, y}] @ p2" 
      "epath G w p1 x \<and> epath G y p2 v \<or> epath G w p1 y \<and> epath G x p2 v"
      using Cons(1)[OF w_prop(3) xy_in_p Cons(4)] by auto
    show ?thesis
      apply(rule exI[of _ "{u, w}#p1"])
      using p1p2(1) p1p2(2) w_prop(1) w_prop(2) w_prop(4) by (auto intro!: exI[of _ p2])
  qed
qed

lemma epath_rev: "epath G u p v \<Longrightarrow> epath G v (rev p) u"
proof(induction G u p v rule: epath.induct)
  case (2  G u x p v)
  thus ?case
    using epath_append[of G v "rev p" _  "[x]" u] epath_single[of x G]  
    by(auto simp add: doubleton_eq_iff )
qed simp

definition depath :: "'a set set \<Rightarrow> 'a \<Rightarrow> ('a set) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "depath G u p v = ( epath G u p v \<and> distinct p)"

subsection \<open>Edges in a Path\<close>

fun edges_of_path where
"edges_of_path [] = []" |
"edges_of_path [v] = []" |
"edges_of_path (v#v'#l) = {v,v'} # (edges_of_path (v'#l))"

lemma path_ball_edges: "path G p \<Longrightarrow> b \<in> set (edges_of_path p) \<Longrightarrow> b \<in> G"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_index:
  "Suc i < length p \<Longrightarrow> edges_of_path p ! i = {p ! i, p ! Suc i}"
proof(induction i arbitrary: p)
  case 0
  then obtain u v ps where "p = u#v#ps" 
    by (auto simp: less_eq_Suc_le Suc_le_length_iff)
  thus ?case by simp
next
  case (Suc i)
  then obtain u v ps where "p = u#v#ps"
    by (auto simp: less_eq_Suc_le Suc_le_length_iff)
  hence "edges_of_path (v#ps) ! i = {(v#ps) ! i, (v#ps) ! Suc i}"
    using Suc.IH Suc.prems
    by simp
  thus ?case using \<open>p = u#v#ps\<close>
    by simp
qed

lemma edge_not_in_edges_in_path:
  "a \<notin> set p \<or> b \<notin> set p \<Longrightarrow> {a, b} \<notin> set (edges_of_path p)"
  by(induction p rule: edges_of_path.induct) auto

lemma edges_of_path_length: "length (edges_of_path p) = length p - 1"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_length': "p \<noteq> [] \<Longrightarrow> length p = length (edges_of_path p) + 1"
  by (induction p rule: edges_of_path.induct, auto)

lemma edges_of_path_for_inner:
  assumes "v = p ! i" "Suc i < length p"
  obtains u w where "{u, v} = edges_of_path p ! (i - 1)" "{v, w} = edges_of_path p ! i"
proof(cases "i = 0")
  case True thus ?thesis 
    using assms(1) edges_of_path_index[OF assms(2)] that
    by auto
next
  case False thus ?thesis
    by (auto simp add: Suc_lessD assms edges_of_path_index that)
qed

lemma path_vertex_has_edge:
  assumes "length p \<ge> 2" "v \<in> set p"
  obtains e where "e \<in> set (edges_of_path p)" "v \<in> e"
proof-
  have "\<exists>e \<in> set (edges_of_path p). v \<in> e"
    using assms Suc_le_eq 
    by (induction p rule: edges_of_path.induct) fastforce+
  thus ?thesis
    using that
    by rule
qed

lemma v_in_edge_in_path:
  assumes "{u, v} \<in> set (edges_of_path p)"
  shows "u \<in> set p"
  using assms
  by (induction p rule: edges_of_path.induct) auto

lemma v_in_edge_in_path_inj:
  assumes "e \<in> set (edges_of_path p)"
  obtains u v where "e = {u, v}"
  using assms
  by (induction p rule: edges_of_path.induct) auto

lemma v_in_edge_in_path_gen:
  assumes "e \<in> set (edges_of_path p)" "u \<in> e"
  shows "u \<in> set p"
proof-
  obtain u v where "e = {u, v}"
    using assms(1) v_in_edge_in_path_inj
    by blast
  thus ?thesis
    using assms
    by (force simp add: insert_commute intro: v_in_edge_in_path)
qed

lemma distinct_edges_of_vpath:
  "distinct p \<Longrightarrow> distinct (edges_of_path p)"
  using v_in_edge_in_path
  by (induction p rule: edges_of_path.induct) fastforce+

lemma distinct_edges_of_paths_cons:
  assumes "distinct (edges_of_path (v # p))"
  shows "distinct (edges_of_path p)"
  using assms
  by(cases "p"; simp)

lemma hd_edges_neq_last:
  assumes "{hd p, last p} \<notin> set (edges_of_path p)" "hd p \<noteq> last p" "p \<noteq> []"
  shows "hd (edges_of_path (last p # p)) \<noteq> last (edges_of_path (last p # p))"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons)
  then show ?case
    apply (auto split: if_splits)
    using edges_of_path.elims apply blast
    by (simp add: insert_commute)
qed

lemma edges_of_path_append_2:
  assumes "p' \<noteq> []"
  shows "edges_of_path (p @ p') = edges_of_path (p @ [hd p']) @ edges_of_path p'"
  using assms
proof(induction p rule: induct_list012, goal_cases)
  case 2
  obtain a p's where "p' = a # p's" using assms list.exhaust_sel by blast
  thus ?case by simp
qed simp_all

lemma edges_of_path_append_3:
  assumes "p \<noteq> []"
  shows "edges_of_path (p @ p') = edges_of_path p @ edges_of_path (last p # p')"
proof-
  have "edges_of_path (p @ p') = edges_of_path (butlast p @ last p # p')"
    by (subst append_butlast_last_id[symmetric, OF assms], subst append.assoc, simp)
  also have "... = edges_of_path (butlast p @ [last p]) @ edges_of_path (last p # p')"
    using edges_of_path_append_2
    by fastforce
  also have "... = edges_of_path p @ edges_of_path (last p # p')"
    by (simp add: assms)
  finally show ?thesis .
qed

lemma edges_of_path_rev:
  shows "rev (edges_of_path p) = edges_of_path (rev p)"
proof(induction p rule: edges_of_path.induct)
  case (3 v v' l)
  moreover have "edges_of_path (rev l @ [v', v]) = 
                   edges_of_path (rev l @ [v']) @ edges_of_path [v', v]"
    apply(subst edges_of_path_append_2)
    by auto
  ultimately show ?case
    by auto
qed auto

lemma edges_of_path_append: "\<exists>ep. edges_of_path (p @ p') = ep @ edges_of_path p'"
proof(cases p')
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis using edges_of_path_append_2 by blast
qed

lemma last_v_in_last_e: 
  "length p \<ge> 2 \<Longrightarrow> last p \<in> last (edges_of_path p)"
  by (induction "p" rule: induct_list012) (auto elim: edges_of_path.elims simp add: Suc_leI)

lemma hd_v_in_hd_e: 
  "length p \<ge> 2 \<Longrightarrow> hd p \<in> hd (edges_of_path p)"
  by (auto simp: Suc_le_length_iff numeral_2_eq_2)

lemma last_in_edge:
  assumes "p \<noteq> []"
  shows "\<exists>u. {u, last p} \<in> set (edges_of_path (v # p)) \<and> u \<in> set (v # p)"
  using assms
proof(induction "length p" arbitrary: v p)
  case (Suc x)
  thus ?case
  proof(cases p)
    case p: (Cons _ p')
    thus ?thesis
    proof(cases "p' = []")
      case False
      then show ?thesis
        using Suc
        by(auto simp add: p)
    qed auto
  qed auto
qed simp

lemma edges_of_path_append_subset:
  "set (edges_of_path p') \<subseteq> set (edges_of_path (p @ p'))"
proof(cases p')
  case (Cons a list)
  then show ?thesis
    apply(subst edges_of_path_append_2)
    by auto
qed auto

lemma edges_of_path_append_subset_2:
  "set (edges_of_path p) \<subseteq> set (edges_of_path (p @ p'))"
proof(cases p)
  case (Cons a list)
  then show ?thesis 
   by(metis edges_of_path_append_subset edges_of_path_rev rev_append set_rev)
qed auto

lemma path_edges_subset:
  assumes "path G p"
  shows "set (edges_of_path p) \<subseteq> G"
  using assms
  by (induction, simp_all)

lemma edges_of_path_symmetric_split:"edges_of_path (xs@[x,y]@ys) = edges_of_path (xs@[x]) @[{x,y}] @ edges_of_path (y#ys)"
  by (metis append_is_Nil_conv edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append_2 
           edges_of_path_append_3 hd_append2 last_ConsL last_ConsR list.discI list.sel(1))

lemma non_last_vertex_or_even_list_in_even_edge:
  assumes "distinct p" "length p \<ge> 2" "x \<in> set p"
             "x \<noteq> last p \<or> even (length p)"
   obtains i where "even i" "i < length p - 1" "x \<in> edges_of_path p ! i"
proof(goal_cases)
  case 1
  obtain i where i: "p ! i = x" "i < length p"
    using assms(3) by(auto simp add: in_set_conv_nth)
  have  "even i" "i < length p - 1" "x \<in> edges_of_path p ! i"
    if evi:"even i"
  proof-
    show a: "i < length p - 1"
      using evi assms  i(1,2) last_conv_nth[of p] not_less_less_Suc_eq
      by fastforce
    thus  "x \<in> edges_of_path p ! i"
      by (simp add: edges_of_path_index i(1))
  qed (rule evi)
    moreover have  "even (i-1)" "i-1 < length p - 1" "x \<in> edges_of_path p ! (i-1)"
      if odi:"odd i"  
    proof-
      show  "even (i-1)"
        by (simp add: that)
      show "i-1 < length p - 1"
        using i(2) odd_pos that by fastforce
      thus "x \<in> edges_of_path p ! (i-1)"
        by (simp add: edges_of_path_index i(1) that)
    qed
    ultimately show ?case
      by(cases "even i")
        (auto intro: 1[of i] 1[of "i-1"])
  qed

lemma path_edges_of_path_refl: "length p \<ge> 2 \<Longrightarrow> path (set (edges_of_path p)) p"
proof (induction p rule: edges_of_path.induct)
  case (3 v v' l)
  thus ?case
    apply (cases l)
    by (auto intro: path_subset simp add: edges_are_Vs insert_commute path2)
qed simp_all

lemma edges_of_path_Vs: "Vs (set (edges_of_path p)) \<subseteq> set p"
  by (auto elim: vs_member_elim intro: v_in_edge_in_path_gen)

lemma graph_abs_edges_of_distinct_path:
  "distinct p \<Longrightarrow> graph_invar (set (edges_of_path p))"
  by (induction p rule: edges_of_path.induct) auto

lemma distinct_no_self_loop_in_edges_of_path:
"distinct p \<Longrightarrow> \<nexists> x. {x} \<in> set (edges_of_path p)"
  by(induction p rule: edges_of_path.induct) auto

lemma walk_in_edges_of_path:
  "\<lbrakk>walk_betw A v p w; 2 \<le> length p\<rbrakk> \<Longrightarrow> walk_betw (set (edges_of_path p)) v p w"
proof(induction v p w rule: induct_walk_betw)
  case (path2 v v' vs b)
  show ?case
  proof(cases vs)
    case Nil
    hence b'_is_v:"b = v'" 
      using path2.hyps(2) walk_between_nonempty_pathD(4) by force
    show ?thesis
      by (simp add: b'_is_v edges_are_walks local.Nil)
  next
    case (Cons a list)
    hence elngth: "length ( v' # vs) \<ge> 2" by auto
    show ?thesis 
      by(subst walk_betw_cons)
        (auto intro: walk_subset[OF path2(3)[OF elngth]] walk_subset[of "{{v, v'}}"] 
          simp add: edges_are_walks )
  qed
qed auto

lemma walk_betw_strengthen:
  "\<lbrakk>walk_betw G u p v; length p \<ge> 2; set (edges_of_path p) \<subseteq> G'\<rbrakk> \<Longrightarrow> walk_betw G' u p v"
proof(induction  u p v rule: induct_walk_betw)
  case (path1 v)
  then show ?case by auto
next
  case (path2 v v' vs b)
  hence helper: " vs = Nil \<Longrightarrow> v' = b"  
    by (metis last_ConsL walk_betw_def)
  show ?case 
  proof(cases vs)
    case Nil
    then show ?thesis
      using path2(5) by (auto intro!:  edges_are_walks simp add: helper)
  next
    case (Cons a list)
    have "walk_betw G' v' (v' # vs) b"
      using local.Cons path2.IH path2.prems(2) by auto
    moreover have "walk_betw G' v [v, v'] v'" 
      using edges_are_walks path2.prems(2) by force
    ultimately show ?thesis 
      by (meson walk_betw_cons)
  qed
qed

lemma in_edges_of_path':
  "\<lbrakk> v \<in> set p; length p \<ge> 2\<rbrakk> \<Longrightarrow> v \<in> Vs (set (edges_of_path p))"
  by(auto dest: path_vertex_has_edge simp: Vs_def)

lemma in_edges_of_path:
  assumes "v \<in> set p" "v \<noteq> hd p"
  shows "v \<in> Vs (set (edges_of_path p))"
proof-
  have "length p \<ge> 2" using assms 
    by(cases p, auto dest!: length_pos_if_in_set simp: neq_Nil_conv)
  thus ?thesis by (simp add: assms(1) in_edges_of_path')
qed

lemma edges_of_path_nempty:
  "edges_of_path xs \<noteq> [] \<longleftrightarrow> length xs \<ge> 2"
  by(induction xs rule: edges_of_path.induct) auto

lemma last_edge_in_last_vert_in:
  assumes "length p \<ge> 2" "last (edges_of_path p) \<in> G"
  shows "last p \<in> Vs G"
  using assms
proof(induction p rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case
  using last_in_edge[where p="v'#l"]
  by( auto split: if_splits simp: neq_Nil_conv)
qed auto
 
lemma hd_edge_in_hd_vert_in:
  assumes "length p \<ge> 2" "hd (edges_of_path p) \<in> G"
  shows "hd p \<in> Vs G"
  using assms
proof(induction p rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case
  using last_in_edge[where p="v'#l"]
  by( auto split: if_splits simp: neq_Nil_conv)
qed auto

lemma last_vert_in_last_edge:
  assumes "last p \<in> e" "e \<in> set (edges_of_path p)" "distinct p" "length p \<ge> 2"
  shows "e = last (edges_of_path p)"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case cons1: (Cons a p)
  then show ?case
  proof(cases p)
    case Nil
    then show ?thesis using cons1 by simp
  next
    case cons2: (Cons a' p')
    then show ?thesis 
      using cons1 cons2 not_less_eq_eq
      by (auto split: if_splits)
  qed
qed

lemma edges_of_path_snoc:
  assumes "p \<noteq> []"
  shows "(edges_of_path p) @ [{last p, a}] = edges_of_path (p @ [a])"
  using assms
  by (simp add: edges_of_path_append_3)

lemma in_edges_of_path_split: "e \<in> set (edges_of_path p) \<Longrightarrow> \<exists>v1 v2 p1 p2. e = {v1, v2} \<and> p = p1 @ [v1, v2] @ p2"
proof(induction p)
  case Nil
  then show ?case
    by auto
next
  case (Cons v p')
  then have "p' \<noteq> []"
    by auto
  show ?case
  proof(cases "e \<in> set (edges_of_path p')")
    case True
    then show ?thesis
      using Cons
      by (metis append_Cons)
  next
    case False
    then have "e = {v, hd p'}"
      using Cons
      by (cases p'; auto)
    moreover have "v # p' = [] @ [v, hd p'] @ tl p'"
      using \<open>p' \<noteq> []\<close>
      by auto
    ultimately show ?thesis
      by metis
  qed
qed

lemma xy_in_edges_of_path_split: 
  "{x, y} \<in> set (edges_of_path p) \<Longrightarrow> \<exists> p1 p2. p =p1@[x,y]@p2 \<or> p =p1@[y, x]@p2"
  by(force intro: exE[OF in_edges_of_path_split[of "{x, y}" p]] simp add: doubleton_eq_iff)

lemma in_edges_of_path_hd_or_tl:
      assumes "e \<in> set (edges_of_path p)"
      shows "e = hd (edges_of_path p) \<or> e \<in> set (edges_of_path (tl p))"
proof-
  obtain v1 v2 p1 p2 where "e = {v1, v2}" "p = p1 @ [v1, v2] @ p2"
    using in_edges_of_path_split[OF assms]
    by auto
  then show ?thesis
    apply(cases "p1 = []"; simp)
    using edges_of_path_append_2
    by (metis edges_of_path.simps(3) in_set_conv_decomp list.distinct(1))
qed

lemma where_is_v:
  assumes "e \<in> set (edges_of_path (p @ (v # p')))" "v \<in> e" "v \<notin> set p" "v \<notin> set p'" "p \<noteq> []"
  shows "e = {last p, v} \<or> e = {v, hd p'}"
proof-
  obtain v1 v2 p1 p2 us
    where v1v2p1p2us:
      "e = {v1, v2}" 
      "p = p1 @ us \<and> us @ v # p' = v1 # v2 # p2 \<or> p @ us = p1 \<and> v # p' = us @ v1 # v2 # p2"
    using in_edges_of_path_split[OF assms(1)]
    apply(simp add: append_eq_append_conv2)
    by metis
  moreover have "v1 = v \<or> v2 = v"
    using assms(2) v1v2p1p2us
    by auto
  ultimately consider
    "p = p1 @ us \<and> us @ v # p' = v # v2 # p2" |
    "p @ us = p1 \<and> v # p' = us @ v # v2 # p2" |
    "p = p1 @ us \<and> us @ v # p' = v1 # v # p2" |
    "p @ us = p1 \<and> v # p' = us @ v1 # v # p2"
    by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using assms(3-) v1v2p1p2us(1)
      by (metis \<open>v1 = v \<or> v2 = v\<close> append_eq_Cons_conv in_set_conv_decomp list.sel(1) list.sel(3))
  next
    case 2
    then show ?thesis
      using assms(3-) v1v2p1p2us(1)
      by (metis \<open>v1 = v \<or> v2 = v\<close> append.assoc append_Cons_eq_iff list.sel(1) list.set_intros(1))
  next
    case 3
    then have "v \<notin> set us"
      using assms(3) v1v2p1p2us(1)
      by auto
    then have "e = {last us, v}"
      using assms(4) v1v2p1p2us(1)
      by (metis "3" \<open>v1 = v \<or> v2 = v\<close> hd_append2 last_ConsL list.exhaust_sel list.sel(1) list.sel(3) list.set_intros(1) list.set_sel(2) self_append_conv2 tl_append2)
    then have "e = {last p, v}"
      by (metis "3" assms(4) last_appendR list.inject list.set_intros(1) self_append_conv2)
    then show ?thesis
      by simp
  next
    case 4
    then show ?thesis
      using assms(3-) v1v2p1p2us(1)
      by (metis Cons_in_lists_iff append.left_neutral append_in_lists_conv in_listsI list.sel(3) same_append_eq tl_append2)
  qed
qed

lemma length_edges_of_path_rev[simp]: "length (edges_of_path (rev p)) = length (edges_of_path p)"
  by (simp add: edges_of_path_length)

lemma mem_eq_last_edge:
  "\<lbrakk>distinct p; e \<in> set (edges_of_path p); last p \<in> e\<rbrakk>
           \<Longrightarrow> e = last (edges_of_path p)"
  using edges_of_path_nempty last_vert_in_last_edge
  by fastforce

lemma edges_of_path_disj:
  assumes "set p1 \<inter> set p2 = {}"
  shows "set (edges_of_path p1) \<inter> set (edges_of_path p2) = {}"
  using assms
proof(induction p1 arbitrary: p2)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a1' p1')
  then show ?case
    by (cases p1'; auto simp add: v_in_edge_in_path)
qed

lemma edges_of_path_nempty_edges:
  "e \<in> set (edges_of_path p) \<Longrightarrow> e \<noteq> {}"
  using in_edges_of_path_split
  by auto

lemma edges_of_path_snoc_2:
  "edges_of_path (p @ [v1, v2]) = edges_of_path (p @ [v1]) @ [{v1 ,v2}]"
  apply(subst edges_of_path_append_2)
  by auto

lemma edges_of_path_snoc_3: 
  "p \<noteq> [] \<Longrightarrow> edges_of_path (p @ [v1, v2]) = edges_of_path p @ [{last p, v1}, {v1 ,v2}]"
  apply(subst edges_of_path_append_3)
  by auto

lemma walk_betw_imp_epath:
  assumes "dblton_graph G" 
  shows "walk_betw G u p v \<Longrightarrow> epath G u (edges_of_path p) v" 
  using assms
  by (induction p arbitrary: u v rule: edges_of_path.induct)
     (force simp add: doubleton_eq_iff walk_betw_def)+

lemma epath_imp_walk_betw:
  "\<lbrakk>epath G u p v; length p \<ge> 1\<rbrakk> \<Longrightarrow>\<exists> q. walk_betw G u q v \<and> p = edges_of_path q"
proof(induction p arbitrary: u v rule: edges_of_path.induct)
  case (3 e d l u v)
  then obtain a b where e_prop:"e = {a, b}" "a \<noteq> b" "a = u" "e \<in> G"
    by auto 
  hence epath:"epath G b (d # l) v" 
    using "3.prems"(1) doubleton_eq_iff by auto
  then obtain q where q_prop:"walk_betw G b q v"  "d # l = edges_of_path q"
    using 3(1)[OF epath] by auto
  moreover have "walk_betw G u [u, b] b" 
    using e_prop edges_are_walks by force
  moreover have "e#d#l = edges_of_path (u#q)" 
    using e_prop(1) e_prop(3) q_prop(2) walk_between_nonempty_pathD(3)[OF q_prop(1)] 
      walk_nonempty [OF q_prop(1)] by(cases q) auto

  ultimately show ?case 
    using e_prop walk_betw_cons 
    by (auto intro!: exI[of _ "u#q"], cases q)fastforce+
next
  case (2 e u v)
  hence "e \<in> G" "e = {u, v}" "u \<noteq> v" by auto
  thus ?case 
    by(auto intro: exI[of _ "[u, v]"] simp add: edges_are_walks)
qed simp

subsection \<open>Reachability\<close>

definition reachable where
  "reachable G u v = (\<exists>p. walk_betw G u p v)"

lemma reachableE:
  "reachable G u v \<Longrightarrow> (\<And>p. p \<noteq> [] \<Longrightarrow> walk_betw G u p v \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: reachable_def)

lemma reachableD:
  "reachable G u v \<Longrightarrow> \<exists>p. walk_betw G u p v"
  by (auto simp: reachable_def)

lemma reachableI:
  "walk_betw G u p v \<Longrightarrow> reachable G u v"
  by (auto simp: reachable_def)

lemma reachable_trans:
  "\<lbrakk>reachable G u v; reachable G v w\<rbrakk> \<Longrightarrow> reachable G u w"
  apply(erule reachableE)+
  apply (drule walk_transitive)
   apply assumption
  by (rule reachableI)

lemma reachable_sym:
  "reachable G u v \<longleftrightarrow> reachable G v u"
  by(auto simp add: reachable_def dest: walk_symmetric)

lemma reachable_refl:
  "u \<in> Vs G \<Longrightarrow> reachable G u u"
  by(auto simp add: reachable_def dest: walk_reflexive)

lemma not_reachable_empt: "reachable {} u v \<Longrightarrow> False"
  using subset_path_Vs[of empty _, simplified Vs_def Union_empty] 
  by (auto simp add: reachable_def walk_betw_def)

lemma reachable_after_insert:
  assumes "\<not> reachable E u v" "reachable (insert {a, b} E) u v"
          "\<not> (reachable E u a)" "u \<noteq> v"
   shows "reachable E u b \<or> u = a \<or> u = b"
proof-
  note asm = assms
  then obtain p where p_prop:"walk_betw (insert {a, b} E) u p v" 
    using asm  unfolding reachable_def by auto
  hence "\<not> walk_betw E u p v" 
    by (meson \<open>\<not> reachable E u v\<close> reachableI)
  have "set (edges_of_path p) \<subseteq> (insert {a, b} E)"
    using path_edges_subset p_prop unfolding walk_betw_def by auto
  have length_p: "length p \<ge> 2"
  proof(rule ccontr)
    assume " \<not> 2 \<le> length p"
    hence "length p \<le> 1" by simp
    hence "length p = 1"
      using   p_prop  unfolding walk_betw_def 
      by (cases p) auto
    hence "hd p = last p" 
      by (cases p) auto
    thus False
      using p_prop asm unfolding walk_betw_def by simp
  qed
  have 12:"path (set (edges_of_path p)) p"
    by(auto intro: path_edges_of_path_refl simp add: length_p)
  have "\<not> set (edges_of_path p) \<subseteq> E"
  proof
    assume "set (edges_of_path p) \<subseteq> E"
    hence "path E p" 
      using "12" path_subset by blast
    hence "reachable E u v"
      unfolding reachable_def walk_betw_def 
      by (metis p_prop walk_betw_def)
    thus False using asm by simp
  qed
  hence "{a, b} \<in> set (edges_of_path p)" 
    using \<open>set (edges_of_path p) \<subseteq> insert {a, b} E\<close> by blast
  hence "a \<in> set p" "b \<in> set p"
    by (meson insertCI v_in_edge_in_path_gen)+
  then obtain p' x q where p'xq:"p = p'@[x]@q" "x = a \<or> x = b" "a \<notin> set p'" "b \<notin> set p'"
    using extract_first_x[of a p "\<lambda> x. x = a \<or> x = b"]
    by blast
  have 13:"{a, b} \<notin> set (edges_of_path (p'@[x]))" 
    apply(cases "a=b")
    using p'xq  edges_of_path.simps(2)[of x] edges_of_path.simps(3)[of "last p'" x Nil]
             edges_of_path_append_3[of p' "[x]"]   v_in_edge_in_path[of a b "p'@[x]"]
             v_in_edge_in_path[of a b "p'"] edge_not_in_edges_in_path[of a "p'@[x]" b] 
    by(cases p', force, auto)
  show "reachable E u b \<or> u = a\<or> u = b"
  proof(cases "x = b")
    case True
    have "path (insert {a,b} E) (p' @ [x])" 
      using p'xq(1) p_prop walk_between_nonempty_pathD(1)[of "insert {a,b} E" u "p'@[x]" x]
             walk_pref[of "insert {a,b} E" u p' x q v] by simp
    show ?thesis 
    proof(cases "u = b")
      case False
      hence p'_not_empt:"p' \<noteq> []" 
        using True  p'xq(1) p_prop  walk_betw_def[of "insert {a,b} E" u p v] by force
    have "path E (p' @ [x])" 
      apply(rule path_subset, rule path_edges_of_path_refl)
      using  p'_not_empt  "13" \<open>path (insert {a, b} E) (p' @ [x])\<close> path_edges_subset 
      by (auto  simp add: Suc_leI)
    hence "walk_betw E u (p'@[x]) b"
      unfolding walk_betw_def
      using True p'_not_empt p'xq(1) p_prop
                walk_between_nonempty_pathD(3)[of "insert {a,b} E" u p v] by simp
    then show ?thesis unfolding reachable_def by auto
  qed simp
next
  case False
  note false = this
  show ?thesis
  proof(cases "x = a")
    case True
    have "path (insert {a,b} E) (p' @ [x])"
      using p'xq(1) p_prop walk_between_nonempty_pathD(1)[of "insert {a,b} E" u "p'@[x]" x]
            walk_pref[of "insert {a,b} E" u p' x q v] by simp
    show ?thesis 
    proof(cases "u = a")
      case False
      hence p'_not_empt:"p' \<noteq> []" 
        using True  p'xq(1) p_prop  walk_betw_def[of "insert {a,b} E" u p v] by force
     have "path E (p' @ [x])" 
      apply(rule path_subset, rule path_edges_of_path_refl)
      using  p'_not_empt  "13" \<open>path (insert {a, b} E) (p' @ [x])\<close> path_edges_subset 
      by (auto  simp add: Suc_leI)
    hence "walk_betw E u (p'@[x]) a"
      unfolding walk_betw_def 
      using True  p'_not_empt p'xq(1) p_prop 
             walk_between_nonempty_pathD(3)[of "insert {a,b} E" u p v] by simp
    then show ?thesis using asm unfolding reachable_def by auto
  qed simp
next 
  case False
  then show ?thesis using false p'xq by simp
qed
qed
qed

lemma reachable_subset:
  "\<lbrakk>reachable G u v; G \<subseteq> G'\<rbrakk> \<Longrightarrow> reachable G' u v"
  by (auto dest: walk_subset intro: reachableI elim!: reachableE)

lemma reachability_split_2:
  "\<lbrakk>reachable (insert {w, x} G) u v; w \<in> Vs G; x \<notin> Vs G\<rbrakk> \<Longrightarrow>
     (reachable G u v) \<or>
     (reachable G u w \<and> v = x) \<or>
     (reachable G w v \<and> u = x) \<or>
     (u = x \<and> v = x)"
  by(auto simp: reachable_def dest: vwalk_betw_can_be_split_2)

lemma reachability_split3:
  "\<lbrakk>reachable (insert {w, x} G) u v; w \<notin> Vs G; x \<notin> Vs G\<rbrakk> \<Longrightarrow> 
  reachable G u v \<or> reachable {{w, x}} u v"
  by(auto simp: reachable_def dest: vwalk_betw_can_be_split_3)

lemma reachable_in_Vs:
  assumes "reachable G u v"
  shows "u \<in> Vs G" "v \<in> Vs G"
  using assms
  by(auto dest: reachableD)

lemma reachable_insertE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>reachable (insert e G) v1 v2;
     (\<lbrakk>v1 \<in> e; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<lbrakk>v1 \<in> Vs G; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable {e} v1 v3; reachable (insert e G) v3 v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable G v1 v3; reachable (insert e G) v3 v2\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding reachable_def
  apply(erule exE)
  apply(erule walk_betw_insertE)
  by (force simp: Vs_def)+

lemma reachable_unionE[case_names nil sing1 sing2 in_e in_E]:
   "\<lbrakk>reachable (G1 \<union> G2) v1 v2;
     (\<lbrakk>v1 \<in> Vs G2; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<lbrakk>v1 \<in> Vs G1; v1 = v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable G1 v1 v3; reachable (G1 \<union> G2) v3 v2\<rbrakk> \<Longrightarrow> P);
     (\<And>p' v3. \<lbrakk>reachable G2 v1 v3; reachable (G1 \<union> G2) v3 v2\<rbrakk> \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  unfolding reachable_def
  apply(erule exE)
  apply(erule walk_betw_unionE)
  by (force simp: Vs_def)+

lemma reachability_split:
  "\<lbrakk>reachable (insert {w, x} G) u v; w \<in> Vs G; x \<in> Vs G\<rbrakk> \<Longrightarrow>
        (reachable G u v) \<or>
         (reachable G u w \<and> reachable G x v) \<or>
         (reachable G u x \<and> reachable G w v)"
  by(auto simp: reachable_def dest: vwalk_betw_can_be_split)

lemma edges_reachable:
  "{v, w} \<in> G \<Longrightarrow> reachable G v w"
  by (auto intro: edges_are_walks reachableI)

subsection \<open>Paths and Degrees\<close>

lemma degree_edges_of_path_hd:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (hd p) = 1"
proof-
  obtain h nxt rest where p_def: "p = h # nxt # rest" using assms(2)
    by (auto simp: Suc_le_length_iff eval_nat_numeral)
  have calc: "{e. hd (h # nxt # rest) \<in> e} \<inter> set (edges_of_path (h # nxt # rest)) = {{h, nxt}}"
  proof(standard; standard)
    fix e assume "e \<in> {e. hd (h # nxt # rest) \<in> e} \<inter> set (edges_of_path (h # nxt # rest))"
    hence "e = {h, nxt} \<or> e \<in> set (edges_of_path (nxt # rest))" "h \<in> e" by fastforce+
    hence "e = {h, nxt}" using assms(1) v_in_edge_in_path_gen unfolding p_def by fastforce
    then show "e \<in> {{h, nxt}}" by simp
  qed simp
  show ?thesis unfolding p_def degree_def calc by (simp add: one_enat_def)
qed

lemma degree_edges_of_path_last:
  assumes "distinct p" "length p \<ge> 2"
  shows "degree (set (edges_of_path p)) (last p) = 1"
proof-
  have "distinct (rev p)" using assms(1) by simp
  moreover have "length (rev p) \<ge> 2" using assms(2) by simp
  ultimately have "degree (set (edges_of_path (rev p))) (hd (rev p)) = 1"
    using degree_edges_of_path_hd by blast
  then show ?thesis
    by(simp add: edges_of_path_rev[symmetric] hd_rev)
qed

lemma degree_edges_of_path_ge_2:
  assumes "distinct p" "v\<in>set p" "v \<noteq> hd p" "v \<noteq> last p"
  shows "degree (set (edges_of_path p)) v = 2"
  using assms
proof(induction p arbitrary: v rule: induct_list012)
  case nil then show ?case by simp
next
  case single then show ?case by simp
next
  case Cons: (sucsuc a a' p v)
  thus ?case
  proof(cases p)
    case Nil thus ?thesis using Cons.prems by simp
  next
    case p: (Cons a'' p')
    let ?goalset = "{e. a' \<in> e} \<inter> set (edges_of_path (a # a' # a'' # p'))"
    {
      have anotaa: "{a, a'} \<noteq> {a', a''}" using p Cons.prems(1) by fastforce
      moreover have "?goalset = {{a, a'}, {a', a''}}"
      proof(standard; standard)
        fix e assume "e \<in> ?goalset"
        moreover have "a' \<notin> f" if "f \<in> set (edges_of_path (a'' # p'))" for f
          using Cons.prems(1) p that v_in_edge_in_path_gen by fastforce
        ultimately show "e \<in> {{a, a'}, {a', a''}}" by force
      qed fastforce
      moreover have "card {{a, a'}, {a', a''}} = 2" using anotaa by simp
      ultimately have "2 = degree (set (edges_of_path (a # a' # p))) a'"
        unfolding degree_def p by (simp add: eval_enat_numeral one_enat_def)
    }
    moreover {
      fix w assume "w \<in> set (a' # p)" "w \<noteq> hd (a' # p)" "w \<noteq> last (a' # p)"
      hence "2 = degree (set (edges_of_path (a' # p))) w"
        using Cons.IH(2) Cons.prems(1) by fastforce
      moreover have "w \<notin> {a, a'}"
        using Cons.prems(1) \<open>w \<in> set (a' # p)\<close> \<open>w \<noteq> hd (a' # p)\<close> by auto
      ultimately have "2 = degree (set (edges_of_path (a # a' # p))) w" unfolding degree_def by simp
    }
    ultimately show ?thesis using Cons.prems(2-4) by auto
  qed
qed

lemma complete_path_degree_one_head_or_tail:
  assumes "path G p" "distinct p" "v \<in> set p" "degree G v = 1"
  shows "v = hd p \<or> v = last p"
proof(rule ccontr)
  assume "\<not> (v = hd p \<or> v = last p)"
  hence "v \<noteq> hd p" "v \<noteq> last p" by simp_all
  hence "degree (set (edges_of_path p)) v = 2"
    by (simp add: degree_edges_of_path_ge_2 assms(2) assms(3))
  hence "2 \<le> degree G v"
    using subset_edges_less_degree[OF path_edges_subset[OF assms(1)], where v = v]
    by presburger
  then show False
    using assms(4) not_eSuc_ilei0
    by simp
qed

lemma mid_path_deg_ge_2:
  assumes "path G p"
    "v \<in> set p"
    "v \<noteq> hd p"
    "v \<noteq> last p"
    "distinct p"
    "finite G"
  shows "degree G v \<ge> 2"
  using assms
  by (metis degree_edges_of_path_ge_2 path_edges_subset subset_edges_less_degree)

lemma degree_edges_of_path_ge_2_all:
  assumes "distinct p" "length p \<ge> 3" "v\<in>set p"
  shows "degree (set (edges_of_path (last p # p))) v \<ge> 2"
proof(cases "v = hd p \<or> v = last p")
  case True
  moreover obtain a a' a'' p' where p: "p = a # a' # a'' # p'"
    using assms(2)
    by(auto simp add: Suc_le_length_iff eval_nat_numeral)
  ultimately have "v = a \<or> v = last (a'' # p')"
    by auto
  moreover have "2 \<le> degree (set (edges_of_path (last p # p))) a"
  proof-
    have "last p \<noteq> a'" using assms(1) p by auto
    hence "{last p, a} \<noteq> {a, a'}" by (auto simp: doubleton_eq_iff)
    hence "2 \<le> degree {{last p, a}, {a, a'}} a"
      by (simp add: degree_insert eval_enat_numeral one_eSuc)
    moreover have "{{last p, a}, {a, a'}} \<subseteq> set (edges_of_path (last p # p))"
      by (simp add: p)
    ultimately show ?thesis
      using order.trans 
      by (force dest!: subset_edges_less_degree[where v = a])
  qed
  moreover have "2 \<le> degree (set (edges_of_path (last p # p))) (last (a'' # p'))"
  proof-
    obtain u where u: "{u, last (a'' # p')} \<in> set (edges_of_path (a' # a'' # p'))" "u \<in> set (a' # a'' # p')"
      by (elim exists_conj_elims, rule exE[OF last_in_edge]) force
    hence "{u, last (a'' # p')} \<noteq> {a, last (a'' # p')}"
      using assms(1) u
      by (auto simp add: p doubleton_eq_iff)
    hence "2 \<le> degree {{u, last (a'' # p')}, {a, last (a'' # p')}} (last (a'' # p'))"
      by (simp add: degree_insert eval_enat_numeral one_eSuc)
    moreover have "{{u, last (a'' # p')}, {a, last (a'' # p')}} \<subseteq> set (edges_of_path (last p # p))"
      using p u(1) by fastforce
    ultimately show ?thesis
      using order.trans
      by (fastforce dest!: subset_edges_less_degree[where v = "(last (a'' # p'))"])
  qed
  ultimately show ?thesis
    by fastforce
next
  case False
  hence "2 = degree (set (edges_of_path p)) v"
    by (simp add: assms(1) assms(3) degree_edges_of_path_ge_2)
  moreover have "set (edges_of_path p) \<subseteq> set (edges_of_path (last p # p))"
    by (cases p) fastforce+
  then show ?thesis
    by (simp add: \<open>2 = degree (set (edges_of_path p)) v\<close> subset_edges_less_degree)
qed

lemma degree_edges_of_path_ge_2':
  "\<lbrakk>distinct p; v\<in>set p; v \<noteq> hd p; v \<noteq> last p\<rbrakk>
    \<Longrightarrow> degree (set (edges_of_path p)) v \<ge> 2"
  using degree_edges_of_path_ge_2
  by force

end