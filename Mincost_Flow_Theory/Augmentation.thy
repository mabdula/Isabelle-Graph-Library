theory Augmentation
  imports Residual
begin

context flow_network
begin

section \<open>Augmentations in a Residual Graph\<close>
text \<open>In the following we will formalize the concepts of augmenting paths and augmentation.\<close>

subsection \<open>Paths in the Residual Graph\<close>

text \<open>In general, a path in the residual graph is a list of edges connected by vertices.
For the formal definition, we remove the $F$ and $B$ constructors and reduce the
problem the preexisting formalization via the $awalk$ predicate.
Please note that for this definition we just require connectivity and 
disregard residual capacities for now.
\<close>

definition prepath::" ('edge_type Redge) list \<Rightarrow> bool" where
       "prepath p  = (awalk UNIV (fstv (hd p)) (map to_vertex_pair p) (sndv (last p)) 
                             \<and> p \<noteq> [] )"

text \<open>As for residual reachability, we will frequently use some inductive reasoning.
For doing this properly we carefully prepare the rules.
\<close>

lemma prepath_intros:  "prepath  [e]"
                       "sndv e = fstv d \<Longrightarrow> prepath  (d # es) \<Longrightarrow> prepath  (e # d # es)"
  unfolding prepath_def
  by (auto intro: awalk_intros(1) 
        simp add: vs_to_vertex_pair_pres awalk_intros(2)[of "to_vertex_pair e" UNIV] )

lemma prepath_induct: 
  assumes  "prepath  es"
           "(\<And> e. P  [e])"
           "(\<And> e d es. sndv e = fstv d \<Longrightarrow> prepath  (d # es) \<Longrightarrow> P  (d # es) \<Longrightarrow> P  (e # d # es))"
    shows  "P  es"
proof-
  have p_props: "awalk UNIV (fstv (hd es)) (map to_vertex_pair es) (sndv (last es)) "
                           "es \<noteq> []" 
    using assms unfolding prepath_def by auto
  from this assms(2)  assms(3) show ?thesis
  proof(induction es)
    case Nil
    then show ?case using p_props by simp
  next
    case (Cons e p1)
    note IH = this   
    then show ?case 
    proof(cases p1)
      case Nil
      have "P  [e]"
        by(rule IH(4))
      then show ?thesis using Cons Nil by simp
    next
      case (Cons a list)
       show ?thesis
        unfolding prepath_def
          using IH(2) Cons.IH  assms(2) assms(3) awalk_Cons_iff[of _ "sndv e"] vs_to_vertex_pair_pres[of e]
                Cons prepath_def awalk_Cons_iff[of _ "fstv e"]  Cons vs_to_vertex_pair_pres[of a] 
          by (auto intro: IH(5) 
                simp add: awalk_Cons_iff vs_to_vertex_pair_pres prepath_def)
        qed
    qed
  qed

lemma prepath_simps: "prepath a2 = ((\<exists> e. a2 = [e] ) \<or>  (\<exists>e d es.
                                           a2 = e # d # es \<and> sndv e = fstv d \<and> prepath  (d # es)))"
  by(rule, rule prepath_induct[of a2 ], auto intro: prepath_intros)

lemma prepath_cases: "prepath a2 \<Longrightarrow>
                     (\<And>e. a2 = [e]  \<Longrightarrow> P) \<Longrightarrow>
                     (\<And> e d es. a2 = e # d # es \<Longrightarrow> sndv e = fstv d \<Longrightarrow> prepath (d # es) \<Longrightarrow> P) \<Longrightarrow>
                     P"
  using  prepath_induct[of a2 ] by (metis prepath_simps)

text \<open>Now we can reason about some properties of $prepath$.\<close>

lemma prepath_append_single: 
  assumes "prepath es" 
  shows  "sndv(last es) = fstv e \<Longrightarrow> prepath (es@[e])"
  by(induction rule: prepath_induct[OF assms])(auto simp add: prepath_intros)

lemma prepath_append: 
  assumes "prepath es" 
  shows    "prepath ds \<Longrightarrow> sndv(last es) = fstv (hd ds) \<Longrightarrow> prepath (es@ds)"
  apply(induction rule: prepath_induct[OF assms])
  by(cases ds) (auto intro: prepath_intros)

lemma prepath_split1:
  assumes "prepath (xs @ ys)" 
    shows "xs \<noteq> [] \<Longrightarrow> prepath xs"
  by(induction "xs@ys" arbitrary: xs ys rule: prepath_induct)
    (auto intro: non_empt_elim_triple simp add: Cons_eq_append_conv prepath_intros assms)
 
lemma prepath_split2: 
  assumes "prepath (xs@ys)"
  shows   "ys \<noteq> []  \<Longrightarrow> prepath ys"
  apply(induction "xs@ys" arbitrary:  xs ys rule: prepath_induct, simp add: assms)
  by (simp add: Cons_eq_append_conv prepath_intros(1)) (metis append_eq_Cons_conv prepath_intros(2))

lemma prepath_split3:
  assumes "prepath (xs@ys)" 
    shows "xs \<noteq> [] \<Longrightarrow> ys \<noteq> []  \<Longrightarrow> sndv (last xs) = fstv (hd ys)"
  apply(induction "xs@ys" arbitrary:  xs ys rule: prepath_induct, simp add: assms)
  apply(simp add: Cons_eq_append_conv) 
  apply(metis (no_types, opaque_lifting) append_Cons append_self_conv2 last_ConsL
          last_ConsR list.inject list.sel(1) neq_Nil_conv)
  done

lemma prepath_drop_cycles:
  assumes "prepath es" "set es \<subseteq> D" "\<not> distinct es"
  obtains ds where "prepath ds" "distinct ds" "set ds \<subseteq> D" "fstv (hd es) = fstv (hd ds)"
                   "sndv (last es) = sndv (last ds)" "ds \<noteq> []"
  using assms
proof(induction "length es" arbitrary: es  thesis rule: less_induct)
  case less
  then obtain  as bs cs x where asbscs:" es = as @ [x] @ bs @ [x] @ cs"
                                       "distinct bs" "x \<notin> set bs"
  using  list_triple_split_mid_distinct[of es "length es"] by auto
  then show ?case
  proof(cases as)
    case Nil
    note Nil' = this
    then show ?thesis 
    proof(cases cs)
      case Nil
       hence "prepath [x]" "distinct [x]" "set [x] \<subseteq> D" "fstv (hd es) = fstv (hd [x])"
                   "sndv (last es) = sndv (last [x])"
       using asbscs(1) less.prems(3) 
       by (auto simp add: prepath_intros(1) local.Nil' local.Nil)
      then show ?thesis using less by simp
    next
      case (Cons a list)
       hence aa: "prepath ( [x] @ cs)" "fstv (hd es) = fstv (hd ([x] @ cs))"
                 "set ([x] @ cs) \<subseteq> D"  "sndv (last es) = sndv (last ([x] @ cs))"                 
         using  prepath_split2[of "as @ [x] @ bs" "[x] @ cs"] less.prems asbscs Nil' 
         by auto
      then show ?thesis       
      proof(cases "distinct ([x] @ cs)")
        case True
        then show ?thesis using less aa by simp
      next
        case False
        obtain p' where  "prepath p'" "distinct p'"
                         "set p' \<subseteq> D" "fstv (hd ([x] @ cs)) = fstv (hd p') "
                         "sndv (last ([x] @ cs)) = sndv (last p')" "p' \<noteq> []"
          using less(1)[of "[x]@cs"] False asbscs(1) aa by auto
        then show ?thesis using aa less by simp
      qed
    qed
  next
    case (Cons a list) 
    note Cons'= this
    then show ?thesis 
    proof(cases cs)
      case Nil
      hence aa: "prepath ( as@[x])" "fstv (hd es) = fstv (hd (as@[x]))"
                "set (as@[x]) \<subseteq> D"  "sndv (last es) = sndv (last (as@[x]))"                  
       using Cons' prepath_split1[of "as @ [x]" "bs @ [x] @ cs"]  less.prems asbscs Cons' Nil
       by auto
      then show ?thesis       
      proof(cases "distinct (as@[x])")
        case True
        then show ?thesis using less aa by simp
      next
        case False
        obtain p' where  "prepath p'" "distinct p'"  "set p' \<subseteq> D" 
                         "fstv (hd (as@[x])) = fstv (hd p') "
                         "sndv (last (as@[x])) = sndv (last p')" "p' \<noteq> []"
          using less(1)[of "as@[x]"] False asbscs(1) aa by auto
        then show ?thesis using aa less by simp
      qed
    next
      case (Cons a list)
      have aa: "prepath ( as@[x]@cs)" "set (as@[x]@cs) \<subseteq> D" 
               "fstv (hd es) = fstv (hd (as@[x]@cs))" "sndv (last es) = sndv (last (as@[x]@cs))"
        using prepath_append[of as "[x] @ cs"] Cons' asbscs  
              prepath_split1[of "as" "[x] @ bs @ [x] @ cs"]
              prepath_split2[of "as @ [x] @ bs" "[x] @ cs"]
              prepath_split3[of as "[x] @ bs @ [x] @ cs"]  less  Nil 
        by auto
     then show ?thesis 
     proof(cases "distinct (as@[x]@cs)")
        case True
        then show ?thesis using less aa by simp
      next
        case False
        obtain p' where  "prepath p'" "distinct p'"
                         "set p' \<subseteq> D" "fstv (hd (as@[x]@cs)) = fstv (hd p') "
                         "sndv (last (as@[x]@cs)) = sndv (last p')" "p' \<noteq> []"
          using less(1)[of "as@[x]@cs"] False asbscs(1) aa(1) aa(2) by auto
        then show ?thesis using aa less by simp
      qed
    qed
  qed
qed

subsection \<open>Augmenting Paths\<close>

text \<open>In addition to $prepath$, an \textit{augmenting path} requires strictly positive residual capacities.\<close>

definition augpath::"('edge_type \<Rightarrow> real)   \<Rightarrow> ('edge_type Redge) list \<Rightarrow> bool" where
       "augpath f p  = (prepath p \<and> Rcap f (set p) > 0 )"

text \<open>Again, some technical lemmas.\<close>

lemma augpath_intros:
  "0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> augpath f [e]"
  "0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> sndv e = fstv d \<Longrightarrow> augpath f (d # es) \<Longrightarrow> augpath f (e # d # es)"
    unfolding augpath_def
    using augpath_def[of f ]  prepath_intros(2)
          rcap_exract_single[of "d # es"]
    by (auto simp add: prepath_intros(1) rcap_single)

lemma augpath_induct: 
  assumes  "augpath f es"
           "(\<And>f e. 0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> P f [e])"
           "(\<And>f e d es. 0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> sndv e = fstv d \<Longrightarrow> 
                       augpath f (d # es) \<Longrightarrow> P f (d # es) \<Longrightarrow> P f (e # d # es))"
  shows    "P f es"
  using assms
proof(induction rule: prepath_induct[of es ])
  case 1
  then show ?case 
    using assms(1) unfolding augpath_def by simp
next
  case (2 e)
  then show ?case 
    unfolding augpath_def Rcap_def
    by auto
next
  case (3 e d es)
  have augpath: "augpath f (d # es)"
      using prepath_simps[of "e#d#es"] "3.hyps"(2) 3(4) Rcap_def[of f "set (d#es)"]
            Rcap_def[of f "set (e#d#es)"] rcap_exract_single[of "d#es" f e]
      unfolding augpath_def Rcap_def augpath_def 
      by auto
 show ?case 
      using 3  Rcap_def[of f "set (e # d # es)"] 
            rcap_extr_non_zero[of e "e#d#es" "set (e # d # es)" f] 
            prepath_cases[of "e#d#es"]  augpath_def[of f "(e # d # es)"]
      by (force intro!: 3(6) simp add: 3(3) augpath  assms(2))
  qed

lemma augpath_simps: 
"augpath a1 a2 =
((\<exists>f e. a1 = f \<and> a2 = [e] \<and> 0 < \<uu>\<^bsub>f\<^esub>e) \<or>
 (\<exists>f e d es. a1 = f \<and> a2 = e # d # es \<and> 0 < \<uu>\<^bsub>f\<^esub>e \<and> sndv e = fstv d \<and> augpath f (d # es)))"
  by(rule, rule augpath_induct[of a1 a2 ], auto simp add: augpath_intros) 

lemma augpath_cases:
"augpath a1 a2 \<Longrightarrow>
(\<And>f e.     a1 = f \<Longrightarrow> a2 = [e] \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> P) \<Longrightarrow>
(\<And>f e d es. a1 = f \<Longrightarrow> a2 = e # d # es \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e \<Longrightarrow> sndv e = fstv d  \<Longrightarrow> 
            augpath f (d # es) \<Longrightarrow> P) \<Longrightarrow>
P"
  using  augpath_induct[of a1 a2 ]
  by (metis augpath_simps)

text \<open>Let us examine the relationship between $augpath$ and $prepath$.\<close>

lemma augpath_imp_resreach: 
  assumes "augpath f es"
  shows   "set es \<subseteq> \<EE> \<Longrightarrow> resreach f  (fstv (hd es)) (sndv (last es))"
   by(induction  rule: augpath_induct[OF assms]) 
     (auto simp add: resreach_intros)

lemma resreach_imp_augpath: 
  assumes "resreach f u v"
  shows "\<exists> es. augpath f es \<and> (fstv (hd es)) = u \<and>  (sndv (last es)) = v \<and> set es \<subseteq> \<EE>"
proof(induction  rule: resreach_induct[OF assms])
  case (1 f e)
  then show ?case
    using augpath_intros(1) by fastforce 
next
  case (2 f e u  v)
  then obtain es where es_Def: "augpath f es" "(fstv (hd es)) = u" 
                               "(sndv (last es)) = v" "set es \<subseteq> \<EE>"
   by blast
  hence "augpath f (e#es)"
      by (metis "2.hyps"(1) "2.hyps"(2) augpath_simps list.collapse)
  moreover have "set (e#es) \<subseteq> \<EE>" 
      by (simp add: "2.hyps"(3) es_Def)
  ultimately show ?case 
      using es_Def augpath_simps[of f es]  by fastforce
  qed

lemma augpath_from_prepath:
  assumes "prepath es"
  shows   "(\<And> e. e \<in> set es \<Longrightarrow> rcap f e > 0) \<Longrightarrow> augpath f es"
  by(induction rule: prepath_induct[OF assms]) 
    (auto simp add: augpath_intros)

text \<open>And then, some properties of $augpath$s.\<close>

lemma augpath_rcap_pos: 
  assumes "augpath f es"
  shows "(\<forall> e \<in> set es.  rcap f e \<ge> 0)"
    by(induction rule: augpath_induct[OF assms]) auto

lemma augpath_rcap_pos_strict: 
  assumes "augpath f es"
  shows "(\<forall> e \<in> set es.  rcap f e > 0)"
    by(induction rule: augpath_induct[OF assms]) auto

lemma augpath_rcap_pos_strict': 
  assumes "augpath f es"
  shows "e \<in> set es \<Longrightarrow> rcap f e > 0"
    by(induction rule: augpath_induct[OF assms]) auto

lemma augpath_app_single: assumes "augpath f es" 
  shows "fstv e \<noteq> sndv e \<Longrightarrow> rcap f e > 0 \<Longrightarrow> sndv (last es) = fstv e \<Longrightarrow>
       augpath f (es @ [e])"
  by(induction rule: augpath_induct[OF assms]) 
    (auto simp add: augpath_intros)

lemma augpath_app: 
  assumes  "augpath f es" 
  shows    "augpath f ds \<Longrightarrow> sndv (last es) = fstv (hd ds)  \<Longrightarrow> augpath f (es@ds)"
  by(induction rule:  augpath_induct[OF assms])
    (cases ds, auto intro:  augpath_intros )
  
lemma augpath_rcap: 
  assumes"augpath f es" 
  shows"Rcap f (set es) > 0"
  using assms unfolding augpath_def  by simp


lemma augpath_split1: 
  assumes "augpath f (xs@ys)" "xs \<noteq> []" 
  shows   "augpath f xs "
  using assms prepath_split1[of xs ys]  Rcap_strictI[of "set xs" 0 f] 
        rcap_extr_non_zero[of _ "xs@ys" _ f] 
  unfolding augpath_def
  by simp

lemma augpath_split2: 
  assumes"augpath f (xs@ys)" "ys \<noteq> []" 
  shows "augpath f ys "
  using assms prepath_split2[of xs ys]  Rcap_strictI[of "set ys" 0 f] 
        rcap_extr_non_zero[of _ "xs@ys" _ f] 
  unfolding augpath_def
  by simp

lemma augpath_split3: 
  assumes"augpath f (xs@ys)" "xs \<noteq> []"  "ys \<noteq> []"
  shows "sndv (last xs) = fstv (hd ys) "
  using assms prepath_split3[of xs ys] 
  unfolding augpath_def
  by simp

subsection \<open>Augmentations\<close>

text \<open>For a plethora of flow computing algorithms the notion of \textit{augmentation}
     is of crucial importance. Basically, the flow values are changed along a certain path.
     If some constraints are respected while doing this, some kind of well-defined behaviour
     is guaranteed.\<close>

text \<open>First, let us consider the augmentation of a single arc.\<close>

fun augment_edge::"('edge_type  \<Rightarrow> real) \<Rightarrow> real \<Rightarrow>'edge_type Redge \<Rightarrow> ('edge_type \<Rightarrow> real)" where
"augment_edge f \<gamma> e = (\<lambda> d. 
     if d = oedge e then
            (case e of F d \<Rightarrow> f d + \<gamma> |
                       B d \<Rightarrow> f d - \<gamma>)
     else f d)"

text \<open>If we augment below residual capacity, we obtain another flow respecting edge capacities.\<close>

lemma augment_edge_validness_pres:
  "isuflow f \<Longrightarrow> 0 \<le> \<gamma> \<Longrightarrow> ereal \<gamma> \<le> rcap f e \<Longrightarrow> isuflow (augment_edge f \<gamma> e)"
  unfolding isuflow_def
  using ereal_umst ereal_le_le
  by(cases rule:  redge_pair_cases)(auto simp add: add.commute u_non_neg )

text \<open>The augmentation along a path is defined as the sequentially preformed augmentation of the edges.\<close>

fun augment_edges::"('edge_type \<Rightarrow> real) \<Rightarrow> real \<Rightarrow>('edge_type Redge) list \<Rightarrow> ('edge_type \<Rightarrow> real)" where
"augment_edges f \<gamma> [] = f"|
"augment_edges f \<gamma> (e#es) = augment_edge (augment_edges f \<gamma> es) \<gamma> e"

lemma augment_edges_fold: "augment_edges f \<gamma> es = foldr (\<lambda> e f. augment_edge f \<gamma> e) es f"
  by(induction es) simp+

text \<open>Residual capacities related to edges that have got nothing to do
      with the augmentation do not change.\<close>

lemma e_not_in_p_aug: 
  "e \<notin> set es \<Longrightarrow> erev e \<notin> set es \<Longrightarrow> rcap (augment_edges f \<gamma> es) e = rcap f e"
  apply(induction f \<gamma> es rule: augment_edges.induct, simp)
     by(rule redge_pair_cases)(simp, metis  oedge.simps sndv.cases)+

text \<open>If we augment a forward residual arc, the flow increases accordingly.\<close>

lemma erev_augment: "rcap (augment_edge f \<gamma> e) (erev e) = rcap f (erev e) + \<gamma>"
  apply(cases rule: redge_pair_cases) 
  apply (smt (verit, ccfv_threshold) Redge.simps(6) add.right_neutral add_diff_eq_ereal augment_edge.elims case_prod_conv ereal_diff_add_assoc2 ereal_minus(1) erev.simps(1) erve_erve_id oedge.simps(1) oedge_and_reversed rcap.simps(1) zero_ereal_def)
  by (metis (no_types, lifting) Redge.simps(5) augment_edge.elims case_prod_conv erev.simps(2) erve_erve_id oedge.simps(2) oedge_and_reversed plus_ereal.simps(1) rcap.simps(2))

lemma e_ot_first_unfold: 
  "e \<noteq> d \<Longrightarrow> e \<noteq> erev d \<Longrightarrow>rcap (augment_edges f \<gamma> (d#es)) e = rcap (augment_edges f \<gamma> es) e"
  using augment_edges.simps(1)[of f \<gamma> ]  augment_edges.simps(2)[of f \<gamma> d es]  
        e_not_in_p_aug[ of e "[d]" "augment_edges f \<gamma> es" \<gamma>] erve_erve_id[of e] 
  by force 

text \<open>If the reverse of an edge $e$ is augmented, then $e$'s residual capacity increases.\<close>

lemma rev_e_in_p_aug:
  "e \<notin> set es \<Longrightarrow> erev e \<in> set es \<Longrightarrow>distinct es \<Longrightarrow> rcap (augment_edges f \<gamma> es) e = rcap f e + \<gamma>"
proof(induction f \<gamma> es rule: augment_edges.induct)
  case (2 f \<gamma> d es)
  then show ?case 
  proof(cases "e = erev d")
    case True
    hence 1:"e \<notin> set es" and 2:"erev e\<notin> set es" 
      using "2.prems"(1) "2.prems"(3) True  erve_erve_id[of d]
      by auto
    hence 3: " \<uu>\<^bsub>augment_edges f \<gamma> es\<^esub>e = \<uu>\<^bsub>f\<^esub>e" 
      using e_not_in_p_aug by blast
    then show ?thesis 
      using True erev_augment by auto
  next
    case False
    hence 1: "e \<notin> set es" and 2:"erev e \<in> set es" and 3:"distinct es" 
      using "2.prems" False erve_erve_id[of e] set_ConsD 
      by auto
    have 4:"\<uu>\<^bsub>augment_edges f \<gamma> es\<^esub>e = \<uu>\<^bsub>f\<^esub>e + \<gamma>" 
      using 1 2 "2.IH" "3" by blast
    have 5: " \<uu>\<^bsub>augment_edges f \<gamma> (d # es)\<^esub>e  = \<uu>\<^bsub>augment_edges f \<gamma> (es)\<^esub>e " 
      using "2.prems"(1) False e_ot_first_unfold by force
    then show ?thesis
      using "4" by presburger
  qed
qed simp

text \<open>For any valid flow an augmentation respecting residual capacities will preserve respect
 for capacities.\<close>

lemma uflow_pres_single:
  assumes "isuflow f" "\<gamma> \<le> rcap f e" "e \<in> \<EE>" "0 \<le> \<gamma>"
  shows   "isuflow (augment_edge f \<gamma> e )"
  unfolding isuflow_def
proof
  fix d
  assume assmsD: " d \<in> \<E> "
  show "augment_edge f \<gamma> e d \<le> \<u> d \<and> 0 \<le> augment_edge f \<gamma> e d"
  proof(cases "d = oedge e")
    case True
    then show ?thesis 
    proof(cases "e = F d")
      case True
      have "rcap f e = \<u> d - f d" 
        by (simp add: True)
      moreover have "augment_edge f \<gamma> e d = f d + \<gamma>" 
        using True  augment_edge.simps Redge.simps(5) oedge.simps(1)[of d] 
        by simp
      ultimately show ?thesis 
        using assms  assmsD augment_edge_validness_pres isuflow_def
        by blast 
    next
      case False
      hence false: "e = B d" 
        using True \<EE>_def assms(3) by force
      have "rcap f e =  f d" 
        using False True oedge.elims[of e d] rcap.simps(2)[of f d] 
        by force
      moreover have "augment_edge f \<gamma> e d = f d - \<gamma>" 
        using  false by auto
      ultimately show ?thesis
        using assms assmsD dual_order.trans isuflow_def 
        by fastforce
    qed
  next
    case False
    thus ?thesis
      using e_not_in_p_aug[of e "[e]" f \<gamma>] assms(1) 
      by(auto intro: redge_pair_cases 
           simp add: assmsD isuflow_def)
  qed
qed

text \<open>Similarly, augmenting an augmenting path preserves compliance with capacity constraints.\<close>

lemma augment_path_validness_pres:
 assumes "isuflow f" "0 \<le> \<gamma>" "\<gamma> \<le> Rcap f (set es)" " set es \<subseteq> \<EE>" " distinct es"
 shows   "isuflow (augment_edges f \<gamma> es)"
  using assms
proof(induction es arbitrary: f)
  case (Cons e es)
  hence finite_es: "finite (set (e#es))" 
    using finite_\<EE> rev_finite_subset by simp
  hence  " \<gamma> \<le> rcap f e" 
    apply(subst  miny(2)[of \<gamma> "rcap f e"],
          subst Min.in_idem[of "{\<uu>\<^bsub>f\<^esub>ea |ea. ea \<in> set (e # es)}" "rcap f e"])
    using  Cons(4) finite_es Rcap_same[of "set (e#es)" f, simplified]    
    unfolding Rcap_old_def
    by(auto simp add: finite_img[of "set (e#es)" "\<lambda> e. rcap f e"])
  have distinct_es: "distinct es"
    using Cons.prems(5) by fastforce
  have e_not_in_es: " e \<notin> set es" 
    using Cons.prems(5) by auto
  have gamma_Rcap: "\<gamma> \<le> Rcap f (set (e # es))" 
    using Cons by simp
  have uflow_tail: " isuflow (augment_edges f \<gamma>  es)"
  proof(cases es)
    case (Cons a list)
     have "\<gamma> \<le> Rcap f (set es)"
        using  Min_antimono[of "{\<uu>\<^bsub>f\<^esub>ea |ea. ea \<in> set (es)}" "{\<uu>\<^bsub>f\<^esub>ea |ea. ea \<in> set (e # es)}"]
               finite_es  finite_img[of "set (e#es)" "\<lambda> e. rcap f e"] gamma_Rcap local.Cons
        unfolding Rcap_def
        by fastforce
     then show ?thesis 
     using Cons.IH Cons.prems(1) Cons.prems(2) Cons.prems(4) distinct_es by auto
 qed  (simp add: Cons.prems(1))
  have gamma_lesseq_res: "\<gamma> \<le> \<uu>\<^bsub>augment_edges f \<gamma> es\<^esub>e"
    using rev_e_in_p_aug[of e es f \<gamma>] distinct_es e_not_in_es Cons.prems(2) 
          \<open>\<gamma> \<le> \<uu>\<^bsub>f\<^esub>e\<close> e_not_in_p_aug[of e es f \<gamma>] e_not_in_es \<open>\<gamma> \<le> \<uu>\<^bsub>f\<^esub>e\<close> 
    by (cases "erev e \<in> set es") (auto simp add: add.commute  add_increasing)
  show ?case 
    using uflow_tail uflow_pres_single[of "(augment_edges f \<gamma> es)" \<gamma> e]
          Cons.prems(2) Cons.prems(4) gamma_lesseq_res 
    by auto
qed simp

lemma augment_edge_away:"oedge d \<noteq> oedge e \<Longrightarrow> (augment_edge f \<gamma> e) (oedge d) = f (oedge d)"
  by force

text \<open>If we augment an edge that has got nothing to do with a certain vertex,
      then this vertex's excess flow won't change.\<close>

lemma augment_edge_away_from_node:
  assumes "fstv e \<noteq> v" "sndv e\<noteq> v"
    shows "ex (augment_edge f \<gamma> e) v = ex f v"
  unfolding ex_def
proof-
  have " d \<in> (\<delta>\<^sup>- v) \<Longrightarrow> (augment_edge f \<gamma> e) d = f d" for d
    using  \<EE>_def assms  o_edge_res  delta_minus_def  by auto
  moreover have "d \<in> (\<delta>\<^sup>+ v) \<Longrightarrow> (augment_edge f \<gamma> e) d = f d" for d
    using  \<EE>_def assms  o_edge_res  delta_plus_def  by auto
  ultimately show "sum (augment_edge f \<gamma> e) (\<delta>\<^sup>- v) - sum (augment_edge f \<gamma> e) (\<delta>\<^sup>+ v) =
    sum f (\<delta>\<^sup>- v) - sum f (\<delta>\<^sup>+ v)" by auto
qed

text \<open>Now we examine how an augmentation affects excess flows.
We consider all combinations of forward vs. backward and incoming vs. outgoing separately.
\<close>

lemma augment_edge_head_forward:
  assumes "x \<in> \<V>" "y\<in> \<V>" "e \<in> \<E>"  "x \<noteq> y" "x = fst e" "y = snd e"
    shows "ex (augment_edge f \<gamma> (F e)) x = ex f x - \<gamma>"
  unfolding ex_def
proof-
  have 11:"augment_edge f \<gamma> (F e) e = f e +\<gamma>" 
    by simp
  moreover have 33:"snd d \<noteq> y \<Longrightarrow> augment_edge f \<gamma>  (F e) d = f d" for d
    using assms(6) by auto
  have "d \<in>  (\<delta>\<^sup>- x) \<Longrightarrow> snd d \<noteq> y" for d
    using assms(4-6) 
    by(auto simp add: assms delta_minus_def) 
  hence "sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>- x) = sum f (\<delta>\<^sup>- x)"  
    using snd_conv sum.cong[of "{e \<in> \<E>. snd e = x} " ] "33" by (auto simp add: delta_minus_def)
  have "d \<in>  (\<delta>\<^sup>+ x) \<Longrightarrow> snd d \<noteq> y \<Longrightarrow> augment_edge f \<gamma>  (F e) d = f d" for d
       using  assms delta_minus_def by fastforce
  have "sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>+ x) = 
        sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>+ x - {e})  +  (augment_edge f \<gamma>  (F e)) e"
    using assms delta_plus_finite[of x] 
          sum.remove[of "\<delta>\<^sup>+ x "e "(augment_edge f \<gamma> (F e))"]  delta_plus_def
    by (cases "e \<in> delta_plus x") auto
  have  "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>+ x - {e}) = sum f (\<delta>\<^sup>+ x - {e})"  
            by force
  hence  "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>+ x)  = sum f(\<delta>\<^sup>+ x) + \<gamma> "
     using 11 
     by(cases "e \<in> delta_plus x")
     (simp add: assms(1) delta_plus_finite sum.remove, auto simp add: assms(3,5) delta_plus_def)
  then show "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- x) - sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>+ x) =
                  sum f (\<delta>\<^sup>- x) - sum f (\<delta>\<^sup>+ x) - \<gamma>"
    using \<open>sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- x) = sum f (\<delta>\<^sup>- x)\<close> by linarith
qed

lemma augment_edge_head_backward:
  assumes "x \<in> \<V>" "y\<in> \<V>" "e \<in> \<E>""x \<noteq> y" "x= fst e" "y = snd e"
    shows "ex (augment_edge f \<gamma> (B e)) x = ex f x + \<gamma>"
  unfolding ex_def
proof-
  have 11:"augment_edge f \<gamma> (B e) e = f e - \<gamma>" 
    by simp
  moreover have 33:"snd d \<noteq> y \<Longrightarrow> augment_edge f \<gamma>  (B e) d = f d" for d
    using assms(5,6) by auto
  have "d \<in>  (\<delta>\<^sup>- x) \<Longrightarrow> snd d \<noteq> y" for d
    using assms(5,6,4)
    by (auto simp add: assms delta_minus_def )
  hence "sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>- x) = sum f (\<delta>\<^sup>- x)" 
    using snd_conv sum.cong[of "{e \<in> \<E>. snd e = x} " ] 33 
    by(auto simp add: delta_minus_def )
  have " d \<in>  (\<delta>\<^sup>+ x) \<Longrightarrow> snd d \<noteq> y \<Longrightarrow> augment_edge f \<gamma>  (B e) d = f d" for d
    using  assms delta_minus_def by fastforce
  have "sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>+ x) = 
        sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>+ x - {e})  +  (augment_edge f \<gamma>  (B e)) e"
    using assms delta_plus_finite[of x] 
          sum.remove[of "\<delta>\<^sup>+ x " e "(augment_edge f \<gamma> (B _))"]  delta_plus_def
    by (cases "e \<in> delta_plus x") auto
 have  "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>+ x - {e}) =  sum f (\<delta>\<^sup>+ x - {e})"  
            by force
 hence  "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>+ x)  = sum f(\<delta>\<^sup>+ x) - \<gamma> "
     using 11 
     by(cases "e \<in> delta_plus x")
       (simp add: assms(1) delta_plus_finite sum.remove, auto simp add: assms(3,5) delta_plus_def)
  then show "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- x) - sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>+ x) =
                  sum f (\<delta>\<^sup>- x) - sum f (\<delta>\<^sup>+ x) + \<gamma>"
    using \<open>sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- x) = sum f (\<delta>\<^sup>- x)\<close> by linarith
qed

lemma augment_edge_tail_forward:
  assumes "x \<in> \<V>" "y\<in> \<V>" "e \<in> \<E>" "x \<noteq> y" "fst e = x" "snd e = y"
    shows "ex (augment_edge f \<gamma> (F e)) y = ex f y + \<gamma>"
  unfolding ex_def
proof-
  have 11:"augment_edge f \<gamma> (F e) e = f e + \<gamma>" 
    by simp
  have "d \<in>  (\<delta>\<^sup>+ y) \<Longrightarrow> augment_edge f \<gamma> (F e) d = f d" for d
    using assms(4,5) delta_plus_def by force
  have " d \<in>  (\<delta>\<^sup>- y) \<Longrightarrow> fst  d \<noteq> x \<Longrightarrow> augment_edge f \<gamma>  (F e) d = f d" for d
    using assms(5) by force
  have "sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>- y) = 
        sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>- y - {e})  +  (augment_edge f \<gamma>  (F e)) e"
    using  assms delta_minus_finite delta_minus_def
           sum.remove[of "\<delta>\<^sup>- y" "e" "(augment_edge f \<gamma> (F e))"]
    by(cases "e \<in> delta_minus y") auto
  have  "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- y - {e}) =  sum f (\<delta>\<^sup>- y - {e})"  
            by force
  hence  "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- y)  = sum f(\<delta>\<^sup>- y) + \<gamma> "
           using 11 assms(2) delta_minus_finite[of y ] sum.remove[of "(\<delta>\<^sup>- y)"e f] 
                 sum.remove[of "(\<delta>\<^sup>- y)" e "(augment_edge f \<gamma> (F e))"]
    by (cases "e \<in> delta_minus y") (auto simp add: assms(3,6) delta_minus_def)
  then show "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- y) - sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>+ y) =
             sum f (\<delta>\<^sup>- y) - sum f (\<delta>\<^sup>+ y) + \<gamma>"
    using \<open>\<And>d. d \<in> \<delta>\<^sup>+ y \<Longrightarrow> augment_edge f \<gamma> (F e) d = f d\<close> by auto
qed

lemma augment_edge_tail_backward:
  assumes "x \<in> \<V>" "y\<in> \<V>" "e \<in> \<E>" "x \<noteq> y" "fst e = x" "snd e = y"
    shows "ex (augment_edge f \<gamma> (B e)) y = ex f y - \<gamma>"
  unfolding ex_def
proof-
  have 11:"augment_edge f \<gamma> (B e) e = f e - \<gamma>" 
    by simp
  have "d \<in>  (\<delta>\<^sup>+ y) \<Longrightarrow> augment_edge f \<gamma> (B e) d = f d" for d
    using assms(4,5) delta_plus_def  by force
  have "d \<in>  (\<delta>\<^sup>- y) \<Longrightarrow> fst  d \<noteq> x \<Longrightarrow> augment_edge f \<gamma>  (B e) d = f d" for d
    using assms(5)  by force
  have "sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>- y) = 
        sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>- y - {e}) + (augment_edge f \<gamma>  (B e)) e"
    using assms(1) delta_minus_finite[of y] assms(3) delta_minus_def
          sum.remove[of "\<delta>\<^sup>- y" e "(augment_edge f \<gamma> (B e))"] assms(6)
    by (cases "e \<in> delta_minus y") auto
  have  "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- y - {e}) = sum f (\<delta>\<^sup>- y - {e})"  
    by force
  hence  "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- y)  = sum f(\<delta>\<^sup>- y) - \<gamma> "
    using 11 assms(2) delta_minus_finite sum.remove[of "\<delta>\<^sup>- y"e f]
          sum.remove[of "\<delta>\<^sup>- y"e "(augment_edge f \<gamma> (B e))"] 
    by (cases "e \<in> delta_minus y") (auto simp add: assms(3,6) delta_minus_def)
  then show "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- y) - sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>+ y) =
                           sum f (\<delta>\<^sup>- y) - sum f (\<delta>\<^sup>+ y) - \<gamma>"
    using \<open>\<And>d. d \<in> \<delta>\<^sup>+ y \<Longrightarrow> augment_edge f \<gamma> (B e) d = f d\<close> by auto
qed

lemma augment_loop_backward:
  assumes  "x \<in> \<V>" "e \<in> \<E>" "x = fst e" "x = snd e"
    shows  "ex (augment_edge f \<gamma> (B e)) x = ex f x"
  unfolding ex_def 
proof-
  have 11:"augment_edge f \<gamma> (B e) e = f e - \<gamma>" 
    by simp
  have "d \<in>  (\<delta>\<^sup>+ x) \<Longrightarrow> snd d \<noteq> x\<Longrightarrow> augment_edge f \<gamma> (B e) d = f d" for d
    using assms delta_plus_def  by fastforce
  have "d \<in>  (\<delta>\<^sup>- x) \<Longrightarrow> fst  d \<noteq> x \<Longrightarrow> augment_edge f \<gamma>  (B e) d = f d" for d
    using assms(3) by force
  have "sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>- x) = 
        sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>- x - {e}) + (augment_edge f \<gamma>  (B e)) e"
     using delta_minus_finite[of x] sum.remove[of "\<delta>\<^sup>- x"e "(augment_edge f \<gamma> (B e))"]
           sum.remove[of "\<delta>\<^sup>- x" e f]  assms delta_minus_def 
     by auto
  have  "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- x - {e}) =sum f (\<delta>\<^sup>- x - {e})"  
     by force
  hence  "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- x)  = sum f(\<delta>\<^sup>- x) - \<gamma>"
    using delta_minus_finite[of x] sum.remove[of "\<delta>\<^sup>- x" e "(augment_edge f \<gamma> (B e))"]
          sum.remove[of "\<delta>\<^sup>- x" e f]  assms delta_minus_def 11 
     by auto
  have "sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>+ x) = 
        sum (augment_edge f \<gamma>  (B e)) (\<delta>\<^sup>+ x - {e})  +  (augment_edge f \<gamma>  (B e)) e"
    using assms delta_plus_finite[of x] sum.remove[of "\<delta>\<^sup>+ x" e f] 
          sum.remove[of "\<delta>\<^sup>+ x" e "(augment_edge f \<gamma> (B e))"] delta_plus_def 
    by auto
  have  "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>+ x - {e}) = sum f (\<delta>\<^sup>+ x - {e})"  
    by force
  hence "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>+ x)  = sum f(\<delta>\<^sup>+ x) - \<gamma>"
    using delta_plus_finite[of x] sum.remove[of "\<delta>\<^sup>+ x"e "(augment_edge f \<gamma> (B e))"]
          sum.remove[of "\<delta>\<^sup>+ x" e f]  assms delta_plus_def 11 
     by auto
  then show "sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- x) - sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>+ x) =
             sum f (\<delta>\<^sup>- x) - sum f (\<delta>\<^sup>+ x)" 
    using \<open>sum (augment_edge f \<gamma> (B e)) (\<delta>\<^sup>- x) = sum f (\<delta>\<^sup>- x) - \<gamma>\<close> by linarith
qed

lemma augment_loop_forward:
  assumes "x \<in> \<V>" "e \<in> \<E>" "x = fst e" "x = snd e"
    shows "ex (augment_edge f \<gamma> (F e)) x = ex f x"
  unfolding ex_def 
proof-
  have 11:"augment_edge f \<gamma> (F e) e = f e + \<gamma>" 
    by simp
  have "d \<in>  (\<delta>\<^sup>+ x) \<Longrightarrow> snd d \<noteq> x\<Longrightarrow> augment_edge f \<gamma> (F e) d = f d" for d
    using assms delta_plus_def by fastforce
  have "d \<in>  (\<delta>\<^sup>- x) \<Longrightarrow> fst  d \<noteq> x \<Longrightarrow> augment_edge f \<gamma>  (F e) d = f d" for d
    using assms(3) by force
  have "sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>- x) = 
        sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>- x - {e})  +  (augment_edge f \<gamma>  (F e)) e"
     using delta_minus_finite[of x] sum.remove[of "\<delta>\<^sup>- x" e "(augment_edge f \<gamma> (F e))"]
           sum.remove[of "\<delta>\<^sup>- x" e f]  assms delta_minus_def 
     by auto
  have "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- x - {e}) = sum f (\<delta>\<^sup>- x - {e})"  
       by force
  hence  "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- x)  = sum f(\<delta>\<^sup>- x) + \<gamma>"
    using delta_minus_finite[of x] sum.remove[of "\<delta>\<^sup>- x" e "(augment_edge f \<gamma> (F e))"]
          sum.remove[of "\<delta>\<^sup>- x" e f]  assms delta_minus_def 11 
     by auto
  have "sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>+ x) = 
        sum (augment_edge f \<gamma>  (F e)) (\<delta>\<^sup>+ x - {e})  +  (augment_edge f \<gamma>  (F e)) e"
   using assms delta_plus_finite[of x] sum.remove[of "\<delta>\<^sup>+ x" e f] 
          sum.remove[of "\<delta>\<^sup>+ x" e "(augment_edge f \<gamma> (F e))"] delta_plus_def 
   by auto
  have "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>+ x - {e}) =  sum f (\<delta>\<^sup>+ x - {e})"  
      by force
  hence  "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>+ x)  = sum f(\<delta>\<^sup>+ x) + \<gamma>"
    using delta_plus_finite[of x] sum.remove[of "\<delta>\<^sup>+ x"e "(augment_edge f \<gamma> (F e))"]
          sum.remove[of "\<delta>\<^sup>+ x" e f]  assms delta_plus_def 11 
     by auto
  then show "sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- x) - sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>+ x) =
             sum f (\<delta>\<^sup>- x) - sum f (\<delta>\<^sup>+ x)" 
    using \<open>sum (augment_edge f \<gamma> (F e)) (\<delta>\<^sup>- x) = sum f (\<delta>\<^sup>- x) + \<gamma>\<close> by linarith
qed

text \<open>Let us look at how the balances get affected by performing an augmentation.\<close>

lemma augment_validness_b_pres_single:
  assumes "f is b flow" "0 \<le> \<gamma>"  "\<gamma> \<le> rcap f e" "e \<in> \<EE>" 
  defines "b' \<equiv> \<lambda> v. (if v = sndv e then b v - \<gamma>
                      else b v)"
  shows "(augment_edge f \<gamma> e) is (\<lambda> v. if v = fstv e then b' v + \<gamma>  else b' v) flow"
  unfolding isbflow_def
proof
  show " isuflow (augment_edge f \<gamma> e)" 
    using assms uflow_pres_single 
    unfolding isbflow_def by auto
  show "\<forall>v\<in>\<V>. - ex\<^bsub>augment_edge f \<gamma> e\<^esub> v = (if v = fstv e then b' v + \<gamma> else b' v)"
  proof
   fix v
   assume " v \<in> \<V>"
   show "- ex\<^bsub>augment_edge f \<gamma> e\<^esub> v = (if v = fstv e then b' v + \<gamma>  else b' v)"
   proof(cases "fstv e \<noteq> sndv e")
    case True
    hence aaa: "fstv e \<noteq> sndv e" by simp
    then show ?thesis 
    proof(cases e)
      case (F ee)
      then show ?thesis 
        proof(cases "v = fstv e")
          case True
          then show ?thesis 
            using  augment_edge_head_forward[OF _ _ _ _ _ refl]  F assms(4) o_edge_res[of e]
                   snd_E_V[of ee] aaa \<open>v \<in> \<V>\<close> assms(1) 
            by(auto simp add: b'_def isbflow_def)       
         next
          case False
          hence caseFalse:"v\<noteq> fstv e" by simp
          then show ?thesis 
          proof(cases "v = sndv e")
            case True
            then show ?thesis
              using augment_edge_tail_forward[OF _ _ _ _ refl]
                      F \<open>v \<in> \<V>\<close> assms(1) assms(4)  caseFalse 
                      fst_E_V[of ee]  o_edge_res[of e] oedge_simps'(1) 
              by(auto simp add: b'_def isbflow_def)
            next
            case False
            hence "fstv e \<noteq> v" "sndv e \<noteq> v"
              using F caseFalse by auto
            then show ?thesis 
              using \<open>v \<in> \<V>\<close> assms(1) b'_def augment_edge_away_from_node[of e v f \<gamma>] 
                    isbflow_def[of f b] 
              by auto
            qed
          qed
    next
      case (B ee)
      then show ?thesis 
        proof(cases "v = fstv e")
          case True
          then show ?thesis 
            using B  aaa assms augment_edge_tail_backward[OF _ _ _ _ refl] 
                  o_edge_res[of e] \<open>v \<in> \<V>\<close> 
            by (auto simp add: isbflow_def b'_def  fst_E_V)
         next
          case False
          hence caseFalse:"v\<noteq> fstv e" by simp
          then show ?thesis 
          proof(cases "v = sndv e")
            case True
            then show ?thesis
              using B  assms(1) assms(4) augment_edge_head_backward[OF _ _ _ _ _ refl]  \<open>v \<in> \<V>\<close>
                    caseFalse  o_edge_res[of e]  
              by (simp add: snd_E_V  isbflow_def b'_def)
            next
            case False
            hence "fstv e \<noteq> v" "sndv e \<noteq> v"
              using B  caseFalse by auto
            then show ?thesis 
              using \<open>v \<in> \<V>\<close> assms b'_def augment_edge_away_from_node[of e v f \<gamma>] isbflow_def[of f b] 
              by simp
          qed
        qed
      qed
  next 
    case False
    then show ?thesis 
    proof(cases rule: redge_pair_cases, goal_cases)
      case (1  ee)
      then show ?thesis 
        using \<open>v \<in> \<V>\<close>  assms(1) assms(4) augment_edge_away_from_node[of e v f]
              augment_loop_forward[of v ee]  o_edge_res[of e]
        by (auto simp add:  b'_def isbflow_def )    
    next
      case (2  ee)
      then show ?thesis 
        using \<open>v \<in> \<V>\<close> assms(1) assms(4) augment_edge_away_from_node[of e v f \<gamma>]
              augment_loop_backward[of v ee f \<gamma>]  o_edge_res[of e] 
        by (auto simp add: isbflow_def b'_def)
    qed
   qed
 qed
qed

text \<open>Just for convenience with $b$ unfolded.\<close>

corollary augment_edge_b_flow_pres_unwrapped:
  assumes  "f is b flow" "0 \<le> \<gamma> " "\<gamma> \<le> \<uu>\<^bsub>f\<^esub>e" "e \<in> \<EE>"  "v \<in> \<V> "
  shows "(- ex (augment_edge f \<gamma> e) v) = (\<lambda>v. if v = fstv e 
                                              then (if v = sndv e then b v - \<gamma> else b v) + \<gamma>
                                              else if v = sndv e then b v - \<gamma> else b v) v" 
  using augment_validness_b_pres_single[of f b \<gamma> e] assms
  unfolding isbflow_def by simp

text \<open>Finally, we can conclude that by augmenting below residual capacity, 
flow validity will be preserved.
\<close>

theorem augment_path_validness_b_pres:
  assumes "f is b flow" "0 \<le> \<gamma>"  "augpath f es" "\<gamma> \<le> Rcap f (set es)" "set es \<subseteq> \<EE>" "distinct es"
  defines "b' \<equiv> \<lambda> v. (if v = sndv (last es) then b v - \<gamma>
                                            else b v)"
  shows "(augment_edges f \<gamma> es) is (\<lambda> v. if v = fstv (hd es) then b' v + \<gamma> else b' v) flow"
  unfolding isbflow_def
proof
  show "isuflow (augment_edges f \<gamma> es)"
    using assms(1)unfolding isbflow_def 
    by (simp add: assms augment_path_validness_pres)
  show "(\<forall>v\<in>\<V>. - ex\<^bsub>augment_edges f \<gamma> es\<^esub> v = (if v = fstv (hd es) then b' v + \<gamma> else b' v))"
    proof
      fix v
      assume "v \<in> \<V>"
      thus "- ex\<^bsub>augment_edges f \<gamma> es\<^esub> v = (if v = fstv (hd es) then b' v + \<gamma> else b' v) "
      using assms
      unfolding b'_def
       proof(induction es arbitrary: f v)
        case Nil
         then show ?case 
          using augpath_simps by blast
       next
        case (Cons e es)
         note cons1 = "Cons"
         have "isuflow f "  
           using Cons.hyps isbflow_def by force
         then show ?case
        proof(cases es)
         case Nil
          have "isuflow f \<and> (\<forall>v\<in>\<V>. - ex\<^bsub>f\<^esub> v = b v)"  "0 \<le> \<gamma>"   "\<gamma> \<le> \<uu>\<^bsub>f\<^esub>e"   "e \<in> \<EE> "
           using isbflow_def assms Cons rcap_extr_head cons1 by auto
          hence 00:"(\<forall>v\<in>\<V>. - ex\<^bsub>augment_edge f \<gamma> e\<^esub> v =
            (if v = fstv e then (if v = sndv e then b v - \<gamma> else b v) + \<gamma>
             else if v = sndv e then b v - \<gamma> else b v))"
           using augment_validness_b_pres_single[of f b \<gamma> e] 
           unfolding isbflow_def by simp
          moreover hence "- ex\<^bsub>augment_edge f \<gamma> e\<^esub> v =
                (if v = fstv e then (if v = sndv e then b v - \<gamma> else b v) + \<gamma>
                 else if v = sndv e then b v - \<gamma> else b v)" 
           using Cons.hyps(2) by blast 
          then show ?thesis 
            by (simp add: local.Nil)
        next
         case (Cons a list)
         let ?b' = "\<lambda>v. (if v = fstv (hd es) then (if v = sndv (last es) 
                                                   then b v - \<gamma> else b v) + \<gamma>
                         else if v = sndv (last es) then b v - \<gamma> else b v)"
         have "\<gamma> \<le> Rcap f (set es)" using cons1 
           using local.Cons rcap_extr_tail by blast
         hence "isuflow (augment_edges f \<gamma> es)"
           using augment_path_validness_pres[of f \<gamma> es] Cons  \<open>isuflow f\<close> cons1 by auto
         have aa:"augpath f es" 
           using augpath_cases cons1(5) local.Cons by auto
         have "(\<forall>v\<in>\<V>. - ex\<^bsub>augment_edges f \<gamma> es\<^esub> v = ?b' v)"
           using cons1(3)  cons1(4) aa \<open>\<gamma> \<le> Rcap f (set es)\<close>  cons1(7) cons1(8) 
           by (fastforce intro!: cons1(1))
         hence IH_used: "(augment_edges f \<gamma> es) is ?b' flow"
           unfolding isbflow_def
           using Cons  \<open>isuflow (augment_edges f \<gamma> es)\<close>  by simp    
         have bb: "\<gamma> \<le> \<uu>\<^bsub>augment_edges f \<gamma> es\<^esub>e"
          using cons1(1)[of v f]  cons1(2-) e_not_in_p_aug[of e es f \<gamma>] rcap_extr_head[of \<gamma> f e es]  
                rev_e_in_p_aug[of e es f \<gamma>] cons1(4) cons1(6) ereal_less_eq(5)[of \<gamma>] 
                dual_order.trans[of "ereal \<gamma>" "\<uu>\<^bsub>f\<^esub>e"] 
                ereal_le_add_self2[of "\<uu>\<^bsub>f\<^esub>e" "ereal \<gamma>"] by force
         show ?thesis
         apply(subst augment_edges.simps, rule trans, rule augment_edge_b_flow_pres_unwrapped)
           using IH_used bb  augpath_cases cons1 local.Cons
         by (simp,simp,simp,simp, simp, cases rule: case_split[where P="v = fstv e"]) auto
      qed
    qed
  qed
qed
  
lemma bflow_cong: "b = b' \<Longrightarrow> f is b flow \<Longrightarrow> f is b' flow"
  by auto

text \<open>Our analysis also entails that source and target need to be distinct.\<close>

corollary  augment_path_validness_b_pres_source_target_distinct:
  assumes "f is b flow" "0 \<le> \<gamma>"  "augpath f es"
          "\<gamma> \<le> Rcap f (set es)" "set es \<subseteq> \<EE>" "distinct es"
          "fstv (hd es) \<noteq> sndv (last es)"
 shows    "(augment_edges f \<gamma> es) is 
                                    (\<lambda> v. if v = fstv (hd es) then b v + \<gamma>
                                          else if v = sndv (last es) then b v - \<gamma>
                                          else b v) flow"
  using assms augment_path_validness_b_pres[of f b \<gamma> es] isbflow_def by fastforce

text \<open>After augmenting a cycle, the flow will still respect demands and supplies.\<close>

corollary aug_cycle_pres_b:
  assumes "f is b flow" "0 \<le> \<gamma>"  "augpath f es"
          "\<gamma> \<le> Rcap f (set es)" "set es \<subseteq> \<EE>" "distinct es"
          "fstv (hd es) = sndv (last es)"
  shows   "(augment_edges f \<gamma> es) is b flow"
  apply(rule bflow_cong)
  defer
  apply(rule augment_path_validness_b_pres[of f b \<gamma> es])
  using assms by auto

lemma e_not_in_es_flow_not_change: 
"(\<And> e. e \<in> set es \<Longrightarrow> oedge e \<noteq> d) \<Longrightarrow> augment_edges f \<gamma> es d = f d"
  by(induction f \<gamma> es rule: augment_edges.induct) auto

text \<open>If a forward edge gets augmented, then the flow through  the original edge increases accordingly.\<close>

lemma e_rev_in_es_flow_change: 
 "F d \<in> set es \<Longrightarrow> B d \<notin> set es \<Longrightarrow>distinct es\<Longrightarrow> augment_edges f \<gamma> es d = f d + \<gamma>"
proof(induction f \<gamma> es rule: augment_edges.induct)
  case (2 f \<gamma> e es)
  then show ?case 
  proof(cases rule: redge_pair_cases, goal_cases)
    case (1  ee)
    then show ?thesis 
      by(auto intro: redge_pair_cases intro!: e_not_in_es_flow_not_change[of es "ee"  "f" \<gamma> ])        
  next
    case (2 ee)
    then show ?thesis 
      using rev_e_in_p_aug by auto
  qed
qed simp 

text \<open>When augmenting a backward edge, the flow assigned to the original edge is lowered.\<close>

lemma rev_e_in_es_flow_change: "B d \<in> set es \<Longrightarrow> F d \<notin> set es \<Longrightarrow>distinct es \<Longrightarrow>
       augment_edges f \<gamma> es  d = f  d - \<gamma>"
proof(induction f \<gamma> es rule: augment_edges.induct)
  case (2 f \<gamma> e es)  
  then show ?case 
  proof(cases "e = B d")
    case True
      have "augment_edges f \<gamma> es d = f d"
      using e_not_in_es_flow_not_change[of es d "f" \<gamma> ] 
      using "2.prems"(2) "2.prems"(3) True e_not_in_p_aug 
      by (metis distinct.simps(2) distinct_length_2_or_more ereal.inject erev.simps(2)  rcap.simps(2) )   
    then show ?thesis 
      by(auto simp add: True)
  next
    case False
    hence " augment_edges f \<gamma> (e # es) d = augment_edges f \<gamma> ( es) d"
      apply(subst augment_edges.simps)
      by (metis (no_types, lifting) "2.prems"(2) augment_edges.simps(2) e_ot_first_unfold ereal.inject erev.simps(2)
        erve_erve_id list.set_intros(1) rcap.simps(2))
     then show ?thesis 
       using "2.IH" "2.prems"(1) "2.prems"(2) "2.prems"(3) False by auto   
    qed
qed simp

text \<open>If as well a forward as the corresponding backward edge get augmented,
       then there are no changes regarding the flow through the original arc.\<close>

lemma there_and_back_flow_not_change: 
"F d \<in> set es \<Longrightarrow> B d \<in> set es \<Longrightarrow>distinct es \<Longrightarrow>  augment_edges f \<gamma> es  d = f d"
proof(induction f \<gamma> es rule: augment_edges.induct)
  case (2 f \<gamma> e es)  
  then show ?case 
  proof(cases "oedge e = d")
    case True
    then show ?thesis 
    proof(cases e)
      case (F x1)
        hence "augment_edges f \<gamma> (e # es) d =
              augment_edges f \<gamma> (es) d + \<gamma>" 
          using F True by force
        moreover have "augment_edges f \<gamma> (es) d = f d - \<gamma>" 
          using "2.prems"(2) "2.prems"(3) F True rev_e_in_es_flow_change by force
        ultimately show ?thesis by simp
    next
      case (B x2)
        hence "augment_edges f \<gamma> (e # es) d =
              augment_edges f \<gamma> (es) d - \<gamma>" 
          using B True by force
        moreover have "augment_edges f \<gamma> (es) d = f d + \<gamma>" 
          using "2.prems"(1) "2.prems"(3) B True e_rev_in_es_flow_change by force
        ultimately show ?thesis by simp
      qed
  next
    case False
    then show ?thesis 
      by (metis "2.IH" "2.prems" augment_edge_away augment_edges.simps(2) distinct.simps(2) 
                erev.simps(1) oedge.simps(2) oedge_and_reversed set_ConsD)
  qed
qed simp

lemma distinct_path_augment:
    "distinct es \<Longrightarrow> \<gamma> \<ge> 0 \<Longrightarrow> (augment_edges f \<gamma> es) e \<ge> f e - \<gamma>" for es f \<gamma> e
    apply(cases "\<exists> ee \<in> set es. oedge ee = e")
    subgoal
      apply(rule exE[where P="\<lambda> ee. ee\<in>set es \<and> oedge ee = e"], blast) 
      subgoal for ee
        apply(cases rule: oedge.elims[of ee e], simp)
          using there_and_back_flow_not_change e_rev_in_es_flow_change
                rev_e_in_es_flow_change 
          by (cases "erev ee \<in> set es", auto)+
        done
      subgoal
        using e_not_in_es_flow_not_change by simp
      done

lemma isbflow_cong: "f = f'  \<Longrightarrow> b = b' \<Longrightarrow> f is b flow \<Longrightarrow> f' is b' flow" 
  for f f' b b' by auto

lemma rcap_extr_strict: "e \<in> set es \<Longrightarrow>  \<gamma> < Rcap f (set es)  \<Longrightarrow> \<gamma> < rcap f e"
  using rcap_extr  dual_order.strict_trans1 by blast

end

context cost_flow_network
begin
subsection \<open>Affecting Costs\<close>

text \<open>How are costs changed by augmenting a single arc?\<close>

text \<open>We observe that residual costs denote the per-unit change of costs by augmenting an edge.\<close>

lemma cost_change_single:
  assumes "oedge e \<in> \<E>"
  shows "\<C> (augment_edge f \<gamma> e) = (\<C> f + \<gamma> * \<cc> e)"
  unfolding \<C>_def
proof-
  have "(\<Sum>ea\<in>\<E>. augment_edge f \<gamma> e ea * \<c> ea) = 
            (\<Sum>ea\<in>(\<E>-{oedge e}) \<union> {oedge e}. augment_edge f \<gamma> e ea * \<c> ea)"
    using assms insert_Diff by fastforce
  also have "... = (\<Sum>ea\<in>(\<E>-{oedge e}). augment_edge f \<gamma> e ea * \<c> ea)+ 
                   (\<Sum>ea\<in>{oedge e}. augment_edge f \<gamma> e ea * \<c> ea)"
     by(rule sum.union_disjoint) (auto simp add: finite_E)
   also have "... = (\<Sum>ea\<in>(\<E>-{oedge e}). augment_edge f \<gamma> e ea * \<c> ea)
                       +  augment_edge f \<gamma> e (oedge e) * \<c> (oedge e)"
     by simp
   also have "... =  (\<Sum>ea\<in>(\<E>-{oedge e}).f ea * \<c> ea)
                       +  augment_edge f \<gamma> e (oedge e) * \<c> (oedge e)" by auto
   also have "... = (\<Sum>ea\<in>(\<E>-{oedge e}).f ea * \<c> ea)
                       +  \<gamma> * \<cc> e + f (oedge e) * \<c> (oedge e)" 
     by(auto intro: redge_pair_cases simp add:  algebra_simps)
   also have "... = (\<Sum>ea\<in>(\<E>).f ea * \<c> ea)
                       +  \<gamma> * \<cc> e " 
        by (smt (verit, ccfv_SIG) assms finite_E sum.remove)
   finally show "(\<Sum>ea\<in>\<E>. augment_edge f \<gamma> e ea * \<c> ea) = (\<Sum>e\<in>\<E>. f e * \<c> e) + \<gamma> * \<cc> e" by simp
 qed

text \<open>After augmenting by $\gamma$ along $es$, 
     the change in overall costs can be determined by multiplying $\gamma$
     with the accumulated residual costs.\<close>

lemma cost_change_aug:
  assumes "set es \<subseteq> \<EE>"
          "distinct es"
    shows "\<C> (augment_edges f \<gamma> es) = (\<C> f + \<gamma> * (\<Sum> e \<in> set es. \<cc> e))"
  using assms
  unfolding \<C>_def
proof(induction f \<gamma> es rule: augment_edges.induct)
  case (2 f \<gamma> e es)
  have "(\<Sum>ea\<in>\<E>. augment_edges f \<gamma> (e # es) ea * \<c> ea) =
        (\<Sum>ea\<in>\<E>. augment_edge (augment_edges f \<gamma> es) \<gamma> e ea * \<c> ea)" 
    using augment_edges.simps(2) by presburger
  also have "(\<Sum>ea\<in>\<E>. augment_edge (augment_edges f \<gamma> es) \<gamma> e ea * \<c> ea) =
             (\<Sum>ea\<in>\<E>. augment_edges f \<gamma> es ea * \<c> ea) + \<gamma> * \<cc> e"
    using cost_change_single[of e "augment_edges f \<gamma> es" \<gamma>]
    unfolding \<C>_def 
    using "2.prems"(1) o_edge_res by fastforce
  also have "... = (\<Sum>e\<in>\<E>. f e * \<c> e) + \<gamma> * sum \<cc> (set es) + \<gamma> * \<cc> e"
    using "2.IH" "2.prems"(1) "2.prems"(2) by auto
  also have "... =  (\<Sum>e\<in>\<E>. f e * \<c> e) + \<gamma> * sum \<cc> (set (e#es))"
    by (smt (verit, del_insts) "2.prems"(2) List.finite_set distinct.simps(2) 
            list.set(2) sum.insert_if sum_distrib_left)
  finally show "(\<Sum>ea\<in>\<E>. augment_edges f \<gamma> (e # es) ea * \<c> ea) =
       (\<Sum>e\<in>\<E>. f e * \<c> e) + \<gamma> * sum \<cc> (set (e # es))" by simp
qed simp

text \<open>Regarding the zero flow, costs along a path in the original graph and residual paths are identical.\<close>

lemma augpath_to_awalk_zero_flow:
  assumes "augpath f P" 
    shows "set P \<subseteq> \<EE> \<Longrightarrow> f = (\<lambda> e. 0)   \<Longrightarrow> awalk (make_pair ` \<E>) (fstv (hd P)) (map to_vertex_pair P) (sndv (last P)) \<and> 
           foldr (\<lambda> e acc. acc + \<cc> e) P bas = 
           foldr (\<lambda> e acc. acc + \<c> e) (map oedge P) bas"
proof(induction arbitrary: bas rule: augpath_induct[OF assms])
  case (1 f e)
  have "awalk (make_pair ` \<E>) (fstv e) ([to_vertex_pair e]) (sndv e)"
    using 1 
    by(auto intro:  arc_implies_awalk simp add: make_pair  \<EE>_def )
  moreover have "\<c> (oedge e) = \<cc> e"
    using 1 unfolding \<EE>_def 
    by force
  ultimately show ?case by simp
next
  case (2 f e d es)
have awalke:"awalk (make_pair ` \<E>) (fstv e) ([to_vertex_pair e]) (sndv e)"
    using 2 
    by(auto intro:  arc_implies_awalk simp add: make_pair  \<EE>_def rev_image_eqI )
  have c_e: "\<c> (oedge e) = \<cc> e"
    using 2 unfolding \<EE>_def 
    by force
  have sndefstrest:"sndv e = fstv (hd (d # es))" using 2 by simp
  have "awalk (make_pair ` \<E>) (fstv (hd (e # d # es))) ([to_vertex_pair e] @ map to_vertex_pair (d # es)) (sndv (last (d # es)))"
      using awalke sndefstrest 2 by (intro awalk_appendI) auto
  moreover have 
                   "foldr (\<lambda>e acc. acc + \<cc> e) (e # d # es) bas =
                    foldr (\<lambda>e acc. acc + \<c> e) (map oedge (e#d # es)) bas"  
    using 2 c_e by simp
  ultimately show ?case by simp
qed
end
end