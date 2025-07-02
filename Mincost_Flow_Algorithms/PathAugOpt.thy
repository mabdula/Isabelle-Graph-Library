theory PathAugOpt 
  imports "Flow_Theory.Cost_Optimality"
begin

context cost_flow_network
begin

section \<open>Augmenting Paths and Preservation of Optimality\<close>

text \<open>This theory gives a formal proof of Theorem 9.11 in the book by Korte and Vygen.\<close>

text \<open>The standard approach for solving a maximum flow problem is to repeatedly augment along paths.

This can be adapted to computing a minimum cost flow. 
\<close>

text \<open>\begin{theorem}
Fix two vertices $s$ and $t$ and an optimum $b$-flow $f$. 
By augmenting along a path $P$ in the residual graph from $s$ to $t$ with minimum costs,
we again obtain a minimum cost flow for different balances $b'$.
\end{theorem}\<close>

text \<open>The textbook gives a proof sketch which is now paraphrased.
For aiming a contradiction, assume that the resulting flow $f'$ was not optimum for modified balances $b'$.
From the optimality condition proven in the previous section 
we immediately conclude that there has to be an augmenting cycle.
Now we take the union of the path $P$ (augmenting w.r.t. $f$) and the cycle $C$ (augmenting w.r.t. $f'$).
Edges in reverse direction are deleted: $F\, (v, u)$ and $B \, (u, v)$ annihilate each other.
Additionally, arcs appearing both in $P$ and $C$ are taken twice.
We call the resulting multigraph $H$.
One can show that $H$ is already contained in the residual graph of $f$.
Furthermore, $H$ consists of an $s$-$t$-path $P'$ and some cycles. Since $f$ was optimum, 
those cycles have to be non-negative. 
By construction, the costs of $H$ equal the costs of $P$ and $C$. 
Because $C$ is negative, the costs of $P'$ are strictly less than those of $P$.
However, this contradicts the fact that $P$ was chosen to be an augmenting $s$-$t$-path with minimum costs.

\<close>

text \<open>This informal argument is now completely translated to an Isabelle proof script.
The first issue to be dealt with is how to transfer the construction of $H$ down to a formal level.
Neither the set of edges $\mathcal{E}$ nor residual edges can mirror the construction of $H$.
There is need for distinguishing between arcs from $P$ and $C$. 
In order to do so, we introduce a data type wrapping residual edges by constructors 
indicating this distinction.
\<close>

subsection \<open>Setup of basic Notions and their Properties\<close>

subsubsection \<open>Hpaths\<close>
 
datatype 'b Hedge = is_path_edge: PP "('b Redge)" 
                   | is_cycle_edge: CC "('b Redge)" | is_additional_edge: AA "'b Redge"
print_theorems 
lemma hedge_pair_cases:
      " \<not> is_additional_edge a \<Longrightarrow> \<not> is_additional_edge b \<Longrightarrow>
       (\<And> x y. a = PP x \<Longrightarrow> b = CC y \<Longrightarrow> P a b) \<Longrightarrow>
       (\<And> x y. a = CC x \<Longrightarrow> b = PP y \<Longrightarrow> P a b) \<Longrightarrow>
       (\<And> x y. a = PP x \<Longrightarrow> b = PP y \<Longrightarrow> P a b) \<Longrightarrow>
       (\<And> x y. a = CC x \<Longrightarrow> b = CC y \<Longrightarrow> P a b) \<Longrightarrow> P a b"
  by(cases a, all \<open>cases b\<close>, auto)

text \<open>Unsurprisingly, $PP$ denotes an edge from $P$ whereas $CC$ marks those originating from $C$.\<close>

text \<open>Wrapped arcs might be reduced to the corresponding residual arcs.\<close>

fun to_redge where
"to_redge (PP e) = e"|
"to_redge (CC e) = e"|
"to_redge (AA e) = e"

fun fstvv where
"fstvv (PP e) = fstv e"|
"fstvv (CC e) = fstv e"|
"fstvv (AA e) = fstv e"

lemma fstvv_fstv: "fstvv e = fstv (to_redge e)"
  by (metis fstvv.simps(1) fstvv.simps to_redge.elims)

fun sndvv where
"sndvv (PP e) = sndv e"|
"sndvv (CC e) = sndv e"|
"sndvv (AA e) = sndv e"

lemma sndvv_sndv: "sndvv e = sndv (to_redge e)" 
  by (metis sndvv.simps(1) sndvv.simps to_redge.elims)

text \<open>Pattern for case analysis.\<close>

lemma hedge_cases:
      "(\<And> e. E = PP (F e) \<Longrightarrow> P E) \<Longrightarrow>
       (\<And> e. E = PP (B e) \<Longrightarrow> P E)  \<Longrightarrow>
       (\<And> e. E = CC (F e) \<Longrightarrow> P E) \<Longrightarrow>
       (\<And> e. E = CC (B e) \<Longrightarrow> P E) \<Longrightarrow>
       (\<And> e. E = AA (F e) \<Longrightarrow> P E) \<Longrightarrow>
       (\<And> e. E = AA (B e) \<Longrightarrow> P E) \<Longrightarrow> P E"
  apply(cases E)
  subgoal for x1
    by(cases x1) auto
  subgoal for x1
    by(cases x1) auto
  subgoal for x1
    by(cases x1) auto
  done

text \<open>We formalize the notion of paths composed by edges from $H$.\<close>

definition "hpath p \<longleftrightarrow> (p \<noteq> [] \<and> 
         awalk UNIV (fstvv (hd p)) (map ( to_vertex_pair o to_redge) p) (sndvv (last p)))"

text \<open>Introduction and elimination.\<close>

lemma hpathE: " hpath p \<Longrightarrow>
                (p \<noteq> [] \<Longrightarrow>  awalk UNIV (fstvv (hd p)) 
                        (map (to_vertex_pair o to_redge) p) (sndvv (last p)) \<Longrightarrow> P) 
                 \<Longrightarrow> P"
  unfolding hpath_def by simp

lemma hpathI: "p \<noteq> [] \<Longrightarrow>
         awalk UNIV (fstvv (hd p)) (map (to_vertex_pair o to_redge) p) (sndvv (last p)) \<Longrightarrow>
               hpath p"
  unfolding hpath_def by simp

text \<open>Technical lemmas.\<close>

lemma hpath_intros:
"hpath [e]"
"sndvv e = fstvv d \<Longrightarrow> hpath (d # es) \<Longrightarrow> hpath (e # d # es)"
    by(auto    intro: awalk_intros(1) 
            simp add: fstvv_fstv sndvv_sndv vs_to_vertex_pair_pres hpath_def)
      (auto simp add: hpath_def awalk_Cons_iff fstvv_fstv sndvv_sndv vs_to_vertex_pair_pres)
  
lemma hpath_induct:
  assumes  "hpath ES"
           "(\<And>e. P [e])"
           "(\<And>e d es. sndvv e = fstvv d \<Longrightarrow> hpath (d # es) \<Longrightarrow> P (d # es) \<Longrightarrow> P (e # d # es))"
     shows "P ES"
  apply(rule hpathE[OF assms(1)], induction ES, simp)
  subgoal for a ES
         by(cases ES, cases rule: hedge_cases[where E =a])
           (auto intro:  assms(3)
              simp add:  assms(1,2) awalk_Cons_iff fstvv_fstv sndvv_sndv vs_to_vertex_pair_pres hpathI)
 done

lemma hpath_simps: "hpath a =
((\<exists>e. a = [e]) \<or> (\<exists>e d es. a = e # d # es \<and> sndvv e = fstvv d \<and> hpath (d # es)))"
  apply rule
  subgoal
    by(rule hpath_induct) force+
  subgoal
    using hpath_intros by blast+
  done

lemma hpath_cases:
"hpath a \<Longrightarrow>
(\<And>e. a = [e] \<Longrightarrow> P) \<Longrightarrow>
(\<And>e d es. a = e # d # es \<Longrightarrow> sndvv e = fstvv d \<Longrightarrow> hpath (d # es) \<Longrightarrow> P) \<Longrightarrow> P"
  using hpath_simps by blast

lemma hpath_non_empt: "hpath xs \<Longrightarrow> xs \<noteq> []"
  using hpath_cases by blast

text \<open>There is a connection to augmenting paths.\<close>

lemma hpath_to_augpath: 
  assumes "hpath es" 
  shows "(\<And> e. e \<in> set es \<Longrightarrow> rcap f (to_redge e) > 0 )
                         \<Longrightarrow> augpath f (map to_redge es)"
  by(induction rule: hpath_induct[OF assms])
    (auto intro: augpath_intros
       simp add:  sndvv_sndv  fstvv_fstv)

lemma augpath_to_hpath:
  assumes "augpath f mapes"
  shows   "mapes = (map to_redge es) \<Longrightarrow> hpath es"
  apply(induction arbitrary: es rule: augpath_induct[OF assms])
  using hpath_intros(1) 
  by (force, smt (verit, best) fstvv_fstv hpath_simps map_eq_Cons_D sndvv_sndv)

text \<open>Furthermore, we see some topological properties.\<close>

lemma h_path_split1: 
  assumes "hpath (xs@ys)"
  shows "xs \<noteq> []  \<Longrightarrow> hpath xs"
  apply(induction "xs@ys" arbitrary:  xs ys rule: hpath_induct, simp add: assms)
   apply(force intro: list.exhaust hpath_intros) 
   by (smt (verit, ccfv_SIG) append_eq_Cons_conv hpath_simps)  

lemma h_path_split2: 
  assumes "hpath (xs@ys)"
  shows   "ys \<noteq> []  \<Longrightarrow> hpath ys"
  apply(induction "xs@ys" arbitrary:  xs ys rule: hpath_induct, simp add: assms)
   apply (simp add: Cons_eq_append_conv hpath_intros(1))
   apply (metis append_eq_Cons_conv hpath_intros(2))
  done

lemma h_path_split3:
  assumes "hpath (xs@ys)" 
  shows   "xs \<noteq> [] \<Longrightarrow> ys \<noteq> []  \<Longrightarrow> sndvv (last xs) = fstvv (hd ys)"
  apply(induction "xs@ys" arbitrary:  xs ys rule: hpath_induct, simp add: assms)
  apply (simp add: Cons_eq_append_conv hpath_intros(1))
  apply(force intro: list.exhaust hpath_intros)
 done

lemma h_path_append: 
  assumes "hpath xs"
  shows   "hpath ys \<Longrightarrow> sndvv (last xs) = fstvv (hd ys) \<Longrightarrow> hpath (xs@ys)"
  apply(induction xs rule: hpath_induct, simp add: assms)
  subgoal by(cases ys)(auto intro: hpath_intros)
  apply(simp add: hpath_intros(2))
  done

lemma hpath_to_prepath: 
  assumes "hpath xs" 
  shows   "prepath (map to_redge xs)"
  by(induction rule: hpath_induct, simp add: assms) 
    (simp add: prepath_intros fstvv_fstv sndvv_sndv)+

lemma hpath_first_node: 
  assumes "hpath xs"
  shows "fstvv (hd xs) = fstv (hd (map to_redge xs))"
  by(induction rule: hpath_induct, simp add: assms) 
    (simp add: fstvv_fstv)+

lemma hpath_last_node: 
  assumes "hpath xs"
  shows "sndvv (last xs) = sndv (last (map to_redge xs))"
  apply(induction rule: hpath_induct, simp add: assms) 
   apply (simp add: sndvv_sndv)
  subgoal for e d es
    by(cases es, simp, simp)
  done

lemma fist_edge_loop_info:"fstvv b = sndvv b \<Longrightarrow> fs \<noteq> [] \<Longrightarrow> hpath ([b]@fs) \<Longrightarrow>
       fstvv (hd ([b] @ fs)) = sndvv (last ([b] @ fs)) \<Longrightarrow> 
       fstvv (hd fs) = sndvv (last fs)"
  by(auto simp add: sym[OF  h_path_split3[of "[b]" fs]])

subsubsection \<open>Forward-Backward Pairs\<close>

text \<open>After deducing those properties for $hpath$s, we will formalize a concept central to the proof.
Recall that for constructing $H$, pairs of edges pointing in opposite directions have to be cancelled.
We call those pairs \textit{forward-backward pairs}.
(Please note that there is no immediate connection to the $F$ and $B$ constructors.) 
\<close>

definition "isFBP a b \<longleftrightarrow> (to_redge a = erev (to_redge b) \<and> 
                           (is_path_edge a \<longleftrightarrow> is_cycle_edge b) 
                            \<and> \<not> is_additional_edge a \<and> \<not> is_additional_edge b)"

text \<open>The $isFBP$ relation is symmetric.\<close>

lemma FBP_sym: "isFBP a b \<longleftrightarrow> isFBP b a"
  by (metis Hedge.distinct_disc(2) Hedge.exhaust_disc erve_erve_id isFBP_def)

text \<open>For all forward-backward pairs $a$ $b$: The source of $a$ is the target of $b$ and the other way round.\<close>

lemma FBP_fst_snd1: "isFBP a b \<Longrightarrow> fstvv a = sndvv b" 
  unfolding isFBP_def
  apply(rule hedge_pair_cases, simp, simp)
  subgoal for x y
    by(cases x, cases y, auto, cases y, auto)
  subgoal for x y
    by(cases x, cases y, auto, cases y, auto)
  by auto

lemma FBP_fst_snd2: "isFBP a b \<Longrightarrow> sndvv a = fstvv b" 
  unfolding isFBP_def
  apply(rule hedge_pair_cases, simp, simp)
  subgoal for x y
    by(cases x, cases y, auto, cases y, auto)
  subgoal for x y
    by(cases x, cases y, auto, cases y, auto)
  by auto
  
text \<open>$FBP$s do not allow for self-loops.\<close>

lemma FBP_not_eq: "isFBP a b \<Longrightarrow> a \<noteq> b"
  unfolding isFBP_def 
  apply(rule hedge_pair_cases, simp, simp)
  subgoal for x y
    by(cases x, cases y, force, cases y, auto)
  subgoal for x y
    by(cases x, cases y, force, cases y, auto)
  by auto
 
text \<open>$FBP$s are unique.\<close>

lemma FBP_unique: "isFBP a b \<Longrightarrow> isFBP a c \<Longrightarrow> b = c" 
  unfolding isFBP_def
  apply(cases a)
  subgoal
    by(cases b, simp, metis erve_erve_id is_cycle_edge_def to_redge.simps(2), simp)
  subgoal
    apply(cases b, rule exE[of "\<lambda> x1. c = PP x1"])
    using Hedge.disc(2) Hedge.exhaust_disc  is_path_edge_def[of c] to_redge.simps(1) erve_erve_id[of "to_redge b"] erve_erve_id[of "to_redge c"]
    by (blast, auto)
  by simp

text \<open>Then we define the set of $FBP$s that are completely contained in a set of Hedges.\<close>

definition "FBPs E = {{a,b}| a b. {a,b} \<subseteq> E \<and> isFBP a b }"

lemma FBP_in_E:"ab \<in> FBPs E \<Longrightarrow> ab \<subseteq> E"
  unfolding FBPs_def by auto

lemma FBP_mono: "C \<subseteq> A \<Longrightarrow> FBPs C \<subseteq> FBPs A"
  unfolding FBPs_def by auto

text \<open>A forward-backward pair might be extracted and added separately.\<close>

lemma FBP_extract:
  assumes "isFBP a b" "a \<in> E" "b \<in> E" 
  shows "FBPs E = FBPs (E - {a,b}) \<union> {{a,b}}"
proof
  show "FBPs E \<subseteq> FBPs (E - {a, b}) \<union> {{a, b}}"
  proof
    fix xy
    assume "xy \<in> FBPs E"
    then obtain x y where xy_prop:"xy = {x,y} \<and> isFBP x y" unfolding FBPs_def by force
    then show "xy \<in> FBPs (E - {a, b}) \<union> {{a, b}}"
    proof(cases "xy = {a,b}")
      case False
      have "xy \<subseteq> E - {a, b}" 
      proof
        fix d
        assume "d \<in> xy"
        show "d \<in> E - {a, b}"
        proof
          show "d \<in> E" 
            using FBP_in_E \<open>d \<in> xy\<close> \<open>xy \<in> FBPs E\<close> by blast 
          show "d \<notin> {a, b}"
            by (metis FBP_sym FBP_unique False \<open>d \<in> xy\<close> \<open>xy = {x, y} \<and> isFBP x y\<close> assms(1) doubleton_eq_iff insertE singleton_iff)
        qed
      qed
      then show ?thesis unfolding FBPs_def xy_prop 
        using xy_prop by blast
    qed simp
  qed
  show "FBPs (E - {a, b}) \<union> {{a, b}} \<subseteq> FBPs E"
    using  FBP_mono
    unfolding FBPs_def using assms by auto
qed

text \<open>Similarly to residual edges, we define a lifted version of costs.
Costs of an Hedge are equal to those of the wrapped residual arc.\<close>

fun cc where 
"cc (PP e) = \<cc> e"|
"cc (CC e) = \<cc> e"|
"cc (AA e) = \<cc> e"

text \<open>For any $FBP$ costs cancel.\<close>

lemma FBP_cost: "isFBP a b \<Longrightarrow> cc a + cc b = 0"
  unfolding isFBP_def
  apply(rule hedge_pair_cases, simp, simp)
  subgoal for a b
    by(cases a, cases b, auto, cases b, auto)
  subgoal for a b
    by(cases a, cases b, auto, cases b, auto)
  by auto


lemma FBP_finite: "finite E \<Longrightarrow> finite (FBPs E)"
  apply(rule rev_finite_subset[of "Pow E"],simp)
  unfolding FBPs_def by auto

text \<open>We can show that after extracting a single $FBP$ accumulated costs do not change.\<close>

lemma FBP_extract_cost_single:
  assumes "isFBP a b" "a \<in> E" "b \<in> E" "finite E"
  shows "(\<Sum> e \<in> E. cc e) = (\<Sum> e \<in> (E - {a,b}). cc e)"
proof-
  have "(\<Sum> e \<in> E. cc e) = 
        (\<Sum> e \<in> (E - {a,b}) \<union> {a,b}.cc e)"
    by (metis Un_Diff_cancel2 Un_insert_right assms(2) assms(3) insert_Diff insert_Diff_single
        set_extract_singleton)
  also have "... =(\<Sum> e \<in> (E - {a,b}).cc e) + 
                  (\<Sum> e \<in> {a,b}.cc e)" 
    apply(rule sum.union_disjoint)
    using assms(4) by auto
  also have "... = (\<Sum> e \<in> (E - {a,b}).cc e) + cc a + cc b" 
    by (smt (verit, del_insts) FBP_cost assms(1) finite.emptyI finite_insert insert_absorb 
        singletonD sum.insert sum_singleton)
  also have "... =  (\<Sum> e \<in> (E - {a,b}).cc e)" 
    by (simp add: FBP_cost assms(1))
  finally show ?thesis by simp
qed

lemma FBP_set_substr_cancel: 
  assumes "a \<in> E"
          "b \<in> E"
          "isFBP a b"
   shows  "E - {a, b} - \<Union> (FBPs (E - {a, b})) = E - \<Union> (FBPs E)"
proof
  show "E - {a, b} - \<Union> (FBPs (E - {a, b})) \<subseteq> E - \<Union> (FBPs E)"
  proof
    fix x
    assume "x \<in> E - {a, b} - \<Union> (FBPs (E - {a, b})) "
    show "x \<in> E - \<Union> (FBPs E)"
    proof
      show "x \<in> E" 
        using \<open>x \<in> E - {a, b} - \<Union> (FBPs (E - {a, b}))\<close> by blast
      show "x \<notin> \<Union> (FBPs E)"
      proof
        assume assm:"x \<in> \<Union> (FBPs E)"
        then show False
        proof(cases "x = a")
          case True
          then show ?thesis
            using \<open>x \<in> E - {a, b} - \<Union> (FBPs (E - {a, b}))\<close> by blast
        next
          case False
          hence "x \<noteq> b"
            using \<open>x \<in> E - {a, b} - \<Union> (FBPs (E - {a, b}))\<close> by fastforce
          hence "x \<in> \<Union> (FBPs (E - {a, b}))" 
            using FBP_extract[of a b E] assm 
            using \<open>x \<in> E - {a, b} - \<Union> (FBPs (E - {a, b}))\<close> assms(1) assms(2) assms(3) by blast
          then show ?thesis 
            using \<open>x \<in> E - {a, b} - \<Union> (FBPs (E - {a, b}))\<close> by blast
        qed
      qed
    qed
  qed
  show "E - \<Union> (FBPs E) \<subseteq> E - {a, b} - \<Union> (FBPs (E - {a, b}))"
  proof
    fix x
    assume assm: "x \<in> E - \<Union> (FBPs E)"
    show " x \<in> E - {a, b} - \<Union> (FBPs (E - {a, b}))"
    proof
      have "x \<noteq> a \<and> x \<noteq> b" 
      using FBP_extract assms(1) assms(2) assms(3) assm by fastforce
    then show " x \<in> E - {a, b}"
      using assm by force
    show "x \<notin> \<Union> (FBPs (E - {a, b}))"
    proof
      assume "x \<in> \<Union> (FBPs (E - {a, b}))"
      hence "x \<in> \<Union> (FBPs E)" 
        using FBP_extract assms(1) assms(2) assms(3) by blast
      thus False 
        using assm by blast
    qed
  qed
qed
qed

text \<open>By extracting all $FBP$s, the overall costs do not change.
This means that the graph $H$ will have the same total costs as $P$ and $C$ together.
\<close>

lemma FBPs_extract_cost:
  assumes "finite E"
  shows "(\<Sum> e \<in> E. cc e) = (\<Sum> e \<in> (E - \<Union> (FBPs E)). cc e)"
  using assms 
  proof(induction "card (FBPs E)" arbitrary: E rule: less_induct)
  case less
  then show ?case 
  proof(cases "(FBPs E) = {}")
    case False
    then obtain a b where "{a,b} \<in> FBPs E" unfolding FBPs_def by auto
    hence "a \<in>E \<and> b \<in>E \<and> isFBP a b" unfolding FBPs_def 
      by (smt (verit, best) FBP_sym doubleton_eq_iff insert_subset mem_Collect_eq)
    hence 11: "(\<Sum> e \<in> E. cc e)  = (\<Sum> e \<in> E -{a,b}. cc e)" 
      using FBP_extract_cost_single less.prems by presburger
    have "FBPs (E - {a,b}) \<subset> FBPs E" 
      apply(rule psubsetI)
      using FBP_mono apply blast
      using \<open>a \<in> E \<and> b \<in> E \<and> isFBP a b\<close> unfolding FBPs_def by blast
    have"card (FBPs (E - {a,b})) < (card (FBPs E))"
      apply(rule psubset_card_mono)
      apply (simp add: FBP_finite less.prems)
      by (simp add: \<open>FBPs (E - {a, b}) \<subset> FBPs E\<close>)
    hence 22: " (\<Sum> e \<in> E -{a,b}. cc e) =  
               (\<Sum> e \<in> (E -{a,b}) - \<Union>(FBPs  (E -{a,b})). cc e)" 
      using less.hyps less.prems by blast
    also have "(\<Sum> e \<in> (E -{a,b}) - \<Union>(FBPs  (E -{a,b})). cc e) = 
               (\<Sum> e \<in> (E ) - \<Union>(FBPs E). cc e)" 
      by(rule sum.cong) (simp add: FBP_set_substr_cancel \<open>a \<in> E \<and> b \<in> E \<and> isFBP a b\<close>)+
    ultimately show ?thesis using 11 by simp
  qed simp
qed

text \<open>A set of Hedges is called \textit{clean} iff is does not contain a forward-backward pair.\<close>

definition "clean es = (\<nexists> a b. isFBP a b \<and> {a,b} \<subseteq> set es)"

text \<open>For a set of disjoint $hpath$s:
A single $FBP$ might be deleted before applying the global $FBPs$ function or afterwards.
\<close>

lemma FBP_exchange:
  assumes  "\<And> C D. C \<in> CCC \<Longrightarrow> D \<in> CCC \<Longrightarrow>D \<noteq> C \<Longrightarrow> D \<inter> C = {}"
          "isFBP a b"
          " D =  C - {a,b}"
          "C =  D \<union> {a,b}"
          "C \<in> CCC"
  shows   "FBPs (\<Union> ({ C' |C'. C' \<in> (CCC - {C}) \<union> {D}})) = FBPs (\<Union> CCC) - {{a,b}}" 
proof
  show "FBPs (\<Union> {C' |C'. C' \<in> CCC - {C} \<union> {D}}) \<subseteq> FBPs (\<Union> CCC) - {{a, b}}"
  proof
    fix xy 
    assume  assm: "xy \<in> FBPs (\<Union> {C' |C'. C' \<in> CCC - {C} \<union> {D}})"
    then obtain x y where "xy = {x,y} \<and> isFBP x y" unfolding FBPs_def by auto
    then obtain C' D' where 11: "C' \<in> CCC - {C} \<union> {D}" "D' \<in> CCC - {C} \<union> {D}"
                            "x \<in> C'" "y \<in> D'"using assm 
      unfolding FBPs_def
      by (smt (verit, best) Union_iff insertCI mem_Collect_eq subsetD)
    have "{x,y} \<noteq> {a,b}" 
    proof
    assume "{x, y} = {a, b} "
    hence "C' \<noteq> D \<and> D' \<noteq> D" using assms 
      by (metis DiffD2 11 insert_iff)
    hence "C \<inter> C' \<noteq> {}" 
      by (metis IntD2 Un_Int_eq(4) 11 \<open>{x, y} = {a, b}\<close> assms(4) disjoint_iff_not_equal insertCI)
    then show False using assms(1)[of C C'] 
      using 11\<open>C' \<noteq> D \<and> D' \<noteq> D\<close> assms(5) by blast
  qed
  have "xy \<in> FBPs (\<Union> CCC)" unfolding FBPs_def 
    using 11 \<open>xy = {x, y} \<and> isFBP x y\<close> assms(4) assms(5) by blast
  then show "xy \<in> FBPs (\<Union> CCC) - {{a, b}}" 
    using \<open>xy = {x, y} \<and> isFBP x y\<close> \<open>{x, y} \<noteq> {a, b}\<close> by force
qed
  show "FBPs (\<Union> CCC) - {{a, b}} \<subseteq> FBPs (\<Union> {C' |C'. C' \<in> CCC - {C} \<union> {D}})"
  proof
    fix xy
    assume ass:"xy \<in> FBPs (\<Union> CCC) - {{a, b}}"
    then obtain x y where xy_def:"xy = {x,y} \<and> isFBP x y" unfolding FBPs_def by auto
    have xy_prop:"xy \<subseteq>(\<Union> CCC) \<and> xy \<noteq>{a,b}"
      using ass  by (simp add: FBP_in_E ass)
    have "x \<in> \<Union> {C' |C'. C' \<in> CCC - {C} \<union> {D}}"
    proof(cases "x \<in> C")
      case True
      hence "x \<in> D" 
        by (metis FBP_sym FBP_unique UnE \<open>xy = {x, y} \<and> isFBP x y\<close> \<open>xy \<subseteq> \<Union> CCC \<and> xy \<noteq> {a, b}\<close> 
            assms(2) assms(4) doubleton_eq_iff insertE singleton_iff)
      then show ?thesis 
        by blast
    next
      case False
      then obtain C' where "C' \<noteq> C \<and> C' \<in> CCC \<and> x \<in> C'" 
        using xy_def xy_prop 
        by blast
      then show ?thesis 
        by blast
    qed
      have "y \<in> \<Union> {C' |C'. C' \<in> CCC - {C} \<union> {D}}"
    proof(cases "y \<in> C")
      case True
      hence "y \<in> D" 
        by (metis FBP_sym FBP_unique UnE \<open>xy = {x, y} \<and> isFBP x y\<close> \<open>xy \<subseteq> \<Union> CCC \<and> xy \<noteq> {a, b}\<close> 
            assms(2) assms(4) doubleton_eq_iff insertE singleton_iff)
      then show ?thesis 
        by blast
    next
      case False
      then obtain C' where "C' \<noteq> C \<and> C' \<in> CCC \<and> y \<in> C'" 
        using xy_def xy_prop 
        by blast
      then show ?thesis 
        by blast
    qed
    then show  "xy \<in> FBPs (\<Union> {C' |C'. C' \<in> CCC - {C} \<union> {D}})" 
      unfolding FBPs_def
      using \<open>x \<in> \<Union> {C' |C'. C' \<in> CCC - {C} \<union> {D}}\<close> xy_def by auto
  qed
qed

lemma FBP_substr_union_distr: 
  assumes "isFBP a b" "{a,b} \<subseteq> A" 
  shows "FBPs (A - {a,b}) = FBPs A  - {{a,b}}"
proof
  show "FBPs (A - {a, b}) \<subseteq> FBPs A - {{a, b}}"
    unfolding FBPs_def by auto
  show "FBPs A - {{a, b}} \<subseteq> FBPs (A - {a, b})"
  proof
    fix fbp
    assume "fbp \<in> FBPs A - {{a, b}}"
    then obtain x y where "fbp = {x,y}" "x \<in> A" "y \<in> A" "{x,y} \<noteq> {a,b}" "isFBP x y"
      unfolding FBPs_def by auto
    moreover hence "x \<noteq> a" "y \<noteq> a" "x \<noteq> b" "y \<noteq> b" 
      using FBP_sym FBP_unique \<open>isFBP x y\<close> \<open>{x, y} \<noteq> {a, b}\<close> assms(1) 
      by blast+
    ultimately show "fbp \<in> FBPs (A - {a, b})"
      unfolding FBPs_def by auto
  qed
qed

text \<open>Furthermore, we can look at the forward-backward pairs between two sets,
i.e. those where each set provides an edge.
This definition requires all arcs to be in \textit{exactly} one set.
\<close>

definition "FBPs_inter A C = {{a, b} | a b. a \<in> A \<and> a \<notin> C \<and>
                                            b \<in> C \<and> b \<notin> A \<and>
                                                   isFBP a b}"

lemma FBPs_inter_commute: "FBPs_inter A C = FBPs_inter C A" 
  unfolding FBPs_inter_def
  by rule (smt (verit, ccfv_threshold) Collect_mono FBP_sym insert_commute)+

text \<open>There holds a property of distributivity.\<close>

lemma FBPs_union_distr_inter:
"FBPs (A \<union> C) = FBPs A \<union> FBPs C \<union> FBPs_inter A C"
proof
  show "FBPs (A \<union> C) \<subseteq> FBPs A \<union> FBPs C \<union> FBPs_inter A C"
  proof
    fix xy
    assume "xy \<in> FBPs (A \<union> C)"
    then obtain x y where xy_def: "xy = {x,y} " "x \<in> A \<union> C" "y \<in> A \<union> C" "isFBP x y" 
      unfolding FBPs_def by auto
    show "xy \<in> FBPs A \<union> FBPs C \<union> FBPs_inter A C"
         unfolding FBPs_inter_def 
         using FBP_extract xy_def FBP_sym by blast+
    qed
    show "FBPs A \<union> FBPs C \<union> FBPs_inter A C \<subseteq> FBPs (A \<union> C)"
    proof
      fix xy
      assume " xy \<in> FBPs A \<union> FBPs C \<union> FBPs_inter A C"
      hence "xy \<in> FBPs A \<or> xy \<in>  FBPs C \<or> xy \<in> FBPs_inter A C" by auto
      
      thus "xy \<in> FBPs (A \<union> C)"
      proof(cases "xy \<in> FBPs A ")
        case False
        hence "xy \<in>  FBPs C \<or> xy \<in> FBPs_inter A C" 
          using \<open>xy \<in> FBPs A \<or> xy \<in> FBPs C \<or> xy \<in> FBPs_inter A C\<close> by auto
        then show ?thesis 
        proof(cases "xy \<in>  FBPs C ")
          case False
          hence " xy \<in> FBPs_inter A C" 
            using \<open>xy \<in> FBPs C \<or> xy \<in> FBPs_inter A C\<close> by blast
          then obtain x y where "xy = {x,y} \<and> isFBP x y \<and> x \<in> A \<and> y \<in> C"
            unfolding FBPs_inter_def by auto
          then show ?thesis unfolding FBPs_def by auto
        qed (meson FBP_mono subsetD sup_ge2)
      qed  (meson FBP_mono subsetD sup.cobounded1)
    qed
  qed

lemma FBPs_inter_finite: "finite A \<Longrightarrow> finite C \<Longrightarrow> finite (FBPs_inter A C)"
  by (metis FBP_finite FBPs_union_distr_inter finite_Un)

text \<open>A more relaxed version of $FBP$s between two sets of Hedges.\<close>

definition "FBPs_inter2 A C = {{a, b} | a b. a \<in> A \<and> b \<in> C \<and>
                                                   isFBP a b}"

text \<open>Again, some properties.\<close>

lemma FBPs_inter2_commute: "FBPs_inter2 A C = FBPs_inter2 C A" 
  unfolding FBPs_inter2_def
  by rule (smt (verit, ccfv_threshold) Collect_mono FBP_sym insert_commute)+

lemma FBPs_union_distr_inter2:
"FBPs (A \<union> C) = FBPs A \<union> FBPs C \<union> FBPs_inter2 A C"
proof
  show "FBPs (A \<union> C) \<subseteq> FBPs A \<union> FBPs C \<union> FBPs_inter2 A C"
  proof
    fix xy
    assume "xy \<in> FBPs (A \<union> C)"
    then obtain x y where xy_def: "xy = {x,y} " "x \<in> A \<union> C" "y \<in> A \<union> C" "isFBP x y" 
      unfolding FBPs_def by auto
    show "xy \<in> FBPs A \<union> FBPs C \<union> FBPs_inter2 A C"
      unfolding FBPs_inter2_def
      using xy_def FBP_extract FBP_sym by fast
    qed
    show "FBPs A \<union> FBPs C \<union> FBPs_inter2 A C \<subseteq> FBPs (A \<union> C)"
    proof
      fix xy
      assume " xy \<in> FBPs A \<union> FBPs C \<union> FBPs_inter2 A C"
      hence "xy \<in> FBPs A \<or> xy \<in>  FBPs C \<or> xy \<in> FBPs_inter2 A C" by auto
      
      thus "xy \<in> FBPs (A \<union> C)"
      proof(cases "xy \<in> FBPs A ")
        case False
        hence "xy \<in>  FBPs C \<or> xy \<in> FBPs_inter2 A C" 
          using \<open>xy \<in> FBPs A \<or> xy \<in> FBPs C \<or> xy \<in> FBPs_inter2 A C\<close> by auto
        then show ?thesis 
        proof(cases "xy \<in>  FBPs C ")
          case False
          hence " xy \<in> FBPs_inter2 A C" 
            using \<open>xy \<in> FBPs C \<or> xy \<in> FBPs_inter2 A C\<close> by blast
          then obtain x y where "xy = {x,y} \<and> isFBP x y \<and> x \<in> A \<and> y \<in> C"
            unfolding FBPs_inter2_def by auto
          then show ?thesis unfolding FBPs_def by auto
        qed (meson FBP_mono subsetD sup_ge2)
      qed  (meson FBP_mono subsetD sup.cobounded1)
    qed
  qed

lemma FBPs_inter2_finite: "finite A \<Longrightarrow> finite C \<Longrightarrow> finite (FBPs_inter2 A C)"
  by (metis FBP_finite FBPs_union_distr_inter2 finite_Un)

text \<open>For clean sets with no $FBP$s in between, their union is also clean.\<close>

lemma clean_append: assumes "clean xs" "clean ys" "FBPs_inter (set xs) (set ys) = {}"
  shows  "clean (xs@ys)"
proof(rule ccontr)
  assume "\<not> clean (xs@ys)"
  then obtain a b where ab_Def: "a \<in> set (xs@ys) \<and> b \<in> (set (xs@ys)) \<and> isFBP a b" 
    unfolding clean_def by auto
  then show False
    using assms clean_def[ of ys] 
    by(fastforce simp add: clean_def FBPs_inter_def FBP_sym)+
qed

lemma FBPs_inter_Subset_FBPs_inter2: "FBPs_inter A C \<subseteq> FBPs_inter2 A C"
  unfolding FBPs_inter_def FBPs_inter2_def by auto

lemma clean_subset:"set A \<subseteq> set C \<Longrightarrow> clean C \<Longrightarrow> clean A"
  unfolding clean_def by auto

lemma FBPs_inter_subset: " A \<subseteq> C \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> C \<inter> Y = {} \<Longrightarrow>FBPs_inter A X \<subseteq> FBPs_inter C Y"
  unfolding FBPs_inter_def by blast 

lemma FBP_insert:"isFBP a b \<Longrightarrow> FBPs A \<union> {{a,b}} = FBPs (A \<union> {a,b})"
proof
  show "isFBP a b \<Longrightarrow> FBPs A \<union> {{a, b}} \<subseteq> FBPs (A \<union> {a, b})"
    unfolding FBPs_def by auto
  show "isFBP a b \<Longrightarrow> FBPs (A \<union> {a, b}) \<subseteq> FBPs A \<union> {{a, b}}" unfolding FBPs_def
  proof
   assume asm: "isFBP a b"
   fix xy
   assume xy_assm: "isFBP a b" "xy  \<in> {{aa, ba} |aa ba. {aa, ba} \<subseteq> A \<union> {a, b} \<and> isFBP aa ba} "
   then obtain  x y where "x \<in> A \<union> {a, b} \<and> y \<in> A \<union> {a, b} \<and> isFBP x y  \<and> xy = {x,y}" by auto
   thus " xy \<in> {{a, b} |a b. {a, b} \<subseteq> A \<and> isFBP a b} \<union> {{a, b}} "
     apply(cases "x = a") 
     using FBP_unique xy_assm(1) apply blast
     apply(cases "x = b")
     using FBP_sym FBP_unique xy_assm(1) apply blast
     by (rule UnI1)(auto simp add: FBP_sym FBP_unique xy_assm)
 qed
qed

lemma FBPs_intro: "isFBP x y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> {x,y} \<in> FBPs A" for x y A
  unfolding FBPs_def by blast

lemma FBPs_inter2_mono: "A \<subseteq> B \<Longrightarrow> C \<subseteq> D\<Longrightarrow> FBPs_inter2 A C \<subseteq> FBPs_inter2 B D"  for A B C D
      unfolding FBPs_inter2_def by auto

subsubsection \<open>Hcycles\<close>

text \<open>An \textit{hcycle} is a closed and distinct $hpath$.\<close>

definition "hcycle cs \<longleftrightarrow> (hpath cs \<and> fstvv (hd cs) = sndvv (last cs) \<and> distinct cs)"

lemma hcycle_non_empt: "hcycle xs \<Longrightarrow> xs \<noteq> []" 
  using hcycle_def hpath_non_empt by blast

lemma hcycleI:
  "\<lbrakk>hpath cs; fstvv (hd cs) = sndvv (last cs); distinct cs\<rbrakk> \<Longrightarrow> hcycle cs"
  by (auto simp: hcycle_def)

lemma hcycleE:
  "hcycle cs \<Longrightarrow> (\<lbrakk>hpath cs; fstvv (hd cs) = sndvv (last cs); distinct cs\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: hcycle_def)

subsection \<open>Generating $H$ by deleting Forward-Backward Pairs.\<close>

subsubsection \<open>Deleting $FBP$s from Cycles\<close>

text \<open>Now we will show an auxiliary claim for the major proof.
Whenever there is a set of hcycles, then deleting all forward-backward pairs again results in hcycles.

The proof is conducted by induction with the number of $FBP$s.
Then we examine two cases.
If both components of the $FBP$ belong two the same cycle, then this cycle is split into two cycles.
On the contrary, dropping an $FBP$ with edges from distinct circuits results in single new cycles.
\<close>

lemma cycle_decompose:
  assumes "finite CCC"
          "\<And> C. C \<in> CCC \<Longrightarrow> hcycle C"
          "\<And> C D. C \<in> CCC \<Longrightarrow> D \<in> CCC \<Longrightarrow>D \<noteq> C \<Longrightarrow>set D \<inter> set C = {}"
          "n = card(FBPs (\<Union> {set C| C. C \<in> CCC }))"
  shows "\<exists> CCC'. (finite CCC' \<and>
                     (\<forall>  C \<in> CCC'. hcycle C) \<and>  
                     (\<forall> C D. C \<in> CCC' \<longrightarrow> D \<in> CCC'\<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {})\<and>
                     \<Union> {set C| C. C \<in> CCC' }  = 
                      (\<Union> {set C| C. C \<in> CCC }) - \<Union> (FBPs (\<Union> {set C| C. C \<in> CCC })))"
  using assms
proof(induction n arbitrary: CCC )
  case 0
  have "finite  (FBPs (\<Union> {set C| C. C \<in> CCC }))" 
    using 0 by(force intro: FBP_finite)
  hence " (FBPs (\<Union> {set C| C. C \<in> CCC })) = {}"
    using "0.prems"(4) by auto
  then show ?case
    using "0.prems"(1) "0.prems"(2) "0.prems"(3) "0.prems"(4) 
    by blast
next
  case (Suc n)
  have finite_FBPs_of_CCC:"finite  (FBPs (\<Union> {set C| C. C \<in> CCC }))" 
    using Suc by(fastforce intro: FBP_finite)
  then obtain a b where ab_prop:"{a,b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})" 
    by (smt (verit, ccfv_threshold) Suc FBPs_def card_Suc_eq_finite insertCI mem_Collect_eq)
  hence ab_def: "a \<in> \<Union> {set C |C. C \<in> CCC}" "b \<in> \<Union> {set C |C. C \<in> CCC}" "isFBP a b" 
     unfolding FBPs_def
     using FBP_sym[of a b] doubleton_eq_iff[of a b]  by auto
  then obtain C D where CD_Def: "a \<in> set C""b \<in> set D""C \<in> CCC""D \<in> CCC" by blast
  hence "\<nexists> F. F \<in> CCC \<and> ((F \<noteq> C \<and> a \<in> set F) \<or> (F \<noteq> D \<and> b \<in> set F))" 
    using Suc.prems(3) by auto
  hence ab_extract: "\<Union> {set C |C. C \<in> CCC} - \<Union>(FBPs (\<Union> {set C |C. C \<in> CCC})) = 
        (\<Union> ({set C |C. C \<in> CCC}) -{a,b}) - \<Union>(FBPs ((\<Union> {set C |C. C \<in> CCC}) - {a,b}))" 
    by (metis (no_types, lifting) FBP_set_substr_cancel ab_def) 
  have distinctC:"distinct C" 
          using CD_Def Suc.prems(2) hcycle_def by blast
  then show ?case
  proof(cases "C = D")
    case True
    hence 00:"a \<in> set C \<and> b \<in> set C \<and> a \<noteq>b" 
      using  CD_Def ab_def by (simp add: FBP_not_eq)
    then obtain es fs where esfs_Def: "C = es@[a]@fs" 
      by (metis Cons_eq_appendI append_self_conv2 split_list)
    then obtain gs hs where "fs = gs@[b]@hs \<or> es= gs@[b]@hs"  
      apply(cases "b \<in> set es")
      subgoal using in_set_conv_decomp[of b es] by auto
      using in_set_conv_decomp[of b fs] 00  esfs_Def 
      by (cases "b \<in> set fs") auto
    hence "C =  gs@[b]@hs@[a]@fs \<or> C = es@[a]@gs@[b]@hs"
      using esfs_Def by force
    then obtain a' b' cs1 cs2 cs3 where a'b'_def: "C = cs1@[a']@cs2@[b']@cs3" "{a',b'} = {a,b}"
      by blast
    hence "isFBP a' b'"
      using FBP_sym[of a b] ab_def doubleton_eq_iff[of a' b' a b] by auto
     then show ?thesis
    proof(cases cs2)
      case Nil
      hence "cs2 = []" by simp
      hence hpathCC: "hpath (cs1@[a',b']@cs3) \<and> distinct (cs1@[a',b']@cs3)
           \<and> fstvv (hd (cs1@[a',b']@cs3)) = sndvv (last (cs1@[a',b']@cs3))" 
        using Suc.prems(2)[of C, OF CD_Def(3) ] a'b'_def  hcycle_def by auto
        then show ?thesis
      proof(cases "cs1@cs3")
        case Nil
        hence "C = [a',b']"
          by (simp add: \<open>C = cs1 @ [a'] @ cs2 @ [b'] @ cs3\<close>  \<open>{a', b'} = {a, b}\<close> \<open>cs2 = []\<close>)
        have 11:"\<Union> ({set C |C. C \<in> CCC}) -{a',b'} = \<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {[]}})"
          apply(rule subset_big_union_diff[of "[]" C "{a',b'}" CCC])
          using CD_Def \<open>C = [a', b']\<close>
                Suc.prems hcycle_def hpath_simps[of "[]"]  "00" by auto

        have 12:"FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {[]}})) =
                   FBPs (\<Union> ({set C' |C'. C' \<in> CCC })) - {{a',b'}}" 
        proof
          show "FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {[]}}) 
                \<subseteq> FBPs (\<Union> {set C' |C'. C' \<in> CCC}) - {{a', b'}}"
            apply(subst sym[OF 11])
            apply(subst FBP_substr_union_distr[of a b "(\<Union> {set C' |C'. C' \<in> CCC}) ", 
                                                      simplified sym[OF a'b'_def(2)]])
            using \<open>isFBP a' b'\<close> a'b'_def(2) ab_prop set_eq_subset FBP_sym  ab_def 
                      FBP_in_E a'b'_def(2) ab_prop by force+
          show "FBPs (\<Union> {set C' |C'. C' \<in> CCC}) - {{a', b'}} 
                \<subseteq> FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {[]}})"
                using  ab_def  FBP_extract[of a b] 
                by (subst sym[OF  "11"], subst  a'b'_def(2), subst  a'b'_def(2),
                    simp add: ab_def  FBP_extract[of a b])
            qed

        have emptyBigU:"\<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {[]}})=
              \<Union> ({set C' |C'. C' \<in> (CCC - {C})})" by auto  

        hence "card (FBPs (\<Union> ({set C' |C'. C' \<in> CCC - {C}}))) =
                   card (FBPs (\<Union> ({set C |C. C \<in> CCC }))) -1"  using 12 
          by (simp add: \<open>{a, b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})\<close> a'b'_def)

        hence "card (FBPs (\<Union> ({set C' |C'. C' \<in> CCC - {C}}))) = n"
          using Suc by presburger

        have "finite (CCC-{C})"
          "\<And> C'. C' \<in> CCC-{C} \<Longrightarrow> hcycle C'"
          "\<And> C' D'. C \<in> CCC-{C} \<Longrightarrow> D' \<in> CCC-{C} \<Longrightarrow>D' \<noteq> C' \<Longrightarrow>set D' \<inter> set C' = {}"
          by(simp add: Suc)+

        have CC'_ex: " \<exists>CCC'.
                finite CCC' \<and>
                 (\<forall> C\<in> CCC'. hcycle C) \<and>
                (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
                \<Union> {set C |C. C \<in> CCC'} =
                \<Union> {set C' |C'. C' \<in> CCC - {C}} - \<Union> (FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C}}))"
          apply(rule Suc(1)[of "CCC - {C}"])
          using  \<open>finite (CCC - {C})\<close> \<open>\<And>C'. C' \<in> CCC - {C} \<Longrightarrow> hcycle C'\<close>
                 Suc.prems(3) \<open>card (FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C}})) = n\<close> by auto 

        have " \<Union> {set C' |C'. C' \<in> CCC} - \<Union> (FBPs (\<Union> {set C' |C'. C' \<in> CCC})) = 
               \<Union> {set C' |C'. C' \<in> CCC - {C}} - \<Union> (FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C}}))"
          using "11" ab_extract emptyBigU  a'b'_def by force
       
        then show ?thesis
          using CC'_ex by presburger
      next
        case (Cons aaaa list)

        have 001: "cs1 \<noteq> [] \<Longrightarrow> cs3 \<noteq> [] \<Longrightarrow> sndvv (last cs1) = fstvv (hd cs3)"
                  apply(rule trans, rule h_path_split3[of _ "[a',b']@cs3"])
                  using h_path_split3[of "[a',b']" cs3] h_path_split2[of cs1] hpathCC \<open>isFBP a' b'\<close>
                  by(auto simp add: FBP_fst_snd1[of _ b'])

        have 002: "cs1 = [] \<Longrightarrow> hpath (cs1 @ cs3)"
                  using hpathCC Cons by(auto intro: h_path_split2[of "[a',b']"])

        have 003: "cs1 \<noteq> []  \<Longrightarrow> cs3 = [] \<Longrightarrow> hpath (cs1 @ cs3)"
                  using hpathCC Cons by(auto intro: h_path_split1[of _ "[a', b'] @ cs3"])
  
        have hpathcs1cs2: "hpath (cs1 @cs3)" 
          using 002 apply(cases cs1, simp)
          using 003 apply(cases cs3, simp)
          using hpathCC Cons h_path_split2[of "cs1@[a',b']" "cs3"]  001
            by(intro h_path_append[of cs1 cs3] | auto intro: h_path_split1[of _ "[a', b'] @ cs3"])+
 
        have 004 :"cs3 \<noteq> [] \<Longrightarrow> fstvv (hd (cs1 @ cs3)) = sndvv (last (cs1 @ cs3))"
          using h_path_split3[of "cs1 @ [a', b']" "(cs1 @ cs3)"] hpathCC FBP_fst_snd1[of a' b'] 
          \<open>isFBP a' b'\<close> by (cases cs1)  auto

        have 005: " cs3 = [] \<Longrightarrow> fstvv (hd (cs1 @ cs3)) = sndvv (last (cs1 @ cs3))"
          using  FBP_fst_snd1[of "hd [a', b']"]  \<open>isFBP a' b'\<close>  h_path_split3[of cs1 "[a', b']"]
                 hpathCC Cons by auto

      have "hcycle (cs1@cs3)"
          using hpathcs1cs2  004 005 hpathCC 
          by(intro hcycleI, simp, cases cs3, auto)

     have "set (cs1 @ cs3) = set C - {a', b'}"
          using a'b'_def Nil distinctC  a'b'_def by auto
     have "{a', b'} = set C - (set cs1 \<union> set cs3)"
        using a'b'_def Nil distinctC  a'b'_def by auto

      have 006: "cs1 @ cs3 \<notin> CCC"
        using Suc(4)[of "cs1@cs3" C, OF _ CD_Def(3) ] a'b'_def(1) a'b'_def(1)  local.Cons
              hcycle_non_empt[of "cs1@cs3", OF Suc(3)[of "cs1@cs3"]] \<open>set (cs1 @ cs3) = set C - {a', b'}\<close>
        by fastforce+

      have g007: "\<Union> ({set C |C. C \<in> CCC}) -{a',b'} = \<Union> ({set C' |C'. C' \<in> CCC - {C} \<union>{(cs1@cs3)}})" 
          using \<open>set (cs1 @ cs3) = set C - {a', b'}\<close>  \<open>{a', b'} = set C - (set cs1 \<union> set cs3)\<close>
                CD_Def a'b'_def Suc.prems(3) 006 
          by (intro subset_big_union_diff, auto)

      have CCC_without_C_subset:
                "\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs3}}
                = \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs3)}}"
      proof
        show "\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs3}}
              \<subseteq> \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs3)}}"
        proof
          fix x
          assume "x \<in> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs3}}"
          then obtain E where "x \<in> set E \<and> E \<in> CCC - {C} \<union> {cs1 @ cs3}"
            by blast
          hence "set E \<in>  {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs3)}" 
            by (metis (mono_tags, lifting) CD_Def Diff_iff UnI2 Un_empty_right Un_insert_right 
                \<open>\<nexists>F. F \<in> CCC \<and> (F \<noteq> C \<and> a \<in> set F \<or> F \<noteq> D \<and> b \<in> set F)\<close> insert_iff mem_Collect_eq)
          then show " x \<in> \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs3)}}"
            using \<open>x \<in> set E \<and> E \<in> CCC - {C} \<union> {cs1 @ cs3}\<close> by blast
        qed
        show "\<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs3)}}
              \<subseteq> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs3}}"
        proof
          fix x
          assume "x \<in> \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs3)}}"
          then obtain E where "x \<in> set E \<and> set E \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs3)}"
            by blast
          then obtain E' where  "set E = set E' \<and> E' \<in>  CCC - {C} \<union> {(cs1 @ cs3)}" 
            by blast
          then show "  x \<in> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs3}}" 
            using \<open>x \<in> set E \<and> set E \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs3)}\<close> by blast
        qed
      qed

      have 007: "C \<in> {set C |C. C \<in> CCC} \<Longrightarrow> D \<in> {set C |C. C \<in> CCC} \<Longrightarrow> D \<noteq> C \<Longrightarrow> D \<inter> C = {}" for C D    
        using Suc.prems(3) by auto

      have 008: "set C = set (cs1 @ cs3) \<union> {a', b'}"
          using "00" \<open>set (cs1 @ cs3) = set C - {a', b'}\<close> a'b'_def by auto

      have "FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {(cs1@cs3)}})) =
                   FBPs (\<Union> ({set C |C. C \<in> CCC })) - {{a',b'}}"
         apply(rule trans) defer
         apply(rule FBP_exchange[of "{set C |C. C \<in> CCC }" a' b' "set (cs1@cs3)" "set C"])
          using Suc.prems(3) \<open>isFBP a' b'\<close> \<open>set (cs1 @ cs3) = set C - {a', b'}\<close>  008
                CD_Def  CCC_without_C_subset by auto

      hence card_prop:"card (FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {(cs1@cs3)}}))) =
                   card (FBPs (\<Union> ({set C |C. C \<in> CCC }))) -1" 
        by (simp add: \<open>{a, b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})\<close> a'b'_def)

      have hcycleC':"\<And>C'. C' \<in> CCC - {C}\<union> {(cs1@cs3)} \<Longrightarrow> hcycle C'" 
        using Suc.prems(2) \<open>hcycle (cs1 @ cs3)\<close> by blast

      have "set(cs1@cs3) \<subseteq> set C"using a'b'_def by auto

      have disjointC':" Ca \<in> (CCC - {C}) \<union> {cs1 @ cs3} \<Longrightarrow>
                Da \<in> (CCC - {C}) \<union> {cs1 @ cs3} \<Longrightarrow> Da \<noteq> Ca \<Longrightarrow> set Da \<inter> set Ca = {}" for Ca Da
        proof-
          assume ass:" Ca \<in> (CCC - {C}) \<union> {cs1 @ cs3}"
                 "Da \<in> (CCC - {C}) \<union> {cs1 @ cs3}" "Da \<noteq> Ca"
          show "set Da \<inter> set Ca = {}"
          proof(cases "Ca = cs1 @ cs3")
            case True
            have "set Da \<inter> set C = {}" 
              using CD_Def  True \<open>Da \<in> CCC - {C} \<union> {cs1 @ cs3}\<close> \<open>Da \<noteq> Ca\<close> 
              by (intro Suc(4), auto)
            then show ?thesis 
              using True \<open>set (cs1 @ cs3) = set C - {a', b'}\<close> by auto
          next
            case False
            hence CaFalse:" Ca \<noteq> cs1 @ cs3" by simp
            then show ?thesis 
            proof(cases " Da \<noteq> cs1 @ cs3")
              case True
              have "set Da \<inter> set Ca = {}"
                using ass False CaFalse True \<open>Da \<in> CCC - {C} \<union> {cs1 @ cs3}\<close> \<open>Da \<noteq> Ca\<close> 
                by (intro  Suc(4), auto)
            then show ?thesis 
              using True \<open>set (cs1 @ cs3) = set C - {a', b'}\<close> by auto
            next
              case False
              hence "Da = cs1 @ cs3" by simp 
              have "set Ca \<inter> set C = {}"
                using False ass(1) ass(3) ass CaFalse 
                by (intro Suc(4))(simp add: CD_Def)+    
              then show ?thesis 
                using \<open>Da = cs1 @ cs3\<close> \<open>set (cs1 @ cs3) = set C - {a', b'}\<close> by fastforce
            qed
          qed
        qed
       have CC'_ex: " \<exists>CCC'.
                finite CCC' \<and>
                (\<forall> C\<in> CCC'. hcycle C) \<and>
                (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
                \<Union> {set C |C. C \<in> CCC'} =
                \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {(cs1@cs3)}} 
                          - \<Union> (FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {(cs1@cs3)}}))"
            apply(rule Suc(1)[of "CCC - {C}\<union> {(cs1@cs3)}"])
            using Suc.prems(1)  hcycleC' Suc.prems(4) card_prop disjointC' by force+
       then show ?thesis 
          using ab_extract g007 a'b'_def by auto
      qed
    next
      case (Cons aaaa list)
      
      hence hpathCC: "hpath (cs1@[a']@cs2@[b']@cs3)" "distinct (cs1@[a']@cs2@[b']@cs3)"
            "fstvv (hd (cs1@[a']@cs2@[b']@cs3)) = sndvv (last(cs1@[a']@cs2@[b']@cs3))"
        using CD_Def Suc.prems(2) a'b'_def hcycle_def by blast+

      have 000: "hpath cs2"
        using  h_path_split1[of cs2 "[b']"] h_path_split2[of "[a']" "cs2@[b']"] hpathCC local.Cons
               h_path_split1[of "[a']@cs2@[b']" cs3] h_path_split2[of cs1 "[a']@cs2@[b']@cs3"] 
        by auto

      have 001: "fstvv (hd cs2) = sndvv (last cs2)"
        using FBP_fst_snd2[of a' b']  \<open>isFBP a' b'\<close> h_path_split3[of "cs1@[a']@cs2" "[b']@cs3"]
              h_path_split3[of "cs1@[a']" "cs2 @ [b'] @ cs3"]  hpathCC(1) local.Cons           
        by auto

      have "hcycle cs2"  
        using  000 001 hpathCC by(intro hcycleI, auto)
          
     then show ?thesis 
      proof(cases "cs1@cs3")
        case Nil
        hence cs1Nil: "cs1 = []" and cs3Nil: "cs3=[]" by auto
        hence "C = [a']@cs2@[b']"
          by (simp add: \<open>C = cs1 @ [a'] @ cs2 @ [b'] @ cs3\<close> \<open>{a', b'} = {a, b}\<close>)
        have "set cs2 = set C - {a', b'}" 
          using distinctC  a'b'_def 
          by (subst  a'b'_def, subst cs1Nil, subst cs3Nil, auto)
        have "{a', b'} = set C - set cs2"
          using distinctC  a'b'_def 
          by (subst a'b'_def, subst cs1Nil, subst cs3Nil, auto)
        have cs2_not_in_CCC:"cs2 \<notin> CCC"
            using Suc.prems(3)[of C cs2, OF CD_Def(3)] a'b'_def(1) local.Cons by auto
        have "\<Union> ({set C |C. C \<in> CCC}) -{a',b'} = \<Union> ({set C' |C'. C' \<in> CCC - {C} \<union> {cs2} })" 
          apply(rule subset_big_union_diff[of cs2 C "{a',b'}" CCC])
          using \<open>{a', b'} = set C - set cs2\<close> Suc.prems(3)cs2_not_in_CCC 
          by (simp add: \<open>set cs2 = set C - {a', b'}\<close>, 
              auto simp add:  CD_Def \<open>{a', b'} = set C - set cs2\<close> )

        have seteq: "\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs2}} =
                         \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set cs2}}"
        proof
          show "\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs2}} 
                   \<subseteq> \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set cs2}}"
        proof
          fix x
          assume "x \<in> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs2}}"
          then obtain E where E_prop:"x \<in> set E \<and> E \<in> CCC - {C} \<union> {cs2}"
            by blast
          have "set E \<in>  {set C |C. C \<in> CCC} - {set C} \<union> {set cs2}" 
            using CD_Def(1) E_prop \<open>\<nexists>F. F \<in> CCC \<and> (F \<noteq> C \<and> a \<in> set F \<or> F \<noteq> D \<and> b \<in> set F)\<close> 
            by auto
          then show " x \<in> \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set cs2}}"
            using \<open>x \<in> set E \<and> E \<in> CCC - {C} \<union> {cs2}\<close> by blast
        qed
        show "\<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set cs2}} 
                 \<subseteq> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs2}}"
        proof
          fix x
          assume "x \<in> \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set cs2}}"
          then obtain E where "x \<in> set E \<and> set E \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set cs2}"
            by blast
          then obtain E' where  "set E = set E' \<and> E' \<in>  CCC - {C} \<union> {cs2}" 
            by blast
          then show "  x \<in> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs2}}" 
            using \<open>x \<in> set E \<and> set E \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set cs2}\<close> by blast
        qed
      qed

      have 004: "set cs2 = set C - {a', b'}"
        using \<open>set cs2 = set C - {a', b'}\<close> by blast

      have 005: "set C = set cs2 \<union> {a', b'}"
        using  \<open>set cs2 = set C - {a', b'}\<close> \<open>{a', b'} = set C - set cs2\<close>  by auto

      have "FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {cs2}})) =
                   FBPs (\<Union> ({set C |C. C \<in> CCC })) - {{a',b'}}"
          apply(rule trans) defer
          apply(rule FBP_exchange[of "{set C |C. C \<in> CCC }" a' b' "set cs2" "set C"])
          using Suc.prems(3) \<open>isFBP a' b'\<close>  004 005 CD_Def seteq
          by auto

      hence card_prop:"card (FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {C} \<union> {cs2}) }))) =
                   card (FBPs (\<Union> ({set C |C. C \<in> CCC}))) -1" 
          by (simp add: \<open>{a, b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})\<close> a'b'_def)
      have hcycleC':"\<And>C'. C' \<in> CCC - {C}\<union> {cs2} \<Longrightarrow> hcycle C'" 
          using Suc.prems(2) \<open>hcycle cs2\<close> by blast
      have "set(cs2) \<subseteq> set C"using a'b'_def by auto

      have disjointC':" Ca \<in> (CCC - {C}) \<union> {cs2} \<Longrightarrow>
                Da \<in> (CCC - {C}) \<union> {cs2} \<Longrightarrow> Da \<noteq> Ca \<Longrightarrow> set Da \<inter> set Ca = {}" for Ca Da
        proof-
          assume ass:" Ca \<in> (CCC - {C}) \<union> {cs2}"
                 "Da \<in> (CCC - {C}) \<union> {cs2}" "Da \<noteq> Ca"
          show "set Da \<inter> set Ca = {}"
          proof(cases "Ca = cs2")
            case True
            have "set Da \<inter> set C = {}" 
              using CD_Def  True \<open>Da \<in> CCC - {C} \<union> {cs2}\<close> \<open>Da \<noteq> Ca\<close> 
              by (intro Suc(4), auto)
            then show ?thesis 
              using True \<open>set cs2 = set C - {a', b'}\<close> by auto
          next
            case False
            hence CaFalse:" Ca \<noteq> cs2" by simp
            then show ?thesis 
            proof(cases " Da \<noteq> cs2")
              case True
              have "set Da \<inter> set Ca = {}" 
                using ass False CaFalse True \<open>Da \<in> CCC - {C} \<union> {cs2}\<close> \<open>Da \<noteq> Ca\<close> 
                by (intro Suc(4), auto)
            then show ?thesis 
              using True \<open>set cs2 = set C - {a', b'}\<close> by auto
            next
              case False
              hence "Da = cs2" by simp 
              have "set Ca \<inter> set C = {}"
                using CD_Def  False ass(1) ass(3) ass CaFalse 
                by (intro Suc(4), auto)
              then show ?thesis 
                using \<open>Da = cs2\<close> \<open>set cs2 = set C - {a', b'}\<close> by fastforce
            qed
          qed
        qed

        have CC'_ex: " \<exists>CCC'.
                finite CCC' \<and>
                 (\<forall> C\<in> CCC'. hcycle C) \<and>
                (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
                \<Union> {set C |C. C \<in> CCC'} =
                \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs2}} 
                          - \<Union> (FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs2}}))"
          apply(rule Suc(1)[of "CCC - {C}\<union> {cs2}"])
          using Suc.prems(1) hcycleC'  disjointC' Suc.prems(4)card_prop by simp+
        then show ?thesis
          using \<open>\<Union> {set C |C. C \<in> CCC} - \<Union> (FBPs (\<Union> {set C |C. C \<in> CCC})) = \<Union> {set C |C. C \<in> CCC} - {a, b} - \<Union> (FBPs (\<Union> {set C |C. C \<in> CCC} - {a, b}))\<close> \<open>\<Union> {set C |C. C \<in> CCC} - {a', b'} = \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs2}}\<close> a'b'_def by auto
      next
        case (Cons aaaa list)

        have hpathcprop: "hpath (cs1 @ [a']@cs2@[b'] @ cs3)" "distinct (cs1 @ [a']@cs2@[b'] @ cs3)"
              "fstvv (hd (cs1 @ [a']@cs2@[b'] @ cs3)) = sndvv (last (cs1 @ [a']@cs2@[b'] @ cs3))"        
          using hpathCC by blast+

        have 000: "cs1 \<noteq> [] \<Longrightarrow> cs3 \<noteq> []\<Longrightarrow> sndvv (last cs1) = fstvv (hd cs3)"
            apply(rule trans, rule h_path_split3[of _ "[a']@cs2@[b']@cs3"])
            using  hpathcprop(1) apply (simp, simp, simp)
            apply(rule trans[of _ "sndvv (last (cs1@[a'] @ cs2 @ [b']))"])           
            using \<open>isFBP a' b'\<close> FBP_fst_snd1  hpathcprop(1)      
            by(fastforce intro: h_path_split3 simp add: \<open>isFBP a' b'\<close> FBP_fst_snd1  hpathcprop(1) )+

        have hpathcs1cs2: "hpath (cs1 @cs3)" 
            using  Cons h_path_append[of cs1 cs3] hpathcprop(1) 000 
                  h_path_split1[of cs1 "[a']@cs2@[b']@cs3"] h_path_split2[of "cs1 @ [a']@cs2@[b']" cs3]                 
            by(cases cs1) (auto intro!: h_path_split2[of "cs1 @ [a']@cs2@[b']" cs3],
                           cases cs3, auto intro!: h_path_split1[of cs1 "[a']@cs2@[b']@cs3"] )

        have 001: "cs3 = [] \<Longrightarrow> sndvv (last (cs1 @ [a'] @ cs2 @ [b'])) = sndvv (last (cs1 @ cs3))"
            apply(rule trans, rule sym[OF FBP_fst_snd1[of "hd ([a']@cs2@[b'])"]])
            using hpathCC Cons \<open>isFBP a' b'\<close> FBP_fst_snd1[of "hd ([a']@cs2@[b'])"]
            by(fastforce intro: sym[OF FBP_fst_snd1[of "hd ([a']@cs2@[b'])"]] 
                                sym[OF h_path_split3] h_path_split1[of _ cs3])+
        have "hcycle (cs1@cs3)"
          apply(rule hcycleI[OF hpathcs1cs2])
          subgoal
                using hpathCC Cons 001 hpathCC FBP_fst_snd1[of a'] \<open>isFBP a' b'\<close>  hpathCC
                      h_path_split3[of "cs1 @ [a'] @ cs2 @ [b']"] 
                by (cases cs3, simp, cases cs1, auto)
           subgoal
             using hpathCC  by auto
           done

        have "set (cs1 @ cs2 @cs3)  = set C - {a', b'}"
          using distinctC a'b'_def  by auto

       have "set (cs1 @ cs2 @cs3)  = set C - {a', b'}"
          using distinctC a'b'_def  by auto

        have "{a', b'} = set C - (set cs1 \<union> set cs2 \<union> set cs3)"
          using distinctC a'b'_def  by auto
          

      have "set C \<inter> set (cs1 @ cs2 @ cs3) \<noteq> {}" 
        apply(subst  a'b'_def )
        using Cons by(cases cs1, simp, simp)
        
      have a'b'cs:"\<Union> ({set C |C. C \<in> CCC}) -{a',b'} =
                     \<Union> ({set C' |C'. C' \<in> CCC - {C} \<union>{cs1@cs2@ cs3}})"
        apply(rule subset_big_union_diff)
        using \<open>set (cs1 @ cs2@cs3) = set C - {a', b'}\<close>  Un_assoc Suc(4)[of "cs1@cs2@cs3" C]
              \<open>{a', b'} = set C - (set cs1 \<union> set cs2 \<union> set cs3)\<close> Suc.prems(3) 
               CD_Def  \<open>set C \<inter> set (cs1 @ cs2 @ cs3) \<noteq> {}\<close>  a'b'_def(1) by auto

      have seteq: " (\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs2 @ cs3}}) =
                    (\<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs2 @ cs3)}})"
      proof
        show" (\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs2 @ cs3}})
             \<subseteq>  (\<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs2 @ cs3)}})"
        proof
          fix x
          assume "x \<in> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @cs2@ cs3}}"
          then obtain E where "x \<in> set E \<and> E \<in> CCC - {C} \<union> {cs1 @ cs2@cs3}"
            by blast
          hence "set E \<in>  {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @cs2@ cs3)}" 
            by (metis (mono_tags, lifting) CD_Def(1) Diff_iff UnI2 Un_empty_right Un_insert_right
                 \<open>\<nexists>F. F \<in> CCC \<and> (F \<noteq> C \<and> a \<in> set F \<or> F \<noteq> D \<and> b \<in> set F)\<close> insert_iff mem_Collect_eq)
          then show " x \<in> \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs2@cs3)}}"
            using \<open>x \<in> set E \<and> E \<in> CCC - {C} \<union> {cs1 @ cs2@cs3}\<close> by blast
        qed
        show " \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs2 @ cs3)}}
                \<subseteq> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs2 @ cs3}} "
        proof
          fix x
          assume "x \<in> \<Union> {C' |C'. C' \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @cs2@ cs3)}}"
          then obtain E where "x \<in> set E \<and> set E \<in> {set C |C. C \<in> CCC} -
                                      {set C} \<union> {set (cs1 @ cs2@cs3)}"
            by blast
          then obtain E' where  "set E = set E' \<and> E' \<in>  CCC - {C} \<union> {(cs1 @cs2@ cs3)}" 
            by blast
          then show "  x \<in> \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs2@cs3}}" 
            using \<open>x \<in> set E \<and> set E \<in> {set C |C. C \<in> CCC} - {set C} \<union> {set (cs1 @ cs2@cs3)}\<close> by blast
        qed
      qed

      have FBPs_cs1cs2cs3:"FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {(cs1@cs2@cs3)}})) =
                   FBPs (\<Union> ({set C |C. C \<in> CCC })) - {{a',b'}}"
        using FBP_exchange[of "{set C |C. C \<in> CCC }" a' b' "set (cs1@cs2@cs3)" "set C"]  Suc.prems(3) 
              \<open>isFBP a' b'\<close> \<open>set (cs1 @ cs2 @ cs3) = set C - {a', b'}\<close>  CD_Def True a'b'_def seteq
        by auto

        have csprop:"\<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {(cs1@cs2@cs3)}}) = 
              \<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {(cs1@cs3), cs2}})"
          by(rule bing_union_split,  force)

        hence "FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {cs1 @ cs3, cs2}}) =
               FBPs (\<Union> {set C |C. C \<in> CCC}) - {{a', b'}} "
          using FBPs_cs1cs2cs3 by presburger

        hence card_less: "card (FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {C}) \<union> {cs1 @ cs3, cs2}}))) =
                   card (FBPs (\<Union> ({set C |C. C \<in> CCC }))) -1" 
          by (simp add: \<open>{a, b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})\<close> a'b'_def)

        have hcycle':"\<And>C'. C' \<in> CCC - {C}\<union> {(cs1@cs3), cs2} \<Longrightarrow> hcycle C'" 
          using Suc.prems(2) \<open>hcycle (cs1 @ cs3)\<close> \<open>hcycle cs2\<close> by blast

        have "set(cs1@cs3) \<subseteq> set C"using a'b'_def by auto

        have "set cs2 \<subseteq> set C"using a'b'_def by auto

        have "set (cs1 @ cs3) \<inter> set cs2 = {}"
          using distinctC a'b'_def by auto

        have disjoint':
              " Ca \<in> (CCC - {C}) \<union> {cs1 @ cs3, cs2} \<Longrightarrow>
                Da \<in> (CCC - {C}) \<union> {cs1 @ cs3, cs2} \<Longrightarrow> Da \<noteq> Ca \<Longrightarrow> set Da \<inter> set Ca = {}" for Da Ca
          apply(rule disjoint_lists_sublists[of "CCC" C "cs1@cs3" cs2 "set C"])
          using Suc.prems(3) CD_Def  Un_subset_iff \<open>set (cs1 @ cs3) \<subseteq> set C\<close> \<open>set cs2 \<subseteq> set C\<close>
                \<open>set (cs1 @ cs3) \<inter> set cs2 = {}\<close> distinctC by auto

       have CC'_ex: " \<exists>CCC'.
                finite CCC' \<and>
                 (\<forall> C\<in> CCC'. hcycle C) \<and>
                (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
                \<Union> {set C |C. C \<in> CCC'} =
                \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {(cs1@cs3), cs2}} 
                          - \<Union> (FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {(cs1@cs3), cs2}}))"
         apply(rule Suc(1))
         using  Suc.prems(1) hcycle'  disjoint' Suc.prems(4) card_less by auto

      then show ?thesis
        using ab_extract a'b'cs csprop a'b'_def by auto
    qed
  qed
  next
 case False
  then obtain cs ds fs gs where cdef_def: "C = cs@[a]@ds" "D = fs@[b]@gs"
    by (metis CD_Def append_Cons self_append_conv2 split_list)
  have "C \<noteq> D" using False by simp
  have "hpath C" "hpath D" 
    using CD_Def Suc.prems(2) hcycle_def by blast+
  hence distinctD:"distinct D" 
    using CD_Def Suc.prems(2) hcycle_def by blast
  have "set (ds @ cs) = set C - {a}" 
    using cdef_def(1)  cdef_def distinctC by force
  have "set (fs @ gs ) = set D - {b}" 
   using cdef_def(2) cdef_def distinctD by force
  have FBPsextr: "FBPs (\<Union> ({set C |C. C \<in> CCC})) -{{a,b}} =
                     FBPs (\<Union> ({set C |C. C \<in> CCC}) -{a,b})"
    using FBP_in_E FBP_substr_union_distr[of a b "\<Union> {set C |C. C \<in> CCC}"]
           \<open>{a, b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})\<close> ab_def by simp
  have "card (FBPs (\<Union> ({set C |C. C \<in> CCC}) -{a,b})) = n" 
          apply(subst sym[OF FBPsextr])
          using  \<open>{a, b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})\<close> finite_FBPs_of_CCC Suc(5) by simp 

  then show ?thesis 
    proof(cases "C=[a]")
      case True
      hence "C = [a]" by simp
      have Caprop:"\<Union> ({set C |C. C \<in> CCC}) -{a} = \<Union> ({set C' |C'. C' \<in> CCC - {C}})" 
        apply( subst \<open>C = [a]\<close>, rule trans, rule subset_big_union_diff[of "[]" C "{a}" CCC])
        using Suc.prems(2) hcycle_non_empt CD_Def \<open>hpath C\<close> hpath_non_empt Suc.prems(3)  \<open>C = [a]\<close> 
        by auto

      then show ?thesis 
      proof(cases "D = [b]")
        case True

        hence "fstvv b = sndvv b" 
          using CD_Def Suc.prems(2) hcycle_def[of D]  by simp

        have Cbprop:"\<Union> ({set C' |C'. C' \<in> CCC -{C}}) -{b} 
             = \<Union> ({set C' |C'. C' \<in> (CCC - {C}) -{D}})" 
          apply( subst True, rule trans)
          apply(rule subset_big_union_diff[of "[]" D "{b}" "CCC - {C}" ])
          using CD_Def False  Suc.prems(2) hcycle_non_empt  \<open>hpath D\<close> hpath_non_empt  Suc.prems(3) True 
          by auto

        have abCD:"\<Union> ({set C |C. C \<in> CCC}) -{a,b} = \<Union> ({set C' |C'. C' \<in> CCC - {C,D}})"    
          using  Diff_insert2[of "\<Union> _ " a "{b}"] Caprop Cbprop by simp
       
        have  FBPab_out: "FBPs (\<Union> ({set C |C. C \<in> CCC}) -{a,b}) =
               FBPs (\<Union> ({set C |C. C \<in> CCC})) - {{a,b}}"
          using  FBP_substr_union_distr ab_def FBP_in_E \<open>{a, b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})\<close>
          by fastforce+

       hence "card (FBPs ( \<Union> ({set C' |C'. C' \<in> CCC - {C,D}}))) = n" 
          using abCD FBPab_out  \<open>{a, b} \<in> FBPs (\<Union> {set C |C. C \<in> CCC})\<close> finite_FBPs_of_CCC Suc(5) by simp

        have CC'_ex: " \<exists>CCC'.
                finite CCC' \<and>
                 (\<forall> C\<in> CCC'. hcycle C) \<and>
                (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
                \<Union> {set C |C. C \<in> CCC'} =
                \<Union> {set C' |C'. C' \<in> CCC - {C,D}} 
                          - \<Union> (FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C,D}}))"
          using  Suc.prems  \<open>card (FBPs (\<Union> {set C' |C'. C' \<in> CCC - {C, D}})) = n\<close> by (fast intro!: Suc(1)) 

        then show ?thesis 
          using abCD ab_extract by presburger
      next
        case False

        have 001:"\<Union> {set B |B. B \<in> CCC - {C} - {D} \<union> {gs @ fs}} =
                  \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {gs @ fs} - {D}}"
          using  Suc.prems(3)[of D "gs@fs"] cdef_def  by fastforce

        have "\<Union> ({set C' |C'. C' \<in> CCC -{C}}) -{b} 
             = \<Union> ({set C' |C'. C' \<in> (CCC - {C}) -{D} \<union> {gs@fs}})" 
          apply(subst  inter_minus_distr[of "{gs@fs}" "{D}" "CCC - {C}"], simp add: cdef_def)
          apply(rule trans, rule subset_big_union_diff[of "gs@fs" D "{b}" "CCC - {C}" ])
          using \<open>set (fs @ gs) = set D - {b}\<close>  CD_Def  CD_Def \<open>C \<noteq> D\<close> 
                Suc.prems(3)[of D "gs@fs", OF CD_Def(4)]  
                hcycle_non_empt[of "gs@fs", OF  Suc.prems(2)[of "gs@fs"]] 
                cdef_def set_append_swap[of fs gs] Suc.prems(3) cdef_def 001 
          by auto

        hence ab_gsfs:"\<Union> ({set C' |C'. C' \<in> CCC}) -{a,b} 
             = \<Union> ({set C' |C'. C' \<in> (CCC - {C}) -{D} \<union> {gs@fs}})" 
          using  \<open>\<Union> {set C |C. C \<in> CCC} - {a} = \<Union> {set C' |C'. C' \<in> CCC - {C}}\<close>
                 Diff_insert2[of "\<Union> _" a "{b}"] by simp

        hence card_prop:"card (FBPs(\<Union> ({set C' |C'. C' \<in> (CCC - {C}) -{D} \<union> {gs@fs}}))) = n"
          using \<open>card (FBPs (\<Union> {set C |C. C \<in> CCC} - {a, b})) = n\<close> by presburger

        have 003: "gs \<noteq> [] \<Longrightarrow> fs \<noteq> [] \<Longrightarrow> hpath (gs @ fs)"
             using \<open>hpath D\<close>[simplified cdef_def(2)] Suc.prems(2)[OF CD_Def(4)]
                   h_path_split1[of "fs@[b]" gs] 
             by(intro h_path_append[of gs fs])
               (auto intro:  h_path_split1[of fs "[b]"]   
                             h_path_append h_path_split2[of "fs @ [b]"] h_path_split1 
                      elim:  hcycleE simp: cdef_def(2))

        have "hpath (gs @ fs)" 
          apply(cases "gs")
          subgoal
             using \<open>hpath D\<close>[simplified cdef_def(2)]  False[simplified cdef_def(2)]
             by(auto intro: h_path_split1[of "fs" "[b]" ])
           subgoal
             using \<open>hpath D\<close>[simplified cdef_def(2)] 003
             by(cases fs, auto intro: h_path_split2[of "fs@[b]" ])
           done

        have gs_empt:"gs = [] \<Longrightarrow> fstvv (hd ([b]@fs)) = sndvv (last ([b]@fs))"
                     "gs = [] \<Longrightarrow> fs \<noteq> []"
          using False \<open>hpath D\<close> cdef_def h_path_split3  by fastforce+

        have fs_empt:"fs = [] \<Longrightarrow> gs \<noteq> []"
          using False \<open>hpath D\<close> cdef_def h_path_split3  by fastforce   

        have fstva: "fstvv a = sndvv a"
          using  FBP_fst_snd1[of a b] ab_def(3) Suc.prems(2) True CD_Def(3) hcycle_def[of C] 
          by simp 

        have "hcycle (gs @ fs)"
          apply(rule hcycleI)
          using  FBP_fst_snd1[of a ] FBP_fst_snd2[of a ] CD_Def(4) cdef_def(2) h_path_split3[of fs ]
                 hcycle_def[of D] gs_empt(2) Suc.prems(2)[of D] ab_def(3)h_path_split3[of "fs@[b]"]
                 last_append[of gs fs] fstva
            by(simp add: \<open>hpath (gs @ fs)\<close>,  cases gs, auto)

        have hcycleC':"\<And>Ca. Ca \<in> CCC - {C} - {D} \<union> {gs @ fs} \<Longrightarrow> hcycle Ca"
          using Suc.prems(2) \<open>hcycle (gs @ fs)\<close> by fastforce

        have CCC_disjoint_without_D:"Ca \<in> CCC - {D} \<union> {gs @ fs} \<Longrightarrow>
                       Da \<in> CCC - {D} \<union> {gs @ fs} \<Longrightarrow> Da \<noteq> Ca \<Longrightarrow> set Da \<inter> set Ca = {}" for Ca Da        
            apply(rule disjoint_lists_sublists[of CCC D "gs @ fs" "[]" "set D"])
            using Suc.prems(3) CD_Def \<open>set (fs @ gs) = set D - {b}\<close> using distinctD by force+ 

        have newCCC_disjoint:" Ca \<in> CCC - {D, C} \<union> {gs @ fs} \<Longrightarrow>
              Da \<in> CCC - {D, C} \<union> {gs @ fs} \<Longrightarrow> Da \<noteq> Ca \<Longrightarrow> set Da \<inter> set Ca = {}" for Ca Da
          using CCC_disjoint_without_D by auto

        have CC'_ex: " \<exists>CCC'.
                finite CCC' \<and>
                 (\<forall> C\<in> CCC'. hcycle C) \<and>
                (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
                \<Union> {set C |C. C \<in> CCC'} =
                \<Union> ({set C' |C'. C' \<in> (CCC - {C}) -{D} \<union> {gs@fs}})
                          - \<Union> (FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {C}) -{D} \<union> {gs@fs}})))"
          apply(rule Suc(1))
          using Suc.prems(1)  hcycleC'  CCC_disjoint_without_D  card_prop by auto
        then show ?thesis 
          using ab_extract ab_gsfs by presburger
      qed
    next
      case False
      hence "C \<noteq> [a]" by simp
      then show ?thesis 
      proof(cases "D = [b]")
        case True

        have "\<Union> {set C |C. C \<in> CCC} - {b} = \<Union> {set C' |C'. C' \<in> CCC - {D}}"
          apply( subst True, rule trans, rule subset_big_union_diff[of "[]" D "{b}" "CCC" ])
          using CD_Def False Suc.prems(2) hcycle_non_empt \<open>hpath D\<close> hpath_non_empt Suc.prems(3) True
          by auto

        have pr:"\<Union> ({set C' |C'. C' \<in> CCC -{D}}) -{a} 
             = \<Union> ({set C' |C'. C' \<in> (CCC - {D}) -{C} \<union> {ds @ cs}})" 
          apply(subst  inter_minus_distr, simp add: cdef_def)
          apply(rule trans, rule subset_big_union_diff[of "ds @ cs" C])
          using \<open>set (ds @ cs) = set C - {a}\<close>   CD_Def \<open>C \<noteq> D\<close>  CD_Def(3) DiffD1 Suc.prems(2)[of "ds@cs"] 
                Suc.prems(3)[of C "ds@cs"] hcycle_non_empt[of "ds@cs"] cdef_def(1)  Suc.prems(3) cdef_def(1)
                cdef_def inter_minus_distr[of "{ds@cs}" "{C}" "CCC - {D}"]
          by auto

        have ab_gsfs:"\<Union> ({set C' |C'. C' \<in> CCC}) -{a,b} 
             = \<Union> ({set C' |C'. C' \<in> (CCC - {D}) -{C} \<union> {ds@cs}})" 
          by(subst sym[OF pr], 
             subst sym[OF \<open>\<Union> {set C |C. C \<in> CCC} - {b} = \<Union> {set C' |C'. C' \<in> CCC - {D}}\<close>],
             auto) 

        hence cardn:"card (FBPs(\<Union> ({set C' |C'. C' \<in> (CCC - {D}) -{C} \<union> {ds@cs}}))) = n"
          using \<open>card (FBPs (\<Union> {set C |C. C \<in> CCC} - {a, b})) = n\<close> by presburger

        have 007: "ds = [] \<Longrightarrow> hpath cs"
          using \<open>hpath C\<close> cdef_def(1) False by(auto intro: h_path_split1[of _ "[a]@ds"])

        have 008: "ds \<noteq> [] \<Longrightarrow> hpath (ds @ cs)"
            using \<open>hpath C\<close> cdef_def False h_path_split2[of "cs@[a]" "ds"]   h_path_split1  
                  hcycleE[OF  Suc.prems(2)[OF  CD_Def(3)]] 
            (*Takes some time*)
            by( cases cs, simp, intro h_path_append, simp, fast, fastforce)

        have "hpath (ds @ cs)" 
         using 007 008  by(cases "ds") auto

        have gs_empt:"ds = [] \<Longrightarrow> fstvv (hd ([a]@cs)) = sndvv (last ([a]@cs))"
                     "ds = [] \<Longrightarrow> cs \<noteq> []"
          using False \<open>hpath C\<close> cdef_def(1) h_path_split3[of cs ]  h_path_split3[of "cs@[a]" ] 
          by simp+

        have 009: "fstvv (hd (ds @ cs)) = sndvv (last (ds @ cs))"
            using  FBP_fst_snd1[of a] FBP_fst_snd2[of a] Suc.prems(2)[of C, OF CD_Def(3)]  ab_def(3) 
                   gs_empt(2)  h_path_split3[of cs]  h_path_split3[of "cs@[a]" "ds"] cdef_def(1)
                   hcycle_def[of "cs @ [a] @ _"] False hcycle_def[of "[b]"] True 
                   Suc.prems(2)[of D, OF CD_Def(4)] 
            by(cases cs, simp, cases ds, auto) 

        have "hcycle (ds @ cs)"
          using 009 cdef_def distinctC by(auto intro!: hcycleI[OF \<open>hpath (ds @ cs)\<close>])

        have "\<And>Ca. Ca \<in> CCC - {D} - {C} \<union> {ds @ cs} \<Longrightarrow> hcycle Ca"
          using Suc.prems(2) \<open>hcycle (ds @ cs)\<close> by fastforce

        have CCC_disjoint_without_D:"Ca \<in> CCC - {C} \<union> {ds @ cs} \<Longrightarrow>
              Da \<in> CCC - {C} \<union> {ds @ cs} \<Longrightarrow> Da \<noteq> Ca \<Longrightarrow> set Da \<inter> set Ca = {}" for Ca Da
          apply(rule disjoint_lists_sublists[of CCC C "ds @ cs" "[]" "set C"])
          using Suc.prems(3) CD_Def \<open>set (ds @ cs) = set C - {a}\<close>  distinctC 
          by auto

        have newCCC_disjoint:"
              Ca \<in> CCC - {D, C} \<union> {ds @ cs} \<Longrightarrow>
              Da \<in> CCC - {D, C} \<union> {ds @ cs} \<Longrightarrow> Da \<noteq> Ca \<Longrightarrow> set Da \<inter> set Ca = {}" for Ca Da
          using CCC_disjoint_without_D[of Ca Da] by auto
         
        have CC'_ex: " \<exists>CCC'.
                finite CCC' \<and>
                 (\<forall> C\<in> CCC'. hcycle C) \<and>
                (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
                \<Union> {set C |C. C \<in> CCC'} =
                \<Union> ({set C' |C'. C' \<in> (CCC - {D}) -{C} \<union> {ds@cs}})
                          - \<Union> (FBPs (\<Union> ({set C' |C'. C' \<in> (CCC - {D}) -{C} \<union> {ds@cs}})))"
          apply(rule Suc(1))
          using Suc.prems(1) \<open>\<And>Ca. Ca \<in> CCC - {D} - {C} \<union> {ds @ cs} \<Longrightarrow> hcycle Ca\<close> 
                CCC_disjoint_without_D cardn by fast+
        then show ?thesis 
          using ab_extract ab_gsfs by presburger
      next
        case False
        hence "D \<noteq> [b]" "C \<noteq> [a]" 
          by (simp add: \<open>C \<noteq> [a]\<close>)+

        have ab_fstsndvv: "sndvv a = fstvv b" "sndvv b = fstvv a"
          by (simp add: FBP_fst_snd2 ab_def) (simp add: FBP_fst_snd2 FBP_sym ab_def)

        have csadsafstsnd: "ds = [] \<Longrightarrow> fs = [] \<Longrightarrow> sndvv (last (cs@[a])) = fstvv (hd (b#gs))"
          by (simp add: ab_fstsndvv)

        have hpath_cs_cond:"ds = []\<Longrightarrow> hpath cs"
          using \<open>hpath C\<close> cdef_def \<open>C \<noteq> [a]\<close> 
          by(auto intro:  h_path_split1[of cs "[a]"])

        have hpath_gs_cond:" fs = [] \<Longrightarrow> hpath gs"
          using False \<open>hpath D\<close> append.left_neutral append_Nil2 cdef_def 
          by(auto intro: h_path_split2[of "fs@[b]" gs])

        have last_cs_fst_a_cond: "ds = [] \<Longrightarrow> sndvv (last cs) = fstvv a"
          using \<open>C \<noteq> [a]\<close> \<open>hpath C\<close> cdef_def h_path_split3 by force

        have fst_gs_fst_a_cond: "fs = [] \<Longrightarrow> fstvv a = fstvv (hd gs)"
          apply(rule trans[of _ "sndvv (last [b])"])
          using ab_fstsndvv(2)  False \<open>hpath D\<close>  cdef_def 
          by(fastforce intro: h_path_split3)+

        have hpath_gs_cond: " gs \<noteq> [] \<Longrightarrow> hpath gs"
          using cdef_def(2) hcycleE[OF Suc.prems(2)[OF CD_Def(4)]]
             h_path_split2[of "fs@[b]"] by auto

        have fst_fs_last_gs_cond: "fs \<noteq> [] \<Longrightarrow> gs \<noteq>[] \<Longrightarrow> sndvv (last gs) = fstvv (hd fs)"
          using cdef_def(2) by(auto intro: hcycleE[OF Suc.prems(2)[OF CD_Def(4)]]) 

        have 000: "fs \<noteq> [] \<Longrightarrow> gs \<noteq> [] \<Longrightarrow> hpath (gs @ fs)"
             using hpath_gs_cond \<open>hpath D\<close> cdef_def(2) h_path_split1 fst_fs_last_gs_cond
             by(fast intro: h_path_append)

        have 001: "fs \<noteq> [] \<Longrightarrow> gs = [] \<Longrightarrow> hpath fs"
             using h_path_split1 h_path_split2
                   hcycleE[OF Suc.prems(2)[OF CD_Def(4)]] cdef_def(2) by fast

        have 002: "fs = [] \<Longrightarrow> hpath gs"
            using cdef_def(2) False hcycleE[OF Suc.prems(2)[OF CD_Def(4)], of "hpath D"]
            by(force intro: h_path_split2[of "fs@[b]"])

        have hpath_gs_fs_cond:"hpath (gs @ fs)"
          using 002  001 000 by(cases fs, simp, cases gs, auto)

        have snd_last_cs_fst_gs_fs:"ds = [] \<Longrightarrow> fs \<noteq> [] \<Longrightarrow> sndvv (last cs) = fstvv (hd (gs @ fs))"
             using CD_Def(3,4)  Suc.prems(2)[of C] Suc.prems(2)[of D] \<open>C \<noteq> [a]\<close> ab_fstsndvv(2)  cdef_def 
                   h_path_split3[of cs ]  hcycle_def[of C]  hcycle_def[of D] h_path_split3[of "fs@[b]" ]
             by(cases gs, auto)
          
        have d_hpath_cond: "ds \<noteq> [] \<Longrightarrow> hpath ds"
          using \<open>hpath C\<close> cdef_def(1) h_path_split2 by blast 

        have c_hpath_cond: " cs \<noteq> [] \<Longrightarrow> hpath cs"
          using \<open>hpath C\<close> cdef_def(1) h_path_split1 by blast

        have 003: "cs = [] \<Longrightarrow> hpath (ds @ cs)"
          using cdef_def(1)\<open>C \<noteq> [a]\<close> d_hpath_cond by(cases ds) auto

        have 004: "cs \<noteq> [] \<Longrightarrow> hpath (ds @ cs)"
          using hpath_cs_cond d_hpath_cond c_hpath_cond CD_Def(3) Suc.prems(2) cdef_def(1) 
           by(cases ds) (fastforce intro: h_path_append elim: hcycleE)+

        have ds_cs_hpath:"hpath (ds @ cs)"
          using 003 004 by (cases cs, auto)

         have f_hpath_cond: "fs \<noteq> [] \<Longrightarrow> hpath fs"
           using h_path_split2 hpath_gs_fs_cond by blast

         have cs_a_cond: "cs \<noteq> [] \<Longrightarrow> sndvv(last cs) = fstvv a" 
           using \<open>hpath C\<close> cdef_def(1) h_path_split3 
           by fastforce

         have gs_b_cond: "gs \<noteq> [] \<Longrightarrow> sndvv b =  fstvv(hd gs)" 
           apply(rule trans[of _ "sndvv(last [b])"], simp)
           using  \<open>hpath D\<close>  cdef_def(2) 
           by(fastforce intro: h_path_split3 h_path_split2[of fs])

         have ds_last_a_cond: "cs = [] \<Longrightarrow> sndvv (last ds) = fstvv a" 
           using CD_Def(3) Suc.prems(2) cdef_def(1) \<open>C \<noteq> [a]\<close>
           by(force elim: hcycleE)

         have gs_last_b_cond: "fs = [] \<Longrightarrow> sndvv (last gs) = fstvv b" 
           using CD_Def(4) Suc.prems(2) cdef_def(2) False
           by(force elim: hcycleE)

         have fs_fst_b_cond: "gs =  [] \<Longrightarrow> fstvv (hd fs) = sndvv b" 
           using CD_Def(4) Suc.prems(2) cdef_def(2) False 
           by(force elim: hcycleE)

         have last_ds_cs_hd_gs_fs: "sndvv (last (ds @ cs)) = fstvv (hd (gs@fs))"
           using gs_b_cond ds_last_a_cond False cdef_def  
                 ab_fstsndvv(2) fs_fst_b_cond gs_b_cond cs_a_cond 
           by (cases cs) (cases gs, auto)+

         have 005: "ds = [] \<Longrightarrow> hpath (cs @ gs @ fs)"
           using hpath_cs_cond  hpath_gs_cond  last_cs_fst_a_cond fst_gs_fst_a_cond hpath_cs_cond
                 hpath_gs_fs_cond snd_last_cs_fst_gs_fs
           by(cases fs, simp, force intro: h_path_append)+   

         have 006: "ds \<noteq> [] \<Longrightarrow> hpath (ds @ cs @ gs @ fs)"
           apply(cases fs)
           using  rev_iffD2[of "hpath ((ds @ cs) @ gs)"] ds_cs_hpath hpath_gs_fs_cond  
                  rev_iffD2[of "hpath ((ds @ cs) @ (gs @ fs))"] last_ds_cs_hd_gs_fs 
           by(fastforce intro: h_path_append)+

         have "hpath (ds@cs@gs@fs)"
           using 005 006 by(cases ds, auto)

         have 008: "ds \<noteq> [] \<Longrightarrow> fstvv (hd ds) = sndvv (last [a])"
           apply(rule sym, rule h_path_split3[of "[a]" ds])
           using CD_Def(3) Suc.prems(2)  cdef_def(1)
           by(auto intro: h_path_split3 h_path_split2[of cs] elim: hcycleE)

         have 007: "ds \<noteq> [] \<Longrightarrow> fstvv (hd (ds @ cs)) = sndvv a"
           using CD_Def(3) Suc.prems(2)  cdef_def(1) 008 by auto

         have fst_ds_cs_a:"fstvv (hd ( ds @ cs)) = sndvv a"
           using CD_Def(3) Suc.prems(2) \<open>C \<noteq> [a]\<close> cdef_def(1) 007
           by(cases ds, fastforce intro: hcycleE, auto)

         have 010: "hpath ((fs @ [b]) @ gs)"
           using CD_Def(4) Suc.prems(2)  cdef_def(2) 
           by(auto intro: h_path_split3 elim: hcycleE)

         have 009: "fs \<noteq> [] \<Longrightarrow> sndvv (last (gs @ fs)) = fstvv b"
            using h_path_split3[of fs "[b]"] h_path_split1[of _ gs] 010 by auto

         have fst_gs_fs_a:"sndvv (last ( gs @ fs)) = fstvv b"
           using  hcycle_def[of D] CD_Def(4) Suc.prems(2) False cdef_def(2) False cdef_def(2) 009
           by (cases fs) auto

         have  hcycle_new:"hcycle (ds@cs@gs@fs)"   
           using  fst_ds_cs_a  \<open>C \<noteq> [a]\<close>   hpath_cs_cond hpath_non_empt[of cs]  ab_fstsndvv(1)  
                  fst_gs_fs_a False Nil_is_append_conv hpath_gs_fs_cond \<open>C \<noteq> D\<close>  cdef_def
                  hpath_non_empt[of "gs@fs"] distinctC cdef_def distinctD CD_Def Suc.prems(3)[of C D]
          by (intro hcycleI, simp add: \<open>hpath (ds @ cs @ gs @ fs)\<close>, cases ds, auto) 
 
        have a_extract: "\<Union> ({set C' |C'. C' \<in> CCC }) -{a} = 
                         \<Union> ({set C' |C'. C' \<in> CCC -{C} \<union> {ds@cs}})" 
          apply(subst inter_minus_distr[of "{ds@cs}" "{C}" "CCC"], simp add: cdef_def)
          apply(rule trans, rule subset_big_union_diff[of "ds@cs" C "{a}" "CCC" ], 
                subst set_append_swap)
            using \<open>set (ds @ cs) = set C - {a}\<close> set_append_swap[of cs ds] apply simp
            subgoal using CD_Def(1)  \<open>set (ds @ cs) = set C - {a}\<close> by fast
            using CD_Def(3)   Suc.prems(2)[of "ds@cs"] Suc.prems(3)[of C "ds@cs"]  
                \<open>set (ds @ cs) = set C - {a}\<close> 
                 hcycle_non_empt[of "ds@cs"] cdef_def(1)  CD_Def(1) Diff_iff[of _ "set C" "{a}"]
                 insertCI[of a "set (ds@cs)"]
                 Suc.prems(3)  inter_minus_distr[of "{ds@cs}" "{C}"]  
            by(force, fastforce, blast, simp+)

        have 002:"\<Union> {set B |B. B \<in> CCC - {C} \<union> {ds @ cs} - {D} \<union> {gs @ fs}} =
                  \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {ds @ cs} \<union> {gs @ fs} - {D}}"
          using inter_minus_distr[of "{gs@fs}" ] cdef_def by simp

        have 003: "C' \<in> CCC - {C} \<union> {ds @ cs} \<Longrightarrow> 
                    E \<in> CCC - {C} \<union> {ds @ cs} \<Longrightarrow> C' \<noteq> E \<Longrightarrow> set E \<inter> set C' = {}" for C' E          
          using Suc.prems(3)[of C']  CD_Def(1,3) \<open>set (ds @ cs) = set C - {a}\<close>  
                Suc.prems(3)[of C ] Suc.prems(3)[of "ds@gs" E] 
          by (cases "C' \<in> CCC", cases "E \<in> CCC") force+

        have 004: "gs @ fs \<noteq> D"
          using CD_Def(2)  Diff_insert_absorb \<open>set (fs @ gs) = set D - {b}\<close> by auto 

        have "gs@fs \<noteq> ds@cs" 
          using \<open>hcycle (ds @ cs @ gs @ fs)\<close>  hcycle_def[of "ds @ cs @ gs @ fs"]
                hpath_non_empt by force

        hence 005: "gs @ fs \<notin> CCC - {C} \<union> {ds @ cs}" 
          using \<open>set (fs @ gs) = set D - {b}\<close> CD_Def(2,3) Suc.prems(3)[of D "gs@fs", OF CD_Def(4)]
                \<open>set (fs @ gs) = set D - {b}\<close>[simplified set_append_swap[of fs gs]] 
                hcycle_non_empt[OF  Suc.prems(2)[of "gs@fs"]] 
                hcycle_non_empt[of D, OF  Suc.prems(2), OF CD_Def(4)] 
                mk_disjoint_insert[of b "set D"] by (cases "gs @ fs = D") force+

        have 011: "\<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {ds @ cs}} - {b} =
                   \<Union> {set C' |C'. C' \<in> CCC - {C} \<union> {ds @ cs} \<union> {gs @ fs} - {D}}"
          apply(rule trans, rule subset_big_union_diff[of "gs@fs" D "{b}" "CCC -{C} \<union> {ds@cs}" ])
          using \<open>set (fs @ gs) = set D - {b}\<close>  CD_Def(2) set_append_swap[of gs fs]
                CD_Def \<open>C \<noteq> D\<close>  005 004 003 002 by auto

        have b_extract: "\<Union> ({set C' |C'. C' \<in> CCC -{C} \<union> {ds@cs}}) - {b} = 
             \<Union> ({set C' |C'. C' \<in> (CCC -{C} \<union> {ds@cs}) - {D} \<union>{gs@fs}})"
          using  inter_minus_distr[of "{gs@fs}" "{D}" "CCC -{C} \<union> {ds@cs}"] cdef_def 011 
          by auto

        have 12: "\<Union> ({set C' |C'. C' \<in> (CCC -{C} \<union> {ds@cs}) - {D} \<union>{gs@fs}}) = 
                \<Union> ({set C' |C'. C' \<in> (CCC -{C,D} \<union> {ds@cs, gs@fs})})" 
          using inter_minus_distr[of "{ds@cs}" "{D}" "CCC -{C}"]  Suc(4)[of C D] cdef_def  CD_Def 
                \<open>C \<noteq> D\<close> \<open>set (ds @ cs) = set C - {a}\<close>  by blast

        have 13: "\<Union> ({set C' |C'. C' \<in> (CCC -{C,D} \<union> {ds@cs, gs@fs})}) = 
              \<Union> ({set C' |C'. C' \<in> (CCC -{C,D} \<union> {ds@cs@gs@fs})})"
          using in_union_of_sets_append [of "CCC -{C,D}" "ds@cs" "gs@fs"] by simp
        
        have ab_extracted:"\<Union> ({set C' |C'. C' \<in> CCC }) - {a,b} = 
              \<Union> ({set C' |C'. C' \<in> (CCC -{C,D} \<union> {ds@cs, gs@fs})})"
          apply(rule trans[of _ "\<Union> {set C' |C'. C' \<in> CCC} - {a} -{b}"]) 
          using  "12"  a_extract b_extract by(blast, simp)

        have cardn:"card (FBPs (\<Union> ({set C' |C'. C' \<in> (CCC -{C,D} \<union> {ds@cs, gs@fs})}))) = n"
          using finite_FBPs_of_CCC Suc(5) ab_extracted ab_extract 
                \<open>card (FBPs (\<Union> {set C |C. C \<in> CCC} - {a, b})) = n\<close> by presburger

        have CaDD:"\<And> Ca. Ca \<in> CCC -{C,D} \<union> {ds@cs@gs@fs} \<Longrightarrow> hcycle Ca"
          using Suc(3) hcycle_new by auto

        have 33:"set (ds @ cs @ gs @ fs)  \<subseteq> set C \<union> set D"
          apply rule
          subgoal for x
            apply(cases "x \<in> set ds", simp add: cdef_def)
            apply(cases "x \<in> set cs", simp add: cdef_def)
            apply(cases "x \<in> set gs", simp add: cdef_def)
            apply(cases "x \<in> set ds", auto simp add: cdef_def)
            done
          done
        
        have CCC_disjoint_without_D:
                    " Ca \<in>  CCC -{C,D} \<union> {ds@cs@gs@fs} \<Longrightarrow>
                      Da \<in>  CCC -{C,D} \<union> {ds@cs@gs@fs} \<Longrightarrow> Da \<noteq> Ca \<Longrightarrow> set Da \<inter> set Ca = {}" for Ca Da
            apply(rule disjoint_lists_sublists'
                 [of CCC "{C,D}" "ds@cs@gs@fs" "[]" "\<Union> {set H |H. H \<in> {C, D}}"], simp add: Suc.prems(3),
                 simp add: CD_Def) 
            subgoal
              apply(subst sym[OF empty_set], subst  Un_empty_right)
              apply(rule rev_iffD2[of "(set (ds @ cs @ gs @ fs) \<subseteq> set C \<union> set D)"], rule 33)
              by blast
            using distinctC distinctD by auto
         
        have CC'_ex: " \<exists>CCC'.
                finite CCC' \<and>
                 (\<forall> C\<in> CCC'. hcycle C) \<and>
                (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
                \<Union> {set C |C. C \<in> CCC'} =
                \<Union> ({set C' |C'. C' \<in> CCC -{C,D} \<union> {ds@cs@gs@fs}})
                          - \<Union> (FBPs (\<Union> ({set C' |C'. C' \<in> CCC -{C,D} \<union> {ds@cs@gs@fs}})))"
          apply(rule Suc(1))
          using Suc.prems(1) CaDD CCC_disjoint_without_D  "13" cardn by auto
 
           then show ?thesis 
             using "13" ab_extract ab_extracted by presburger
      qed
    qed
  qed
qed

subsubsection \<open>Generating $H$\<close>

lemma AA_not_in_FBPs: "AA redge \<notin> \<Union> (FBPs E)"
  unfolding FBPs_def isFBP_def by auto

lemma delete_AA_inside_FBPs: "\<Union> (FBPs (E - {AA redge})) = \<Union> (FBPs E)"
  unfolding FBPs_def isFBP_def 
  by (smt (verit, ccfv_SIG) Collect_cong Diff_empty Hedge.disc(9)
 in_insertE_pair insertCI insert_absorb subset_Diff_insert)

lemma disjoint_subs_commute: "B \<inter> C = {} \<Longrightarrow> (A - B) -C = (A - C) - B" for A B C
  by blast

lemma set_diff_eq_cong: "A = B \<Longrightarrow> C = D \<Longrightarrow> A - C = B - D" for A B C D
  by simp

(*The main lemma says that the deletion of all FBPs from a path and a cycle,
results again in a path and some cycles. The following proof is done by reduction
to the deletion of FBPs from a set of cycles. 
We add an additional edge to turn the path into another cycle.
Please see commit f87caf7d09e1cb701a95ce6fb76c0bf80c87880f for the old proof.
*)

theorem path_cycle_decompose_simple_proof:
  assumes "fstvv (hd P) = s"
          "sndvv (last P) = t" "s \<noteq> t"
          "hpath P"
          "distinct P"
          "clean P"
          "finite CCC"
          "\<And> C. C \<in> CCC \<Longrightarrow> hcycle C"
          "\<And> C. C \<in> CCC \<Longrightarrow> clean C"
          "\<And> C D. C \<in> CCC \<Longrightarrow> D \<in> CCC \<Longrightarrow>D \<noteq> C \<Longrightarrow>set D \<inter> set C = {}"
          "FBPs (\<Union> {set C | C. C \<in> CCC}) = {}"
          "\<And> C. C \<in> CCC \<Longrightarrow> set P \<inter> set C = {}"
          "n = card(FBPs (set P \<union> \<Union> {set C| C. C \<in> CCC }))"
          "\<And> e. e \<in> set P \<union> \<Union> {set C| C. C \<in> CCC } \<Longrightarrow> \<not> is_additional_edge e"
  shows "\<exists> P' CCC'.(fstvv (hd P') = s \<and>
                    sndvv (last P') = t \<and> hpath P' \<and> distinct P' \<and>
                    finite CCC' \<and>
                    (\<forall>  C \<in> CCC'. hcycle C) \<and>  
                    (\<forall> C D. C \<in> CCC' \<longrightarrow> D \<in> CCC'\<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {})\<and>
                    (\<forall>  C \<in> CCC'. set P' \<inter> set C = {}) \<and> 
                     set P' \<union> \<Union> {set C| C. C \<in> CCC' }  = 
                         (set P \<union> \<Union> {set C| C. C \<in> CCC }) - 
                             \<Union> (FBPs (set P \<union> \<Union> {set C| C. C \<in> CCC })))"
proof-
  define CCC' where "CCC' = insert ((AA (F (create_edge t s)))#P) CCC"
  have "finite CCC'"
    by (simp add: CCC'_def assms(7))
  moreover have "C \<in> CCC' \<Longrightarrow> hcycle C" for C
  proof(subst (asm) CCC'_def, rule in_insertE[of C "AA (create_edge_residual t s) # P" CCC], goal_cases)
    case 2
    note 1 = 2
    show ?case 
    proof(rule hcycleI)
      show "hpath (AA (F (create_edge t s)) # P)"
        using assms(4)  create_edge make_pair
        by(auto intro!: h_path_append[of "[AA (F (create_edge t s))]" P, simplified single_in_append]
                 intro: hpath_intros(1)[of "AA (F (create_edge t s))"] 
              simp add: assms(1))
      show "fstvv (hd (AA (F (create_edge t s)) # P)) = sndvv (last (AA (F (create_edge t s)) # P))"
        using create_edge make_pair by (simp add: assms(2) assms(4) hpath_non_empt)
      show "distinct (AA (F (create_edge t s)) # P)" 
        using assms(14,5) by force
    qed
  qed (simp add: assms(8))+
  moreover have "C \<in> CCC' \<Longrightarrow> D \<in> CCC' \<Longrightarrow> D \<noteq> C \<Longrightarrow> set D \<inter> set C = {}" for C D
    apply((subst (asm) CCC'_def)+, rule in_insertE_pair[of C _ _ D], simp, simp, simp)
    using assms(10)[of C D] assms(14)[of "AA (F (create_edge t s))", simplified] assms(12)[of D] 
     assms(12)[of C]by auto
  ultimately obtain CCC'a where CCC'a_props:"finite CCC'a"
    "\<And> C. C\<in>CCC'a \<Longrightarrow> hcycle C"
    "\<And> C D. C \<in> CCC'a \<Longrightarrow> D \<in> CCC'a \<Longrightarrow> D \<noteq> C \<Longrightarrow> set D \<inter> set C = {}"
    "\<Union> {set C |C. C \<in> CCC'a} = \<Union> {set C |C. C \<in> CCC'} - \<Union> (FBPs (\<Union> {set C |C. C \<in> CCC'}))"
    by(rule exE[OF cycle_decompose[of CCC']]) force+
  have "\<exists> C \<in> CCC'a. (AA (F (create_edge t s))) \<in> set C"
  proof(rule ccontr, goal_cases)
    case 1
    moreover have " (AA (F (create_edge t s))) \<in> \<Union> {set C |C. C \<in> CCC'} "
      using CCC'_def by fastforce
    ultimately have "(AA (F (create_edge t s))) \<in> \<Union> (FBPs (\<Union> {set C |C. C \<in> CCC'}))" 
      using CCC'a_props(4) by blast
    thus False
      by(auto simp add:FBPs_def isFBP_def)
  qed
  then obtain C where C_prop:"C \<in> CCC'a" "(AA (F (create_edge t s))) \<in> set C" by auto
  then obtain C1 C2 where C1_C2_prop:"C = C1@[AA (F (create_edge t s))]@C2" 
    by(auto simp add: in_set_conv_decomp_first[of _ C])
  define P' where "P' = C2@C1"
  define CCC'' where "CCC'' = CCC'a - {C}"
  show ?thesis
  proof(rule exI[of _ P'], rule exI[of _ CCC''], goal_cases)
    case 1
    have hcycle: "hcycle C" 
      by (simp add: CCC'a_props(2) C_prop(1))
    hence C_prop': "hpath C" "fstvv (hd C) = sndvv (last C)" "distinct C"
   using hcycle_def[of C] by auto
    have "fstvv (hd P') = s" 
      using C1_C2_prop C_prop' assms(3)  h_path_split3[of "C1@[_]" C2]
            create_edge make_pair
      by (cases C2, all \<open>cases C1\<close>) (fastforce simp add: P'_def)+
    moreover have "sndvv (last P') = t"
      using C1_C2_prop C_prop' assms(3)  h_path_split3[of "C1" "[_]@C2"] 
            create_edge make_pair
      by (cases C2, all \<open>cases C1\<close>) (fastforce simp add: P'_def)+
    moreover have "hpath P'"
        using C1_C2_prop C_prop' assms(3)  h_path_split3[of "C1" "[_]@C2"] 
              h_path_split1[of C1 "[_]@C2"]  h_path_split2[of "C1@[_]" "C2"] 
              h_path_append[of C2 C1] create_edge[of t s] 
        by (cases C2, all \<open>cases C1\<close>) (*Takes some time*)
         (fastforce simp add: P'_def vs_to_vertex_pair_pres)+
    moreover have "distinct P'"
      using C1_C2_prop C_prop' by (auto simp add: P'_def)
    moreover have "\<forall>C\<in>CCC''. hcycle C"
      using CCC''_def CCC'a_props(2) by blast
    moreover have "finite CCC''"
      by (simp add: CCC''_def CCC'a_props(1))
    moreover have "\<forall>C. C \<in> CCC'' \<longrightarrow> (\<forall>D. D \<in> CCC'' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {})"
      by (simp add: CCC''_def CCC'a_props(3))
    moreover have "\<forall>C\<in>CCC''. set P' \<inter> set C = {}"
    proof(rule, goal_cases)
      case (1 D)
      have "set C \<inter> set D = {}"
        using "1" CCC''_def CCC'a_props(3) C_prop(1) by blast
      then show ?case using C1_C2_prop
        by(auto simp add: P'_def)
    qed
    moreover have " set P' \<union> \<Union> {set C |C. C \<in> CCC''} =
    set P \<union> \<Union> {set C |C. C \<in> CCC} - \<Union> (FBPs (set P \<union> \<Union> {set C |C. C \<in> CCC}))"
    proof-
      have "set P \<union> \<Union> {set C |C. C \<in> CCC} - \<Union> (FBPs (set P \<union> \<Union> {set C |C. C \<in> CCC})) =
           (set (AA (F (create_edge t s)) # P) \<union> \<Union> {set C |C. C \<in> CCC} 
              - \<Union> (FBPs (set (AA (F (create_edge t s)) # P) \<union> \<Union> {set C |C. C \<in> CCC}))) - {AA (F (create_edge t s))}"
        apply(subst disjoint_subs_commute)
        using AA_not_in_FBPs apply blast
        apply(subst (2) Un_Diff)
        apply(rule set_diff_eq_cong)
        apply(rule set_union_eq_cong)
        using assms(14)[of "AA (F (create_edge t s))", simplified] apply auto[2]
        apply(subst (2) sym[OF delete_AA_inside_FBPs[of _ "F (create_edge t s)"]])
        using assms(14)[of "AA (F (create_edge t s))", simplified]
        by (auto intro!: arg_cong[of _ _  Union] arg_cong[of _ _  FBPs])
      also have "... = (\<Union> {set C |C. C \<in> CCC'} - \<Union> (FBPs (\<Union> {set C |C. C \<in> CCC'}))) 
                     - {AA (F (create_edge t s))}"
        by(auto intro!:  set_diff_eq_cong arg_cong[of _ _  Union] arg_cong[of _ _  FBPs]
              simp add: CCC'_def )
      also have "... = \<Union> {set C |C. C \<in> CCC'a}- {AA (F (create_edge t s))} "
        using CCC'a_props(4) by presburger
      also have "... = (insert (AA (F (create_edge t s))) (set P') \<union> \<Union> {set C |C. C \<in> CCC''}) - {AA (F (create_edge t s))}"
      proof-
        have "\<Union> {set C |C. C \<in> CCC'a} =
            insert (AA (create_edge_residual t s)) (set (C2 @ C1)) \<union> \<Union> {set Ca |Ca. Ca \<in> CCC'a - {C}}"
          using C1_C2_prop C_prop by auto force
        thus ?thesis
          by(auto intro: set_diff_eq_cong simp add: P'_def CCC''_def)
      qed
      also have "... = (set P') \<union> \<Union> {set C |C. C \<in> CCC''}" 
        using C1_C2_prop C_prop'(3)  CCC''_def CCC'a_props(3)[OF  C_prop(1)] 
        by (auto simp add:  P'_def CCC'_def)
      finally show ?thesis by simp
    qed       
    ultimately show ?case by simp
  qed
qed

subsection \<open>$hpaths$ and $augpaths$\<close>

text \<open>In the informal proof, the graph $H$ is constructed from the same type 
   of edges as the $s$-$t$-path $P$ and the augmenting cycle $C$.
For the formal proof, however, we had to distinguish among edges according to their origin.
This resulted in wrapping residual arcs by $PP$ and $CC$.
Now, we have to bridge the gap between $Hedge$, $Redge$ and the different notions
 of paths/cycles based on them.
\<close>

text \<open>First we observe that by switching to arcs related the graph $H$ (Hedges), 
connectivity properties will be preserved.\<close>

lemma augpath_to_hpath_PP: 
  assumes "augpath f P"
  shows "hpath (map PP P)"
  apply(induction rule: augpath_induct[OF assms])
  by (simp add: hpath_intros(1))
     (metis (no_types, lifting) fstvv.simps(1) hpath_simps list.simps(9) sndvv.simps(1))

lemma augpath_to_hpath_CC: 
  assumes "augpath f P"
  shows" hpath (map CC P)"
  apply(induction rule: augpath_induct[OF assms])
  by (simp add: hpath_intros(1))
     (metis (no_types, lifting) fstvv.simps(2) hpath_simps list.simps(9) sndvv.simps(2))

text \<open>After switching to Hedges, as well $P$ as $C$ will be clean paths.
Intuitively, that's trivial: $P$ contains just edges from $P$ and analogously, so does $C$.\<close>

lemma pure_PP_clean: "clean (map PP xs)"
proof(rule ccontr)
  assume "\<not> clean (map PP xs)"
  then obtain x y where xy_def: "x \<in> set (map PP xs)" "y \<in> set (map PP xs)" "isFBP x y" 
    unfolding clean_def by auto
  obtain a b where "x = PP a" "y = PP b"
    by (meson in_set_map xy_def(1) xy_def(2))
  thus False using xy_def(3) unfolding isFBP_def by simp
qed

lemma pure_CC_clean: "clean (map CC xs)"
proof(rule ccontr)
  assume "\<not> clean (map CC xs)"
  then obtain x y where xy_def: "x \<in> set (map CC xs)" "y \<in> set (map CC xs)" "isFBP x y" 
    unfolding clean_def by auto
  obtain a b where "x = CC a" "y = CC b"
    by (meson in_set_map xy_def(1) xy_def(2))
  thus False using xy_def(3) unfolding isFBP_def by simp
qed

lemma pure_CC_pure_PP_disjoint: "set (map CC xs) \<inter> set (map PP ys) = {}"
proof(rule ccontr)
  assume "set (map CC xs) \<inter> set (map PP ys) \<noteq> {}"
  then obtain x where xy_def: "x \<in> set (map CC xs)" "x \<in> set (map PP ys)" 
    by auto
  obtain a b where "x = CC a" "x = PP b"
    by (meson in_set_map xy_def(1) xy_def(2))
  thus False by simp
qed

text \<open>Additionally, costs do not change by wrapping with $CC$s and $PP$s.\<close>

lemma distinct_CC_sum:"distinct P \<Longrightarrow> sum \<cc> (set P) = sum cc (set (map CC P))"
proof(induction P)
  case (Cons a P)
  have 1:" set (map CC [a]) \<inter> set (map CC P)= {}"
    using distinct_map Cons.prems
    by (auto simp add: inj_on_def)
  have "sum \<cc> (set (a # P)) = 
       sum \<cc> (set P \<union> {a})" by simp
  also have "... = sum \<cc> (set P) +sum \<cc> {a}"
    using Cons(2) by simp
  also have "... = sum cc (set (map CC P)) +sum cc {CC a}"
    using Cons by simp
  also have "... = sum cc (set (map CC P) \<union> {CC a})"
    using 1 by simp
  finally show ?case  by simp
qed simp

lemma distinct_PP_sum: "distinct P \<Longrightarrow> sum \<cc> (set P) = sum cc (set (map PP P))"
proof(induction P)
  case (Cons a P)
  have 1:" set (map PP [a]) \<inter> set (map PP P)= {}"
    using  distinct_map  Cons.prems
    by (auto simp add: inj_on_def)
  have "sum \<cc> (set (a # P)) = 
       sum \<cc> (set P \<union> {a})" by simp
  also have "... = sum \<cc> (set P) +sum \<cc> {a}"
    using Cons by simp
  also have "... = sum cc (set (map PP P)) +sum cc {PP a}"
    using Cons by simp
  also have "... = sum cc (set (map PP P) \<union> {PP a})"
    using 1 by simp
  finally show ?case by simp
qed simp

text \<open>For distinct paths, costs are reduced to the notion of costs already used
 for augmenting paths.\<close>

lemma hpath_to_prepath_costs: 
"distinct C \<Longrightarrow> C = map to_redge C'  \<Longrightarrow>(\<Sum> e \<in> set C'. cc e) =  \<CC> C"
proof(induction C arbitrary: C')
  case (Cons a C)
  then show ?case 
    unfolding \<CC>_def
    apply(cases C', simp) 
    subgoal for b D 
      apply(simp, subst sum.insert_remove, simp)
      apply(subst single_diff_remove)
      using distinct_map[of to_redge D] apply blast
      using cc.simps to_redge.elims by metis
    done
qed (auto simp add: \<CC>_def)

text \<open>Unfortunately, the informal proof neglects a detail: After deleting forward-backward pairs,
we obtain a distinct $s$-$t$-path and distinct cycles.
However, distinctness refers to $Hedge$s not to the desired $Redge$s.
It might be, that the corresponding $prepath$ consisting of residual
 arcs is not distinct although the $hpath$ is. This little issue is due to the wrapping constructors.
\<close>

text \<open>First we show how to generate an equivalent set of $precycle$s from an $hcycle$.
The important property is that costs are preserved.
\<close>

lemma hcycle_to_augcycles:
  assumes "C = map to_redge C'"
          "hcycle C'"
          "set C \<subseteq> \<EE>"
          "length C = n"
    shows "\<exists> CCC. (\<forall> D \<in> set CCC. precycle D) \<and> 
                  (\<Sum> e \<in> set C'. cc e) = foldr (\<lambda> D costs. \<CC> D + costs) CCC (0::real) \<and>
                   set C = \<Union>{set D| D. D \<in> set CCC}"
  using assms 
proof(induction arbitrary: C C' rule: less_induct)
  case (less n)
  hence 0:"prepath (map to_redge C')"
    unfolding hcycle_def using hpath_to_prepath[of C'] by auto
  have 1:"C = map to_redge (map CC C)" 
    by(subst map_map, rule trans[of _ "map id C"], simp, 
       metis comp_apply eq_id_iff to_redge.simps(2))
  then show ?case
  proof(cases "distinct C")
    case True
    have "precycle C"
      unfolding precycle_def
      using 0 less True hpath_first_node[of C'] unfolding hcycle_def 
      using hpath_last_node by force  
    hence "(\<forall> D \<in> set [C]. precycle D) \<and> 
                (\<Sum> e \<in> set C'. cc e) = foldr (\<lambda> D costs. \<CC> D + costs) [C] (0::real) \<and>
                set C = \<Union>{set D| D. D \<in> set [C]}"
      by simp (rule hpath_to_prepath_costs, simp add: True, simp add: less)
    then show ?thesis by meson
  next
    case False
    then obtain C1 x C2 C3 where C1_x_C2_C3_Def: "C = C1@[x]@C2@[x]@C3" 
      using list_triple_split_mid_distinct by blast
    then obtain C1' Ca1 where C1'_def: "C1 = map to_redge C1'"
                              "[x]@C2@[x]@C3 = map to_redge Ca1"
                              "C' = C1'@Ca1"
      using map_split_exists[of to_redge C' C1 "[x]@C2@[x]@C3"] less(2) 
      by metis
    then obtain a Ca2 where a_def: "x = to_redge a"
                              "C2@[x]@C3 = map to_redge Ca2"
                              "Ca1 = [a]@Ca2"
      using map_split_exists[of to_redge Ca1 "[x]" "C2 @ [x] @ C3"] by auto
    moreover then obtain C2' Ca3 where C3'_def: "C2 = map to_redge C2'"
                              "[x]@C3 = map to_redge Ca3"
                              "Ca2 =C2'@Ca3"
      using map_split_exists[of to_redge Ca2 "C2" "[x] @ C3"] by metis
    moreover then obtain b C3' where b_C3'_def: "x = to_redge b"
                              "C3 = map to_redge C3'"
                              "Ca3 =[b]@C3'"
      using map_split_exists[of to_redge Ca3 "[x]" "C3"] by auto

    ultimately have C'_decomposed: "map to_redge C1' = C1" "to_redge a = x" 
             "map to_redge C2' = C2"  "to_redge b = x"
             "map to_redge C3' = C3"  "C1'@[a]@C2'@[b]@C3' = C'"  
      using C1'_def(1)  b_C3'_def(2) 
          by (force, simp add: a_def(1))
             (force simp add: C3'_def(1) b_C3'_def(1) C1'_def C3'_def a_def b_C3'_def)+
    have ab_same:"fstvv a = fstvv b" "sndvv a = sndvv b"
      by (metis a_def(1) b_C3'_def(1) fstvv_fstv sndvv_sndv)+

    have 000: "C3' \<noteq> [] \<Longrightarrow> hpath C3'"
          using h_path_split2[of "C1'@[a]@C2'@[b]" C3']
                C1'_def(3) C3'_def(3)  a_def(3) b_C3'_def(3) less.prems(2) hcycle_def[of C'] by simp

    note split_props = h_path_split3[of "C1'@[a]@C2'@[b]" C3']C1'_def(3) C3'_def(3)  a_def(3)
                           b_C3'_def(3) less.prems(2) hcycle_def[of C'] ab_same 

    have 001: " C3' \<noteq> [] \<Longrightarrow> sndvv (last [a]) = fstvv (hd C3')"
      using split_props by simp

    have 002:"C3' \<noteq> [] \<Longrightarrow>  hpath ([a] @ C3')"
      using hpath_intros(1) 000 001 by(fastforce intro: h_path_append)

    have 003: "C1' \<noteq> [] \<Longrightarrow> hpath C1'"
      using C1'_def(3) h_path_split1 hcycle_def less.prems(2) by blast

    have 004: "C1' \<noteq> [] \<Longrightarrow> sndvv (last C1') = fstvv (hd [a])"
      using h_path_split3[of "C1'" "[a]@C2'@[b]@C3'"] split_props
      by simp

    have 005:"C1' \<noteq> [] \<Longrightarrow> hpath (C1' @ [a])"
      using hpath_intros(1) 003 004 by (fastforce intro: h_path_append)

    have 006: "C1' \<noteq> [] \<Longrightarrow> C3' \<noteq> [] \<Longrightarrow> sndvv (last C1') = fstvv (hd ([a] @ C3'))"
      using h_path_split3[of "C1'" "[a]@C2'@[b]@C3'"] split_props
      by simp

    have 007: "C1' \<noteq> [] \<Longrightarrow> C3'\<noteq> [] \<Longrightarrow> hpath (C1' @ [a] @ C3')"
      using  005 h_path_split1[of C1'] 002  006 by (auto intro: h_path_append)
 
    have 008: " hpath (C1' @ [a] @ C3')"
      using hpath_intros(1) using 002 007 005  by (cases C1')auto
          
    have 009:"fstvv (hd (C1' @ [a] @ C3')) = sndvv (last (C1' @ [a] @ C3'))"
      using split_props C1'_def(3) C3'_def(3) a_def(3) b_C3'_def(3) hcycle_def less.prems(2)
            hcycle_def 
      by (cases C1') auto
           
    have hcycle_new1:"hcycle (C1'@[a]@C3')"
          using 008 009
          unfolding hcycle_def
          using C'_decomposed  hcycle_def[of C'] less.prems(2) by auto

    have 010: "fstvv (hd (C2' @ [b])) = sndvv (last (C2' @ [b]))"
      using  002 009 h_path_split3[of  "C1'@[a]" "C2'@[b]@C3'"]  split_props 
      by (cases C2') auto

    have 011: "hpath (C2' @ [b])"
      using hpath_intros(1) C'_decomposed(6)   h_path_split1[of "C2' @ [b]" C3']
            h_path_split2[of "C1' @ [a]" "C2' @ [b] @ C3'"] hcycle_def[of  C'] less.prems(2)
      by(cases C2') auto
     
    have  hcycle_new2:"hcycle (C2'@[b])"
          unfolding hcycle_def
          using 011  010  C'_decomposed(6) hcycle_def[of C'] less.prems(2) 
          by auto
  
    have 012: "sum cc (set C') = sum cc (set (C1' @ [a] @ C3') \<union> set (C2' @ [b]))"
              apply(subst arg_cong[of " set C'" "set (C1' @ [a] @ C3') \<union> set (C2' @ [b])"
                                   "sum cc"])
              using C'_decomposed(6) by auto

    have sum_C'_split:"(\<Sum> e \<in> set C'. cc e)  = 
             (\<Sum> e \<in> set (C1' @ [a] @ C3'). cc e) + (\<Sum> e \<in> set (C2' @ [b]). cc e)"
          apply(rule trans) defer
          apply(rule sum.union_disjoint[of "set (C1' @ [a] @ C3')" "set (C2' @ [b])"])
          using less(3) unfolding hcycle_def
          using C'_decomposed(6) 012 by auto

     have length_new1:"length (C1 @ [x] @ C3) <  n" 
          using C1_x_C2_C3_Def less by auto

     have map_new1:"map to_redge (C1' @ [a] @ C3') = C1@[x]@C3"
          by (simp add: C1'_def(1) a_def(1) b_C3'_def(2))

     have " set (C1 @ [x] @ C3) \<subseteq> \<EE>"
          using C1_x_C2_C3_Def less by simp
     
     then obtain CCC1 where CCC1_def:"(\<forall> D \<in> set CCC1. precycle D)"
                "(\<Sum> e \<in> set (C1' @ [a] @ C3'). cc e) = foldr (\<lambda> D costs. \<CC> D + costs) CCC1 (0::real)"
                "set (C1@[x]@C3) = \<Union>{set D| D. D \<in> set CCC1}"
          using less(1)[of "length (C1 @ [x] @ C3)" " C1@[x]@C3" "C1' @ [a] @ C3'"]
               hcycle_new1 length_new1 map_new1 by fastforce

      have length_new2:"length (C2@[x]) <  n" 
          using C1_x_C2_C3_Def less by auto

      have map_new2:"map to_redge (C2'@[b]) = C2@[x]"
          by (simp add: C3'_def(1) b_C3'_def(1))

      have " set (C2@[x]) \<subseteq> \<EE>"
          using C1_x_C2_C3_Def less by simp
     
      then obtain CCC2 where CCC2_def:"(\<forall> D \<in> set CCC2. precycle D)"
                "(\<Sum> e \<in> set (C2'@[b]). cc e) = foldr (\<lambda> D costs. \<CC> D + costs) CCC2 (0::real)"
                "set (C2@[x]) = \<Union>{set D| D. D \<in> set CCC2}"
          using less(1)[of "length (C2@[x])" " C2@[x]" "C2'@[b]"]
               hcycle_new2 length_new2 map_new2 by fastforce

      hence "(\<forall> D \<in> set (CCC1@CCC2). precycle D)"
             using CCC2_def CCC1_def by auto
      moreover have "(\<Sum> e \<in> set C'. cc e) = foldr (\<lambda> D costs. \<CC> D + costs) (CCC1@CCC2) (0::real)"
            apply(subst sum_C'_split, subst map_sum_split)
            using CCC1_def CCC2_def by auto
      moreover have 0013:"set ((C1 @ [x] @ C3) @ C2 @ [x]) = \<Union> {set D |D. D \<in> set (CCC1 @ CCC2)}"
            apply(subst set_append[of "(C1 @ [x] @ C3)" "C2 @ [x]"])
            using C1_x_C2_C3_Def CCC1_def(3) CCC2_def by auto
      moreover have  "set C = \<Union>{set D| D. D \<in> set (CCC1@CCC2)}"
            using C1_x_C2_C3_Def 0013 by auto
     ultimately show ?thesis by blast
  qed
qed

text \<open>Similarly, an $s$-$t$-path based on $Hedge$s can be transformed to
a path and some cycles consisting of $Redge$s.
Once again, costs are preserved.
\<close>

lemma distinct_hpath_to_distinct_augpath_and_augcycles:
  assumes "P = map to_redge P'"
          "hpath P'"
          "distinct P'"
          "set P \<subseteq> \<EE>"
          "length P = n"
          "fstvv (hd P') = s"
          "sndvv (last P') = t"
    shows "\<exists> PP CCC. (\<forall> D \<in> set CCC. precycle D) \<and> prepath PP \<and> distinct PP \<and> 
                (\<Sum> e \<in> set P'. cc e) = \<CC> PP + foldr (\<lambda> D costs. \<CC> D + costs) CCC (0::real) \<and>
                set P = set PP \<union> \<Union>{set D| D. D \<in> set CCC} \<and> fstv (hd PP) = s \<and> sndv (last PP) = t"
  using assms proof(induction arbitrary: P P' rule: less_induct)
  case (less n)
  hence 0:"prepath (map to_redge P')" 
    unfolding hcycle_def using hpath_to_prepath[of P'] by auto
  then show ?case
  proof(cases "distinct P")
    case True
    have  1:"fstv (hd P) = s"
          "sndv (last P) = t" 
      using hpath_first_node less.prems(1) less.prems(2) less.prems(6) hpath_last_node   less.prems(7)
      by force+
    have "prepath P"
      using 0 less by simp
    hence "(\<forall> D \<in> set []. precycle D)" "prepath P" "distinct P" 
                "(\<Sum> e \<in> set P'. cc e) = \<CC> P + foldr (\<lambda> D costs. \<CC> D + costs) [] (0::real)"
                "set P = set P \<union> \<Union>{set D| D. D \<in> set []}" "fstv (hd P) = s" "sndv (last P) = t"
      using True  hpath_to_prepath_costs less 1 0 by auto
    then show ?thesis by blast
  next
    case False
    then obtain P1 x P2 P3 where P1_x_P2_P3_Def: "P = P1@[x]@P2@[x]@P3"
                                                 "distinct P2" "x \<notin> set P2"
      using list_triple_split_mid_distinct by blast
    then obtain P1' Pa1 where P1'_def: "P1 = map to_redge P1'"
                              "[x]@P2@[x]@P3 = map to_redge Pa1"
                              "P' = P1'@Pa1"
      using map_split_exists[of to_redge P' P1 "[x]@P2@[x]@P3"] less(2) 
      by metis
    then obtain a Pa2 where a_def: "x = to_redge a"
                              "P2@[x]@P3 = map to_redge Pa2"
                              "Pa1 = [a]@Pa2"
      using map_split_exists[of to_redge Pa1 "[x]" "P2 @ [x] @ P3"] by auto
    moreover then obtain P2' Pa3 where P3'_def: "P2 = map to_redge P2'"
                              "[x]@P3 = map to_redge Pa3"
                              "Pa2 =P2'@Pa3"
      using map_split_exists[of to_redge Pa2 "P2" "[x] @ P3"] by metis
    moreover then obtain b P3' where b_P3'_def: "x = to_redge b"
                              "P3 = map to_redge P3'"
                              "Pa3 =[b]@P3'"
      using map_split_exists[of to_redge Pa3 "[x]" "P3"] by auto

    ultimately have P'_decomposed: "map to_redge P1' = P1" "to_redge a = x" 
             "map to_redge P2' = P2"  "to_redge b = x"
             "map to_redge P3' = P3"  "P1'@[a]@P2'@[b]@P3' = P'"  
      using b_P3'_def P1'_def P3'_def a_def b_P3'_def by auto

    have ab_same: "fstvv a = fstvv b" "sndvv a = sndvv b"
      by(metis a_def(1) b_P3'_def(1) fstvv_fstv  a_def(1) b_P3'_def(1) sndvv_sndv)+

    have 000:"P3' \<noteq> [] \<Longrightarrow> hpath P3'"
      using h_path_split2[of "P1'@[a]@P2'@[b]" "P3'"] less(3) P'_decomposed by simp

    have 001: "P3' \<noteq> [] \<Longrightarrow> sndvv (last [a]) = fstvv (hd P3')"
      using h_path_split3[of "P1'@[a]@P2'@[b]" "P3'"] less(3) P'_decomposed ab_same by simp

    have 002:"P3' \<noteq> [] \<Longrightarrow>  hpath ([a] @ P3')"
      using 000 001 hpath_intros(1)  by(fastforce intro!: h_path_append)

    have 003: "P1' \<noteq> [] \<Longrightarrow> sndvv (last P1') = fstvv (hd [a])"
      using h_path_split3[of "P1'" "[a]@P2'@[b]@P3'"] less(3) P'_decomposed ab_same by simp

    have 004: "P1' \<noteq> [] \<Longrightarrow> hpath P1'"
      using h_path_split1[of "P1'" "[a]@P2'@[b]@P3'"] less(3) P'_decomposed ab_same by simp

    have 005:"P1' \<noteq> [] \<Longrightarrow> hpath (P1' @ [a])"
      using 003 004 hpath_intros(1)  by(fastforce intro!: h_path_append)

    have 007: "P1' \<noteq> [] \<Longrightarrow> P3' \<noteq> [] \<Longrightarrow> sndvv (last P1') = fstvv (hd ([a] @ P3'))"
      using 005 h_path_split3 hd_append list.distinct(1) by force

    have 008: "P1' \<noteq> []  \<Longrightarrow> P3' \<noteq> [] \<Longrightarrow> hpath (P1' @ [a] @ P3')"
      using 005 h_path_split1  002  007 by (auto intro!:  h_path_append)

    have 006:" hpath (P1' @ [a] @ P3')"
     using hpath_intros(1) 002 005 008 by(cases P1') auto

   have "fstv (hd (P1@[x]@P3)) = s"
     using  hpath_first_node[of P'] less.prems(1) P1_x_P2_P3_Def(1) less.prems(2) less.prems(6)
     by (cases P1) auto

   have "sndv (last (P1@[x]@P3)) = t" 
     using  hpath_last_node[of P'] less.prems(1) P1_x_P2_P3_Def(1) less.prems(2) less.prems(7)
     by force

   have aa:"map to_redge (P2' @ [b]) = P2 @ [x]" 
     by (simp add: P3'_def(1) b_P3'_def(1))

   have bb:"distinct (P2 @[x])" 
     by (simp add: P1_x_P2_P3_Def(2) P1_x_P2_P3_Def(3))

   have 007: "hpath (P2' @ [b])"
     using P'_decomposed(6)  h_path_split1[of "P1' @ [a] @ P2' @ [b]" "P3'"]
           h_path_split2[of "P1' @ [a]" "P2' @ [b]"]   less.prems(2) 
     by simp

   have 008: "fstvv (hd (P2' @ [b])) = sndvv (last (P2' @ [b]))"
     using P'_decomposed(6) less.prems(2) h_path_split3[of "P1' @ [a]" "P2' @ [b]@P3'"] 
           ab_same  hd_append2[of "P2' @ [b]" "P3'"] last_snoc by simp

   have  hcycle_new2:"hcycle (P2'@[b])"
     unfolding hcycle_def
     using 007 distinct_map[of to_redge "P2'@[b]"] aa bb 008  by auto

   have 010: "sum cc (set P') = sum cc (set (P1' @ [a] @ P3') \<union> set (P2' @ [b]))"
          apply(subst arg_cong[of " set P'" "set (P1' @ [a] @ P3') \<union> set (P2' @ [b])"
                                   "sum cc"])
          using P'_decomposed(6) by auto

   have sum_C'_split:"(\<Sum> e \<in> set P'. cc e)  = 
             (\<Sum> e \<in> set (P1' @ [a] @ P3'). cc e) + (\<Sum> e \<in> set (P2' @ [b]). cc e)"
          apply(rule trans) defer
          apply(rule sum.union_disjoint)
          using less(4)  P'_decomposed(6) 010 by auto

   have length_new1:"length (P1 @ [x] @ P3) <  n" 
    using P1_x_P2_P3_Def less by auto

   have map_new1:"map to_redge (P1' @ [a] @ P3') = P1@[x]@P3"
     by (simp add: P1'_def(1) a_def(1) b_P3'_def(2))

   have " set (P1 @ [x] @ P3) \<subseteq> \<EE>"
     using P1_x_P2_P3_Def less by simp

   have 011: "fstvv (hd (P1' @ [a] @ P3')) = s"
     using \<open>fstv (hd (P1 @ [x] @ P3)) = s\<close> \<open>hpath (P1' @ [a] @ P3')\<close> hpath_first_node map_new1 
     by force

   have 012: "sndvv (last (P1' @ [a] @ P3')) = t"
     using \<open>hpath (P1' @ [a] @ P3')\<close> \<open>sndv (last (P1 @ [x] @ P3)) = t\<close>  
           hpath_last_node map_new1 by force

   have 013: "distinct (P1' @ [a] @ P3')"
     using  P'_decomposed(6)  less.prems(3) by auto

   have "\<exists>PP CCC. Ball (set CCC) precycle \<and> prepath PP \<and> distinct PP \<and>
                  sum cc (set (P1' @ [a] @ P3')) = \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 \<and>
                  set (P1 @ [x] @ P3) = set PP \<union> \<Union> {set D |D. D \<in> set CCC} \<and>
                  fstv (hd PP) = s \<and> sndv (last PP) = t"
     apply(rule less(1)[of "length (P1 @ [x] @ P3)" " P1@[x]@P3" "P1' @ [a] @ P3'"])
     using length_new1  map_new1  \<open>hpath (P1' @ [a] @ P3')\<close>  013 \<open>set (P1 @ [x] @ P3) \<subseteq> \<EE>\<close>  011 012 
     by auto

   then obtain PP CCC1 where PP_CCC1_def:
     "(\<forall> D \<in> set CCC1. precycle D)" "prepath PP" "distinct PP"  "fstv (hd PP) = s"
     "(\<Sum> e \<in> set (P1' @ [a] @ P3'). cc e) = \<CC> PP +  foldr (\<lambda> D costs. \<CC> D + costs) CCC1 (0::real)"
     "set (P1 @ [x] @ P3) = set PP \<union> \<Union>{set D| D. D \<in> set CCC1}"  "sndv (last PP) = t"                
          by auto

    have map_new2:"map to_redge (P2'@[b]) = P2@[x]"
       by (simp add: P3'_def(1) b_P3'_def(1))

    have " set (P2@[x]) \<subseteq> \<EE>"
          using P1_x_P2_P3_Def less by simp

    have "\<exists> CCC2. (\<forall> D \<in> set CCC2. precycle D)\<and>
                  (\<Sum> e \<in> set (P2'@[b]). cc e) = foldr (\<lambda> D costs. \<CC> D + costs) CCC2 (0::real) \<and>
                   set (P2@[x]) = \<Union>{set D| D. D \<in> set CCC2}"
      using map_new2 hcycle_new2  \<open>set (P2 @ [x]) \<subseteq> \<EE>\<close> 
      by ( intro hcycle_to_augcycles, auto)

    then  obtain CCC2 where CCC2_def:"(\<forall> D \<in> set CCC2. precycle D)"
                "(\<Sum> e \<in> set (P2'@[b]). cc e) = foldr (\<lambda> D costs. \<CC> D + costs) CCC2 (0::real)"
                "set (P2@[x]) = \<Union>{set D| D. D \<in> set CCC2}" 
      by auto

    hence "(\<forall> D \<in> set (CCC1@CCC2). precycle D)" 
      using CCC2_def PP_CCC1_def by auto

    moreover have 
          "(\<Sum> e \<in> set P'. cc e) = \<CC> PP + foldr (\<lambda> D costs. \<CC> D + costs) (CCC1@CCC2) (0::real)"
      using sum_C'_split  PP_CCC1_def(5) map_sum_split[of _ CCC1 CCC2] CCC2_def(2) 
      by auto

    moreover have
          "set P = set PP \<union> \<Union>{set D| D. D \<in> set (CCC1@CCC2)}" 
      using  P1_x_P2_P3_Def PP_CCC1_def(6) CCC2_def(3) by auto

    ultimately show ?thesis using PP_CCC1_def by blast
  qed
qed

subsection \<open>The final Theorem\<close>

text \<open>Let us first precisely define the meanings of $s$-$t$-paths and
      minimum $s$-$t$-paths. We require distinctness.\<close>

definition "is_s_t_path f s t P = (augpath f P \<and> set P \<subseteq> \<EE> \<and> 
                                   fstv (hd P) = s \<and> sndv (last P) = t \<and> distinct P)"

text \<open>The existence of a path implies the existence of a distinct path.\<close>

lemma there_is_s_t_path:
  assumes "augpath f P" "fstv (hd P) = s" "sndv (last P) = t"
          "l = length P"
  obtains Q where "fstv (hd Q) = s" "sndv (last Q) = t" "distinct Q" "set Q \<subseteq> set P"
                        "augpath f Q"
 using assms
proof(induction l arbitrary: P thesis rule : less_induct)
  case (less l)
  show ?case 
  proof (cases "distinct P")
    case True
    show ?thesis 
      using less(3,4,5,6) True
      by (auto intro: less(2)[of P] 
            simp add: is_s_t_path_def)
  next
    case False
    then obtain e cs1 cs2 cs3 where cs_split:"P = cs1@[e]@cs2@[e]@cs3"
      using not_distinct_decomp by blast
      have augpath:"local.augpath f (cs1 @ [e] @ cs3)" 
        using augpath_split1[of f "cs1" "[e]@cs2@[e]@cs3"] cs_split less.prems(2)
              augpath_split2[of f "cs1@[e]@cs2" "[e]@cs3"] augpath_split3[of f "cs1@[e]@cs2" "[e]@cs3"] 
              augpath_split3[of f "cs1" "[e]@cs2@[e]@cs3"]
        by (cases cs1)  (fastforce intro: augpath_app)+
      have s_src: "fstv (hd (cs1 @ [e] @ cs3)) = s" 
        using cs_split less.prems(3) 
        by(cases cs1) auto
      have t_tgt: "sndv (last (cs1 @ [e] @ cs3)) = t" 
        using cs_split less.prems(4) by simp
      obtain Q where "fstv (hd Q) = s" "sndv (last Q) = t" "distinct Q" 
                      "set Q \<subseteq> set (cs1 @ [e] @ cs3)" "local.augpath f Q"
        apply(rule less(1)[where P2 = "cs1 @ [e] @ cs3"])
        using augpath  s_src t_tgt  less(5)  False  cs_split  less(4,6) augpath s_src t_tgt
        by auto
      then show ?thesis
        using cs_split by (auto intro!: less(2)[of Q])
    qed
  qed


text \<open>An $s$-$t$-path is optimum iff there is no better $s$-$t$-path.\<close>

definition "is_min_path f s t P = (is_s_t_path f s t P  \<and>
                                   (\<forall> P'. is_s_t_path f s t P' \<longrightarrow> \<CC> P \<le> \<CC> P'))"

text \<open>Due to distinctness, there is always a distinct minimum cost path.\<close>

lemma there_is_min_path:
  assumes  "is_s_t_path f s t P"
  obtains Q where "is_min_path f s t Q"
proof-
  have finite_number_of_paths:"finite {P . is_s_t_path f s t P}" 
    apply(rule finite_subset[of _ "{P. set P \<subseteq> \<EE> \<and> distinct P}"], force simp add: is_s_t_path_def )
    apply(rule finite_subset[rotated], rule finite_lists_length_le[OF finite_\<EE>, of "card \<EE>"])
    using double_occur_non_dist finite_\<EE> by fastforce
  define minc where "minc = Min {\<CC> P | P . is_s_t_path f s t P}"
  have "minc \<in> {\<CC> P | P . is_s_t_path f s t P}"
    apply(subst minc_def, rule linorder_class.Min_in)
    using finite_number_of_paths assms(1) by auto
  then obtain Q where "\<CC> Q = minc" "is_s_t_path f s t Q"
    by auto
  moreover have "\<And>P'. is_s_t_path f s t Q \<Longrightarrow> minc = \<CC> Q \<Longrightarrow> is_s_t_path f s t P' \<Longrightarrow> \<CC> Q \<le> \<CC> P'"
  proof(goal_cases)
    case (1 P')
    show ?case 
      apply(subst sym[OF 1(2)])
      using  finite_number_of_paths 1(3)
      by (auto intro: linorder_class.Min_le simp add: minc_def)
  qed
  ultimately have "is_min_path f s t Q"
    by(auto simp add: is_min_path_def)
  thus ?thesis
    using that by auto
qed

text \<open>Finally, we can show Theorem 9.11 from the textbook by Korte and Vygen.
We assume source $s$ and target $t$ to be distinct. 
A flow $f$ optimum for the current balance $b$ is fixed.
Let then $P$ be an $s$-$t$-path of minimum costs. After augmenting with $\gamma$ below residual capacity, 
we obtain a flow $f'$ being optimum for modified balances $b'$.
$b'(s) = b(s) + \gamma$ and $b'(t) = b(t) - \gamma$, i.e. both the supply by $s$ and the demand at $t$ have to be increased.
\<close>

theorem path_aug_opt_pres:
  assumes "s \<noteq> t"
          "is_Opt b f "
          "\<gamma> \<le> Rcap f (set P)"
          " 0 \<le> \<gamma>"
          "is_min_path f s t P"
    and    f'_def: "f' = augment_edges f \<gamma> P"         
    and    b'_def: "b' = (\<lambda>v. if v = fstv (hd P) then b v + \<gamma> 
                         else if v = sndv (last P) then b v - \<gamma> else b v)"

  shows "is_Opt b' f'"
  apply(subst is_opt_iff_no_augcycle)
  unfolding is_Opt_def
proof-
  have distinctP: "distinct P"
    using assms unfolding is_min_path_def is_s_t_path_def by simp
  have is_s_t_path:"is_s_t_path f s t P "
    using assms(5) unfolding is_min_path_def by simp
  have rest_assms_from_last_assm: 
          "set P \<subseteq> \<EE>"
          "fstv (hd P) = s"
          "sndv (last P) = t"
          "augpath f P"
       using is_s_t_path unfolding is_s_t_path_def by simp+

  text \<open>Flow validness preservation is for free due to previous work.\<close>

  show "f' is b' flow"
    unfolding f'_def b'_def
    using assms rest_assms_from_last_assm distinctP unfolding is_Opt_def 
    by (intro augment_path_validness_b_pres_source_target_distinct) simp+

  have P_not_empt: "P \<noteq> []" 
    using rest_assms_from_last_assm augpath_cases by blast

  show "\<not> Ex (augcycle f')"
  proof(rule ccontr)

    text \<open>So, for aiming a contradiction, let's assume there was an augmenting cycle.\<close>

    assume assm_contr: "\<not> \<not> Ex (augcycle f')"
    then obtain C where C_def: "augcycle f' C" by auto
    hence C_props: "\<CC> C < 0" "augpath f' C" "fstv (hd C) = sndv (last C)" "distinct C" "set C \<subseteq> \<EE>"
      unfolding augcycle_def by auto

    text \<open>Both the path and the cycle are transformed to structures over $Hedge$s
         while preserving certain properties.\<close>

    define Ch where "Ch = map CC C"
    define Ph where "Ph = map PP P"
    have C_not_empt: "C \<noteq> []" 
      using \<open>augpath f' C\<close> augpath_cases by blast
    have 1:"fstvv (hd Ph) = s" 
      apply(rule trans[of _ "fstv (hd P)"])
      unfolding Ph_def
      using P_not_empt
      by(cases P, simp, simp, simp add: assms rest_assms_from_last_assm)
    have 2:"sndvv (last Ph) = t" 
      unfolding Ph_def 
      using map_last'[of P sndvv PP sndv] P_not_empt assms rest_assms_from_last_assm 
      by auto
    have 4: "hpath Ph" unfolding Ph_def
      using assms rest_assms_from_last_assm 
      by(auto intro: augpath_to_hpath_PP[of f])
    have 5: "distinct Ph" unfolding Ph_def
      by(subst distinct_map, rule) 
        (simp add: inj_on_def assms distinctP)+
    have 6: "clean Ph"
      unfolding Ph_def by(rule pure_PP_clean)
    have 7: "finite {Ch}" by auto
    have 8: "hcycle Ch" unfolding hcycle_def Ch_def 
      using C_def  distinct_map C_def unfolding augcycle_def  
      by (auto intro: augpath_to_hpath_CC[of f'] 
            simp add: C_not_empt \<open>fstv (hd C) = sndv (last C)\<close> hd_map last_map inj_on_def)
    have 9: "clean Ch"
      unfolding Ch_def by(rule pure_CC_clean)
    have 11: "set Ph \<inter> set Ch = {}" unfolding Ph_def Ch_def
      by(subst Int_commute, rule pure_CC_pure_PP_disjoint)
    have 12: "e \<in> set Ph \<union> \<Union> {set C |C. C \<in> {Ch}} \<Longrightarrow> \<not> is_additional_edge e" for e
      by(auto simp add: Ph_def Ch_def)

  text \<open>Recall that $H$ is the union of $P$ and $C$ with forward-backward pairs cancelled.
       By the decomposition lemma, we see that the graph $H$ consists of an $s$-$t$-path and some cycles.\<close>

    have " \<exists>P' CCC'.
    fstvv (hd P') = s \<and>
    sndvv (last P') = t \<and>
    hpath P' \<and>
    distinct P' \<and>
    finite CCC' \<and>
    Ball CCC' hcycle \<and>
    (\<forall>C D. C \<in> CCC' \<longrightarrow> D \<in> CCC' \<longrightarrow> D \<noteq> C \<longrightarrow> set D \<inter> set C = {}) \<and>
    (\<forall>C\<in>CCC'. set P' \<inter> set C = {}) \<and>
    set P' \<union> \<Union> {set C |C. C \<in> CCC'} =
    set Ph \<union> \<Union> {set C |C. C \<in> {Ch}} - \<Union> (FBPs (set Ph \<union> \<Union> {set C |C. C \<in> {Ch}}))"
      apply(rule path_cycle_decompose_simple_proof)
      using assms(1) 1 2 4 5 6 7 8 9 11  12
      unfolding FBPs_def clean_def by auto

    then obtain P' CCC' where P'_CCC'_props:
     "fstvv (hd P') = s"       "sndvv (last P') = t"   "hpath P'"   "distinct P'"    "finite CCC'"
     " \<And> C. C \<in> CCC' \<Longrightarrow> hcycle C"
     " \<And> C D. C \<in> CCC' \<Longrightarrow> D \<in> CCC' \<Longrightarrow>  D \<noteq> C \<Longrightarrow> set D \<inter> set C = {}"
     "(\<And> C. C\<in>CCC'\<Longrightarrow> set P' \<inter> set C = {})"
     "set P' \<union> \<Union> {set C |C. C \<in> CCC'} =
         set Ph \<union> \<Union> {set C |C. C \<in> {Ch}} - \<Union> (FBPs (set Ph \<union> \<Union> {set C |C. C \<in> {Ch}}))"
      by force

    have "\<CC> P + \<CC> C = 
          (\<Sum> e \<in> set Ph. cc e) + (\<Sum> e \<in> \<Union> {set C |C. C \<in> {Ch}}. cc e)"
      unfolding \<CC>_def Ph_def
      using distinct_PP_sum distinctP
      unfolding Ch_def using distinct_CC_sum \<open>distinct C\<close> by auto

    also  have "... = (\<Sum> e \<in> set Ph \<union> \<Union> {set C |C. C \<in> {Ch}}. cc e)"
      using "11" by (auto intro: sym[OF sum.union_disjoint])

    also have "... = (\<Sum> e \<in> set P' \<union> \<Union> {set C |C. C \<in> CCC'}. cc e)" 
      using P'_CCC'_props 
      by (auto intro: FBPs_extract_cost)

    also have "... = (\<Sum> e \<in> set P'. cc e) + (\<Sum> e \<in> \<Union> {set C |C. C \<in> CCC'}. cc e)"
      using  P'_CCC'_props(5) P'_CCC'_props(8)
      by (auto intro!: sum.union_disjoint)

    also have "... = (\<Sum> e \<in> set P'. cc e) + (\<Sum> D \<in> CCC' .(\<Sum> e \<in> set D. cc e))"
      using disjoint_multiple_sum[of CCC' set cc] P'_CCC'_props(5) P'_CCC'_props(7)
      by (auto simp add: collapse_to_img)

    text \<open>$H$ has still the same costs of $P$and $C$, i.e. costs are not changed
          by the $FBP$ deletion.\<close>

    ultimately have PC_sum:"\<CC> P + \<CC> C = sum cc (set P') + (\<Sum>D\<in>CCC'. sum cc (set D))" by simp

    text \<open>Since $C$ is an augmenting cycle, the costs imposed by $H$ are strictly less than those of $P$.\<close>

    hence sumP'CCC'_compared_P:"sum cc (set P') + (\<Sum>D\<in>CCC'. sum cc (set D)) < \<CC> P" 
      using \<open>\<CC> C < 0\<close> by linarith

    text \<open>Now we show that all edges in $H$ (those edges surviving $FBP$ cancelling) are
         contained in the residual graph w.r.t. $f$.
         In a first step we prove all edges from $H$ being also in the residual graph for $f$ or $f'$.
         This is rather technical.\<close>

    have edges_rcap:"e \<in>  set P' \<union> \<Union> {set C |C. C \<in> CCC'} 
             \<Longrightarrow> rcap f (to_redge e) > 0 \<or> rcap f' (to_redge e) >0" for e
    proof-
      fix e
      assume e_Assm: "e \<in>  set P' \<union> \<Union> {set C |C. C \<in> CCC'}"
      moreover hence " e \<in>  set Ph \<union> \<Union> {set C |C. C \<in> {Ch}}"
        by (simp add: P'_CCC'_props(9))
      moreover have "e \<in> set Ph \<Longrightarrow> rcap f (to_redge e) > 0"
      proof-
        assume e_assm:"e \<in> set Ph"
        then obtain oe where "e = PP oe \<and> oe \<in> set P" unfolding Ph_def by auto
        moreover  hence "rcap f oe > 0"
          unfolding Ph_def using rest_assms_from_last_assm
                  augpath_rcap_pos_strict[of f P] by simp
        ultimately show ?thesis by simp
      qed
      moreover have "e \<in> set Ch \<Longrightarrow> rcap f' (to_redge e) > 0"
      proof-
        assume e_assm:"e \<in> set Ch"
        then obtain oe where "e = CC oe \<and> oe \<in> set C" unfolding Ch_def by auto
        moreover  hence "rcap f' oe > 0"
          unfolding Ch_def using augpath_rcap_pos_strict[of f' C] C_props(2) by simp
        ultimately show ?thesis by simp
      qed
      ultimately show "rcap f (to_redge e) > 0 \<or> rcap f' (to_redge e) >0"  by auto
    qed

    have e_inP'CCC'_inPh_Ch:"e \<in>  set P' \<union> \<Union> {set C |C. C \<in> CCC'}  
                 \<Longrightarrow> e \<in> set Ph \<or> e\<in> set Ch" for e 
      using P'_CCC'_props(9) by simp

    have e_inPh_PP: "e \<in> set Ph \<Longrightarrow> e = PP (to_redge e)" for e
      unfolding Ph_def by(induction P) auto

    have e_inCh_CC: "e \<in> set Ch \<Longrightarrow> e = CC (to_redge e)" for e
      unfolding Ch_def by(induction Ch) auto

    have e_inP'CCC'_CC_PP:"e \<in>  set P' \<union> \<Union> {set C |C. C \<in> CCC'}  
                 \<Longrightarrow> PP (to_redge e) \<in> set Ph \<or> CC (to_redge e)\<in> set Ch" for e
      using e_inCh_CC e_inP'CCC'_inPh_Ch e_inPh_PP by fastforce

    text \<open>In the second step we conclude that the residual graph w.r.t. $f$ is the only possibility.
         For contradiction, if $e$ was not in $G_f$ then $e$ is in $G_{f'}$.
         This means that the residual capacity was changed by the augmentation.
         Hence, $e$ or its reverse were contained in the residual graph for $f$. 
         By the assumption we know that it has to be $e$'s reverse.        
         But this constitutes a forward-backward pair and thus, gives rise to a contradiction.\<close>

    have P'_in_Gf:"e \<in>  set P' \<Longrightarrow> rcap f (to_redge e) > 0" for e
    proof(cases "rcap f (to_redge e) > 0")
      case False
      assume e_assm:" e \<in> set P'"
      hence "rcap f' (to_redge e) >0" using edges_rcap[of e] False by simp
      hence 11:"(to_redge e) \<in> set P \<or> erev(to_redge e) \<in> set P"
        using e_not_in_p_aug[of "to_redge e" P f \<gamma>] False unfolding f'_def 
        by fastforce
      hence 12:" erev(to_redge e) \<in> set P" "\<not> (to_redge e) \<in> set P "
      using augpath_rcap_pos_strict[of f P] rest_assms_from_last_assm False by auto
      hence "rcap f (to_redge e) > 0 \<or> rcap f (erev(to_redge e) ) > 0 "
        using augpath_rcap_pos_strict[of f P] rest_assms_from_last_assm by blast
      hence "rcap f (erev(to_redge e) ) > 0" using False by simp
      have "PP (erev(to_redge e) ) \<in> set Ph" 
        unfolding Ph_def
        using \<open>erev (to_redge e) \<in> set P\<close> 
        by (intro map_in_set, auto)
      have "e \<in> set Ch" 
        using  12(2)  in_set_map[of e PP P ] e_inP'CCC'_inPh_Ch[of e] unfolding Ph_def 
        using e_assm by fastforce
      hence "CC (to_redge e) \<in> set Ch" 
        using e_inCh_CC by auto
      have "e = CC (to_redge e)"
        by (simp add: \<open>e \<in> set Ch\<close> e_inCh_CC)
      have "isFBP (PP (erev(to_redge e) )) (CC (to_redge e))"
        unfolding isFBP_def by simp
      hence "isFBP (PP (erev(to_redge e) )) e"
        using \<open>e = CC (to_redge e)\<close> by auto
      hence "{(PP (erev(to_redge e) )), e} \<in> FBPs (\<Union> {set Ph \<union> set Ch})"
        using \<open>PP (erev (to_redge e)) \<in> set Ph\<close> 
        by (auto intro: FBPs_intro simp add: \<open>e \<in> set Ch\<close>)
      hence "e \<notin> set P' \<union> \<Union> {set C |C. C \<in> CCC'} " 
        using P'_CCC'_props(9) Un_commute by auto
      hence False using e_assm by simp
      thus ?thesis by simp
    qed

    text \<open>Analogue argument concerning the cycles.\<close>

    moreover have CCC'_in_Gf:"e \<in>  set D \<Longrightarrow>D \<in> CCC' \<Longrightarrow>rcap f (to_redge e) > 0" for D e
     proof(cases "rcap f (to_redge e) > 0")
      case False
      assume e_assm: "e \<in>  set D" "D \<in> CCC'"     
      hence "rcap f' (to_redge e) >0" using edges_rcap[of e] False by auto
      hence 11:"(to_redge e) \<in> set P \<or> erev(to_redge e) \<in> set P"
        using e_not_in_p_aug[of "to_redge e" P f \<gamma>] False unfolding f'_def 
        by fastforce
      hence 12:" erev(to_redge e) \<in> set P" "\<not> (to_redge e) \<in> set P "
      using augpath_rcap_pos_strict[of f P] rest_assms_from_last_assm False by auto
      hence "rcap f (to_redge e) > 0 \<or> rcap f (erev(to_redge e) ) > 0 "
        using augpath_rcap_pos_strict[of f P] rest_assms_from_last_assm by blast
      hence "rcap f (erev(to_redge e) ) > 0" using False by simp
      have "PP (erev(to_redge e) ) \<in> set Ph" 
        unfolding Ph_def using \<open>erev (to_redge e) \<in> set P\<close> 
        by (auto intro: map_in_set)
      have "e \<in> set Ch" 
        using  12(2)  in_set_map[of e PP P ] e_inP'CCC'_inPh_Ch[of e] unfolding Ph_def 
        using e_assm by fastforce
      hence "CC (to_redge e) \<in> set Ch" 
        using e_inCh_CC by auto
      have "e = CC (to_redge e)"
        by (simp add: \<open>e \<in> set Ch\<close> e_inCh_CC)
      have "isFBP (PP (erev(to_redge e) )) (CC (to_redge e))"
        unfolding isFBP_def by simp
      hence "isFBP (PP (erev(to_redge e) )) e"
        using \<open>e = CC (to_redge e)\<close> by auto
      hence "{(PP (erev(to_redge e) )), e} \<in> FBPs (\<Union> {set Ph \<union> set Ch})"
        using \<open>PP (erev (to_redge e)) \<in> set Ph\<close> 
        by (auto intro: FBPs_intro simp add: \<open>e \<in> set Ch\<close>)
      hence "e \<notin> set P' \<union> \<Union> {set C |C. C \<in> CCC'} " using P'_CCC'_props(9) 
        using Un_commute by auto
      hence False using e_assm by auto
      thus ?thesis by simp
    qed

    text \<open>Hence, all edges surviving the deletion of FBPs are completely contained in $G_f$:\<close>

    ultimately have P'CCC'_in_Gf:"e \<in>  (set P' \<union> \<Union> {set C |C. C \<in> CCC'}) 
                                  \<Longrightarrow> rcap f (to_redge e) > 0" for e by auto
    

    text \<open>
          Strictly speaking, this applies just to the \textit{corresponding residual} edges,
         and thus, we transform the $hpath$s and $hcycle$s back to residual paths and residual cycles.\<close>

    have 11:"e \<in> set P' \<union> \<Union> {set C |C. C \<in> CCC'} \<Longrightarrow> to_redge e \<in> \<EE>" for e
    proof-
      assume "e \<in> set P' \<union> \<Union> {set C |C. C \<in> CCC'}"
      hence "e \<in> set Ph \<union> set Ch" 
        by (simp add: e_inP'CCC'_inPh_Ch)
      hence "to_redge e \<in> set (map to_redge Ph) \<union> set (map to_redge Ch)"
        by auto
      hence "to_redge e \<in> set P \<union> set C" 
        by (simp add: Ch_def Ph_def)
      thus "to_redge e \<in> \<EE>"
        using  C_props(5) rest_assms_from_last_assm  by auto
    qed
      
    have " \<exists>PP CCC.  Ball (set CCC) precycle \<and>prepath PP \<and> distinct PP \<and>
                     sum cc (set P') = \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 \<and>
                     set (map to_redge P') = set PP \<union> \<Union> {set D |D. D \<in> set CCC} \<and> 
                     fstv (hd PP) = s \<and> sndv (last PP) = t"
      using  P'_CCC'_props(3)  P'_CCC'_props(4) 11 
      by (fastforce intro!: distinct_hpath_to_distinct_augpath_and_augcycles
            simp add: P'_CCC'_props(1)  P'_CCC'_props(2))

    then obtain PP CCC where PP_CC_props:" Ball (set CCC) precycle" "prepath PP "
               "distinct PP "  "sum cc (set P') = \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0"
               "set (map to_redge P') = set PP \<union> \<Union> {set D |D. D \<in> set CCC}" 
               "fstv (hd PP) = s" "sndv (last PP) = t"
      by blast

    text \<open>So far we just face $prepath$s and $precycle$s. For augmenting paths/cycles we
          add our knowledge on residual capacities.\<close>

    have "augpath f PP"
    proof(rule augpath_from_prepath, goal_cases)
      case (2 e)
        assume " e \<in> set PP"
        then obtain ee where ee_prop:"ee \<in> set P'" "to_redge ee = e" 
          using PP_CC_props by force
        show "0 < \<uu>\<^bsub>f\<^esub>e "
          using  P'CCC'_in_Gf ee_prop by auto
    qed (simp add: PP_CC_props(2))

    have aaa:"e \<in> set PP \<Longrightarrow> e \<in> \<EE>" for e
    proof-
      assume assm: "e \<in> set PP"
      then obtain ee where ee_prop:"to_redge ee = e" "ee \<in> set P'" 
        using PP_CC_props(5) by force
      show "e \<in> \<EE>"
        using ee_prop(1) 11 ee_prop(2) by blast
    qed

    have "is_s_t_path f s t PP"
      unfolding is_s_t_path_def
      using \<open>augpath f PP\<close> aaa 
      by (auto simp add: PP_CC_props(6) PP_CC_props(3) PP_CC_props(7))

  text \<open>Finally we have proven that after the elimination there is still an $s$-$t$-path.
       By the minimality assumption, it's costs have to be greater or equal than those of $P$.\<close>

  hence P_better_PP:"\<CC> PP \<ge> \<CC> P"
    using assms unfolding is_min_path_def by simp

  have 12:"\<CC> P + \<CC> C = \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 + (\<Sum>D\<in>CCC'. sum cc (set D))"
    by (simp add: PC_sum PP_CC_props(4))

  text \<open>It follows:\<close>

  hence "\<CC> P >  \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 + (\<Sum>D\<in>CCC'. sum cc (set D))"
    using C_props(1) by simp

  text \<open>But on the other hand, we can show that the costs of the cycles have to be non-negative.
Otherwise there was a negative cycle and since this was in the residual graph
 w.r.t. $f$, we reach a contradiction.
\<close>

  moreover have "foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 \<ge> 0"
  proof(rule ccontr)
    assume assm: "\<not> 0 \<le> foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 "
    hence " foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 < 0" by simp
    then obtain D where D_props:"D \<in> set CCC" "\<CC> D < 0"
      using  fold_sum_neg_neg_element[of \<CC> CCC] by auto
    have "augcycle f D"
    proof(rule augcycle_from_precycle, goal_cases)
      case (1 e)
        assume assm: "e \<in> set D"
        hence "e \<in> set PP \<union> \<Union> {set D |D. D \<in> set CCC}"
          using D_props by auto
       then obtain ee where ee_prop:"to_redge ee = e" "ee \<in> set P'" 
        using PP_CC_props(5) 
        by (metis (no_types, lifting) in_set_map)
       show "0 < \<uu>\<^bsub>f\<^esub>e"
        using ee_prop by (auto intro: P'_in_Gf)
    qed (simp add: D_props(2), simp add: D_props(1) PP_CC_props(1))

  then show False using assms(5) is_opt_iff_no_augcycle[of f b] assms 
    unfolding is_Opt_def by simp
  qed

  moreover have "(\<Sum>D\<in>CCC'. sum cc (set D)) \<ge> 0"
  proof(rule ccontr)
    assume assm:" \<not> 0 \<le> (\<Sum>D\<in>CCC'. sum cc (set D))"
    hence "(\<Sum>D\<in>CCC'. sum cc (set D)) < 0" by auto
    then obtain D where D_props: "D \<in> CCC'" "sum cc (set D) < 0" 
      by (smt (verit) sum_nonneg)
    have "\<exists> CCC. (\<forall> D \<in> set CCC. precycle D) \<and> 
                (\<Sum> e \<in> set D. cc e) = foldr (\<lambda> D costs. \<CC> D + costs) CCC (0::real) \<and>
                set (map to_redge D) = \<Union>{set D| D. D \<in> set CCC}"
     proof(rule hcycle_to_augcycles, goal_cases)
       case 3
       then show ?case 
       proof
         fix e
         assume assm: "e \<in> set (map to_redge D) "
         then obtain ee where ee_prop:"to_redge ee = e" "ee \<in> set D" by auto
         hence "ee \<in> set Ph \<or> ee \<in> set Ch"
          using  e_inP'CCC'_CC_PP[of ee] D_props(1)
          using e_inP'CCC'_inPh_Ch by fastforce
         hence "e \<in> set P \<or> e \<in> set C"
          unfolding Ph_def Ph_def using ee_prop 
          by (metis Ch_def Hedge.sel(2) e_inCh_CC in_set_map to_redge.simps(1))
        then show "e \<in> \<EE>" using assms(2) C_props(5)rest_assms_from_last_assm by blast
      qed
     qed (simp add: D_props(1) P'_CCC'_props(6))+

     then obtain CCC2 where CCC2_def:"(\<forall> D \<in> set CCC2. precycle D)"" 
                (\<Sum> e \<in> set D. cc e) = foldr (\<lambda> D costs. \<CC> D + costs) CCC2 (0::real)"
                "set (map to_redge D) = \<Union>{set D| D. D \<in> set CCC2}" by auto
     then obtain E where E_prp:"E \<in> set CCC2 \<and> \<CC> E < 0"
      using D_props(2) fold_sum_neg_neg_element[of \<CC> CCC2] by auto
     have "augcycle f E"
      proof(rule augcycle_from_precycle, goal_cases)
        case (1 e)
          assume assm: "e \<in> set E"
          hence "e \<in> set (map to_redge D) "  using E_prp  CCC2_def  by auto
          then obtain ee where ee_prop:"to_redge ee = e" "ee \<in> set D" 
           by auto
          show "0 < \<uu>\<^bsub>f\<^esub>e"
            using  CCC'_in_Gf[of _ D] ee_prop D_props by auto
      qed  (simp add: CCC2_def(1) E_prp)+

      thus False 
        using assms(5) unfolding is_Opt_def using is_opt_iff_no_augcycle[of f b]
              rest_assms_from_last_assm assms min_cost_flow_no_augcycle 
        by force
   qed

   text \<open>We obtain the final contradiction.\<close>

  ultimately show False using P_better_PP by simp
qed
qed

end
end
