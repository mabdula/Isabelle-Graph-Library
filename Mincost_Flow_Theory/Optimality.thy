theory Optimality
imports Augmentation Decomposition
begin

context cost_flow_network
begin
section \<open>An Optimality Criterion\<close>

text \<open>Luckily, there is a simple criterion indicating (non-)optimality of a flow assignment $f$.
We follow Korte, Vygen chapter 9.2.
\<close>

text \<open>Since we will need this notion frequently, 
      let us define residual costs for a list of residual edges.\<close>

definition "\<CC> cs \<equiv> (\<Sum> c \<in> (set cs). \<cc> c)"

text \<open>We define augmenting cycles as closed augmenting paths with negative residual costs.\<close>

definition "augcycle f cs \<equiv> (\<CC> cs < 0 \<and> augpath f cs \<and> fstv (hd cs) = sndv (last cs)
                              \<and> distinct cs \<and> set cs \<subseteq> \<EE>)"

text \<open>Similarly, we obtain precycles from prepaths.\<close>

definition "precycle cs = (prepath cs \<and> fstv (hd cs) = sndv (last cs) \<and> set cs \<subseteq> \<EE> \<and> distinct cs)"

text \<open>This means, that precycles are cycles in the residual graph without
 any restrictions on residual capacities.\<close>

text \<open>A conditioned lemma of equivalence.\<close>

lemma augcycle_from_precycle: 
"(\<And> e. e \<in> set es \<Longrightarrow> rcap f e > 0)  \<Longrightarrow>\<CC> es < 0 \<Longrightarrow> precycle es \<Longrightarrow> augcycle f es"
  unfolding precycle_def augcycle_def 
  using augpath_from_prepath by simp

text \<open>An augmenting cycle in the zero flow corresponds to a cycle in the original graph.\<close>

lemma augcycle_to_closed_w:
 assumes "augcycle f C" "f = (\<lambda> e. 0)"
 shows   "closed_w (make_pair ` \<E>) (map to_vertex_pair C)"
         "foldr (\<lambda> e acc. acc + \<cc> e) C bas = foldr (\<lambda> e acc. acc + \<c> e) (map oedge C) bas" 
proof-
  show "closed_w (make_pair ` \<E>) (map to_vertex_pair C)"
  proof-
  have "awalk (make_pair ` \<E>) (fstv (hd C)) (map to_vertex_pair C) (sndv (last C))"
        "0 < length (map to_vertex_pair C)"
    using augpath_to_awalk_zero_flow assms augpath_cases 
    unfolding augcycle_def 
    by blast+
  thus ?thesis unfolding closed_w_def 
    using assms(1) augcycle_def by force
qed
  show "foldr (\<lambda> e acc. acc + \<cc> e) C bas = 
        foldr (\<lambda> e acc. acc + \<c> e) (map oedge C) bas"
    using  augpath_to_awalk_zero_flow  assms 
    unfolding augcycle_def 
    by auto
qed

text \<open>A closed augmenting path with negative total costs contains an augmenting cycle.\<close>

lemma augcycle_from_non_distinct_cycle:
      assumes "augpath f cs" "fstv (hd cs) = sndv (last cs)" "set cs \<subseteq> \<EE>"
              "foldr (\<lambda> e acc. \<cc> e + acc) cs 0 < 0"
              "l = length cs"
            obtains C where "augcycle f C"
  using assms
proof(induction l arbitrary: cs rule : less_induct)
  case (less l)
  show ?case 
  proof (cases "distinct cs")
    case True
    show ?thesis 
      using less(3,4,5,6) True
      by (auto intro: less(2)[of cs] 
            simp add: augcycle_def \<CC>_def distinct_sum[of cs \<cc>] add.commute)
  next
    case False
    then obtain e cs1 cs2 cs3 where cs_split:"cs = cs1@[e]@cs2@[e]@cs3"
      using not_distinct_decomp by blast
    have "foldr (\<lambda>e. (+) (\<cc> e)) cs 0  = 
          foldr (\<lambda>e. (+) (\<cc> e)) (cs1@[e]@cs3) 0 + foldr (\<lambda>e. (+) (\<cc> e)) ([e]@cs2) 0"
      apply(subst cs_split)
      apply(subst map_sum_split)+ 
      by auto
    hence one_less_0:"foldr (\<lambda>e. (+) (\<cc> e)) (cs1@[e]@cs3) 0 < 0 \<or> foldr (\<lambda>e. (+) (\<cc> e)) ([e]@cs2) 0 < 0"
      using less(6) by auto
    show ?thesis 
    proof(rule disjE[OF one_less_0], goal_cases)
      case 1
      have augpath:"local.augpath f (cs1 @ [e] @ cs3)" 
        using augpath_split1[of f "cs1" "[e]@cs2@[e]@cs3"] cs_split less.prems(2)
              augpath_split2[of f "cs1@[e]@cs2" "[e]@cs3"] augpath_split3[of f "cs1@[e]@cs2" "[e]@cs3"] 
              augpath_split3[of f "cs1" "[e]@cs2@[e]@cs3"]
        by (cases cs1)  (fastforce intro: augpath_app)+
      have same_ends: " fstv (hd (cs1 @ [e] @ cs3)) = sndv (last (cs1 @ [e] @ cs3))"
        using augpath_split1[of f "cs1" "[e]@cs2@[e]@cs3"] cs_split less.prems(3)
              augpath_split2[of f "cs1@[e]@cs2" "[e]@cs3"] augpath_split3[of f "cs1@[e]@cs2" "[e]@cs3"] 
              augpath_split3[of f "cs1" "[e]@cs2@[e]@cs3"]
        by (cases cs1) auto
      show ?case 
        apply(rule less(1)[where cs2 = "cs1 @ [e] @ cs3"])
        using augpath  same_ends  less(5)  1 less(7) cs_split 
        by (auto intro: less(2))
    next
      case 2
      have augpath:"local.augpath f ([e] @ cs2)" 
        using augpath_split1[of f "[e]@cs2" "[e]@cs3"] augpath_split2 [of f cs1 "[e]@cs2@[e]@cs3"]
              cs_split less.prems(2) by simp 
      have same_ends: "fstv (hd ([e] @ cs2)) = sndv (last ([e] @ cs2))"
        using augpath_split3[of f "cs1@[e]@cs2" "[e]@cs3"] cs_split less.prems(2)
        by(cases cs2) auto
      show ?case 
        apply(rule less(1)[where cs2 = "[e] @ cs2"])
        using augpath  same_ends  less(5)  2 less(7) cs_split 
        by (auto intro: less(2))
    qed
  qed
qed

text \<open>A flow $f$ is an optimum $b$-flow iff
\begin{itemize}
\item it is a flow assignment respecting the required balance $b$ and the fixed capacity 
constraints $u$ (validity), and
\item there is no other valid $b$-flow incurring lesser costs.
\end{itemize}
\<close>

definition "is_Opt b f \<equiv> f is b flow \<and> (\<forall> f'. (f' is b flow \<longrightarrow> \<C> f'  \<ge> \<C> f))"

lemma ex_cong: "(\<And>e. e \<in> \<E> \<Longrightarrow> f e = f' e) \<Longrightarrow>
    (\<And>v. v \<in> \<V> \<Longrightarrow> b v = b' v) \<Longrightarrow>v \<in> \<V> \<Longrightarrow>  - ex f v = b v \<Longrightarrow> - ex f' v = b' v"
  by(auto simp add: ex_def delta_minus_def delta_plus_def)

lemma isuflow_cong: "(\<And>e. e \<in> \<E> \<Longrightarrow> f e = f' e) \<Longrightarrow> isuflow f  \<Longrightarrow> isuflow f'"
  by(simp add: isuflow_def)

lemma flow_costs_cong:  "(\<And>e. e \<in> \<E> \<Longrightarrow> f e = f' e) \<Longrightarrow> \<C> f  = \<C> f'"
  by(simp add: \<C>_def) 

lemma isbflow_cong: "(\<And> e. e \<in> \<E> \<Longrightarrow> f e = f' e) \<Longrightarrow> (\<And> v. v \<in> \<V> \<Longrightarrow> b v = b' v) 
                    \<Longrightarrow> isbflow f b \<Longrightarrow> isbflow f' b'"
  by(auto intro: isuflow_cong ex_cong  simp add:  isbflow_def)

lemma is_Opt_cong: "(\<And> e. e \<in> \<E> \<Longrightarrow> f e = f' e) \<Longrightarrow> (\<And> v. v \<in> \<V> \<Longrightarrow> b v = b' v) 
                    \<Longrightarrow> is_Opt b f \<Longrightarrow> is_Opt b' f'"
proof(subst is_Opt_def, rule, auto, goal_cases)
  case 1
  then show ?case 
    using is_Opt_def isbflow_cong by blast
next
  case (2 g)
  moreover hence "isbflow g b"
    using isbflow_cong[OF refl] by simp
  moreover have "\<C> f' = \<C> f" 
    using 2(1) flow_costs_cong by fastforce
  ultimately show ?case 
    by(simp add: is_Opt_def) 
qed

subsection \<open>Absence of Augmenting Cycles from Optimality\<close>

text \<open>We present a proof of the first direction:
     If a flow is Optimum for some balance, then there cannot be an augmenting cycle.
The proof is easily done by contradiction:
If there was an augmenting cycle, let's simply augment which results in a decrease in costs.
\<close>

lemma min_cost_flow_no_augcycle:
      assumes "is_Opt b f"
      shows "\<nexists> cs. augcycle f cs"
proof(rule ccontr)
  assume "\<not> (\<nexists>cs. augcycle f cs) "
  then obtain cs where cs_def: "augcycle f cs" by auto
  then obtain \<gamma> where gamma_def: "\<gamma> > 0 \<and> ereal \<gamma> \<le> Rcap f (set cs)"
    using augcycle_def augpath_rcap
    by (metis (no_types, lifting) ereal_dense2 less_ereal.simps(1) order_less_imp_le zero_ereal_def)
  have lst:"\<C> (augment_edges f \<gamma> cs) = \<C> f + \<gamma> * \<CC> cs"
    unfolding \<CC>_def
    using augcycle_def cs_def 
    by (auto intro: cost_change_aug[of cs f \<gamma>])
  hence "\<C> f > \<C> (augment_edges f \<gamma> cs)" 
    using  add_less_same_cancel1[of " \<C> f"  "\<gamma> * \<CC> cs"]  augcycle_def[of f cs] 
          cs_def gamma_def mult_pos_neg 
    by auto
  then show False using assms unfolding is_Opt_def
    using aug_cycle_pres_b[of f b \<gamma> cs] augcycle_def[of f cs] cs_def gamma_def 
    by force
qed

subsection \<open>Optimality from Absence of Augmenting Cycles\<close>

text \<open>In this section we prove that the non-existence of an augmenting cycle is also sufficient for
 optimality.
For this, we first look at $residual flows$. 
Formally, a residual flow is a function assigning non-negative reals to residual arcs.
Differences of flows as defined in the following are residual flows.

We follow the presentation from section 9.1 in the book by Korte and Vygen.
\<close>

subsubsection \<open>Difference Flows and their Properties\<close>

text \<open>We reinterpret past results on residual graphs.\<close>

abbreviation "make_pair_residual \<equiv> (\<lambda> e. (fstv e, sndv e))"

abbreviation "create_edge_residual \<equiv> (\<lambda> u v. F (create_edge u v))"

interpretation residual_flow: cost_flow_network where
fst = fstv and snd = sndv and make_pair = make_pair_residual and create_edge = create_edge_residual
and \<E> = \<EE>  and \<c> = \<cc> and \<u> = "\<lambda> _. PInfty"
  using  make_pair create_edge  E_not_empty oedge_on_\<EE> 
  by(auto simp add: finite_\<EE> make_pair[OF refl refl] create_edge cost_flow_network_def flow_network_axioms_def flow_network_def multigraph_def)
 

text \<open>Difference between flows.\<close>

fun difference::"('edge_type \<Rightarrow> real) \<Rightarrow> ('edge_type \<Rightarrow> real) \<Rightarrow> ('edge_type Redge \<Rightarrow> real)" 
                       where
"difference f' f (F e) = max 0 (f' e - f e)"|
"difference f' f (B e) = max 0 (f e - f' e)"

text \<open>We prove that the difference between two valid flows behaves like a valid flow itself.
We see non-negativity of flow values assigned, respect of residual capacities etc. 
\<close>

lemma diff_non_neg: "difference f' f e \<ge> 0"
  apply(cases e)
  using prod_elim[where P= "\<lambda> ee. (e = _ ee)"] 
  by (force simp add: isuflow_def )+
  
lemma diff_of_diff_edge:
  "difference f' f (F e) - difference f' f (B e) = f' e - f e"
  using  difference.simps
  by simp

lemma difference_less_rcap: "isuflow f \<Longrightarrow> isuflow f' \<Longrightarrow> e\<in> \<EE> \<Longrightarrow> rcap f e \<ge> difference f' f e"
  apply(cases e)
  using prod_elim[where P= "\<lambda> ee. (e = _ ee)"] o_edge_res
  apply (smt (verit, ccfv_SIG) difference.simps(1) dual_order.trans ereal_less_eq(5) ereal_umst isuflow_def oedge.simps(1) rcap.simps(1))
  by (smt (verit) \<open>\<And>uu p Q. \<lbrakk>e = uu p; \<And>a b. \<lbrakk>p = (a, b); e = uu p\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q\<close> difference.simps(2) ereal_less_eq(3) isuflow_def o_edge_res oedge.simps(2) rcap.simps(2))

lemma pos_difference_pos_rcap:
 "isuflow f \<Longrightarrow> isuflow f' \<Longrightarrow> e\<in> \<EE> \<Longrightarrow>  difference f' f e > 0 \<Longrightarrow> rcap f e > 0"
  using difference_less_rcap dual_order.strict_trans1 ereal_less(2)
  by blast

lemma difference_flow_pos: "isuflow f \<Longrightarrow> isuflow f' \<Longrightarrow> residual_flow.flow_non_neg (difference f' f)"
  by (simp add: diff_non_neg residual_flow.flow_non_neg_def)

text \<open>The difference of two $b$-flows is a circulation in the residual graph.
We give a formal proof of Proposition 9.4 in the book.
\<close>

lemma diff_is_res_circ:
  assumes "f is b flow" "f' is b flow"
  shows   "residual_flow.is_circ (difference f' f)"
  unfolding residual_flow.is_circ_def
proof
  fix v
  assume v_Assm: "v \<in> residual_flow.\<V>"
  hence v_Assm': "v \<in> \<V>"
    by(auto simp add: image_def make_pair \<EE>_def dVs_def) blast+   
  have aa: "finite {F e |e. e \<in> \<delta>\<^sup>- v}" "finite {F e |e. e \<in> \<delta>\<^sup>+ v}"
           "finite {B e |e. e \<in> \<delta>\<^sup>+ v}" 
           "finite {B e |e. e \<in> \<delta>\<^sup>- v}"
    using finite_imageI[of "\<delta>\<^sup>- v" F ] delta_minus_finite[of v]
          finite_imageI[of "\<delta>\<^sup>+ v" "\<lambda> e. B e"]   delta_plus_finite[of v]
          finite_imageI[of "\<delta>\<^sup>+ v" F ] finite_imageI[of "\<delta>\<^sup>- v" "\<lambda> e. B e"]
    by (metis Setcompr_eq_image)+
  have 00: "(\<Sum> e \<in> {F e |e. e \<in> \<delta>\<^sup>- v} \<union> {B e |e. e \<in> \<delta>\<^sup>+ v}.  
                                  (difference f' f)  e)                =
                ((\<Sum> e \<in> {F e |e. e \<in> \<delta>\<^sup>- v}.  (difference f' f)  e) +
            (\<Sum> e \<in> {B e |e. e \<in> \<delta>\<^sup>+ v}. (difference f' f)  e))"
    using aa  by (auto intro: sum.union_disjoint)
  have 11:"(\<Sum> e \<in>  {F e |e. e \<in> \<delta>\<^sup>+ v} \<union> {B e |e. e \<in> \<delta>\<^sup>- v}.
                                  (difference f' f)  e) = 
                 (\<Sum> e \<in> {F e |e. e \<in> \<delta>\<^sup>+ v}. (difference f' f)  e)+
                  (\<Sum> e \<in> {B e |e. e \<in> \<delta>\<^sup>- v}. (difference f' f)  e)"
    using aa  by (auto intro: sum.union_disjoint)
  have bb:"difference f' f (F x) - difference f' f (B x) = f' x - f x" for x
    using diff_of_diff_edge[of f' f] by simp
  have cc: "difference f' f (B x) - difference f' f (F x) = f x - f' x" for x     
    using diff_of_diff_edge[of  f' f] by simp

  text \<open>More interesting reasoning.\<close>

  have 1:"residual_flow.ex (difference f' f) v  =
        (\<Sum> e \<in> residual_flow.delta_minus v.  (difference f' f)  e) - (\<Sum> e \<in> residual_flow.delta_plus v.  (difference f' f)  e)"
    unfolding residual_flow.ex_def by simp
  also have 2:"... =    (\<Sum> e \<in> {F e |e. e \<in> \<delta>\<^sup>- v} \<union> {B e |e. e \<in> \<delta>\<^sup>+ v}.  
                                  (difference f' f)  e) 
                      -(\<Sum> e \<in>  {F e |e. e \<in> \<delta>\<^sup>+ v} \<union> {B e |e. e \<in> \<delta>\<^sup>- v}.
                                  (difference f' f)  e)"
    using \<EE>_def residual_flow.delta_minus_def  residual_flow.delta_plus_def
    by(auto simp add: delta_plus_def delta_minus_def  
                 intro!: diff_eq_split cong[of "sum (difference f' f)", OF refl]) 
  also have 3:"... =  ((\<Sum> e \<in> {F e |e. e \<in> \<delta>\<^sup>- v}.  (difference f' f)  e) - 
                     (\<Sum> e \<in> {B e |e. e \<in> \<delta>\<^sup>- v}. (difference f' f)  e) )
                  + ((\<Sum> e \<in>{B e |e. e \<in> \<delta>\<^sup>+ v}. (difference f' f)  e) -
                     (\<Sum> e \<in>  {F e |e. e \<in> \<delta>\<^sup>+ v} . (difference f' f)  e))"
    using 00 11 by simp
  also have 4:"... = ((\<Sum>  e \<in> \<delta>\<^sup>- v.  (difference f' f)  (F e)) - 
                     (\<Sum> e \<in> \<delta>\<^sup>- v. (difference f' f)   (B e)) )
                  + ((\<Sum> e \<in> \<delta>\<^sup>+ v. (difference f' f)  (B e)) -
                     (\<Sum> e  \<in> \<delta>\<^sup>+ v. (difference f' f)  (F e)))" 
    using sum_inj[of F " difference f' f", simplified]
          sum_inj[of "(\<lambda>e. B e)" " difference f' f"]  inj_on_def 
    by (subst collapse_to_img)+ fastforce
  also have 5:"... =  ((\<Sum>  e \<in> \<delta>\<^sup>- v.  (difference f' f)  (F e) 
                                     - (difference f' f)   (B e)))
                  + ((\<Sum> e \<in> \<delta>\<^sup>+ v. (difference f' f)  (B e)
                                 - (difference f' f)  (F e)))"
    by (simp add: sum_subtractf)
  also have 6:"... = (\<Sum>  e \<in> \<delta>\<^sup>- v. f' e - f e)+ (\<Sum> e \<in> \<delta>\<^sup>+ v.  f e - f' e)"
    using bb cc by auto
  also have 7:"... = ((\<Sum>  e \<in> \<delta>\<^sup>- v. f' e) + (\<Sum>  e \<in> \<delta>\<^sup>- v. - f e) )
                 + ((\<Sum> e \<in> \<delta>\<^sup>+ v.  f e) + (\<Sum> e \<in> \<delta>\<^sup>+ v.- f' e)) "
    using sum_negf[of f "\<delta>\<^sup>- v"] sum_negf[of f' "\<delta>\<^sup>+ v"]
          sum_subtractf[of f' f "\<delta>\<^sup>- v"] sum_subtractf[of f f' "\<delta>\<^sup>+ v"] by auto
  also have 8:"... = ((\<Sum>  e \<in> \<delta>\<^sup>- v. f' e) - (\<Sum>  e \<in> \<delta>\<^sup>- v. f e) )
                 + ((\<Sum> e \<in> \<delta>\<^sup>+ v.  f e) - (\<Sum> e \<in> \<delta>\<^sup>+ v. f' e)) " 
    using Groups_Big.sum_negf by (fastforce intro!: sum_eq_split)
  also have 9:"... = ((\<Sum>  e \<in> \<delta>\<^sup>- v. f' e) - (\<Sum> e \<in> \<delta>\<^sup>+ v. f' e)) 
                  +((\<Sum> e \<in> \<delta>\<^sup>+ v.  f e) -  (\<Sum>  e \<in> \<delta>\<^sup>- v. f e))" by simp
  also have a:"... = ex f' v -  ex f v" unfolding ex_def by simp
  also have b:"... = - b v + b v" 
    using v_Assm' assms  isbflow_def by fastforce 
  also have c:"... = 0" by simp
  finally show"residual_flow.ex (difference f' f) v = 0" 
    by blast
qed

text \<open>
Residual costs of a difference flow is the difference between costs of two flows.
Another part of Proposition 9.4 by Korte and Vygen.
\<close>

lemma  rcost_difference: "residual_flow.\<C> (difference f' f) = \<C> f' - \<C> f"
  unfolding residual_flow.\<C>_def \<C>_def
proof-
  define \<FF> where "\<FF> = {F e| e. e \<in>\<E>}"

  define \<BB> where  "\<BB> = {B e| e. e \<in>\<E>}"

  have finite_F: "finite \<FF>"
  using \<EE>_def \<FF>_def finite_\<EE> by force

  have finite_B: "finite \<BB>"
  using \<EE>_def \<BB>_def finite_\<EE> by force

have F_B_union:     "\<FF> \<union> \<BB> = \<EE>"
  and F_B_disjoint:  "\<FF> \<inter> \<BB> = {}"
  using \<BB>_def \<EE>_def \<FF>_def  \<BB>_def \<FF>_def flow_network_axioms 
  by fastforce+
  have aa: "(difference f' f (F e) - difference f' f (B e)) * \<c> e = 
            (f' e - f e) * \<c> e" for e
    using diff_of_diff_edge[of  f' f] by simp
  have "(\<Sum>e\<in>\<EE>. difference f' f e * \<cc> e) = 
        (\<Sum>e\<in>\<FF>. difference f' f e * \<cc> e) + 
        (\<Sum>e\<in>\<BB>. difference f' f e * \<cc> e)"
    by(subst sym[OF F_B_union]) 
      (rule sum.union_disjoint, rule finite_F, rule finite_B,rule  F_B_disjoint)
  also have "... =  (\<Sum>e\<in>\<E>. difference f' f (F e) * \<cc> ( F e)) + 
                    (\<Sum>e\<in>\<E>. difference f' f (B e) * \<cc>  (B e))" 
      using collapse_to_img[of F \<E>] sum_inj[of F "\<lambda> e. difference f' f e * \<cc> e " \<E>]  inj_on_def 
            sum_inj[of F "\<lambda> e. difference f' f e * \<cc> e " \<E>]  
            collapse_to_img[of "\<lambda> e. B e" \<E>]  
            sum_inj[of  "\<lambda> e. B e" "\<lambda> e. difference f' f e * \<cc> e " \<E>] 
      unfolding \<BB>_def \<FF>_def
      by fastforce 
  also have " ... = (\<Sum>e\<in>\<E>. difference f' f (F e) *\<c> e) +
                    (\<Sum>e\<in>\<E>. - difference f' f (B e) * \<c> e) "
    by (smt (verit) \<cc>.simps(1) \<cc>.simps(2) minus_mult_minus prod.collapse sum.cong)
  also have "... = (\<Sum>e\<in>\<E>.     difference f' f (F e) *\<c> e
                             - difference f' f (B e) * \<c> e) " 
    using sym[OF sum.distrib[of "\<lambda> e. difference f' f (F e) * \<c> e"_ \<E>]] by simp
  also have "... = (\<Sum>e\<in>\<E>. (difference f' f (F e)- difference f' f (B e)) * \<c> e)" 
    by (simp add: left_diff_distrib)
  also have " ... = (\<Sum>e\<in>\<E>. (f' e - f e) * \<c> e)"
    using aa by(auto intro: sum.cong)
  also have "... =  (\<Sum>e\<in>\<E>. f' e * \<c> e + - f e * \<c> e)" 
    by (simp add: left_diff_distrib)
  also have "... =  (\<Sum>e\<in>\<E>. f' e * \<c> e) +  (\<Sum>e\<in>\<E>. - f e * \<c> e)"
    by(rule sum.distrib)
  finally show " (\<Sum>e\<in>\<EE>. difference f' f e * \<cc> e) = (\<Sum>e\<in>\<E>. f' e * \<c> e) - (\<Sum>e\<in>\<E>. f e * \<c> e)"
    using sum_negf[of "\<lambda> e. f e * \<c> e" \<E>] by simp
qed

text \<open>We collect the important lemmas on difference flows:\<close>

lemmas difference_lemmas = diff_of_diff_edge 
                           difference_less_rcap
                           pos_difference_pos_rcap
                           diff_is_res_circ
                           rcost_difference

text \<open>Korte and Vygen applied a flow decomposition result from a previous chapter.
Unfortunately, we could not use that since this would require more general theory on network 
flows and additionally,
in our formal setting the difference between a flow and a residual flow cannot simply be disregarded.
Despite this, the very essence of the proof is the same because the central idea of 
looking for a cycle by recursion is inherited.
\<close>

text \<open>We can derive the other direction of 
the optimality criterion by contradiction.
We assume that the flow was not optimum. 
Then take some flow with lesser costs and consider the difference flow.
This residual flow is a circulation which itself can be decomposed into some cycles.
Furthermore, we know that the costs of the residual flow equal the difference of flow costs.
From this we deduce that there has to be a negative cycle which can be transformed to a augmenting cycle.
However, that is impossible due to the premises.
\<close>

theorem no_augcycle_min_cost_flow:
assumes "f is b flow"
        "\<nexists> cs. augcycle f cs"
  shows "is_Opt b f"
proof(rule ccontr)
  assume "\<not> is_Opt b f"
  then obtain f' where f'_Def: "\<C> f' < \<C> f \<and> f' is b flow"
    using assms(1) unfolding is_Opt_def by force
  hence f_f'_diff_neg:"\<C> f' - \<C> f < 0" by simp
  define g where "g = difference f' f"
  have R_cost_g: "residual_flow.\<C> g = \<C> f' - \<C> f"
    by (simp add: g_def rcost_difference)
  have "residual_flow.flow_non_neg g" 
    by(simp add: diff_non_neg g_def residual_flow.flow_non_neg_def)
  moreover hence "0 \<le> residual_flow.Abs g" 
    by (simp add: sum_nonneg residual_flow.Abs_def residual_flow.flow_non_neg_def)
  moreover have "0 <  residual_flow.Abs g" 
  proof(rule ccontr)
    assume "\<not> 0 < residual_flow.Abs g"
    hence "residual_flow.Abs g = 0" 
      using \<open>0 \<le> residual_flow.Abs g\<close> by fastforce
    hence "\<forall> e \<in> \<EE>. g e = 0" 
      using \<open>residual_flow.flow_non_neg g\<close>   sum_nonneg_eq_0_iff[OF finite_\<EE>]
      by(auto simp add: residual_flow.flow_non_neg_def residual_flow.Abs_def)
    hence "residual_flow.support g = {}" 
      using residual_flow.support_def by auto
    hence "residual_flow.\<C> g = 0" 
      using \<open>\<forall>e\<in>\<EE>. g e = 0\<close> by (force simp add:  residual_flow.support_def residual_flow.\<C>_def)
    hence "\<C> f' - \<C> f = 0" 
      by (simp add: g_def rcost_difference)
    then show False 
      using f'_Def  by auto
  qed
  moreover have "residual_flow.is_circ g" 
    unfolding g_def
    using diff_is_res_circ assms f'_Def by simp
  thm residual_flow.flowcycle_decomposition[of g]

  moreover have "residual_flow.support g \<noteq> {}" 
  proof
    assume "residual_flow.support g = {}"
    hence "residual_flow.\<C> g = 0"
      using calculation(1)
      by(force intro!: sum.neutral[of \<EE> "\<lambda> e. g e * \<cc> e"]
               simp add:  residual_flow.support_def residual_flow.\<C>_def
                          residual_flow.flow_non_neg_def ) 
    hence "\<C> f' - \<C> f = 0" 
      by (simp add: g_def rcost_difference)
    then show False 
      using f'_Def  by auto
  qed

  thm residual_flow.flowcycle_decomposition[of g]
  ultimately obtain css ws where css_ws_def:
     "length css = length ws"
     "set css \<noteq> {}" "\<forall> w \<in> set ws. w > 0"
     "(\<forall>cs\<in>set css. residual_flow.flowcycle g cs \<and> set cs \<subseteq> residual_flow.support g \<and> distinct cs)"
     "(\<forall>e\<in>\<EE>. g e = (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0))"
    using  residual_flow.flowcycle_decomposition by blast
  hence "residual_flow.\<C> g = (\<Sum> e \<in> \<EE>. (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)"
    unfolding residual_flow.\<C>_def by simp
  also have "... = (\<Sum> e \<in> \<EE>.(\<Sum>i<length css.
                                        ((if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)))" 
   using sum_distrib_right by(fastforce intro: sum.cong)   
  also have "... = (\<Sum> i<length css. (\<Sum>e \<in> \<EE>. ((if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)))"
    by(rule sum.swap)
  finally have Rcost_sum: "residual_flow.\<C> g = (\<Sum>i<length css. \<Sum>e\<in>\<EE>. 
                                 (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)" by simp
  have "residual_flow.\<C> g < 0"  
    using  f_f'_diff_neg  R_cost_g by fastforce
  then obtain i where i_Def:"i<length css" 
              "(\<Sum>e\<in>\<EE>. (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e) < 0" 
    by (smt (verit, best) Rcost_sum lessThan_iff sum_nonneg)
  hence "set (css ! i) \<subseteq> residual_flow.support g"  
     using css_ws_def(4) nth_mem by blast
  hence "set (css ! i) \<subseteq> \<EE> " "\<forall> e \<in> set (css ! i). g e > 0" by(auto simp add: residual_flow.support_def)
  have support_subs: "residual_flow.support g \<subseteq>  \<EE>" 
    using residual_flow.support_def by force
  have "(\<Sum>e\<in>\<EE>. (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e) =
        (\<Sum>e\<in> ((\<EE> \<inter> residual_flow.support g ) \<union> (\<EE> - residual_flow.support g)). 
                                 (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)" 
    by (simp add: Int_Diff_Un) 
  also have "... = 
         (\<Sum>e\<in> (\<EE> \<inter> residual_flow.support g ) . (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)
        + (\<Sum>e\<in>  (\<EE> - residual_flow.support g). (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)" 
    by(rule sum.union_disjoint, simp add: finite_\<EE> , simp add: finite_\<EE>,
                                    simp add: finite_\<EE> Int_Diff_disjoint)
  also have "... = (\<Sum>e\<in> residual_flow.support g. (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)
        + (\<Sum>e\<in>{}. (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)" 
    using support_subs  \<open>set (css ! i) \<subseteq> residual_flow.support g\<close>
    by(fastforce intro: sum_eq_split sum.cong sum.neutral) +  
  also have "... = (\<Sum>e\<in> ((residual_flow.support g \<inter>  set (css ! i))\<union> (residual_flow.support g - set (css ! i)) ).
                          (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)" 
    by (simp add: Int_Diff_Un)
  also have "... = (\<Sum>e\<in> residual_flow.support g \<inter>  set (css ! i).
                          (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e) + 
                   (\<Sum>e\<in> residual_flow.support g - set (css ! i).
                          (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)"
    using finite_Diff[of "residual_flow.support g" "set (css ! i)"] finite_\<EE> rev_finite_subset support_subs 
    by (intro sum.union_disjoint) auto
  also have "... = (\<Sum>e\<in>  set (css ! i).
                          (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e) + 
                   (\<Sum>e\<in> residual_flow.support g - set (css ! i).0)"
    by(rule sum_eq_split)(simp add: Int_absorb1 \<open>set (css ! i) \<subseteq> residual_flow.support g\<close>)+
  also have "... =  (\<Sum>e\<in>  set (css ! i).
                          (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)" by simp
  finally have "(\<Sum>e\<in>\<EE>. (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)  = 
                (\<Sum>e\<in>  set (css ! i).
                          (if e \<in> set (css ! i) then ws ! i else 0) * \<cc> e)" by simp
  hence sum_weigt_c:"(\<Sum>e\<in>  set (css ! i). (ws ! i) * \<cc> e) < 0" 
    using i_Def by force
  have flowpath:  "css ! i \<noteq> []" "residual_flow.flowpath g (css ! i) "
    using css_ws_def  i_Def 
    by (simp add: residual_flow.flowcycle_def)+
  have "e \<in> residual_flow.support g \<Longrightarrow> rcap f e > 0" for e 
    using difference_less_rcap[of f f' e] assms(1) f'_Def g_def isbflow_def pos_difference_pos_rcap 
    by(force simp add: residual_flow.support_def)
  hence "\<forall> e \<in> set (css ! i). rcap f e > 0" 
    using \<open>set (css ! i) \<subseteq> residual_flow.support g\<close> by blast
  hence "augpath f (css ! i)"
    using flowpath ext[of to_vertex_pair make_pair_residual, OF to_vertex_pair_fst_snd]
          linorder_class.Min_gr_iff[of "rcap f ` (set (css ! i))"]
    by(auto simp add: augpath_def prepath_def residual_flow.flowpath_def residual_flow.multigraph_path_def Rcap_def)
  moreover have "fstv (hd  (css ! i)) = sndv (last  (css ! i))"
                              " distinct  (css ! i) \<and> set  (css ! i) \<subseteq> \<EE>" 
    using css_ws_def i_Def unfolding residual_flow.flowcycle_def 
    by (simp add: \<open>set (css ! i) \<subseteq> \<EE>\<close>)+
  moreover have "\<CC> (css ! i) < 0" 
  proof-
    have "(\<Sum>e\<in>  set (css ! i). (ws ! i) * \<cc> e) = 
           (ws ! i) * (\<Sum>e\<in>  set (css ! i). \<cc> e)" 
      by (metis sum.cong sum_distrib_left)
    also have 000:"... = (ws ! i)*(\<CC> (css ! i))" unfolding \<CC>_def by simp
    show "(\<CC> (css ! i)) < 0" 
     using calculation css_ws_def(1) css_ws_def(3) i_Def  sum_weigt_c unfolding \<CC>_def 
      by(auto intro: mul_zero_cancel[of "ws ! i"])
  qed
  ultimately have "augcycle f (css ! i)"
    unfolding augcycle_def 
    by simp
  thus False 
    using assms(2) 
    by simp
qed

text \<open>Finally, the optimality criterion.\<close>

corollary is_opt_iff_no_augcycle:
  assumes "f is b flow"
  shows "is_Opt b f \<longleftrightarrow> (\<nexists> cs. augcycle f cs)" 
  using assms min_cost_flow_no_augcycle no_augcycle_min_cost_flow 
  by auto

text \<open>By this both necessary and sufficient condition,
flow optimality can  be reduced to a comparably simple property 
concerning the structure of the residual graph.
This gives already rise to a first algorithm: After finding an initial $b$-flow,
use repeatedly some cycle-detection procedure and augment along those circuits.
As an invariant, we have flow validity, i.e. supplies, demands (both types of balances) 
and arc capacities are respected.
Correctness finally follows by termination due to the non-existence of any other augmenting cycles.

However, there is a different approach maintaining optimality throughout the algorithm while changing
the balances. We will see an invariant for this way of proceeding in the next section.
\<close>
end
end