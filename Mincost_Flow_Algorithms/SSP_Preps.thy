theory SSP_Preps 
  imports Path_Aug_Opt
begin

section \<open>Definitions used by SSP and Capacity Scaling\<close>

text \<open>For indicating results we introduce markers $success$ and $failiure$.
 $notyetterm$ emblematizes that the computation was not completed yet.\<close>

datatype return = success | failure | notyetterm
record ('b, 'edge_type) Algo_state = current_flow::"'edge_type \<Rightarrow> real" 
                       balance::"'b \<Rightarrow> real" 
                       return::return

text \<open>For reasons of termination, one has to restrict to integer capacities and balances.
The following tiny locale is later used as a basis for the other locales promised.
\<close>

locale algo = cost_flow_network where fst = fst
  for fst::"'edge_type \<Rightarrow> 'a" +
  fixes \<b>::"'a \<Rightarrow> real"
   assumes integral_u:  "\<And> e. e\<in> \<E> \<Longrightarrow> \<exists> n::nat. \<u> e = real n \<or> \<u> e = PInfty"
   and   integral_b:  "\<And> v. v\<in> \<V> \<Longrightarrow> \<exists> n::int. \<b> v =  n"
   and   is_balance_b: "is_balance \<b>"
begin

text \<open>We examine the relationship to augmenting paths.\<close>

lemma augpath_cap_to_resreach:
  assumes "augpath f es" "set es \<subseteq> \<EE>"
  shows "Rcap f (set es) > k \<Longrightarrow> resreach_cap f k (fstv (hd es)) (sndv (last es))"
  unfolding resreach_cap_def 
proof(rule exI[of _ es], goal_cases)
  case 1
  then show ?case 
  using assms
  by(force intro: subset_mono_awalk'[of UNIV _ "(map to_vertex_pair es)" _ "to_vertex_pair ` \<EE>"]
        simp add: augpath_def resreach_cap_def Rcap_def prepath_def)
qed

lemma resreach_cap_to_augpath:
  assumes "resreach_cap f k u v"
  obtains es where "augpath f es" "Rcap f (set es) > k" "set es \<subseteq> \<EE>"
                   "fstv (hd es) = u" "sndv (last es) = v"
proof(goal_cases)
  case 1
  note assm = 1
  obtain p where p_props: " awalk (to_vertex_pair ` \<EE>) u (map to_vertex_pair p) v"
                            "Rcap f (set p) > (real k)" "p \<noteq> [] " "set p \<subseteq> \<EE>"
    using assms unfolding resreach_cap_def by auto
  have uv_fst_last: "u = (fstv (hd p))" "v = sndv (last p)"
    using p_props(1) awalk_fst_last[of "map to_vertex_pair p" "to_vertex_pair ` \<EE>" u v]
    by (simp add:list.map_sel(1)  p_props(3) vs_to_vertex_pair_pres
                last_map p_props(3))+
  show thesis 
    using p_props uv_fst_last 
    by (auto    intro: subset_mono_awalk[of "to_vertex_pair ` \<EE>" _ "map to_vertex_pair p" _ UNIV]
                       intro!: augpathI prepathI assm[of p]
             simp add: ereal_less_le zero_ereal_def)
qed

text \<open>The first invariant is rather basic. It requires a total sum of $0$ for balances,
which is the absolute modicum for having a well-defined and sound problem.\<close>

definition "invar1 state = is_balance (balance state)"

lemma invar_1_props[dest!]: "invar1 state \<Longrightarrow> is_balance (balance state)"
  by (auto simp: invar1_def)

lemma invar_1_intro: " is_balance (balance state) \<Longrightarrow> invar1 state"
  by (auto simp: invar1_def)

text \<open>The second invariant talks about integrality.\<close>

definition "invar2 state = (is_integral_flow (current_flow state) \<and>
                            is_integral_balance (balance state))"

text \<open>We provide corresponding introduction and elimination rules.\<close>

lemma invar2I: 
"\<lbrakk>is_integral_flow (current_flow state); is_integral_balance (balance state)\<rbrakk> \<Longrightarrow> invar2 state"
  by(auto simp add: invar2_def)

lemma invar2E: 
  "invar2 state \<Longrightarrow> 
  (\<lbrakk>is_integral_flow (current_flow state); is_integral_balance (balance state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: invar2_def)

lemma is_integral_flowI: 
 "(\<And> e. e \<in> \<E> \<Longrightarrow> \<exists> n::int. (f::_\<Rightarrow> real) e =  n) \<Longrightarrow> is_integral_flow f"
  by(auto simp add: is_integral_flow_def)

lemma is_integral_flowE: 
  "is_integral_flow f \<Longrightarrow>
   ((\<And> e. e \<in> \<E> \<Longrightarrow> \<exists> n::int. f e = n) \<Longrightarrow> P) 
   \<Longrightarrow> P"
  by(auto simp add: is_integral_flow_def)

lemma is_integral_flowD: 
  "is_integral_flow f \<Longrightarrow>  e \<in> \<E> \<Longrightarrow> \<exists> n::int. f e = n"
  by(auto simp add: is_integral_flow_def)

lemma is_integral_balanceI: 
  "(\<And> v. v \<in> \<V> \<Longrightarrow> \<exists> n::int. (b::'a\<Rightarrow> real) v = n) \<Longrightarrow>  is_integral_balance b"
  by(auto simp add: is_integral_balance_def)

lemma is_integral_balanceE: 
 "is_integral_balance b \<Longrightarrow>
  ((\<And> v. v \<in> \<V> \<Longrightarrow> \<exists> n::int. (b::'a\<Rightarrow> real) v = n) \<Longrightarrow> P) 
  \<Longrightarrow> P"
  by(auto simp add: is_integral_balance_def)

text \<open>The third invariant is the most interesting one.
It states that the current flow is optimum for the 
\textit{difference} between the current balance and the initial balance. 
We will always prove preservation by using the hard-earned Theorem 9.11 from the previous theory.
\<close>

definition "invar3 state = (is_Opt (\<lambda> v. \<b> v - balance state v) (current_flow state))"

text \<open>By augmenting an integral flow along a single edge by an integer, integrality is preserved.\<close>

lemma integral_flow_pres_single: 
 "\<lbrakk>is_integral_flow f; is_integral \<gamma>\<rbrakk> \<Longrightarrow> is_integral_flow (augment_edge f \<gamma> e)"
  using integral_add integral_sub is_integral_def is_integral_flow_def 
  by (auto intro: redge_pair_cases elim!: is_integral_flowE)

text \<open>The same holds when augmenting a whole bunch of arcs.\<close>

lemma integral_flow_pres: 
 "\<lbrakk>is_integral_flow f; \<exists> n::int. (\<gamma>::real) = n\<rbrakk> 
   \<Longrightarrow> is_integral_flow (augment_edges f \<gamma> es)"
  apply(induction f \<gamma> es rule: augment_edges.induct)
  using augment_edges.simps(2) integral_flow_pres_single is_integral_def
  by auto

text \<open>For integral capacities and an integral flow, residual capacities are also integral.\<close>

lemma integral_flow_integral_rcap: 
  assumes "is_integral_flow f " "e \<in> \<EE>" 
    shows "is_integral (real_of_ereal (rcap f e))"
proof(cases "\<u> (oedge e)", goal_cases)
  case (1 r)
  note one = this
    moreover obtain n where n: "f (oedge e) = real_of_int n"
      using is_integral_flowD[OF assms(1), of "(oedge e)"] assms(2) 
      by(auto simp add: \<EE>_def)
    moreover obtain n' where n': "\<u> (oedge e) = ereal (real n') \<or> \<u> (oedge e) = PInfty" 
      using  assms(2) integral_u[of "oedge e"] 
      by(auto simp add: o_edge_res) 
    moreover have "\<u> (oedge e) \<noteq> PInfty"
      by (simp add: one)
    ultimately have "is_integral (real n')" 
      using is_integralI of_int_of_nat_eq by metis
    then show ?case
      using one n n' 
      by (cases e)(auto intro!: integral_sub intro: is_integralI)
next
  case 2
    obtain n where n: "f (oedge e) = real_of_int n"
      using is_integral_flowD[OF assms(1), of "oedge e"] assms(2) 2
      by(auto simp add: \<EE>_def)
    then show ?case 
      using 2  assms(2) integral_u[of "oedge e"] 
      by(cases e)(auto simp add: \<EE>_def intro: is_integralI) 
next
  case MInf
  then show ?thesis 
   using u_non_neg by  auto
qed
 
lemma integral_Min': "finite M \<Longrightarrow> M \<noteq> {} \<Longrightarrow>(\<And> x. x \<in> M \<Longrightarrow> 
                      is_integral (real_of_ereal x)) \<Longrightarrow> is_integral (real_of_ereal (Min M))"
  by(induction rule: finite.induct)(meson Min_in finite.insertI)+


text \<open>The previous result is lifted to lists of edges.\<close>

lemma Rcap_integral: 
  assumes "is_integral_flow f" "set es \<subseteq> \<EE>" "es\<noteq> []"
  shows "is_integral (real_of_ereal (Rcap f (set es)))"
proof(rule is_integral_flowE[OF assms(1)], goal_cases)
  case 1
  show ?case
  proof(unfold Rcap_def, rule integral_Min', goal_cases)
    case (3 i)
    moreover have "\<lbrakk>i = \<uu>\<^bsub>f\<^esub>e; ereal r = \<uu>\<^bsub>f\<^esub>e; e \<in> set es\<rbrakk> \<Longrightarrow> is_integral r" for r e
      using integral_flow_integral_rcap[OF assms(1), of e] assms(2)
      by(cases "\<uu>\<^bsub>f\<^esub>e") auto
    ultimately show ?case
      by(cases i)
        (auto intro!: integral_Min' simp add: Rcap_def \<EE>_def intro: is_integralI)
  qed auto
qed

text \<open>We define the absolute value of a balance.\<close>

definition "bABSnat (b::'a \<Rightarrow> real) = (\<Sum> v \<in> \<V>. nat \<lceil> ( abs (b v)) \<rceil>)"

text \<open>Monotonicity of $\vert b \vert$.\<close>

lemma bABSnat_mono: 
  assumes "is_integral_balance b" "is_integral_balance b'"
          "(\<And> v. v \<in> \<V> \<Longrightarrow> abs (b v)  \<le>  abs (b' v))"
          "x \<in> \<V>" "abs (b x)  <  abs (b' x)" 
   shows "bABSnat b < bABSnat b'"
  unfolding bABSnat_def
proof(insert assms, rule sum_strict_mono_ex1[of \<V>], goal_cases)
  case 1
  then show ?case 
    using \<V>_finite by blast
next
  case 2
  then show ?case 
    using ceiling_mono nat_mono by blast
next
  case 3
   show ?case 
    apply(rule is_integral_balanceE[OF 3(1)])
     using 3(3)[OF 3(4)] 3(5)  of_int_minus "3"(4) ceiling_of_int of_int_abs
     by(force elim!: is_integral_balanceE[OF 3(2)] 
              intro: bexI[of _ x, OF _ 3(4)] 
           simp add: less_ceiling_iff)
 qed

lemma is_integral_neg: "is_integral x \<Longrightarrow> is_integral (- x)"
  unfolding is_integral_def 
  by (metis of_int_minus)

lemmas is_integral_ceiling = ceiling_of_int

end
end