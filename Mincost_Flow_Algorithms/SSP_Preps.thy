theory SSP_Preps imports PathAugOpt
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
  fixes
           \<b>::"'a \<Rightarrow> real"
   assumes 
         integral_u:  "\<And> e. e\<in> \<E> \<Longrightarrow> \<exists> n::nat. \<u> e = real n \<or> \<u> e = PInfty"
   and   integral_b:  "\<And> v. v\<in> \<V> \<Longrightarrow> \<exists> n::int. \<b> v =  n"
   and   is_balance_b: "is_balance \<b>"
begin

text \<open>Reachability by a path with at least $cap$ residual capacity.\<close>

definition resreach_cap::"('edge_type \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow>'a \<Rightarrow> 'a \<Rightarrow> bool" where
       "resreach_cap f cap u v \<equiv> (\<exists> p. awalk (to_vertex_pair ` \<EE>) u (map to_vertex_pair p) v 
                            \<and> Rcap f (set p) > (real cap) \<and> p \<noteq> [] \<and> set p \<subseteq> \<EE>)"

text \<open>We examine the relationship to augmenting paths.\<close>

lemma augpath_cap_to_resreach:
  assumes "augpath f es" "set es \<subseteq> \<EE>"
  shows "Rcap f (set es) > k \<Longrightarrow> resreach_cap f k (fstv (hd es)) (sndv (last es))"
  unfolding resreach_cap_def apply(rule exI[of _ es])
  using assms
  unfolding augpath_def resreach_cap_def Rcap_def prepath_def
  by(force intro: subset_mono_awalk'[of UNIV _ "(map to_vertex_pair es)" _ "to_vertex_pair ` \<EE>"])

lemma resreach_cap_to_augpath:
  assumes "resreach_cap f k u v"
  obtains es where "augpath f es" "Rcap f (set es) > k" "set es \<subseteq> \<EE>"
                   "fstv (hd es) = u" "sndv (last es) = v"
proof-
  assume assm: "(\<And>es. augpath f es \<Longrightarrow>
           real k < Rcap f (set es) \<Longrightarrow>
           set es \<subseteq> \<EE> \<Longrightarrow> fstv (hd es) = u \<Longrightarrow> sndv (last es) = v \<Longrightarrow> thesis)"
  obtain p where p_props: " awalk (to_vertex_pair ` \<EE>) u (map to_vertex_pair p) v"
                            "Rcap f (set p) > (real k)" "p \<noteq> [] " "set p \<subseteq> \<EE>"
    using assms unfolding resreach_cap_def by auto
  have uv_fst_last: "u = (fstv (hd p))" "v = sndv (last p)"
    using p_props(1) awalk_fst_last[of "map to_vertex_pair p" "to_vertex_pair ` \<EE>" u v]
    by (simp add: list.map_sel(1) p_props(3) vs_to_vertex_pair_pres
                last_map p_props(3))+
  show thesis
    apply(rule assm[of p])  
    unfolding augpath_def prepath_def
    using p_props uv_fst_last 
    by (auto    intro: subset_mono_awalk[of "to_vertex_pair ` \<EE>" _ "map to_vertex_pair p" _ UNIV]
             simp add: ereal_less_le zero_ereal_def)
qed

text \<open>The first invariant is rather basic. It requires a total sum of $0$ for balances,
which is the absolute modicum for having a well-defined and sound problem.\<close>

definition "invar1 state \<equiv> is_balance (balance state)"

lemma invar_1_props[dest!]: "invar1 state \<Longrightarrow> is_balance (balance state)"
  by (auto simp: invar1_def)

lemma invar_1_intro: " is_balance (balance state) \<Longrightarrow> invar1 state"
  by (auto simp: invar1_def)

text \<open>The second invariant talks about integrality.\<close>

definition "invar2 state \<equiv> (is_integral_flow (current_flow state) \<and>
                            is_integral_balance (balance state))"

text \<open>We provide corresponding introduction and elimination rules.\<close>

lemma invar2I: "is_integral_flow (current_flow state) \<Longrightarrow>
                is_integral_balance (balance state) \<Longrightarrow> invar2 state"
  unfolding invar2_def by simp

lemma is_integral_flowI: "(\<And> e. e \<in> \<E> \<Longrightarrow> \<exists> n::int. (f::_\<Rightarrow> real) e =  n) \<Longrightarrow>
                         is_integral_flow f"
  unfolding is_integral_flow_def by simp

lemma is_integral_flowE: "is_integral_flow f \<Longrightarrow>
                          ((\<And> e. e \<in> \<E> \<Longrightarrow> \<exists> n::int. f e = n) \<Longrightarrow> P) \<Longrightarrow>
                         P"
  unfolding is_integral_flow_def by simp

lemma is_integral_balanceI: "(\<And> v. v \<in> \<V> \<Longrightarrow> \<exists> n::int. (b::'a\<Rightarrow> real) v = n) \<Longrightarrow>
                              is_integral_balance b"
  unfolding is_integral_balance_def by simp

lemma is_integral_balanceE: "is_integral_balance b \<Longrightarrow>
                          ((\<And> v. v \<in> \<V> \<Longrightarrow> \<exists> n::int. (b::'a\<Rightarrow> real) v = n) \<Longrightarrow> P) \<Longrightarrow>
                             P"
  unfolding is_integral_balance_def by simp

text \<open>The third invariant is the most interesting one.
It states that the current flow is optimum for the 
\textit{difference} between the current balance and the initial balance. 
We will always prove preservation by using the hard-earned Theorem 9.11 from the previous theory.
\<close>

definition "invar3 state \<equiv> (is_Opt (\<lambda> v. \<b> v - balance state v) (current_flow state))"

text \<open>By augmenting an integral flow along a single edge by an integer, integrality is preserved.\<close>

lemma integral_flow_pres_single: "is_integral_flow f
         \<Longrightarrow> is_integral \<gamma> \<Longrightarrow> is_integral_flow (augment_edge f \<gamma> e)"
  using integral_add integral_sub is_integral_def is_integral_flow_def 
  by (auto intro: redge_pair_cases elim!: is_integral_flowE)

text \<open>The same holds when augmenting a whole bunch of arcs.\<close>

lemma integral_flow_pres:  "is_integral_flow f \<Longrightarrow> \<exists> n::int. (\<gamma>::real) =  n \<Longrightarrow>
                                   is_integral_flow (augment_edges f \<gamma> es)"
  apply(induction f \<gamma> es rule: augment_edges.induct)
  using augment_edges.simps(2) integral_flow_pres_single is_integral_def
  by auto

text \<open>For integral capacities and an integral flow, residual capacities are also integral.\<close>

lemma integral_flow_integral_rcap: 
  assumes "is_integral_flow f " 
          "e \<in> \<EE>" 
    shows "is_integral (real_of_ereal (rcap f e))"
  unfolding is_integral_def
  apply(cases "\<u> (oedge e)")
  subgoal
  apply(rule redge_pair_cases)
    subgoal
      by(rule is_integral_flowE[of f], simp add: assms)
        (metis assms(2) ereal.distinct(1) ereal_minus(1) integral_u o_edge_res oedge.simps(1)
                               of_int_diff of_int_of_nat_eq rcap.simps(1) real_of_ereal.simps(1))
    subgoal
      by(rule is_integral_flowE[of f], simp add: assms)
        (metis assms(2) o_edge_res oedge.simps(2) rcap.simps(2) real_of_ereal.simps(1))
    done
  subgoal 
    apply(rule redge_pair_cases) apply simp
    by (metis assms(1) assms(2) is_integral_flow_def o_edge_res oedge.simps(2) rcap.simps(2) 
        real_of_ereal.simps(1))
  subgoal
  using u_non_neg by  auto
  done

lemma integral_Min': "finite M \<Longrightarrow> M \<noteq> {} \<Longrightarrow>(\<And> x. x \<in> M \<Longrightarrow> 
                      is_integral (real_of_ereal x)) \<Longrightarrow> is_integral (real_of_ereal (Min M))"
  by(induction rule: finite.induct)(meson Min_in finite.insertI)+


text \<open>The previous result is lifted to lists of edges.\<close>

lemma Rcap_integral: "is_integral_flow f \<Longrightarrow> set es \<subseteq> \<EE> \<Longrightarrow> es\<noteq> [] \<Longrightarrow>
                      is_integral (real_of_ereal (Rcap f (set es)))"
  unfolding Rcap_def
  apply(rule is_integral_flowE, simp, rule integral_Min')
  using is_integral_def  in_mono integral_flow_integral_rcap is_integral_def by auto

text \<open>We define the absolute value of a balance.\<close>

definition "bABSnat (b::'a \<Rightarrow> real) = (\<Sum> v \<in> \<V>. nat \<lceil> ( abs (b v)) \<rceil>)"

text \<open>Monotonicity of $\vert b \vert$.\<close>

lemma bABSnat_mono: "is_integral_balance b \<Longrightarrow> is_integral_balance b' \<Longrightarrow>
                     (\<And> v. v \<in> \<V> \<Longrightarrow> abs (b v)  \<le>  abs (b' v)) \<Longrightarrow>
                     x \<in> \<V> \<Longrightarrow> abs (b x)  <  abs (b' x) \<Longrightarrow> bABSnat b < bABSnat b'"
  unfolding bABSnat_def
  apply(rule sum_strict_mono_ex1[of \<V>])
  using \<V>_finite apply blast
  apply(meson ceiling_mono nat_mono)
  apply(rule is_integral_balanceE, simp)
  apply(rule is_integral_balanceE, simp) 
  by (smt (verit, ccfv_threshold) less_ceiling_iff of_int_minus zless_nat_conj)

lemma is_integral_neg: "is_integral x \<Longrightarrow> is_integral (- x)"
  unfolding is_integral_def 
  by (metis of_int_minus)

lemmas is_integral_ceiling = ceiling_of_int

end
end