theory Edmonds_Matching_LP
  imports Matching_LP HOL.Rings
begin

definition "odd_subsets X = {Y | Y. Y \<subseteq> X \<and> odd (card Y)}"

notation odd_subsets ("\<Omega> _")

lemma in_odd_subsetsI: "\<lbrakk>Y \<subseteq> X; odd (card Y)\<rbrakk> \<Longrightarrow> Y \<in> \<Omega> X"
and in_odd_subsetsE: "\<lbrakk> Y \<in> \<Omega> X; \<lbrakk>Y \<subseteq> X; odd (card Y)\<rbrakk> \<Longrightarrow>P\<rbrakk> \<Longrightarrow> P"
and  in_odd_subsetsD: "Y \<in> \<Omega> X \<Longrightarrow> Y \<subseteq> X"
                      "Y \<in> \<Omega> X \<Longrightarrow> odd (card Y)"
  by(auto simp add: odd_subsets_def)

lemma odd_subsets_finite: "finite X \<Longrightarrow> finite (\<Omega> X)"
  by(auto simp add: odd_subsets_def)

definition "end_sets E e = {U | U. U \<in> \<Omega> (Vs E) \<and> e \<in> Delta E U}"

lemma in_end_setsE:
 "\<lbrakk>U \<in> end_sets E e; \<lbrakk>U \<in> \<Omega> (Vs E); e \<in> Delta E U\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and in_end_setsI:
 "\<lbrakk>U \<in> \<Omega> (Vs E); e \<in> Delta E U\<rbrakk> \<Longrightarrow> U \<in> end_sets E e"
and in_end_setsD:
 "U \<in> end_sets E e \<Longrightarrow> U \<in> \<Omega> (Vs E)"
 "U \<in> end_sets E e \<Longrightarrow> e \<in> Delta E U"
  by(auto simp add: end_sets_def)

lemma finite_end_sets:
 "finite (Vs E) \<Longrightarrow> finite (end_sets E e)"
  by(auto simp add: end_sets_def Delta_def odd_subsets_finite)

definition "odd_subsets_strict X = {Y | Y. Y \<subseteq> X \<and> odd (card Y) \<and> card Y \<ge> 3}"

notation odd_subsets_strict ("\<Omega>\<^sub>\<ge>\<^sub>3 _")

lemma in_odd_subsets_strictI: "\<lbrakk>Y \<subseteq> X; odd (card Y); card Y \<ge> 3\<rbrakk> \<Longrightarrow> Y \<in> \<Omega>\<^sub>\<ge>\<^sub>3 X"
and in_odd_subsets_strictE: "\<lbrakk> Y \<in> \<Omega>\<^sub>\<ge>\<^sub>3 X; \<lbrakk>Y \<subseteq> X; odd (card Y); card Y \<ge> 3\<rbrakk> \<Longrightarrow>P\<rbrakk> \<Longrightarrow> P"
and  in_odd_subsets_strictD: 
 "Y \<in> \<Omega>\<^sub>\<ge>\<^sub>3 X \<Longrightarrow> Y \<subseteq> X" "Y \<in> \<Omega>\<^sub>\<ge>\<^sub>3 X \<Longrightarrow> odd (card Y)" "Y \<in> \<Omega>\<^sub>\<ge>\<^sub>3 X \<Longrightarrow> card Y \<ge> 3"
  by(auto simp add: odd_subsets_strict_def)

lemma odd_subsets_odd_subsets_strict:
  "\<Omega> X = {{x}| x. x \<in> X} \<union> \<Omega>\<^sub>\<ge>\<^sub>3 X"  "\<Omega> X \<supseteq> \<Omega>\<^sub>\<ge>\<^sub>3 X"
  by(auto intro!: nat_geq_3I 
        simp add: odd_subsets_def odd_subsets_strict_def card_1_singleton_iff)

lemma odd_subsets_strict_finite:
  "finite X \<Longrightarrow> finite (\<Omega>\<^sub>\<ge>\<^sub>3 X)"
  by(auto simp add: odd_subsets_strict_def)

lemma odd_subsets_odd_subsets_strict_sum:
  "finite X \<Longrightarrow> sum (\<lambda> x. f {x}) X + sum f (\<Omega>\<^sub>\<ge>\<^sub>3 X) = sum f (\<Omega> X)"
  unfolding odd_subsets_odd_subsets_strict
  by(subst comm_monoid_add_class.sum.union_disjoint)
    (auto intro!: arg_cong2[where f = "(+)"] arg_cong[where f = "sum f"]
           elim!: in_odd_subsets_strictE 
        simp add: odd_subsets_strict_finite sum_inner_function_to_image[OF inj_singleton])

definition "end_sets_strict E e = {U | U. U \<in>  \<Omega>\<^sub>\<ge>\<^sub>3 (Vs E) \<and> e \<in> Delta E U}"

lemma in_end_sets_strictE:
 "\<lbrakk>U \<in> end_sets_strict E e; \<lbrakk>U \<in>  \<Omega>\<^sub>\<ge>\<^sub>3 (Vs E); e \<in> Delta E U\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and in_end_sets_strictI:
 "\<lbrakk>U \<in>  \<Omega>\<^sub>\<ge>\<^sub>3 (Vs E); e \<in> Delta E U\<rbrakk> \<Longrightarrow> U \<in> end_sets_strict E e"
and in_end_sets_strictD:
 "U \<in> end_sets_strict E e \<Longrightarrow> U \<in>  \<Omega>\<^sub>\<ge>\<^sub>3 (Vs E)"
 "U \<in> end_sets_strict E e \<Longrightarrow> e \<in> Delta E U"
  by(auto simp add: end_sets_strict_def)

lemma end_sets_strict_in_omege_eps:
  "end_sets_strict E e \<subseteq> end_sets E e"
  by(auto simp add: end_sets_strict_def end_sets_def odd_subsets_odd_subsets_strict)

lemma finite_end_sets_strict:
 "finite (Vs E) \<Longrightarrow> finite (end_sets_strict E e)"
  by(auto simp add: end_sets_strict_def Delta_def odd_subsets_strict_finite)

definition "feasible_min_perfect_dual_edmonds E w (\<pi>::'v set \<Rightarrow> real) = 
 ((\<forall> e \<in> E. sum \<pi> (end_sets E e) \<le> w e) \<and> (\<forall> U \<in>  \<Omega>\<^sub>\<ge>\<^sub>3 (Vs E). \<pi> U \<ge> 0))"

lemma feasible_min_perfect_dual_edmondsI:
  "\<lbrakk>\<And> e. e \<in> E\<Longrightarrow> sum \<pi> (end_sets E e) \<le> w e;
    \<And> U. U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 (Vs E) \<Longrightarrow> \<pi> U \<ge> 0\<rbrakk>
   \<Longrightarrow> feasible_min_perfect_dual_edmonds E w \<pi>"
and feasible_min_perfect_dual_edmondsE:
  "\<lbrakk>feasible_min_perfect_dual_edmonds E w \<pi>;
    \<lbrakk>\<And> e. e \<in> E \<Longrightarrow> sum \<pi> (end_sets E e) \<le> w e; \<And> U. U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 (Vs E) \<Longrightarrow> \<pi> U \<ge> 0\<rbrakk> \<Longrightarrow>P\<rbrakk> \<Longrightarrow> P"
and feasible_min_perfect_dual_edmondsD:
  "\<lbrakk>feasible_min_perfect_dual_edmonds E w \<pi>; e \<in> E\<rbrakk> \<Longrightarrow> sum \<pi> (end_sets E e) \<le> w e"
   "\<lbrakk>feasible_min_perfect_dual_edmonds E w \<pi>; U \<in>  \<Omega>\<^sub>\<ge>\<^sub>3 (Vs E)\<rbrakk> \<Longrightarrow> \<pi> U \<ge> 0"
  by(auto simp add: feasible_min_perfect_dual_edmonds_def)

lemma end_sets_elementary_and_compound_endsets:
 "\<lbrakk>{u, v} \<in> E; u \<noteq> v\<rbrakk> 
  \<Longrightarrow> end_sets E {u, v} = {{u}, {v}} \<union> end_sets_strict E {u, v}"
  by(auto intro!: nat_geq_3I 
        simp add: end_sets_def odd_subsets_strict_def odd_subsets_def Delta_def doubleton_eq_iff
                  card_1_singleton_iff insert_commute end_sets_strict_def) 

lemma feasible_sum_end_sets_strict_positive:
  assumes "feasible_min_perfect_dual_edmonds E w \<pi>"
  shows "sum \<pi> (end_sets_strict E e) \<ge> 0"
    using assms
    by(auto elim!: in_end_sets_strictE feasible_min_perfect_dual_edmondsE 
           intro!: ordered_comm_monoid_add_class.sum_nonneg)

lemma sum_potential_end_sets_split_off_eps:
  assumes "e \<in> E" "e = {u, v}" "u \<noteq> v" "finite (Vs E)"
  shows "sum \<pi> (end_sets E e) = \<pi> {u} + \<pi> {v} + sum \<pi> (end_sets_strict E {u, v})"
proof((subst assms(2) end_sets_elementary_and_compound_endsets)+, goal_cases)
    case 1
    then show ?case 
      using assms by fastforce
  next
    case 2
    then show ?case 
      using assms by auto
  next
    case 3
    then show ?case 
    by(subst comm_monoid_add_class.sum.union_disjoint)
      (auto intro!: sum_of_two_things 
       elim!: in_end_sets_strictE in_odd_subsets_strictE 
       simp add:  finite_end_sets_strict assms)
qed

lemma feasible_min_perfect_dual_edmonds_is_feasible_min_perfect_dual:
  assumes "graph_invar E" "feasible_min_perfect_dual_edmonds E w \<pi>"
  shows "feasible_min_perfect_dual E w (\<lambda> x. \<pi> {x})"
proof(rule feasible_min_perfect_dualI, goal_cases)
  case (1 e u v)
  note one = this
  hence uv: "u \<noteq> v" 
    using assms(1) by(auto dest: graph_invar_edgeD)
  from 1 have "sum \<pi> (end_sets E {u, v}) \<le> w {u, v}"
    using assms(2)
    by(auto elim!: feasible_min_perfect_dual_edmondsE)
  moreover have "sum \<pi> (end_sets E e) = 
       \<pi> {u} + \<pi> {v} + sum \<pi> (end_sets_strict E {u, v})"
    using 1 uv assms
    by(auto intro!: sum_potential_end_sets_split_off_eps)
  moreover have "sum \<pi> (end_sets_strict E {u, v}) \<ge> 0"
    using assms(2) feasible_sum_end_sets_strict_positive by simp
  ultimately show ?case 
    by(simp add: 1)
qed

definition "odd_tight_subgraph E w \<pi> = {e | e. e \<in> E \<and> w e = sum \<pi> (end_sets E e)}"

lemma in_odd_tight_subgraphE:
  "\<lbrakk>e \<in> odd_tight_subgraph E w \<pi> ;
     \<lbrakk>e \<in> E; w e = sum \<pi> (end_sets E e)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and in_odd_tight_subgraphI:
  "\<lbrakk>e \<in> E; w e = sum \<pi> (end_sets E e)\<rbrakk> \<Longrightarrow> e \<in> odd_tight_subgraph E w \<pi> "
and in_odd_tight_subgraphD:
  "e \<in> odd_tight_subgraph E w \<pi> \<Longrightarrow> e \<in> E"
  "e \<in> odd_tight_subgraph E w \<pi> \<Longrightarrow> w e = sum \<pi> (end_sets E e)"
  by(auto simp add: odd_tight_subgraph_def)

lemma odd_tight_subgraph_in_graph: "odd_tight_subgraph G w \<pi> \<subseteq> G"
  by(auto simp add: odd_tight_subgraph_def)

lemma graph_invar_odd_tight_subgraph:
  "graph_invar G \<Longrightarrow> graph_invar (odd_tight_subgraph G w \<pi>)"
  using odd_tight_subgraph_in_graph[of G] graph_invar_subgraph[of G] by force

lemma weak_duality_theorem_nonneg_primal_min_eq_and_ineq: 
  fixes "A\<^sub>e\<^sub>q" :: "'a :: linordered_comm_semiring_strict mat" 
     and "A\<^sub>i\<^sub>e\<^sub>q" :: "'a :: linordered_comm_semiring_strict mat" 
  assumes Aeq: "A\<^sub>e\<^sub>q \<in> carrier_mat nr\<^sub>e\<^sub>q nc" and Aieq: "A\<^sub>i\<^sub>e\<^sub>q \<in> carrier_mat nr\<^sub>i\<^sub>e\<^sub>q nc" 
    and beq: "b\<^sub>e\<^sub>q \<in> carrier_vec nr\<^sub>e\<^sub>q" and bieq: "b\<^sub>i\<^sub>e\<^sub>q \<in> carrier_vec nr\<^sub>i\<^sub>e\<^sub>q" 
    and c: "c \<in> carrier_vec nc" 
    and x: "x \<in> carrier_vec nc" 
    and Aeqxb: "A\<^sub>e\<^sub>q *\<^sub>v x = b\<^sub>e\<^sub>q" and  Aieqxb: "A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x \<ge> b\<^sub>i\<^sub>e\<^sub>q"
    and x0: "x \<ge> 0\<^sub>v nc"
    and yieq0: "y\<^sub>i\<^sub>e\<^sub>q \<ge> 0\<^sub>v nr\<^sub>i\<^sub>e\<^sub>q" and  yeq: "y\<^sub>e\<^sub>q \<in> carrier_vec nr\<^sub>e\<^sub>q" 
    and yA: "(A\<^sub>e\<^sub>q @\<^sub>r A\<^sub>i\<^sub>e\<^sub>q)\<^sup>T *\<^sub>v (y\<^sub>e\<^sub>q@\<^sub>vy\<^sub>i\<^sub>e\<^sub>q) \<le> c"
  shows "c \<bullet> x \<ge> (b\<^sub>e\<^sub>q @\<^sub>v b\<^sub>i\<^sub>e\<^sub>q) \<bullet> (y\<^sub>e\<^sub>q @\<^sub>v y\<^sub>i\<^sub>e\<^sub>q)"
proof-
  have yieq: "y\<^sub>i\<^sub>e\<^sub>q \<in> carrier_vec nr\<^sub>i\<^sub>e\<^sub>q"
    using carrier_vec_dim_vec[of y\<^sub>i\<^sub>e\<^sub>q] yieq0 index_zero_vec(2)[of nr\<^sub>i\<^sub>e\<^sub>q] 
    by (auto simp add: less_eq_vec_def)
  have carrier1:"A\<^sub>e\<^sub>q *\<^sub>v x \<in> carrier_vec nr\<^sub>e\<^sub>q" 
    by (simp add: Aeqxb beq)
  have carrier2: "A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x \<in> carrier_vec nr\<^sub>i\<^sub>e\<^sub>q"
    using Aieq x by auto
  have "c \<bullet> x \<ge> ((A\<^sub>e\<^sub>q @\<^sub>r A\<^sub>i\<^sub>e\<^sub>q)\<^sup>T *\<^sub>v (y\<^sub>e\<^sub>q@\<^sub>vy\<^sub>i\<^sub>e\<^sub>q)) \<bullet> x" 
    using x0 yA c
    by (auto intro!: sum_mono mult_right_mono simp: less_eq_vec_def scalar_prod_def)
  moreover have "((A\<^sub>e\<^sub>q @\<^sub>r A\<^sub>i\<^sub>e\<^sub>q)\<^sup>T *\<^sub>v (y\<^sub>e\<^sub>q@\<^sub>vy\<^sub>i\<^sub>e\<^sub>q)) \<bullet> x = 
           y\<^sub>e\<^sub>q \<bullet> (A\<^sub>e\<^sub>q *\<^sub>v x) + y\<^sub>i\<^sub>e\<^sub>q \<bullet> (A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x)"
    using yeq yieq carrier1 carrier2  Aeq Aieq x
    by(auto simp add: scalar_prod_append mat_mult_append 
                      transpose_vec_mult_scalar[OF carrier_append_rows  _ append_carrier_vec])
  moreover have " y\<^sub>e\<^sub>q \<bullet> (A\<^sub>e\<^sub>q *\<^sub>v x) + y\<^sub>i\<^sub>e\<^sub>q \<bullet> (A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x) \<ge>  y\<^sub>e\<^sub>q \<bullet> b\<^sub>e\<^sub>q + y\<^sub>i\<^sub>e\<^sub>q \<bullet> b\<^sub>i\<^sub>e\<^sub>q"
    using Aeq Aieq beq bieq Aeqxb Aieqxb yieq0
    by(auto intro!: ordered_ab_semigroup_add_class.add_mono  sum_mono mult_left_mono 
         simp add: scalar_prod_def simp: less_eq_vec_def)
  moreover have "y\<^sub>e\<^sub>q \<bullet> b\<^sub>e\<^sub>q + y\<^sub>i\<^sub>e\<^sub>q \<bullet> b\<^sub>i\<^sub>e\<^sub>q = (b\<^sub>e\<^sub>q @\<^sub>v b\<^sub>i\<^sub>e\<^sub>q) \<bullet> (y\<^sub>e\<^sub>q @\<^sub>v y\<^sub>i\<^sub>e\<^sub>q)"
    using beq bieq yeq yieq
    by(simp add: scalar_prod_append comm_scalar_prod)
  ultimately show ?thesis
    by auto
qed
 
lemma complementary_slackness_nonneg_primal_min_eq_and_ineq: 
  fixes "A\<^sub>e\<^sub>q" :: "real mat" 
     and "A\<^sub>i\<^sub>e\<^sub>q" :: "real mat" 
  assumes Aeq: "A\<^sub>e\<^sub>q \<in> carrier_mat nr\<^sub>e\<^sub>q nc" and Aieq: "A\<^sub>i\<^sub>e\<^sub>q \<in> carrier_mat nr\<^sub>i\<^sub>e\<^sub>q nc" 
    and beq: "b\<^sub>e\<^sub>q \<in> carrier_vec nr\<^sub>e\<^sub>q" and bieq: "b\<^sub>i\<^sub>e\<^sub>q \<in> carrier_vec nr\<^sub>i\<^sub>e\<^sub>q" 
    and c: "c \<in> carrier_vec nc" 
    and x: "x \<in> carrier_vec nc" 
    and  yeq: "y\<^sub>e\<^sub>q \<in> carrier_vec nr\<^sub>e\<^sub>q"
    (*primal feasibilty*)
    and Aeqxb: "A\<^sub>e\<^sub>q *\<^sub>v x = b\<^sub>e\<^sub>q" and  Aieqxb: "A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x \<ge> b\<^sub>i\<^sub>e\<^sub>q" and x0: "x \<ge> 0\<^sub>v nc"
    (*dual feasibility*)
    and yA: "(A\<^sub>e\<^sub>q @\<^sub>r A\<^sub>i\<^sub>e\<^sub>q)\<^sup>T *\<^sub>v (y\<^sub>e\<^sub>q@\<^sub>vy\<^sub>i\<^sub>e\<^sub>q) \<le> c" and yieq0: "y\<^sub>i\<^sub>e\<^sub>q \<ge> 0\<^sub>v nr\<^sub>i\<^sub>e\<^sub>q"
    (*primal slack*)
    and slack_primal: "(b\<^sub>i\<^sub>e\<^sub>q - A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x)\<bullet>y\<^sub>i\<^sub>e\<^sub>q = 0"
    (*dual slack*)
    and slack_dual: "(c - (A\<^sub>e\<^sub>q @\<^sub>r A\<^sub>i\<^sub>e\<^sub>q)\<^sup>T *\<^sub>v (y\<^sub>e\<^sub>q@\<^sub>vy\<^sub>i\<^sub>e\<^sub>q))\<bullet>x = 0"
  shows "c \<bullet> x = (b\<^sub>e\<^sub>q @\<^sub>v b\<^sub>i\<^sub>e\<^sub>q) \<bullet> (y\<^sub>e\<^sub>q @\<^sub>v y\<^sub>i\<^sub>e\<^sub>q)"
proof-
  have yieq: "y\<^sub>i\<^sub>e\<^sub>q \<in> carrier_vec nr\<^sub>i\<^sub>e\<^sub>q"
    using carrier_vec_dim_vec[of y\<^sub>i\<^sub>e\<^sub>q] yieq0 index_zero_vec(2)[of nr\<^sub>i\<^sub>e\<^sub>q]
    by(auto simp add: less_eq_vec_def)
  have carrier1:"A\<^sub>e\<^sub>q *\<^sub>v x \<in> carrier_vec nr\<^sub>e\<^sub>q" 
    by (simp add: Aeqxb beq)
  have carrier2: "A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x \<in> carrier_vec nr\<^sub>i\<^sub>e\<^sub>q"
    using Aieq x by auto
  have carrier3: "(A\<^sub>e\<^sub>q @\<^sub>r A\<^sub>i\<^sub>e\<^sub>q)\<^sup>T *\<^sub>v (y\<^sub>e\<^sub>q @\<^sub>v y\<^sub>i\<^sub>e\<^sub>q) \<in> carrier_vec nc"
    using c yA unfolding carrier_dim_vec less_eq_vec_def by blast
  have cx_is: "c \<bullet> x = ((A\<^sub>e\<^sub>q @\<^sub>r A\<^sub>i\<^sub>e\<^sub>q)\<^sup>T *\<^sub>v (y\<^sub>e\<^sub>q@\<^sub>vy\<^sub>i\<^sub>e\<^sub>q)) \<bullet> x"
    using slack_dual c carrier3 x by(simp add: minus_scalar_prod_distrib)
  moreover have "((A\<^sub>e\<^sub>q @\<^sub>r A\<^sub>i\<^sub>e\<^sub>q)\<^sup>T *\<^sub>v (y\<^sub>e\<^sub>q@\<^sub>vy\<^sub>i\<^sub>e\<^sub>q)) \<bullet> x = 
           y\<^sub>e\<^sub>q \<bullet> (A\<^sub>e\<^sub>q *\<^sub>v x) + y\<^sub>i\<^sub>e\<^sub>q \<bullet> (A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x)"
    using yeq yieq carrier1 carrier2  Aeq Aieq x
    by(auto simp add: scalar_prod_append mat_mult_append 
                      transpose_vec_mult_scalar[OF carrier_append_rows  _ append_carrier_vec])
  moreover have " y\<^sub>e\<^sub>q \<bullet> (A\<^sub>e\<^sub>q *\<^sub>v x) + y\<^sub>i\<^sub>e\<^sub>q \<bullet> (A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x) =  y\<^sub>e\<^sub>q \<bullet> b\<^sub>e\<^sub>q + y\<^sub>i\<^sub>e\<^sub>q \<bullet> (A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x)"
    using Aeq Aieq beq bieq Aeqxb Aieqxb yieq0 slack_primal by auto
  moreover have " y\<^sub>i\<^sub>e\<^sub>q \<bullet> (A\<^sub>i\<^sub>e\<^sub>q *\<^sub>v x) = y\<^sub>i\<^sub>e\<^sub>q \<bullet> b\<^sub>i\<^sub>e\<^sub>q"
    using bieq carrier2 slack_primal yieq 
    by(simp add: minus_scalar_prod_distrib comm_scalar_prod)
  moreover have "y\<^sub>e\<^sub>q \<bullet> b\<^sub>e\<^sub>q + y\<^sub>i\<^sub>e\<^sub>q \<bullet> b\<^sub>i\<^sub>e\<^sub>q = (b\<^sub>e\<^sub>q @\<^sub>v b\<^sub>i\<^sub>e\<^sub>q) \<bullet> (y\<^sub>e\<^sub>q @\<^sub>v y\<^sub>i\<^sub>e\<^sub>q)"
    using beq bieq yeq yieq
    by(simp add: scalar_prod_append comm_scalar_prod)
  ultimately show ?thesis
    by auto
qed

locale edmonds_matching_lp =
 matching_lp_basic where V = V for V ::"'v set" +
fixes \<Omega>\<^sub>3_enum::"'v set \<Rightarrow> nat"
  and \<Omega>\<^sub>3_enum_inv::"nat \<Rightarrow> 'v set"
assumes bij_\<Omega>\<^sub>3_enum: "bij_betw \<Omega>\<^sub>3_enum (\<Omega>\<^sub>\<ge>\<^sub>3 V) {0..< card (\<Omega>\<^sub>\<ge>\<^sub>3 V)}"
  and \<Omega>\<^sub>3_enum_\<Omega>\<^sub>3_enum_inv: "\<And> U. U \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 V) \<Longrightarrow> \<Omega>\<^sub>3_enum_inv (\<Omega>\<^sub>3_enum U) = U"
begin

lemma bij_\<Omega>\<^sub>3_enum_inv[matching_lp_theorems]: "bij_betw \<Omega>\<^sub>3_enum_inv {0..< card (\<Omega>\<^sub>\<ge>\<^sub>3 V)} (\<Omega>\<^sub>\<ge>\<^sub>3 V)"
proof-
  have "\<lbrakk>x < card (\<Omega>\<^sub>\<ge>\<^sub>3 V); y < card (\<Omega>\<^sub>\<ge>\<^sub>3 V); \<Omega>\<^sub>3_enum_inv x = \<Omega>\<^sub>3_enum_inv y\<rbrakk> \<Longrightarrow> x = y" for x y
    by (metis \<Omega>\<^sub>3_enum_\<Omega>\<^sub>3_enum_inv atLeastLessThan_iff bij_\<Omega>\<^sub>3_enum bij_betw_def imageE zero_le)
  moreover have "xa < card (\<Omega>\<^sub>\<ge>\<^sub>3 V) \<Longrightarrow> \<Omega>\<^sub>3_enum_inv xa \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 V)" for xa
    by (metis (full_types) atLeastLessThan_iff bij_\<Omega>\<^sub>3_enum bij_betw_def imageE
        \<Omega>\<^sub>3_enum_\<Omega>\<^sub>3_enum_inv  zero_le)
  moreover have "x \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 V) \<Longrightarrow> x \<in> \<Omega>\<^sub>3_enum_inv ` {0..<card (\<Omega>\<^sub>\<ge>\<^sub>3 V)}" for x
    by (metis \<Omega>\<^sub>3_enum_\<Omega>\<^sub>3_enum_inv bij_\<Omega>\<^sub>3_enum bij_betwE imageI)
  ultimately show ?thesis
    by(auto simp add: bij_betw_def inj_on_def)
qed

definition "\<omega> = card (\<Omega>\<^sub>\<ge>\<^sub>3 V)"

lemmas omega_def = \<omega>_def

definition omega_delta_matrix :: "real mat" where
  "omega_delta_matrix = mat \<omega> m (\<lambda>(i,j). of_bool ( G_enum_inv j \<in> Delta G (\<Omega>\<^sub>3_enum_inv i)))"

definition dual_omega_sol::"('v set \<Rightarrow> real) \<Rightarrow> real vec" where
  "dual_omega_sol \<pi> = vec \<omega> (\<lambda> i. \<pi> (\<Omega>\<^sub>3_enum_inv i))"

lemmas [matching_lp_theorems] = 
  primal_sol_def incidence_matrix_def weight_vect_def dual_sol_def n_def
  dual_omega_sol_def omega_def omega_delta_matrix_def

lemma omega_delta_matrix_carrier_mat[intro, matching_lp_theorems]: 
  "omega_delta_matrix \<in> carrier_mat \<omega> m"
  unfolding omega_delta_matrix_def by simp

lemma omega_delta_matrix_dims[intro, matching_lp_theorems, simp]: 
  "dim_col omega_delta_matrix = m" "dim_row omega_delta_matrix = \<omega>"
  unfolding omega_delta_matrix_def by simp+

lemma dim_weight_dual_omega_sol[simp,matching_lp_theorems]: "dim_vec (dual_omega_sol \<pi>) = \<omega>" 
and dual_omega_sol_carrier_vec[intro,matching_lp_theorems]: "dual_omega_sol \<pi> \<in> carrier_vec \<omega>"
  by(auto simp add: dual_omega_sol_def)

lemma dim_bot_matrices: "dim_row (incidence_matrix @\<^sub>r omega_delta_matrix) = n + \<omega>"
  using carrier_matD(1) by blast

lemma row_of_big_matrix_at_edge's_index_is:
  assumes "i < n + \<omega>" "ie < m"
  shows "row (incidence_matrix @\<^sub>r omega_delta_matrix) i $ ie 
        = (if i < n \<and> Vs_enum_inv i \<in> G_enum_inv ie then 1
           else if i < n then 0
           else if G_enum_inv ie \<in> Delta G (\<Omega>\<^sub>3_enum_inv (i - n)) then 1
           else 0)"
  using assms
  by(auto simp add: incidence_matrix_def omega_delta_matrix_def append_rows_def)

lemma \<Omega>\<^sub>3_inv_enum[simp,matching_lp_theorems]: "U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V \<Longrightarrow> \<Omega>\<^sub>3_enum_inv (\<Omega>\<^sub>3_enum U) = U"
  by(auto intro!: \<Omega>\<^sub>3_enum_\<Omega>\<^sub>3_enum_inv)

lemma \<Omega>\<^sub>3_enum_inv[simp,matching_lp_theorems]: 
  assumes"i < card (\<Omega>\<^sub>\<ge>\<^sub>3 V)" 
  shows "\<Omega>\<^sub>3_enum (\<Omega>\<^sub>3_enum_inv i) = i"
proof(rule ccontr)
  assume asm: "\<Omega>\<^sub>3_enum (\<Omega>\<^sub>3_enum_inv i) \<noteq> i"
  have "i \<in> {0..<card (\<Omega>\<^sub>\<ge>\<^sub>3 V)}"
    using assms by auto
  then show False
    using bij_\<Omega>\<^sub>3_enum bij_\<Omega>\<^sub>3_enum_inv asm  \<Omega>\<^sub>3_inv_enum imageE[of i \<Omega>\<^sub>3_enum "\<Omega>\<^sub>\<ge>\<^sub>3 V"] 
    by (force elim!: bij_betwE inj_onE)
qed

lemma \<Omega>\<^sub>3_enum_less_card[matching_lp_theorems]: "U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V \<Longrightarrow> \<Omega>\<^sub>3_enum U < card (\<Omega>\<^sub>\<ge>\<^sub>3 V)"
  by (metis atLeastLessThan_iff bij_\<Omega>\<^sub>3_enum bij_betw_def imageI)

lemma \<Omega>\<^sub>3_enum_less_n[matching_lp_theorems]: "U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V \<Longrightarrow> \<Omega>\<^sub>3_enum U  < \<omega>"
  by (simp add: \<Omega>\<^sub>3_enum_less_card omega_def)

lemma \<Omega>\<^sub>3_of_G_enum_less_n[matching_lp_theorems]: 
   "\<lbrakk>U \<subseteq> Vs G; odd (card U); 3 \<le> card U\<rbrakk> \<Longrightarrow> \<Omega>\<^sub>3_enum U < \<omega>"
  using G_in_V
  by(auto intro!:  \<Omega>\<^sub>3_enum_less_n in_odd_subsets_strictI)

lemma
  shows  \<Omega>\<^sub>3_enum_inv'[simp,matching_lp_theorems]: "i < \<omega> \<Longrightarrow> \<Omega>\<^sub>3_enum (\<Omega>\<^sub>3_enum_inv i) = i"
    and \<Omega>\<^sub>3_enum_inv_in_G[simp,matching_lp_theorems]: "i < \<omega> \<Longrightarrow> (\<Omega>\<^sub>3_enum_inv i) \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V"
  using  bij_\<Omega>\<^sub>3_enum_inv Fun.bij_betwE[of \<Omega>\<^sub>3_enum_inv "{0..<\<omega>}" "\<Omega>\<^sub>\<ge>\<^sub>3 V"] 
  by (auto simp add: omega_def)

lemma \<Omega>\<^sub>3_enum_inv_inj_below_omega[matching_lp_theorems]:
  "\<lbrakk>\<Omega>\<^sub>3_enum_inv i = \<Omega>\<^sub>3_enum_inv j; i < \<omega>; j < \<omega>\<rbrakk> \<Longrightarrow> i = j"
  using \<Omega>\<^sub>3_enum_inv' by fastforce

lemma dual_omega_sol_i_is[matching_lp_theorems]: "i < \<omega> \<Longrightarrow> dual_omega_sol \<pi> $ i =  \<pi> (\<Omega>\<^sub>3_enum_inv i)"
  by(auto simp add: dual_omega_sol_def)

lemma \<Omega>\<^sub>3_enum_inv_inj_on: "inj_on \<Omega>\<^sub>3_enum_inv {0..<\<omega>}"
  using bij_\<Omega>\<^sub>3_enum_inv bij_betw_def omega_def by auto

lemma \<Omega>\<^sub>3_enum_inj_on: "inj_on \<Omega>\<^sub>3_enum (\<Omega>\<^sub>\<ge>\<^sub>3 V)"
  using bij_\<Omega>\<^sub>3_enum bij_betw_def by blast

lemma omega_entries_delta_count[matching_lp_theorems]:
  assumes "E \<subseteq> G" "i < \<omega>"
  shows  "(omega_delta_matrix *\<^sub>v primal_sol E) $ i = card (Delta E (\<Omega>\<^sub>3_enum_inv i))"
  unfolding omega_delta_matrix_def primal_sol_def mult_mat_vec_def scalar_prod_def
proof (simp_all add: index_vec[OF assms(2)], goal_cases)
  case 1
   show ?case 
   proof(subst sum.cong[OF refl, where h = "\<lambda> j. of_bool (G_enum_inv j \<in> Delta G (\<Omega>\<^sub>3_enum_inv i))"],
         goal_cases)
     case (1 j)
     then show ?case 
       using assms(2) by simp
   next
     case 2
     then show ?case 
       unfolding of_bool_def
     proof(subst comm_monoid_add_class.sum.inter_filter[symmetric], goal_cases)
       case 2
       then show ?case 
         using  assms(1) 
         by(auto intro!: card_bij_eq[of G_enum_inv _ _ G_enum]
                         inj_on_subset[OF G_enum_inv_inj_on] 
                         inj_on_subset[OF G_enum_inj_on] Delta_finite
                   dest: in_DeltaD(2)
                  intro: Delta_set_mp[OF assms(1)] Delta_inverse_set_mp[OF assms(1)]
               simp add: G_inv_enum[OF set_mp[OF _ in_DeltaD(2)]] finite_G finite_subset)
     qed simp
   qed
 qed

lemma perfect_matching_feasible_omega[matching_lp_theorems]:
  assumes "dblton_graph G" "perfect_matching G M" "Vs G = V"
  shows "omega_delta_matrix *\<^sub>v primal_sol M \<ge> 1\<^sub>v \<omega>" 
proof-
  have p_m_unfolded: "M \<subseteq> G" "matching M" "Vs G = Vs M"
    using assms by (auto simp add: perfect_matchingD)
  show ?thesis
    unfolding less_eq_vec_def 
  proof(rule, goal_cases)
    case 1
    then show ?case
      using  omega_delta_matrix_carrier_mat by auto
  next
    case 2
    then show ?case 
    proof(rule+, goal_cases)
      case (1 i)
      hence i_omega:"i < \<omega>"
        using  omega_delta_matrix_carrier_mat by auto
      hence in_odd:"\<Omega>\<^sub>3_enum_inv i \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V"
        by simp
       show ?case
        using p_m_unfolded(1) i_omega
              perfect_maching_odd_set_delta_geq_1[simplified, of "\<Omega>\<^sub>3_enum_inv i" G M]
              finite_VsG in_odd_subsets_strictD(2)[OF in_odd]
        by(subst omega_entries_delta_count)
          (auto simp add: assms(3,2,1) in_odd_subsets_strictD(1))
    qed
  qed
qed

lemma omega_delta_col_times_dual_omega_sol:
  assumes "e \<in> G" "G_enum e = i" "Vs G = V"
  shows "col omega_delta_matrix i \<bullet> dual_omega_sol \<pi> = sum \<pi> (end_sets_strict G e)"
proof-
  have "(\<Sum>ia = 0..<\<omega>. of_bool (G_enum_inv i \<in> Delta G (\<Omega>\<^sub>3_enum_inv ia)) * \<pi> (\<Omega>\<^sub>3_enum_inv ia)) =
    sum \<pi> (end_sets_strict G e)"
  proof-
   have inv:"G_enum_inv i = e" 
    using assms(1,2) by force
   hence "(\<Sum>ia\<in>{0..<\<omega>} \<inter> {ia. G_enum_inv i \<in> Delta G (\<Omega>\<^sub>3_enum_inv ia)}. \<pi> (\<Omega>\<^sub>3_enum_inv ia)) =
    sum \<pi> (end_sets_strict G (G_enum_inv i))"
    by(subst comm_monoid_add_class.sum.reindex[of "\<Omega>\<^sub>3_enum_inv" _ \<pi>, simplified, symmetric])
      (auto intro!: inj_on_subset[OF \<Omega>\<^sub>3_enum_inv_inj_on] arg_cong[where f = "sum \<pi>"]
                    in_end_sets_strictI 
                    rev_image_eqI[of "\<Omega>\<^sub>3_enum _" _ _ \<Omega>\<^sub>3_enum_inv, where uu4 = x and b = x for x]
                    \<Omega>\<^sub>3_enum_less_n
          simp add: assms(1,3)
             elim!: in_end_sets_strictE)
   thus ?thesis
    by (auto simp add: inv)
   qed 
  thus ?thesis
   using G_enum_less_card_G assms(1,2)
   unfolding scalar_prod_def omega_delta_matrix_def col_def dual_omega_sol_def
   by(subst sum.cong[OF refl, where h = "\<lambda> ia. of_bool (G_enum_inv i \<in> Delta G (\<Omega>\<^sub>3_enum_inv ia)) 
                * \<pi> (\<Omega>\<^sub>3_enum_inv ia)"])
     auto
qed

lemma dual_omega_sol_at_index: "i < \<omega> \<Longrightarrow> dual_omega_sol \<pi> $ i = \<pi> (\<Omega>\<^sub>3_enum_inv i)"
  by(auto simp add: dual_omega_sol_def)

lemma is_sum_end_sets:
  assumes "i < m" "dblton_graph G"  "Vs G = V"
  shows "col incidence_matrix i \<bullet> dual_sol (\<lambda>x. \<pi> {x}) + col omega_delta_matrix i \<bullet> dual_omega_sol \<pi>
         = sum \<pi> (end_sets G (G_enum_inv i))"
  proof-
    obtain e where e: "e \<in> G" "G_enum e = i" "G_enum_inv i = e" 
      using assms by fastforce
    moreover then obtain x y where xy: "e = {x, y}" "x \<noteq> y" 
      using assms(2) by auto
    ultimately show ?thesis
      using assms  finite_VsG
      by(simp add: incidence_col_times_dual_sol[of x y i "\<lambda>x. \<pi> {x}"]
                   omega_delta_col_times_dual_omega_sol weight_vect_at_index
                   sum_potential_end_sets_split_off_eps[of _ _ x y])
  qed

lemma dual_omega_dot_pi_vect_pi_sum: "1\<^sub>v \<omega> \<bullet> dual_omega_sol \<pi> = sum \<pi> (\<Omega>\<^sub>\<ge>\<^sub>3 V)"
proof-
  have "(\<Sum>i = 0..<\<omega>. \<pi> (\<Omega>\<^sub>3_enum_inv i)) = sum \<pi> \<Omega>\<^sub>\<ge>\<^sub>3 V"
   using \<Omega>\<^sub>3_enum_inv_inj_on 
   by(subst comm_monoid_add_class.sum.reindex[of \<Omega>\<^sub>3_enum_inv, simplified, symmetric])
     (auto intro!: arg_cong[where f = "sum \<pi>"]
                   rev_image_eqI[ where b = x and x = "\<Omega>\<^sub>3_enum x" for x]
         simp add: \<Omega>\<^sub>3_enum_less_n)
  thus ?thesis
  by(auto simp add: scalar_prod_def dual_omega_sol_def)
qed

lemma potential_sum_graph_matrix:
  assumes "dblton_graph G"  "Vs G = V"
  shows "(1\<^sub>v n @\<^sub>v 1\<^sub>v \<omega>) \<bullet> (dual_sol (\<lambda>x. \<pi> {x}) @\<^sub>v dual_omega_sol \<pi>) = sum \<pi> (\<Omega> V)"
  using finite_VsG[simplified assms(2)]
  by(subst scalar_prod_append)
    (auto simp add: odd_subsets_odd_subsets_strict_sum dual_dot_y_vect_y_sum
                    dual_omega_dot_pi_vect_pi_sum)

lemma dual_sol_lp_feasible_edmonds[matching_lp_theorems]:
  assumes "feasible_min_perfect_dual_edmonds G w \<pi>" "dblton_graph G"  "Vs G = V"
  shows  "incidence_matrix\<^sup>T *\<^sub>v dual_sol (\<lambda>x. \<pi> {x}) + omega_delta_matrix\<^sup>T *\<^sub>v dual_omega_sol \<pi>
         \<le> weight_vect w" (is ?th1)
         "(incidence_matrix @\<^sub>r omega_delta_matrix)\<^sup>T *\<^sub>v (dual_sol (\<lambda>x. \<pi> {x}) @\<^sub>v dual_omega_sol \<pi>)
         \<le> weight_vect w" (is ?th2)
        "0\<^sub>v \<omega> \<le> dual_omega_sol \<pi>" (is ?th3)
proof-
  note feasible_min_perfect_dual_edmondsD = feasible_min_perfect_dual_edmondsD[OF assms(1)]

  have "col incidence_matrix i \<bullet> dual_sol (\<lambda>x. \<pi> {x}) + col omega_delta_matrix i \<bullet> dual_omega_sol \<pi>
         \<le> weight_vect w $ i"
    if asm: "i < m" for i
    using asm assms
    by(auto intro!: feasible_min_perfect_dual_edmondsD(1) 
          simp add: is_sum_end_sets weight_vect_at_index)
  thus ?th1
    by(simp add: less_eq_vec_def)
  thus ?th2
    by(subst append_rows_trans_vect_mul) auto
  show ?th3
    by(auto intro!: feasible_min_perfect_dual_edmondsD(2) 
          simp add: less_eq_vec_def dual_omega_sol_at_index assms(3))
qed

named_theorems results

lemma edmonds_weak_duality_on_matrix[results]:
  assumes "perfect_matching G M" "Vs G = V" "dblton_graph G"
          "feasible_min_perfect_dual_edmonds G w \<pi>"
  shows "(1\<^sub>v n @\<^sub>v 1\<^sub>v \<omega>) \<bullet> (dual_sol (\<lambda>x. \<pi> {x}) @\<^sub>v dual_omega_sol \<pi>) 
           \<le> weight_vect w \<bullet> primal_sol M"
 by(auto intro!: weak_duality_theorem_nonneg_primal_min_eq_and_ineq[
       OF incidence_matrix_carrier_mat omega_delta_matrix_carrier_mat 
          one_carrier_vec one_carrier_vec weight_vect_carrier_vec
          primal_sol_carrier_vec] 
   perfect_matching_feasible assms
   perfect_matching_feasible_omega dual_sol_lp_feasible_edmonds)

lemma edmonds_weak_duality_on_matrix'[results]:
  assumes "perfect_matching G M" "Vs G = V" "dblton_graph G"
          "feasible_min_perfect_dual_edmonds G w \<pi>"
  shows "(1\<^sub>v (n + \<omega>)) \<bullet> (dual_sol (\<lambda>x. \<pi> {x}) @\<^sub>v dual_omega_sol \<pi>) 
           \<le> weight_vect w \<bullet> primal_sol M"
  using edmonds_weak_duality_on_matrix[OF assms] 
  by(auto simp add: one_vect_append)

lemma edmonds_weak_duality_on_graph[results]:
  assumes "perfect_matching G M" "Vs G = V" "dblton_graph G"
          "feasible_min_perfect_dual_edmonds G w \<pi>"
    shows "sum \<pi> (\<Omega> V) \<le> sum w M"
  using  edmonds_weak_duality_on_matrix[OF assms] assms
  by(auto elim: perfect_matchingE 
      simp add: potential_sum_graph_matrix primal_dot_weight_vect_weight_sum)

lemma omega_delta_matrix_row_times_primal_sol:
  assumes "i < \<omega>" "M \<subseteq> G" 
  shows "row omega_delta_matrix i \<bullet> primal_sol M = card (Delta M (\<Omega>\<^sub>3_enum_inv i))"
proof-
  have "(\<Sum>ia = 0..<m. of_bool (G_enum_inv ia \<in> Delta M (\<Omega>\<^sub>3_enum_inv i))) =
    real (card (Delta M (\<Omega>\<^sub>3_enum_inv i)))"
  proof-
    have "Delta M (\<Omega>\<^sub>3_enum_inv i) \<subseteq> G"
      using assms(2) in_DeltaD(2) by blast
    hence "card ({0..<m} \<inter> {ia. G_enum_inv ia \<in> Delta M (\<Omega>\<^sub>3_enum_inv i)}) 
           = card (Delta M (\<Omega>\<^sub>3_enum_inv i))"
      using G_enum_inv_inj_on inj_on_Int
      by (auto intro!: card_image_subst[of G_enum_inv]
                       rev_image_eqI[of "G_enum _" _ _ G_enum_inv, where uu4 = x and b = x for x])
    then show ?thesis
      by auto
  qed
  thus ?thesis
    using assms
    unfolding scalar_prod_def omega_delta_matrix_def col_def dual_omega_sol_def
    by(subst sum.cong[OF refl, where h = "\<lambda> ia. of_bool (G_enum_inv ia \<in> Delta M (\<Omega>\<^sub>3_enum_inv i))"])
      (auto simp add: Delta_def primal_sol_def)
qed

lemma graph_slack_to_matrix_slack_primal:
  assumes "M \<subseteq> G" "\<And> U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V; \<pi> U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M U) = 1"
  shows "(1\<^sub>v \<omega> - omega_delta_matrix *\<^sub>v primal_sol M) \<bullet> dual_omega_sol \<pi> = 0"
proof-
  have "(\<Sum>i = 0..<\<omega>. (1 - row omega_delta_matrix i \<bullet> primal_sol M) * dual_omega_sol \<pi> $ i) = 0"
  proof(rule comm_monoid_add_class.sum.neutral, rule ballI, goal_cases)
    case (1 i)
    hence i_omega: "i < \<omega>" by auto
    hence i_omega_3: "\<Omega>\<^sub>3_enum_inv i \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V" 
      by auto
    show ?case
      using assms(1) i_omega
      by(auto dest: assms(2)[OF i_omega_3] 
          simp add: dual_omega_sol_i_is omega_delta_matrix_row_times_primal_sol) 
  qed
  thus ?thesis
    by(auto simp add: scalar_prod_def)
qed

lemma omega_row_times_dual_sol_dual_pi_sum:
  assumes "ie < m" "dblton_graph G" "Vs G = V"
  shows "(\<Sum>i = 0..< n + \<omega>.
             (dual_sol (\<lambda>x. \<pi> {x}) @\<^sub>v dual_omega_sol \<pi>) $ i *
             row (incidence_matrix @\<^sub>r omega_delta_matrix) i $ ie) = 
      sum \<pi> (end_sets G (G_enum_inv ie))" 
      (is  "(\<Sum>i = 0..< n + \<omega>. ?f i) =  sum \<pi> (end_sets G (G_enum_inv ie))")
proof-
  have ie_G:"G_enum_inv ie \<in> G"
    by (simp add: assms)
   then obtain u v where uv: "G_enum_inv ie = {u, v}" "u \<noteq> v" 
     using assms(2) by auto
   obtain iu where iu: "iu < n" "Vs_enum_inv iu = u" 
     using ie_G uv(1) Vs_of_G_enum_less_n[of u] Vs_inv_enum[of u] edges_are_Vs[of u v G]
     by auto
   obtain iv where iv: "iv < n" "Vs_enum_inv iv = v"
     using ie_G uv(1) Vs_of_G_enum_less_n[of v] Vs_inv_enum[of v] edges_are_Vs_2[of u v G]
     by auto
  have "(\<Sum>i = 0..< n + \<omega>. ?f i) = (\<Sum>i = 0..< n. ?f i) + (\<Sum>i = n..< n+\<omega>. ?f i)"
    by(subst comm_monoid_add_class.sum.union_disjoint[symmetric])
      (auto intro!: sum.cong)
  moreover have "(\<Sum>i = 0..< n. ?f i) =
      (\<Sum>i = 0..<n. dual_sol (\<lambda>x. \<pi> {x}) $ i * (if Vs_enum_inv i \<in> G_enum_inv ie then 1 else 0))"
  using assms
  by(auto intro!: sum.cong simp add: dim_bot_matrices row_of_big_matrix_at_edge's_index_is )
  moreover have "(\<Sum>i\<in>{0..<n} \<inter> {i. Vs_enum_inv i \<in> G_enum_inv ie}. \<pi> {Vs_enum_inv i})
                 = \<pi> {u} + \<pi> {v}"
  proof(subst sum_inner_function_to_image[of "\<lambda> i. {Vs_enum_inv i}"], goal_cases)
    case 1
    then show ?case 
      using Vs_enum_inv_inj_below_n by (auto intro!: inj_onI)
  next
    case 2
    then show ?case 
      using iu iv
      by(subst sum.cong[of  _ "{{u}, {v}}"])
        (auto intro!: rev_image_eqI[of iu _ "{u}" "\<lambda>x. {Vs_enum_inv x}"] 
                      rev_image_eqI[of iv _ "{v}" "\<lambda>x. {Vs_enum_inv x}"] 
            simp add: uv)
  qed
  moreover have 
   "(\<Sum>i\<in>{0..<\<omega>} \<inter> {uu. G_enum_inv ie \<in> Delta G (\<Omega>\<^sub>3_enum_inv uu)}. \<pi> (\<Omega>\<^sub>3_enum_inv i))
    = sum \<pi> (end_sets_strict G {u, v})"
  proof(subst sum_inner_function_to_image[of \<Omega>\<^sub>3_enum_inv], goal_cases)
    case 1
    then show ?case 
      using \<Omega>\<^sub>3_enum_inv_inj_below_omega by (auto intro!: inj_onI) 
  next
    case 2
    then show ?case 
      by(auto elim!: in_end_sets_strictE
             intro!: arg_cong[of _ _"sum \<pi>"] in_end_sets_strictI 
                     rev_image_eqI[of _ _ _ \<Omega>\<^sub>3_enum_inv, where x = "\<Omega>\<^sub>3_enum b" and b = b for b]
           simp add: assms(3) uv(1) \<Omega>\<^sub>3_enum_less_n)
  qed

  ultimately show ?thesis
  using assms ie_G
  by(auto simp add: dim_bot_matrices row_of_big_matrix_at_edge's_index_is
                    if_distrib[of "\<lambda> x. _ * x"]  if_distrib[of "\<lambda> x. x * _"] 
                    comm_monoid_add_class.sum.If_cases dim_weight_dual_sol dual_sol_def 
                    dual_omega_sol_def add.commute[of \<omega> n] sum_nat_some_index_shift
                    sum_potential_end_sets_split_off_eps[OF ie_G uv finite_VsG]) 
qed
  
lemma graph_slack_to_matrix_slack_dual:
  assumes "M \<subseteq> odd_tight_subgraph G w \<pi>" "dblton_graph G" "Vs G = V"
  shows "(weight_vect w -
            (incidence_matrix @\<^sub>r omega_delta_matrix)\<^sup>T *\<^sub>v (dual_sol (\<lambda>x. \<pi> {x}) @\<^sub>v dual_omega_sol \<pi>)) 
        \<bullet> primal_sol M = 0"
proof(subst minus_scalar_prod_distrib[where n = m], goal_cases)
  case 4
  then show ?case 
    by(subst transpose_vec_mult_scalar)
      (auto simp add: scalar_prod_def primal_sol_def semiring_0_class.sum_distrib_left
                      comm_monoid_add_class.sum.swap[where B = "{0..<m} \<inter> {i. G_enum_inv i \<in> M}"]
                      dim_bot_matrices weight_vect_at_index
                      omega_row_times_dual_sol_dual_pi_sum[OF _  assms(2,3), simplified]
                dest: set_mp[OF assms(1)]
              intro!: sum.cong[OF refl] in_odd_tight_subgraphD(2)) 
qed (auto intro!: mult_mat_vec_carrier carrier_append_rows)

lemma edmonds_complementary_slackness_on_matrix[results]:
  assumes "dblton_graph G" "Vs G = V" "perfect_matching G M"
          "feasible_min_perfect_dual_edmonds G w \<pi>"
          "\<And>U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V; \<pi> U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M U) = 1"
          "M \<subseteq> odd_tight_subgraph G w \<pi>"
  shows "weight_vect w \<bullet> primal_sol M = (1\<^sub>v n @\<^sub>v 1\<^sub>v \<omega>) \<bullet> (dual_sol (\<lambda>x. \<pi> {x}) @\<^sub>v dual_omega_sol \<pi>)"
  using assms
   by(intro complementary_slackness_nonneg_primal_min_eq_and_ineq[
          OF incidence_matrix_carrier_mat omega_delta_matrix_carrier_mat
              one_carrier_vec one_carrier_vec weight_vect_carrier_vec
              primal_sol_carrier_vec dual_sol_carrier_vec]
        perfect_matching_feasible perfect_matching_feasible_omega
        primal_sol_nonneg dual_sol_lp_feasible_edmonds(2,3)
        graph_slack_to_matrix_slack_primal
        graph_slack_to_matrix_slack_dual)
     (auto elim: perfect_matchingE)

lemma edmonds_complementary_slackness_on_graph[results]:
  assumes "dblton_graph G" "Vs G = V" "perfect_matching G M"
          "feasible_min_perfect_dual_edmonds G w \<pi>"
          "\<And>U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V; \<pi> U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M U) = 1"
          "M \<subseteq> odd_tight_subgraph G w \<pi>"
    shows "sum w M = sum \<pi> (\<Omega> (Vs G))"
  using edmonds_complementary_slackness_on_matrix[OF assms, simplified]
        assms(1,2,3)
  by(auto elim!: perfect_matchingE 
       simp add: primal_dot_weight_vect_weight_sum[of M w] potential_sum_graph_matrix)

lemma edmonds_min_weight_perfect_matching_criterion[results]:
  assumes "dblton_graph G" "Vs G = V" "perfect_matching G M"
          "feasible_min_perfect_dual_edmonds G w \<pi>"
          "\<And>U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 V; \<pi> U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M U) = 1"
          "M \<subseteq> odd_tight_subgraph G w \<pi>"
    shows "min_weight_perfect_matching G w M"
  using edmonds_complementary_slackness_on_graph[OF assms, simplified] assms(1-4)
  by(auto intro!: min_weight_perfect_matchingI assms(3)
           dest!: edmonds_weak_duality_on_graph)
 
end

locale edmonds_matching_LP_standard =
  fixes V::"'v set"
  fixes G::"'v set set"
  assumes V_and_G: "finite V" "Vs G \<subseteq> V"
begin

definition Vs_enum :: "'v \<Rightarrow> nat" where
  "Vs_enum = to_nat_on V"

definition Vs_enum_inv :: "nat \<Rightarrow> 'v" where
  "Vs_enum_inv= from_nat_into V"

definition G_enum :: "'v set \<Rightarrow> nat" where
  "G_enum \<equiv> to_nat_on G"

definition G_enum_inv :: "nat \<Rightarrow> 'v set" where
  "G_enum_inv \<equiv> from_nat_into G"

definition \<Omega>\<^sub>3_enum :: "'v set \<Rightarrow> nat" where
  "\<Omega>\<^sub>3_enum = to_nat_on (\<Omega>\<^sub>\<ge>\<^sub>3 V)"

definition \<Omega>\<^sub>3_enum_inv :: "nat \<Rightarrow> 'v set" where
  "\<Omega>\<^sub>3_enum_inv= from_nat_into (\<Omega>\<^sub>\<ge>\<^sub>3 V)"

lemma finite_Vs_G: "finite (Vs G)" "finite G"
  using V_and_G(1,2) finite_subset 
  by (auto simp add: finite_Vs_then_finite finite_subset)

lemma bijections:"bij_betw Vs_enum V {0..<card V}"
                 "bij_betw G_enum G {0..<card G}"
                 "bij_betw \<Omega>\<^sub>3_enum (\<Omega>\<^sub>\<ge>\<^sub>3 V) {0..<card (\<Omega>\<^sub>\<ge>\<^sub>3 V)}"
  using V_and_G(1) finite_Vs_G(1,2)
  by(auto intro!: to_nat_on_finite odd_subsets_strict_finite 
        simp add: Vs_enum_def G_enum_def  atLeast0LessThan \<Omega>\<^sub>3_enum_def)
 
lemma inversions: "x \<in> V \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
                  "e \<in> G \<Longrightarrow> G_enum_inv (G_enum e) = e"
                  "U \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 V) \<Longrightarrow> \<Omega>\<^sub>3_enum_inv (\<Omega>\<^sub>3_enum U) = U"
  using V_and_G(1) finite_Vs_G(2)
  by(auto simp add: Vs_enum_def Vs_enum_inv_def countable_finite
                    G_enum_def G_enum_inv_def \<Omega>\<^sub>3_enum_def \<Omega>\<^sub>3_enum_inv_def
                    odd_subsets_strict_finite)

interpretation lp: edmonds_matching_lp G Vs_enum Vs_enum_inv G_enum G_enum_inv V \<Omega>\<^sub>3_enum \<Omega>\<^sub>3_enum_inv
  using V_and_G 
  by(auto intro!: edmonds_matching_lp.intro bijections inversions
                  edmonds_matching_lp_axioms.intro matching_lp_basic.intro)
thm lp.max_matching_weak_duality

lemmas max_matching_weak_duality= lp.max_matching_weak_duality
lemmas max_matching_pd_optimality= lp.max_matching_pd_optimality
lemmas max_weight_if_tight_matching_covers_bads=
          lp.max_weight_if_tight_matching_covers_bads
lemmas min_perfect_matching_weak_duality= lp.min_perfect_matching_weak_duality
lemmas min_perfect_matching_pd_optimality=lp.min_perfect_matching_pd_optimality
lemmas min_weight_perfect_if_tight_perfect_matching=
lp.min_weight_perfect_if_tight_perfect_matching[OF _ _ _ _ _ V_and_G(1)]
abbreviation "incidence_matrix == lp.incidence_matrix"
abbreviation "omega_delta_matrix == lp.omega_delta_matrix"
abbreviation "n == lp.n" 
abbreviation "m == lp.m"
abbreviation "\<omega> == lp.\<omega>"
abbreviation "primal_sol == lp.primal_sol"
abbreviation "dual_sol == lp.dual_sol"
abbreviation "dual_omega_sol == lp.dual_omega_sol"
abbreviation "weight_vect == lp.weight_vect"
lemmas matching_lp_theorems = lp.matching_lp_theorems
lemmas incidence_matrix_def = lp.incidence_matrix_def
lemmas dim_primal_sol= lp.dim_primal_sol
lemmas primal_sol_empty= lp.primal_sol_empty
lemmas primal_sol_nonneg= lp.primal_sol_nonneg
lemmas n_def = lp.n_def
lemma m_def: "m = card G" 
  by auto

lemmas results = lp.results
end

lemma edmonds_weak_duality:
  assumes "graph_invar G" "perfect_matching G M" 
          "feasible_min_perfect_dual_edmonds G w \<pi>"
    shows "sum \<pi> \<Omega> Vs G \<le> sum w M"
  using assms
  by(auto intro!: edmonds_matching_LP_standard.results(3) edmonds_matching_LP_standard.intro)

lemma edmons_complementary_slackness:
  assumes "graph_invar G" "perfect_matching G M" 
          "feasible_min_perfect_dual_edmonds G w \<pi>" 
          "\<And>U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G; \<pi> U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M U) = 1"
          "M \<subseteq> odd_tight_subgraph G w \<pi>"
    shows "sum w M = sum \<pi> \<Omega> Vs G"
  using assms
  by(auto intro!: edmonds_matching_LP_standard.results(5) edmonds_matching_LP_standard.intro)

lemma edmonds_min_weight_perfect_matching_criterion:
  assumes "graph_invar G" "perfect_matching G M" 
          "feasible_min_perfect_dual_edmonds G w \<pi>" 
          "\<And>U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G; \<pi> U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M U) = 1"
          "M \<subseteq> odd_tight_subgraph G w \<pi>"
    shows "min_weight_perfect_matching G w M"
  using assms
  by(auto intro!: edmonds_matching_LP_standard.results(6) edmonds_matching_LP_standard.intro)

lemma edmonds_primal_dual_cases:
  assumes edge: "\<exists> u v. e = {u, v} \<and> u \<noteq> v"
  assumes cases: 
    "\<And> X u v. \<lbrakk>X \<in> pluses; e \<subseteq> X; e = {u, v};u \<noteq> v\<rbrakk> \<Longrightarrow> P"
    "\<And> X u v. \<lbrakk>X \<in> minuses; e \<subseteq> X; e = {u, v};u \<noteq> v\<rbrakk> \<Longrightarrow> P"
    "\<And> u v X Y. \<lbrakk>X \<in> pluses; u \<in> X; Y \<in> minuses; X \<noteq> Y; v \<in> Y; e = {u, v};u \<noteq> v\<rbrakk> \<Longrightarrow> P"
    "\<And> u v X Y. \<lbrakk>X \<in> pluses; u \<in> X; Y \<in> pluses; X \<noteq> Y; v \<in> Y; e = {u, v};u \<noteq> v\<rbrakk> \<Longrightarrow> P"
    "\<And> u v X Y. \<lbrakk>X \<in> minuses; u \<in> X; Y \<in> minuses; X \<noteq> Y; v \<in> Y; e = {u, v};u \<noteq> v\<rbrakk> \<Longrightarrow> P"
    "\<And> u v. \<lbrakk>\<nexists> X. X \<in> pluses \<union> minuses \<and> u \<in> X; \<nexists> X. X \<in> pluses \<union> minuses \<and> v \<in> X;
               e = {u, v};u \<noteq> v\<rbrakk> \<Longrightarrow> P"
    "\<And> u v X . \<lbrakk>X \<in> pluses; u \<in> X; \<nexists> Y. Y \<in> minuses \<union> pluses \<and> v \<in> Y; e = {u, v}; u \<noteq> v\<rbrakk> \<Longrightarrow> P"
    "\<And> u v Y. \<lbrakk>\<nexists> X. X \<in> pluses \<union> minuses \<and> u \<in> X; Y \<in> minuses; v \<in> Y; e = {u, v}; u \<noteq> v\<rbrakk> \<Longrightarrow> P"          
  shows P
proof-
  obtain u v where uv: "e = {u, v}" "u \<noteq> v" 
    using edge by auto
  show ?thesis
proof(cases "e \<inter> \<Union> pluses = {}", goal_cases)
  case 1
  then show ?case 
  proof(cases "e \<inter> \<Union> minuses = {}", goal_cases)
    case 1
    then show ?case 
      using cases(6)[of u v] uv 
      by auto
  next
    case 2
    then obtain Y where "Y \<in> minuses" "e \<inter> Y \<noteq> {}"
      by auto
    then show ?case
      using 2
proof(cases "e \<subseteq> \<Union> minuses", goal_cases, goal_cases)
  case 1
  then obtain X Y where "X \<in> minuses" "Y \<in> minuses" "u \<in> X" "v \<in> Y"
    by (auto simp add: uv)
  then show ?case 
  proof(cases "X = Y", goal_cases)
    case 1
    then show ?case 
      using uv cases(2)[of X u v] by auto
  next
    case 2
    then show ?case 
      using uv cases(5)[of X u Y v] by auto
  qed
next
  case 2
  then show ?case 
    using uv cases(8)[of u Y v] cases(8)[of v Y u] by auto
qed
qed
next
  case 2
  then show ?case
  proof(cases "e \<subseteq> \<Union> pluses", goal_cases)
    case 1
    then obtain X Y where "X \<in> pluses" "u \<in> X" "Y \<in> pluses" "v \<in> Y"
      using uv by auto
    then show ?case
    proof(cases "X = Y", goal_cases)
      case 1
      then show ?case 
        using cases(1)[of X u v] uv by auto
    next
      case 2
      then show ?case 
        using cases(4)[of X u Y v] uv by auto
    qed
  next
    case 2
    then obtain X u v where Xuv: "X \<in> pluses" "e = {u, v}" "u \<in> X" "\<not> (\<exists> X \<in> pluses. v \<in> X)"
      using uv by auto
    then show ?case 
      using 2
    proof(cases "v \<in> \<Union> minuses", goal_cases)
      case 1
      then obtain Y where "Y \<in> minuses" "v \<in> Y" by auto
      then show ?case 
        using 1 cases(3)[of X u Y v] by auto
    next
      case 2
      then show ?case 
        using cases(7)[of X u v] by auto
    qed
  qed
qed
qed
 
lemma edmonds_primal_dual_adjustment_result:
 assumes disjointness:
  "\<And> X Y. \<lbrakk>X \<in> pluses \<union> minuses; Y \<in> pluses \<union> minuses; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}"
  "pluses \<inter> minuses = {}"
 and \<pi>'_def: 
   "\<pi>' = (\<lambda> X. if X \<in> pluses then \<pi> X + (\<epsilon>::real)
               else if X \<in> minuses then \<pi> X - \<epsilon>
               else \<pi> X)"
 and omega: "pluses \<union> minuses \<subseteq> \<Omega> (Vs G)" "e = {u, v}" "u \<noteq> v" "e \<in> G" "finite (Vs G)"
shows
  "\<And> X u v. \<lbrakk>X \<in> pluses; e \<subseteq> X; e = {u, v};u \<noteq> v\<rbrakk> 
             \<Longrightarrow> sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e)"
  "\<And> X u v. \<lbrakk>X \<in> minuses; e \<subseteq> X; e = {u, v};u \<noteq> v\<rbrakk> 
            \<Longrightarrow> sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e)"
  "\<And> u v X Y. \<lbrakk>X \<in> pluses; u \<in> X; Y \<in> minuses; X \<noteq> Y; v \<in> Y; e = {u, v};u \<noteq> v\<rbrakk> 
            \<Longrightarrow> sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e)"
  "\<And> u v X Y. \<lbrakk>X \<in> pluses; u \<in> X; Y \<in> pluses; X \<noteq> Y; v \<in> Y; e = {u, v};u \<noteq> v\<rbrakk> 
            \<Longrightarrow> sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e) + 2 * \<epsilon>"
  "\<And> u v X Y. \<lbrakk>X \<in> minuses; u \<in> X; Y \<in> minuses; X \<noteq> Y; v \<in> Y; e = {u, v};u \<noteq> v\<rbrakk>
            \<Longrightarrow> sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e) - 2 * \<epsilon>"
  "\<And> u v. \<lbrakk>\<nexists> X. X \<in> pluses \<union> minuses \<and> u \<in> X; \<nexists> X. X \<in> pluses \<union> minuses \<and> v \<in> X;
               e = {u, v};u \<noteq> v\<rbrakk> 
            \<Longrightarrow> sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e)"
  "\<And> u v X . \<lbrakk>X \<in> pluses; u \<in> X; \<nexists> Y. Y \<in> minuses \<union> pluses \<and> v \<in> Y; e = {u, v}; u \<noteq> v\<rbrakk> 
            \<Longrightarrow> sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e) + \<epsilon>"
  "\<And> u v X Y. \<lbrakk>\<nexists> X. X \<in> pluses \<union> minuses \<and> u \<in> X; Y \<in> minuses; v \<in> Y; e = {u, v}; u \<noteq> v\<rbrakk> 
            \<Longrightarrow> sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e) - \<epsilon>"
proof(goal_cases)
  case (1 X u v)
  note one = this
  show ?case 
  proof(rule sum.cong[OF refl], goal_cases)
    case (1 x)
    then show ?case 
      using one disjointness 
      by (auto elim!: in_end_setsE in_DeltaE simp add: \<pi>'_def doubleton_eq_iff)+
  qed
next
  case (2 X u v)
  note two = this
  show ?case 
  proof(rule sum.cong[OF refl], goal_cases)
    case (1 x)
    then show ?case 
      using two disjointness 
      by (auto elim!: in_end_setsE in_DeltaE simp add: \<pi>'_def doubleton_eq_iff)+
  qed
next
  case (3 u v X Y)
  note three = this
  hence "u \<notin> Y" "v \<notin> X"
    using disjointness by auto
  hence omega_is: "end_sets G e = (end_sets G e - {X, Y}) \<union> {X, Y}"
    using  omega(1,4)  "3"(1,2,3,4,5,6)
    by(auto intro: in_DeltaI simp add: end_sets_def)
  hence split_off: "sum f (end_sets G e) = sum f (end_sets G e - {X, Y}) + f X + f Y" for f
    using 3(4) 
    by(subst sum.subset_diff[of "{X, Y}" "end_sets G e" f])
      (auto simp add: finite_end_sets omega(5)  ab_semigroup_add_class.add_ac(1))
  have Y_not_pus: "Y \<notin> pluses"
    using disjointness(2) three(3) by blast
  have "sum \<pi>' (end_sets G e - {X, Y}) =  sum \<pi> (end_sets G e - {X, Y})"
  proof(rule sum.cong[OF refl], goal_cases)
    case (1 x)
    then show ?case 
      using  disjointness three(1,2,3,5,6)
      by (auto elim!: in_end_setsE in_DeltaE simp add: \<pi>'_def doubleton_eq_iff)+
  qed
  thus ?case 
    using  Y_not_pus three(1, 3)
    by (auto simp add: split_off \<pi>'_def)
next
  case (4 u v X Y)
note four = this
  hence "u \<notin> Y" "v \<notin> X"
    using disjointness by auto
  hence omega_is: "end_sets G e = (end_sets G e - {X, Y}) \<union> {X, Y}"
    using  omega(1,4)  4(1,2,3,4,5,6)
    by(auto intro: in_DeltaI simp add: end_sets_def)
  hence split_off: "sum f (end_sets G e) = sum f (end_sets G e - {X, Y}) + f X + f Y" for f
    using 4(4) 
    by(subst sum.subset_diff[of "{X, Y}" "end_sets G e" f])
      (auto simp add: finite_end_sets omega(5)  ab_semigroup_add_class.add_ac(1))
  have "sum \<pi>' (end_sets G e - {X, Y}) =  sum \<pi> (end_sets G e - {X, Y})"
  proof(rule sum.cong[OF refl], goal_cases)
    case (1 x)
    then show ?case 
      using  disjointness four(1,2,3,5,6)
      by (auto elim!: in_end_setsE in_DeltaE simp add: \<pi>'_def doubleton_eq_iff)+
  qed
  thus ?case 
    using  four(1,3)
    by (auto simp add: split_off \<pi>'_def)
next
  case (5 u v X Y)
  note five = this
  hence "u \<notin> Y" "v \<notin> X"
    using disjointness by auto
  hence omega_is: "end_sets G e = (end_sets G e - {X, Y}) \<union> {X, Y}"
    using  omega(1,4)  5(1,2,3,4,5,6)
    by(auto intro: in_DeltaI simp add: end_sets_def)
  hence split_off: "sum f (end_sets G e) = sum f (end_sets G e - {X, Y}) + f X + f Y" for f
    using 5(4) 
    by(subst sum.subset_diff[of "{X, Y}" "end_sets G e" f])
      (auto simp add: finite_end_sets omega(5)  ab_semigroup_add_class.add_ac(1))
  have not_in_plus: "X \<notin> pluses" "Y \<notin> pluses" 
    using disjointness(2) five(1,3) by auto
  have "sum \<pi>' (end_sets G e - {X, Y}) =  sum \<pi> (end_sets G e - {X, Y})"
  proof(rule sum.cong[OF refl], goal_cases)
    case (1 x)
    then show ?case 
      using  disjointness five(1,2,3,5,6)
      by (auto elim!: in_end_setsE in_DeltaE simp add: \<pi>'_def doubleton_eq_iff)+
  qed
  thus ?case 
    using five(1,3) not_in_plus
    by (auto simp add: split_off \<pi>'_def)
next
  case (6 u v)
  note six = this
  show ?case
  proof(rule sum.cong[OF refl], goal_cases)
    case (1 x)
    then show ?case 
      using six
      by(auto elim!: in_DeltaE in_end_setsE simp add: \<pi>'_def)
  qed
next
  case (7 u v X)
  note seven = this
   hence omega_is: "end_sets G e = (end_sets G e - {X}) \<union> {X}"
    using  omega(1,4)  seven
    by(auto intro: in_DeltaI simp add: end_sets_def)
  hence split_off: "sum f (end_sets G e) = sum f (end_sets G e - {X}) + f X" for f
    using seven
    by(subst sum.subset_diff[of "{X}" "end_sets G e" f])
      (auto simp add: finite_end_sets omega(5)  ab_semigroup_add_class.add_ac(1))
  have "sum \<pi>' (end_sets G e - {X}) =  sum \<pi> (end_sets G e - {X})"
  proof(rule sum.cong[OF refl], goal_cases)
    case (1 x)
    then show ?case 
      using  disjointness seven
      by (auto elim!: in_end_setsE in_DeltaE simp add: \<pi>'_def doubleton_eq_iff)+
  qed
  then show ?case 
    using seven(1)
    by(auto simp add: split_off \<pi>'_def)
next
  case (8 u v X Y)
  note eight = this
  hence omega_is: "end_sets G e = (end_sets G e - {Y}) \<union> {Y}"
    using  omega(1,4)  eight
    by(auto intro: in_DeltaI simp add: end_sets_def)
  hence split_off: "sum f (end_sets G e) = sum f (end_sets G e - {Y}) + f Y" for f
    using eight
    by(subst sum.subset_diff[of "{Y}" "end_sets G e" f])
      (auto simp add: finite_end_sets omega(5)  ab_semigroup_add_class.add_ac(1))
  have not_plus: "Y \<notin> pluses"
    using disjointness(2) eight(2) by blast
  have "sum \<pi>' (end_sets G e - {Y}) =  sum \<pi> (end_sets G e - {Y})"
  proof(rule sum.cong[OF refl], goal_cases)
    case (1 x)
    then show ?case 
      using  disjointness eight
      by (auto elim!: in_end_setsE in_DeltaE simp add: \<pi>'_def doubleton_eq_iff)+
  qed
  then show ?case 
    using not_plus eight(2)
    by(auto simp add: split_off \<pi>'_def)
qed

lemma edmonds_primal_dual_adjustment_feasibility:
 assumes feasibility:  "feasible_min_perfect_dual_edmonds G w \<pi>" 
 and disjointness:
  "\<And> X Y. \<lbrakk>X \<in> pluses \<union> minuses; Y \<in> pluses \<union> minuses; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}"
  "pluses \<inter> minuses = {}"
 and \<pi>'_def: 
   "\<pi>' = (\<lambda> X. if X \<in> pluses then \<pi> X + (\<epsilon>::real)
               else if X \<in> minuses then \<pi> X - \<epsilon>
               else \<pi> X)"
 and omega: "pluses \<union> minuses \<subseteq> \<Omega> (Vs G)" "graph_invar G"
 and epsilon: "\<epsilon> \<ge> 0"
     "\<And> u v X Y. \<lbrakk>{u, v} \<in> G; u \<in> X; X \<in> pluses; v \<in> Y; Y \<in> pluses; X \<noteq> Y\<rbrakk> 
         \<Longrightarrow>  \<epsilon> \<le> 1/2 * (w {u, v} - sum \<pi> (end_sets G {u, v}))"
     "\<And> u v X . \<lbrakk>{u, v} \<in> G; u \<in> X; X \<in> pluses; \<nexists> Y. Y \<in> pluses \<union> minuses \<and> v \<in> Y\<rbrakk> 
         \<Longrightarrow>  \<epsilon> \<le> w {u, v} - sum \<pi> (end_sets G {u, v})"
     "\<And> X. \<lbrakk>X \<in> minuses; card X > 1\<rbrakk> \<Longrightarrow> \<epsilon> \<le> \<pi> X"
shows "feasible_min_perfect_dual_edmonds G w \<pi>'" 
proof(rule feasible_min_perfect_dual_edmondsI, goal_cases)
  case (1 e)
  obtain u v where preconds: "e = {u, v}" "u \<noteq> v" "e \<in> G" "finite (Vs G)"
    using "1" omega(2) by blast
  hence pc2: "\<exists>u v. e = {u, v} \<and> u \<noteq> v" by auto
  note edmonds_primal_dual_adjustment_result =
       edmonds_primal_dual_adjustment_result[OF disjointness \<pi>'_def omega(1) preconds, simplified]
  show ?case 
  proof(cases rule: edmonds_primal_dual_cases[OF pc2, of pluses _ minuses], goal_cases)
    case (1 X u v)
    then show ?thesis 
      using feasible_min_perfect_dual_edmondsD(1)[OF  feasibility preconds(3)]
            edmonds_primal_dual_adjustment_result(1)[OF 1]
      by simp
  next
    case (2 X u v)
    then show ?thesis 
      using feasible_min_perfect_dual_edmondsD(1)[OF  feasibility preconds(3)]
            edmonds_primal_dual_adjustment_result(2)[OF 2]
      by simp
  next
    case (3 u v X Y)
    then show ?thesis 
      using feasible_min_perfect_dual_edmondsD(1)[OF  feasibility preconds(3)]
            edmonds_primal_dual_adjustment_result(3)[OF 3]
      by simp
  next
    case (4 u v X Y)
    then show ?thesis
      using feasible_min_perfect_dual_edmondsD(1)[OF  feasibility preconds(3)]
            edmonds_primal_dual_adjustment_result(4)[OF 4]
            epsilon(2)[OF _ 4(2,1,5,3,4)] preconds(3)
      by (simp add: 4(6))
  next
    case (5 u v X Y)
    then show ?thesis
      using feasible_min_perfect_dual_edmondsD(1)[OF  feasibility preconds(3)]
            edmonds_primal_dual_adjustment_result(5)[OF 5]
            epsilon(1)
      by (simp add: 5(6))
  next
    case (6 u v)
    note 6 = 6[simplified]
    then show ?thesis 
      using feasible_min_perfect_dual_edmondsD(1)[OF  feasibility preconds(3)]
            edmonds_primal_dual_adjustment_result(6)[OF 6]
      by simp
  next
    case (7 u v X)
    note 7 = 7[simplified]
    then show ?thesis 
      using feasible_min_perfect_dual_edmondsD(1)[OF feasibility]
            edmonds_primal_dual_adjustment_result(7)[OF 7]
            epsilon(3)[OF _ 7(2,1), of v] preconds(3) 
      by force
  next
    case (8 u v Y)
    note 8 = 8[simplified]
    then show ?thesis 
      using feasible_min_perfect_dual_edmondsD(1)[OF feasibility]
            edmonds_primal_dual_adjustment_result(8)[OF 8] preconds(3) 
            epsilon(1)
      by force
  qed
next
  case (2 U)
  then show ?case 
    unfolding \<pi>'_def
  proof(cases "U \<in> pluses", unfold if_P if_not_P, goal_cases)
    case 1
    then show ?case 
      using feasible_min_perfect_dual_edmondsD(2)[OF feasibility]
            epsilon(1)
      by simp
  next
    case 2
    then show ?case 
    proof(cases "U \<in> minuses", unfold if_P if_not_P, goal_cases)
      case 1
      then show ?case
        using feasible_min_perfect_dual_edmondsD(2)[OF feasibility 1(1)]
              epsilon(4)[of U]
        by(auto elim!: in_odd_subsets_strictE)
    next
      case 2
      then show ?case 
        by(intro feasible_min_perfect_dual_edmondsD(2)[OF feasibility])
    qed
  qed
qed

end