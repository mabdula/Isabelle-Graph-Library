theory Tutte_Matrix
  imports "HOL-Combinatorics.Cycles" "HOL-Analysis.Determinants" Tutte_Theorem
    "HOL-Library.Poly_Mapping"
begin

text \<open>Embedding of indeterminates and constants in type-class polynomials,
  can be used as constructors.\<close>

definition Var\<^sub>0 :: "'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::{one,zero}" where
  "Var\<^sub>0 n =( Poly_Mapping.single (Poly_Mapping.single n 1) 1)"


text \<open>this function is used to prove if a determinant is zero
when we have a corresponding inverse element\<close>

lemma var_not_zero:
  shows "((Var\<^sub>0 n) :: ('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 real) \<noteq> 0" unfolding Var\<^sub>0_def 
  by (smt (z3) lookup_single_eq single_zero)


lemma sum_of_values_cancel_out:
  fixes A :: "'a  set"
  fixes f :: "'a \<Rightarrow> 'a"
  fixes val :: "'a \<Rightarrow> 'n::comm_ring_1" 
  assumes "finite A"
  assumes "\<forall>a \<in> A.  f a \<in> A"
  assumes "\<forall>a \<in> A. f ( f a) = a"
  assumes "\<forall>a \<in> A. val a + val (f a) = 0"
  assumes "\<forall>a \<in> A. a = f a \<longrightarrow> val a = 0"
  shows "sum val A = 0"
  using assms
proof(induct "card A" arbitrary: A rule: less_induct)
  case less
  then show ?case
  proof(cases "card A = 0")
    case True
    have "A = {}"  
      using True card_0_eq less.prems(1) by blast
    then show ?thesis 
      using sum_clauses(1) by blast
  next
    case False
    show "sum val A = 0"
    proof(cases "\<forall>x \<in> A. f x = x")
      case True
      then show ?thesis 
        by (simp add: less.prems(5))
    next
      case False
      obtain a where "a \<in> A \<and> f a \<noteq> a" using False 
        by fastforce
      then obtain a' where "a' = f a" 
        by simp
      then have "a'\<in> A" 
        by (simp add: \<open>a \<in> A \<and> f a \<noteq> a\<close> less.prems(2))
      then have "a \<noteq> a'" 
        using \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' = f a\<close> by fastforce
      have "card (A - {a, a'}) < card A" 
        by (metis Diff_insert2 \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' \<in> A\<close> card_Diff2_less less.prems(1))
      have " \<forall>x\<in>(A - {a, a'}). f x \<in> (A - {a, a'})" 
        by (metis Diff_iff \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' = f a\<close> empty_iff insert_iff 
            less.prems(2) less.prems(3))
      moreover have  " \<forall>x\<in>(A - {a, a'}). f (f x) = x" 
        by (meson DiffD1 less.prems(3))
      moreover  have " \<forall>x\<in>(A - {a, a'}). val x + val (f x) = 0" 
        by (meson DiffD1 less.prems(4))
      ultimately have "sum val (A - {a, a'}) = 0" 
        using  \<open>card (A - {a, a'}) < card A\<close> less.hyps less.prems(1)
        using less.prems(5) by fastforce
      have "val a + val (f a) = 0" 
        using \<open>a \<in> A \<and> f a \<noteq> a\<close> less.prems(4) by auto
      have "sum val {a, a'} = 0" 
        using \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' = f a\<close> \<open>val a + val (f a) = 0\<close> by force
      have "sum val A = sum val (A - {a, a'}) + sum val {a, a'}" 
        using \<open>a \<noteq> a'\<close> \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' \<in> A\<close>
        by (meson  empty_subsetI insert_subset less.prems(1) sum.subset_diff)
      then show "sum val A = 0" 
        by (simp add: \<open>sum val (A - {a, a'}) = 0\<close> \<open>sum val {a, a'} = 0\<close>)     
    qed
  qed
qed

text \<open>we define a locale so we can ensure the universe is 
finite and corresponds to the vertices of the graph. We need that 
to define a determinant using permutations over that universe.\<close>

locale tutte_matrix =
  fixes G :: "'a::{wellorder,finite} set set"
  assumes graph: "graph_invar G"
  assumes univ: "(UNIV :: 'a set) =  (Vs G)"
begin

text \<open>random orientation of the edges. 
    CURRENTLY THE SEED IS (1, 1). NEEDS TO BE CHANGED.\<close>


definition get_oriented :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a)" where
  "get_oriented a b = (if fst (Random.range (2::natural) (1, 1)) = 1 then (a, b) else (b, a))"

lemma get_oriented_either_direction:
  shows "get_oriented a b = (a, b) \<or> get_oriented a b = (b, a)"
  by (meson get_oriented_def)

definition oriented_edges :: " ('a \<times> 'a) set"  where 
  "oriented_edges  = {get_oriented a b| a b. {a, b} \<in>  G \<and> a < b}"

lemma univ_is_finite:
  "finite (UNIV :: 'a set)" 
  by (simp add: univ graph)

lemma oriented_edges[elim?]:
  assumes "(a, b) \<in> oriented_edges" 
  shows "{a, b} \<in> G" 
  using assms 
  unfolding oriented_edges_def  
  unfolding get_oriented_def
  by (smt (z3) fst_conv insert_commute mem_Collect_eq prod.sel(2))

lemma one_direction_in_oriented:
  assumes "{a, b} \<in> G"
  shows "(a, b) \<in> oriented_edges \<or> (b, a) \<in> oriented_edges" 
proof -
  have "a \<noteq> b" 
    using assms graph by fastforce
  then show ?thesis  unfolding oriented_edges_def 
    unfolding get_oriented_def 
    by (smt (z3) CollectI assms insert_commute neqE)
qed

text \<open>We define the Tutte matrix. On the rows and columns we have 
the vertices. If we have an edge in the oriented version of the graph, we put 
a variable. If we have an edge in the other direction, we put minus of the variable.
Otherwise we put 0.\<close>

definition tutte_matrix:: "((('a set \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 real, 'a) vec, 'a) vec" where
  "tutte_matrix = (\<chi> i j. if (i, j) \<in> oriented_edges  
                          then Var\<^sub>0 {i, j}
                          else (if (j, i) \<in> oriented_edges 
                                then - (Var\<^sub>0 {i, j})  
                                else 0))"

lemma in_oriented:
  assumes "(i, j) \<in> oriented_edges"
  shows "tutte_matrix $i$j = Var\<^sub>0 {i, j}" 
  unfolding tutte_matrix_def 
  using assms by fastforce

lemma rev_in_oriented:
  assumes "(j, i) \<in> oriented_edges"
  shows "tutte_matrix $i$j = - (Var\<^sub>0 {i, j})" 
proof -
  have "(i, j) \<notin> oriented_edges" 
    unfolding oriented_edges_def 
    using assms get_oriented_def oriented_edges_def by auto
  then show ?thesis   
    unfolding tutte_matrix_def 
    using assms by fastforce
qed

lemma not_in_edges_tutte_zero:
  assumes "{i, j} \<notin> G"
  shows "tutte_matrix $i$j = 0"
proof -
  have "(i, j) \<notin> oriented_edges" 
    using assms oriented_edges by blast
  have "(j, i) \<notin> oriented_edges" 
    using assms  oriented_edges_def 
    by (metis (mono_tags, lifting) insert_commute oriented_edges)
  show ?thesis  unfolding tutte_matrix_def 
    by (simp add: \<open>(i, j) \<notin> oriented_edges\<close> \<open>(j, i) \<notin> oriented_edges\<close>)
qed

lemma in_edges:
  assumes "{i, j} \<in> G"
  shows "tutte_matrix $i$j \<noteq> 0"
proof(cases "(i, j) \<in> oriented_edges")
  case True
  then show ?thesis using in_oriented 
    by (simp add: var_not_zero)
next
  case False
  have "(j, i) \<in> oriented_edges" 
    using one_direction_in_oriented 
      assms  False by blast
  then show ?thesis 
    by (simp add: rev_in_oriented var_not_zero)
qed

lemma zero_tutte_not_in_oriented:
  assumes "tutte_matrix $i$j = 0"
  shows "(i, j) \<notin> oriented_edges" 
proof
  assume "(i, j) \<in> oriented_edges"
  then have "tutte_matrix $i$j = Var\<^sub>0 {i, j}" 
    using in_oriented assms by blast 
  have "Poly_Mapping.lookup (Var\<^sub>0 {i, j}) ((Poly_Mapping.single {i, j} 1)) \<noteq> (0::real)" 
    by (simp add: Var\<^sub>0_def)
  then show False using assms 
    using \<open>local.tutte_matrix $ i $ j = Var\<^sub>0 {i, j}\<close> by fastforce
qed

lemma tutte_skew_symmetric:
  shows "tutte_matrix $i$j = - tutte_matrix $j$i"
  by (metis (no_types, lifting) add.inverse_neutral in_oriented insert_commute
      not_in_edges_tutte_zero one_direction_in_oriented rev_in_oriented verit_minus_simplify(4))

lemma zero_then_not_in_edges:
  assumes "tutte_matrix $i$j = 0"
  shows  "{i, j} \<notin> G"
proof -
  have "(i, j) \<notin> oriented_edges" using zero_tutte_not_in_oriented 
    by (simp add: assms)
  moreover have "(j, i) \<notin> oriented_edges" 
    by (metis add.inverse_neutral assms tutte_skew_symmetric 
        zero_tutte_not_in_oriented)
  ultimately show ?thesis 
    using  one_direction_in_oriented by blast
qed

lemma not_in_both_oriented:
  assumes "(j, i) \<notin> oriented_edges"
  assumes "(i, j) \<notin> oriented_edges" 
  shows "{i, j} \<notin> G" 
  using assms one_direction_in_oriented by auto

lemma tutte_matrix_det:
  "det (tutte_matrix) =  sum (\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set))
      {p. p permutes (UNIV :: 'a set)}" 
  using det_def by blast

definition all_perms where 
  "all_perms = {p. p permutes (UNIV :: 'a set)}"

lemma all_perms_elim[elim]:
  assumes "p \<in> all_perms"
  shows "p permutes (UNIV :: 'a set)"
  using assms
  unfolding all_perms_def
  by auto

lemma all_perms_intro[intro]:
  assumes "p permutes (UNIV :: 'a set)"
  shows "p \<in> all_perms"
  unfolding all_perms_def using assms 
  by auto

definition nonzero_perms :: "('a \<Rightarrow> 'a) set "where
  "nonzero_perms  = {p. p permutes (UNIV :: 'a set) \<and> 
         prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set) \<noteq> 0}"

lemma nonzero_perms_elim[elim]:
  assumes "p \<in> nonzero_perms"
  shows "p permutes (UNIV :: 'a set)"  
    "prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set) \<noteq> 0"
  using assms 
  unfolding nonzero_perms_def
   apply blast
  using assms nonzero_perms_def by force

lemma nonzero_perms_intro[intro]:
  assumes "p permutes (UNIV :: 'a set)"
  assumes "prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set) \<noteq> 0"
  shows "p \<in> nonzero_perms" 
  unfolding nonzero_perms_def using assms by auto

text \<open>edges corresponding to the permutation.\<close>

definition u_edges :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set  set" where
  "u_edges p = {{i, p i}|i. i \<in> (UNIV :: 'a set)}"

lemma u_edges_elim[elim]:
  assumes "e \<in> u_edges p"
  obtains i where "e = {i, p i} \<and>  i \<in> (UNIV :: 'a set)"
  using assms 
  unfolding u_edges_def 
  by blast

lemma u_edges_intro[intro]:
  assumes "i \<in> (UNIV :: 'a set)"
  shows "{i, p i} \<in> u_edges p"
  unfolding u_edges_def 
  by blast

lemma nonzero_perms_nonzero_tutte:
  assumes "p \<in> nonzero_perms"
  shows "\<forall>i. tutte_matrix$i$p i \<noteq> 0"
proof
  fix i
  have "prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV \<noteq> 0"
    using assms nonzero_perms_elim(1) nonzero_perms_elim(2) by blast
  also have "finite (UNIV :: 'a set)" 
    by simp
  ultimately show "(tutte_matrix)$i$p i \<noteq> 0" 
    by (meson UNIV_I prod_zero)
qed

lemma nonzero_edge_in_graph:
  assumes "p \<in> nonzero_perms"
  shows "{i, p i} \<in> G" 
  using assms nonzero_perms_nonzero_tutte 
    not_in_edges_tutte_zero by blast

lemma nonzero_perms_u_edges_in_graph:
  assumes "p \<in> nonzero_perms"
  shows "u_edges p \<subseteq> G"
proof
  fix e
  assume "e \<in> u_edges p"
  then obtain i where "e = {i, (p i)} \<and>  i \<in> (UNIV :: 'a set)" 
    by (meson u_edges_elim)
  then have "{i, (p i)} \<in> G" 
    using assms nonzero_edge_in_graph tutte_matrix_axioms by auto
  then show "e \<in> G" 
    using \<open>e = {i, (p i)} \<and> i \<in> UNIV\<close> by auto
qed

lemma u_edges_finite:
  shows "finite (u_edges p)"
  by simp

lemma u_edges_is_graph:
  assumes "p \<in> nonzero_perms "
  shows "graph_invar (u_edges p)"
  using assms graph nonzero_perms_u_edges_in_graph
  by force

lemma p_is_permutation:
  assumes "p permutes (UNIV :: 'a set)"
  shows "permutation p" 
  using assms finite_class.finite_UNIV permutation_permutes by blast

lemma even_circuits_connected_component':
  shows "{(p^^j) i, (p^^(j+1)) i} \<in>  u_edges p" 
  using u_edges_def by auto

lemma nonzero_perms_not_id:
  assumes "p \<in> nonzero_perms"
  shows "p i \<noteq> i" 
proof(rule ccontr)
  assume "\<not> (p i \<noteq> i)"
  then have "p i = i" by auto
  have "{i, i} \<notin> G" 
    using graph by fastforce
  then show False 
    by (metis \<open>p i = i\<close> assms nonzero_edge_in_graph)
qed

lemma edges_construct_a_path:
  assumes "\<forall>i < size xs-1. {xs!i, xs!(i+1)} \<in> A"
  assumes "size xs \<ge> 2" 
  shows "path A xs" using assms
proof(induct xs)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a xs)
  have "length (a#xs) - 1 = length xs" 
    by simp
  have "\<forall>i<length xs-1. {xs ! i, xs ! (i + 1)} \<in> A" 
    using Cons.prems  less_diff_conv by auto
  have " {(a # xs) ! 0, (a # xs) ! (0 + 1)} \<in> A" 
    using Cons.prems 
    by (metis Nat.le_diff_conv2 \<open>length (a # xs) - 1 = length xs\<close> add_leD2 length_greater_0_conv
        list.size(3) nat_1_add_1 not_one_le_zero)
  then have "{a, xs!0} \<in> A" 
    by simp
  show ?case
  proof(cases "xs = []")
    case True
    have "a \<in> Vs A" 
      by (meson \<open>{a, xs ! 0} \<in> A\<close> edges_are_Vs) 
    then show ?thesis 
      by (simp add: True)
  next
    case False
    have "xs \<noteq> []" 
      by (simp add: False)
    show ?thesis 
    proof(cases "size xs = 1")
      case True
      have "xs!0 \<in> Vs A" 
        using \<open>{(a # xs) ! 0, (a # xs) ! (0 + 1)} \<in> A\<close> nth_Cons' by auto
      have "xs = [xs!0]" 
        by (metis One_nat_def Suc_length_conv True length_0_conv nth_Cons_0)
      have "path A [a, xs!0]" 
        by (simp add: \<open>{a, xs ! 0} \<in> A\<close> \<open>xs ! 0 \<in> Vs A\<close>)
      then show ?thesis 
        using \<open>xs = [xs ! 0]\<close> by auto
    next
      case False
      have "2 \<le> length xs" 
        using Cons.prems(2) False \<open>length (a # xs) - 1 = length xs\<close> by linarith
      then have "path A xs"
        using Cons.hyps \<open>\<forall>i<length xs-1. {xs ! i, xs ! (i + 1)} \<in> A\<close> 
        by blast
      have "xs = hd xs # tl xs" 
        by (simp add: \<open>xs \<noteq> []\<close>)
      then have "{a, hd xs} \<in> A" 
        by (metis \<open>{a, xs ! 0} \<in> A\<close> nth_Cons_0)
      then show ?thesis 
        by (metis \<open>path A xs\<close> \<open>xs = hd xs # tl xs\<close> path_2) 
    qed
  qed
qed

lemma circuit_is_upath:
  assumes "p permutes (UNIV::'a set)"
  shows "path (u_edges p) (support p i)" 
proof(cases "p i \<noteq> i")
  case True
  let ?xs = "support p i"
  have "\<forall>i < size ?xs-1. {?xs!i, ?xs!(i+1)} \<in> (u_edges p)"
    using even_circuits_connected_component' 
    by auto
  have "p i \<noteq> i" using True by auto
  have "permutation p" 
    by (simp add: assms p_is_permutation) 
  have "(least_power p i) > 1" 
    by (simp add: \<open>p i \<noteq> i\<close> \<open>permutation p\<close> least_power_gt_one)
  then have "size (support p i) \<ge> 2" 
    by simp 
  then show "path (u_edges p) (support p i)" 
    using \<open>\<forall>i < size ?xs-1. {?xs!i, ?xs!(i+1)} \<in> (u_edges p)\<close> 
      edges_construct_a_path by blast
next
  case False
  have "p i = i" 
    using False by auto
  then have "{i, (p i)} \<in> u_edges p" 
    using u_edges_def by auto
  then have "i \<in> Vs (u_edges p)" 
    by (meson edges_are_Vs)
  have "(p^^(Suc 0)) i = i" using `p i = i` 
    by auto
  then have "(p^^1) i = i" 
    by simp
  then have "least_power p i = 1" 
    by (meson least_power_minimal nat_dvd_1_iff_1)
  then show ?thesis 
    by (simp add: \<open>i \<in> Vs (u_edges p)\<close>)
qed 


lemma uedge_in_circuit:
  assumes "Suc j < (least_power p i)" 
  shows "{(support p i)!j, (support p i)!(Suc j)} \<in> u_edges p"
  using assms even_circuits_connected_component' by force

lemma mod_least_power_same:
  assumes "permutation p" 
  assumes "(p ^^ n) a = b"
  shows "(p^^(n mod (least_power p a))) a = b"
proof (cases "n = 0", simp)
  {
    let ?lpow = "least_power p" 
    assume "n \<noteq> 0" then have "n > 0" by simp
    have  "(p ^^ (?lpow a)) a = a" 
      using assms  
      by (meson least_power_of_permutation(1))
    hence aux_lemma: "(p ^^ ((?lpow a) * k)) a = a" for k :: nat
      by (induct k) (simp_all add: funpow_add)

    have "(p ^^ (n mod ?lpow a)) ((p ^^ (n - (n mod ?lpow a))) a) = (p ^^ n) a"
      by (metis add_diff_inverse_nat funpow_add mod_less_eq_dividend not_less o_apply)
    with \<open>(p ^^ n) a = b\<close> 
    show "(p ^^ (n mod ?lpow a)) a = b"
      using aux_lemma by (simp add: minus_mod_eq_mult_div) 
  }
  show "n = 0 \<Longrightarrow> a = b" 
    using assms(2) by auto
qed

lemma elemnets_in_support_expo:
  fixes n :: "nat"
  assumes "permutation p" 
  assumes "x \<in> set (support p i)"
  assumes "y = (p^^n) x"
  shows "y \<in> set (support p i)" 
proof -
  let ?len = "least_power p i"
  obtain k where "(p^^k) i = x \<and> k < least_power p i" using assms 
    by fastforce
  have "((p^^n)\<circ>(p^^k)) i = y" 
    by (simp add: \<open>(p ^^ k) i = x \<and> k < least_power p i\<close> assms(3)) 
  then have "(p^^(n+k)) i = y" 
    by (simp add: funpow_add) 
  then have "(p^^((n+k) mod ?len)) i = y" 
    by (simp add: assms(1) mod_least_power_same)
  have "((n+k) mod ?len) < ?len" 
    by (meson assms(1) least_power_of_permutation(2) mod_less_divisor)
  then have "(support p i)!((n+k) mod ?len) = y" 
    by (simp add: \<open>(p ^^ ((n + k) mod least_power p i)) i = y\<close>)
  then show ?thesis  
    using \<open>(n + k) mod least_power p i < least_power p i\<close> by force
qed

lemma inv_least_power_same:
  assumes "p permutes (UNIV:: 'a set)"
  shows "least_power p i = least_power (inv p) i" 
proof -
  let ?l = "least_power p i" 
  let ?inv_l = "least_power (inv p) i"
  have "(p^^?l) i = i" 
    by (simp add: assms least_power_of_permutation(1) p_is_permutation)
  have "((inv p)^^(?inv_l)) i = i" 
    by (simp add: assms least_power_of_permutation(1) p_is_permutation permutation_inverse)
  then have "i = (p^^?inv_l) i" 
    by (metis assms bij_fn bij_inv_eq_iff inv_fn permutes_imp_bij)
  show ?thesis
  proof(rule ccontr)
    assume "?l \<noteq> ?inv_l"
    then have "?l < ?inv_l" 
      by (metis \<open>i = (p ^^ least_power (inv p) i) i\<close> assms le_eq_less_or_eq least_power_le 
          least_power_of_permutation(2) p_is_permutation permutation_inverse)
    then show False 
      by (metis \<open>(p ^^ least_power p i) i = i\<close> assms bij_betw_inv_into_left bij_fn bij_is_surj 
          inv_fn leD least_power_le least_power_of_permutation(2) p_is_permutation permutes_imp_bij 
          range_eqI)
  qed
qed

lemma el_in_own_support:
  assumes "p permutes (UNIV :: 'a set)"
  shows "i \<in> set (support p i)" 
proof -
  have "(p^^0) i = i" by simp
  then have "support p i!0 = i" 
    by (simp add: assms least_power_of_permutation(2) p_is_permutation)
  then show ?thesis 
    by (metis assms least_power_of_permutation(2) length_map length_upt nth_mem p_is_permutation 
        zero_less_diff)
qed

lemma p_diff_inv_p_pow:
  assumes "permutation p"
  assumes "n \<ge> k"
  shows "((inv p)^^ k) ((p^^n) i) = (p^^(n-k)) i" 
proof -
  have "(p^^n) i = ((p^^k) \<circ> (p^^(n-k))) i" 
    by (metis add_diff_inverse_nat assms(2) funpow_add not_le)
  then show ?thesis 
    by (metis assms(1) bij_fn bij_inv_eq_iff comp_apply inv_fn permutation_bijective)
qed

lemma inv_support_same:
  assumes "permutation p"
  shows "set (support p i) = set (support (inv p) i)" 
proof(safe)
  let ?len = "least_power p i"  
  have "i \<in> set (support (inv p) i)" 
    using el_in_own_support assms 
    by (smt (z3) least_power_of_permutation(1) map_eq_conv permutation_inverse
        range_eqI support_set)
  { 
    fix x
    assume "x \<in> set (support p i)"
    then obtain j where "x = (p^^j) i \<and> j < least_power p i" 
      by fastforce
    have "i = ((inv p)^^?len) i" 
      by (metis assms bij_fn bij_inv_eq_iff inv_fn least_power_of_permutation(1) 
          permutation_bijective)
    then have "x = (p^^j) (((inv p)^^?len) i)" 
      using \<open>x = (p ^^ j) i \<and> j < least_power p i\<close> by presburger
    then have "x = ((inv p)^^(?len - j)) i"  
      using p_diff_inv_p_pow[of p j ?len] 
      by (metis \<open>x = (p ^^ j) i \<and> j < least_power p i\<close> assms diff_diff_cancel diff_le_self 
          least_power_of_permutation(1) less_imp_le_nat p_diff_inv_p_pow)
    then show "x \<in>  set (support (inv p) i)"
      using elemnets_in_support_expo[of "inv p" i i x "?len - j"] 
            \<open>i \<in> set (support (inv p) i)\<close> assms p_is_permutation permutation_inverse by blast
  }
  fix x
  assume "x \<in>  set (support (inv p) i)"
  then obtain j where "x = ((inv p)^^j) i \<and> j < least_power (inv p) i" 
    by fastforce
  have "i = (p^^?len) i" 
    by (simp add: assms least_power_of_permutation(1) p_is_permutation)
  then have "x = ((inv p)^^j) (((p)^^?len) i)" 
    using \<open>x = ((inv p) ^^ j) i \<and> j < least_power (inv p) i\<close> by presburger
  then have "x = (p^^(?len - j)) i"   using p_diff_inv_p_pow[of "inv p" j ?len] 
    by (smt (z3) \<open>i = (p ^^ least_power p i) i\<close> \<open>x = (inv p ^^ j) i \<and> j < least_power (inv p) i\<close> 
        assms bij_is_surj dual_order.strict_trans funpow_diff inj_iff inv_inv_eq least_power_le 
        least_power_of_permutation(2) not_le p_diff_inv_p_pow permutation_bijective
        permutation_inverse surj_iff) 
  then show "x \<in>  set (support p i)" 
    using elemnets_in_support_expo[of "p" i i x "?len - j"]
          assms least_power_of_permutation(2) by force
qed

lemma elemnets_in_support_expo':
  fixes n :: "nat"
  assumes "permutation p" 
  assumes "x \<in> set (support p i)"
  assumes "x = (p^^n) y"
  shows "y \<in> set (support p i)"
proof -
  have "permutation (inv p)" 
    using assms(1) permutation_inverse by blast
  have "x \<in>  set (support (inv p) i)" 
    using assms(1) assms(2) inv_support_same by fastforce
  have "((inv p)^^n) x = y" 
    by (metis assms(1) assms(3) bij_fn bij_inv_eq_iff inv_fn permutation_bijective)
  then have "y \<in> set (support (inv p) i)" 
    using \<open>permutation (inv p)\<close> \<open>x \<in> set (support (inv p) i)\<close> elemnets_in_support_expo by fastforce
  then show ?thesis 
    using assms(1) assms(2) inv_support_same by fastforce
qed

lemma support_is_connected_component:
  assumes "p permutes (UNIV :: 'a set)"
  assumes "C \<in> connected_components (u_edges p)" 
  assumes "i \<in> C"
  shows "set (support p i) = C" (is "set ?l = C")
proof(safe)
  have "hd (support p i) = i" 
    by (simp add: assms(1) hd_conv_nth least_power_of_permutation(2) p_is_permutation)
  then have "i \<in> set ?l" 
  proof -
    have "0 < least_power p i"
      by (simp add: assms(1) p_is_permutation least_power_of_permutation(2))
    then have "0 \<in> {0..<least_power p i}" by simp
    then have "(p ^^ 0) i \<in> (\<lambda>n. (p ^^ n) i) ` {0..<least_power p i}"
      by (rule imageI)
    then show ?thesis by simp
  qed
  {
    fix x
    assume "x \<in> set ?l" 
    then obtain j where "?l!j = x" 
      by (meson in_set_conv_nth)
    have "path (u_edges p) ?l" 
      using assms(1) circuit_is_upath by blast
    obtain ys zs where "?l = ys @ x # zs" 
    proof -
      have "\<exists>ys zs. ?l = ys @ x # zs"
        using \<open>x \<in> set ?l\<close> by (rule split_list)
      then show thesis using that by blast
    qed
    then have "(ys @ [x]) @ zs = ?l" by simp
    then have "path (u_edges p) (ys @ [x])" 
      proof -
        have "path (u_edges p) ((ys @ [x]) @ zs)"
          using \<open>path (u_edges p) ?l\<close> \<open>(ys @ [x]) @ zs = ?l\<close> by simp
        then show ?thesis
          by (rule path_pref)
      qed
    then have "hd (ys @ [x]) = i" using `hd ?l = i`
    proof -
      have "hd (ys @ [x]) = hd ((ys @ [x]) @ zs)"
        by (cases ys) simp_all
      also have "\<dots> = hd ?l"
        using \<open>(ys @ [x]) @ zs = ?l\<close> by simp
      also have "\<dots> = i"
        using \<open>hd ?l = i\<close> .
      finally show ?thesis .
    qed
    have "last (ys @ [x]) = x" 
      by simp 
    have "walk_betw (u_edges p) i (ys @ [x]) x" 
      by (simp add: \<open>hd (ys @ [x]) = i\<close> \<open>path (u_edges p) (ys @ [x])\<close> nonempty_path_walk_between)
    then have "x \<in> connected_component (u_edges p) i" 
      using has_path_in_connected_component2 by force
    then show "x \<in> C"
      using assms(2) assms(3) connected_components_closed'' by fastforce 
  }
  fix x 
  assume "x \<in> C"
  obtain xs where "walk_betw (u_edges p) x xs i" 
    by (meson \<open>x \<in> C\<close> assms(2) assms(3) same_con_comp_walk)
  then have "hd xs = x"
    by (simp add: walk_between_nonempty_pathD(3))
  then have "x \<in> set xs" 
    using \<open>walk_betw (u_edges p) x xs i\<close> by force
  have "path (u_edges p) xs"
    by (meson \<open>walk_betw (u_edges p) x xs i\<close> walk_between_nonempty_pathD(1)) 
  have "last xs = i" 
    using \<open>walk_betw (u_edges p) x xs i\<close>
    by (simp add: walk_between_nonempty_pathD(4))
  have "\<forall>y \<in> set xs. \<exists>n. (p^^n) i = y" using `path (u_edges p) xs` `last xs = i`
  proof(induct xs)
    case path0 
    then show ?case by auto
  next
    case (path1 v)
    have "v = i" 
      using path1.prems by auto
    show ?case
    proof (intro ballI)
      fix y
      assume "y \<in> set [v]"
      then have "y = v" by simp
      moreover have "v = i" using path1.prems by simp
      ultimately have "(p ^^ (0::nat)) i = y" by simp
      then show "\<exists>n. (p ^^ n) i = y" by blast
    qed
  next
    case (path2 v v' vs)
    have "v = p v' \<or> v' = p v" 
      proof -
        from path2.hyps(1) obtain w where w: "{v, v'} = {w, p w}"
          unfolding u_edges_def by blast
        then have "(v = w \<and> v' = p w) \<or> (v = p w \<and> v' = w)"
          by (simp add: doubleton_eq_iff)
        then show ?thesis
        proof
          assume "v = w \<and> v' = p w"
          then have "v' = p v" by simp
          then show ?thesis by blast
        next
          assume "v = p w \<and> v' = w"
          then have "v = p v'" by simp
          then show ?thesis by blast
        qed
      qed

    obtain n where "(p^^n) i = v'" 
      using path2.hyps(3) path2.prems by auto
    then have "v' \<in> set (support p i)" 
      using elemnets_in_support_expo[of p i i v' n] 
      using \<open>i \<in> set (support p i)\<close> assms(1) p_is_permutation by blast
    then show ?case 
    proof(cases "v = p v'")
      case True
      have "p ((p^^n) i) = v" 
        by (simp add: True \<open>(p ^^ n) i = v'\<close>)
      then have "(p \<circ> (p^^n)) i = v" by auto
      then have "(p^^(n+1)) i = v" by simp

      then show ?thesis 
      proof -
        have last_eq: "last (v' # vs) = i"
          using path2.prems by simp
        have IH: "\<forall>z \<in> set (v' # vs). \<exists>m. (p ^^ m) i = z"
          using path2.hyps(3) last_eq by blast
        have "(p ^^ Suc n) i = p ((p ^^ n) i)"
          by simp
        then have v_eq: "(p ^^ Suc n) i = v"
          using True \<open>(p ^^ n) i = v'\<close> by simp
        show ?thesis
        proof
          fix y
          assume y: "y \<in> set (v # v' # vs)"
          show "\<exists>m. (p ^^ m) i = y"
          proof (cases "y = v")
            case True
            then have "(p ^^ Suc n) i = y"
              using v_eq by simp
            then show ?thesis by blast
          next
            case False
            then have "y \<in> set (v' # vs)"
              using y by auto
            then show ?thesis using IH by blast
          qed
        qed
      qed
    next
      case False
      have " v' = p v" 
        using False \<open>v = p v' \<or> v' = p v\<close> by auto
      then have "(p^^(1::nat)) v = v'" 
        by (simp add: \<open>(p ^^ n) i = v'\<close>)
      then have "v \<in> set (support p i)"  
        using elemnets_in_support_expo'[of p v' i "(1::nat)" v] 
        using \<open>v' \<in> set (support p i)\<close> assms(1) p_is_permutation by blast
      then obtain j where "v = support p i!j \<and> j < least_power p i" 
      proof -
        obtain m where m_less: "m < least_power p i" and m_eq: "v = (p ^^ m) i"
          using \<open>v \<in> set (support p i)\<close> by fastforce
        have "support p i ! m = (p ^^ m) i"
          using m_less by simp
        with m_eq m_less have "v = support p i ! m \<and> m < least_power p i"
          by simp
        then show thesis
          using that by blast
      qed
      then have "(p^^j) i = v" 
        by simp
      then show ?thesis 
        using path2.hyps(3) path2.prems by auto
    qed
  qed
  then obtain n where "(p^^n) i = x" 
    using \<open>x \<in> set xs\<close> by blast
  then show "x \<in> set (support p i)" 
    using elemnets_in_support_expo[OF p_is_permutation[OF assms(1)]
            \<open>i \<in> set (support p i)\<close> \<open>(p ^^ n) i = x\<close>[symmetric]]
    by blast
qed


lemma perm_support_distinct:
  assumes "p permutes (UNIV :: 'a set)"
  shows "distinct (support p i)" 
  by (simp add: assms cycle_of_permutation p_is_permutation)

lemma cycle_vert_is_distict:
  assumes "p permutes (UNIV :: 'a set)"
  shows "distinct (support p i)"
  by (simp add: assms cycle_of_permutation p_is_permutation)

lemma p_in_same_cycle:
  assumes "p permutes (UNIV :: 'a set)"
  assumes "a \<in> set (support p i)"
  shows "p a \<in> set (support p i)" 
proof -
  have perm: "permutation p"
    using assms(1) by (simp add: p_is_permutation)
  have "p a = (p ^^ (1::nat)) a"
    by simp
  with perm assms(2) show ?thesis
    by (rule elemnets_in_support_expo)
qed

lemma nths_in_result:
  assumes "i \<in> I"
  assumes "i < length xs"
  shows "xs!i \<in> set (nths xs I)" 
  using assms(1) assms(2) set_nths by fastforce

lemma nths_obtain_index:
  assumes "a \<in>  set (nths xs I)"
  obtains i where "a = xs!i" "i \<in> I" "i < length xs"
proof -
  have "a \<in> {xs ! i | i. i < length xs \<and> i \<in> I}"
    using assms by (simp only: set_nths)
  then obtain i where "a = xs ! i" and "i < length xs" and "i \<in> I"
    by blast
  then show ?thesis
    using that by blast
qed

lemma next_elem_by_p:
  assumes "p permutes (UNIV :: 'a set)"
  assumes "0 < n" 
  assumes "n < length (support p i)" 
  shows "support p i ! n = p ((support p i)!(n-1))" 
proof -
  have "support p i ! n = (p^^n) i" 
    using assms(3) by fastforce
  have "(support p i)!(n-1) = (p^^(n-1)) i" 
    using assms(3) by fastforce
  have "(p^^n) i = (p \<circ> (p^^(n-1))) i" 
  proof -
    have "(p ^^ n) i = (p ^^ Suc (n - 1)) i"
      using assms(2) by simp
    also have "\<dots> = (p \<circ> (p ^^ (n - 1))) i"
      by (simp only: funpow.simps(2))
    finally show ?thesis .
  qed
  then have "(p^^n) i = p ((p^^(n-1)) i)" 
    by simp
  then show ?thesis 
    using \<open>support p i ! (n - 1) = (p ^^ (n - 1)) i\<close> \<open>support p i ! n = (p ^^ n) i\<close> by presburger
qed

lemma next_elem_by_p':
  assumes "p permutes (UNIV :: 'a set)"
  assumes "n < length (support p i) - 1" 
  shows "support p i ! (n+1) = p ((support p i)!n)"
proof -
  have "0 < n+1"   using zero_less_one by blast
  have "n + 1< length (support p i)" using assms(2) by linarith
  then show ?thesis
    using next_elem_by_p[of p "n+1"] assms(1) \<open>0 < n + 1\<close>
    by simp
qed

lemma perm_verts_in_all_verts:
  assumes "p permutes (UNIV :: 'a set)"
  shows "Vs (u_edges p) \<subseteq> Vs G" 
  using univ by auto

lemma perm_verts_eq_all:
  assumes "p \<in> nonzero_perms"
  shows "Vs (u_edges p) = Vs G" 
proof - 
  have "Vs (u_edges p) = UNIV" 
    proof (rule equalityI)
    show "Vs (u_edges p) \<subseteq> (UNIV :: 'a set)"
      by (rule subset_UNIV)
  next
    show "(UNIV :: 'a set) \<subseteq> Vs (u_edges p)"
    proof
      fix i :: 'a
      assume "i \<in> (UNIV :: 'a set)"
      have "{i, p i} \<in> u_edges p"
        unfolding u_edges_def by blast
      then show "i \<in> Vs (u_edges p)"
        unfolding Vs_def by blast
    qed
  qed
  then show " Vs (u_edges p) = Vs G" 
    by (simp add: univ)
qed

lemma even_circuit_matching:
  assumes "p \<in> nonzero_perms"
  assumes "C \<in> connected_components (u_edges p)"
  assumes "even (card C)"
  shows "\<exists> M. perfect_matching (component_edges (u_edges p) C) M"
proof -
  have "p permutes (UNIV :: 'a set)" using assms(1) 
    by (simp add: nonzero_perms_elim(1))
  have "even (card C)" using assms(3) by auto
  have "C \<subseteq> Vs (u_edges p)" 
    by (simp add: \<open>C \<in> connected_components (u_edges p)\<close> connected_component_subs_Vs)
  obtain x where "x \<in> C" 
  proof -
    have "C \<noteq> {}"
      using assms(2) by (rule connected_comp_nempty)
    then have "\<exists>x. x \<in> C"
      by (simp add: ex_in_conv)
    then show thesis
      using that by blast
  qed
  then have "x \<in> Vs (u_edges p)" 
    by (meson \<open>C \<in> connected_components (u_edges p)\<close> connected_comp_verts_in_verts)
  have "set (support p x) = C" 
    using \<open>C \<in> connected_components (u_edges p)\<close>  \<open>x \<in> C\<close> `p permutes (UNIV :: 'a set)` 
          support_is_connected_component by fastforce
  let ?l = "(support p x)"
  let ?even_i = "{j. j \<in> {0..<length (support p x)} \<and> even j}"
  let ?start_vert = "nths (support p x) ?even_i"
  let ?m_edges = "{{j, (p j)}| j. j \<in> set ?start_vert}"

  have "even (card (set (support p x)))" 
    using \<open>set (support p x) = C\<close> assms(3) by blast
  then have "even (length (support p x))" 
    using distinct_card[OF perm_support_distinct[OF \<open>p permutes UNIV\<close>]] by simp
  have 3:"set ?start_vert \<subseteq> (UNIV :: 'a set)" 
    by blast
  then have "?m_edges \<subseteq> u_edges p" 
    using tutte_matrix.u_edges_def tutte_matrix_axioms by fastforce
  have "Vs ?m_edges = set (support p x)" 
  proof(safe)
    {  fix y
      assume "y \<in> Vs ?m_edges"
      then obtain a where "y \<in> {a, (p a)} \<and> a \<in> set ?start_vert" 
      proof -
        from \<open>y \<in> Vs ?m_edges\<close> obtain e where ye: "y \<in> e" and em: "e \<in> ?m_edges"
          by (auto simp add: Vs_def)
        from em obtain b where eb: "e = {b, p b}" and bs: "b \<in> set ?start_vert"
          by blast
        have "y \<in> {b, p b}" using ye eb by simp
        then show thesis using that bs by blast
      qed
      then show "y \<in> set (support p x)" 
      proof -
        assume ya: "y \<in> {a, p a} \<and> a \<in> set ?start_vert"
        have a_in: "a \<in> set (support p x)"
        proof (rule ccontr)
          assume "a \<notin> set (support p x)"
          then have "a \<notin> set ?start_vert"
            by (rule notin_set_nthsI)
          with ya show False by blast
        qed
        have pa_in: "p a \<in> set (support p x)"
          using \<open>p permutes UNIV\<close> a_in by (rule p_in_same_cycle)
        from ya have "y = a \<or> y = p a" by simp
        then show "y \<in> set (support p x)"
        proof
          assume "y = a"
          then show ?thesis using a_in by simp
        next
          assume "y = p a"
          then show ?thesis using pa_in by simp
        qed
      qed
    }
    fix y
    assume "y \<in> set (support p x)" 
    then obtain n where n_exp: "y = (support p x)!n \<and> n < least_power p x" 
      proof -
        have len: "length (support p x) = least_power p x"
          by simp
        from \<open>y \<in> set (support p x)\<close> obtain k
          where k_less: "k < length (support p x)" and k_eq: "support p x ! k = y"
          using in_set_conv_nth[of y "support p x"] by blast
        have "y = support p x ! k \<and> k < least_power p x"
          using k_eq k_less len by simp
        then show thesis
          by (rule that)
      qed
    show "y \<in> Vs ?m_edges" 
    proof(cases "even n")
      case True
      then have "n \<in>  {j \<in> {0..<length (support p x)}. even j}" 
        by (simp add: n_exp)
      then have "y \<in> set (nths (support p x) {j \<in> {0..<length (support p x)}. even j})" 
      proof -
        have n_lt: "n < length (support p x)"
          using n_exp by simp
        have n_mem: "n \<in> {j \<in> {0..<length (support p x)}. even j}"
          using True n_lt by simp
        have "support p x ! n
                \<in> set (nths (support p x) {j \<in> {0..<length (support p x)}. even j})"
          by (rule nths_in_result[OF n_mem n_lt])
        then show ?thesis
          using n_exp by simp
      qed
      then have "{y, p y} \<in> ?m_edges" 
        by blast
      then show ?thesis by blast 
    next
      case False
      have "n > 0" using False  
        using odd_pos by auto
      then have "even (n-1)" 
        by (simp add: False)
      then have "n - 1 \<in>  {j \<in> {0..<length (support p x)}. even j}" 
        by (simp add: n_exp less_imp_diff_less)
      then have 1:"(support p x)!(n-1) \<in> 
                 set (nths (support p x) {j \<in> {0..<length (support p x)}. even j})"      
      proof -
        have lt: "n - 1 < length (support p x)"
          using n_exp by (simp add: less_imp_diff_less)
        have mem: "n - 1 \<in> {j \<in> {0..<length (support p x)}. even j}"
          using lt \<open>even (n - 1)\<close> by simp
        show ?thesis
          by (rule nths_in_result[OF mem lt])
      qed
      have "support p x ! n = p ((support p x)!(n-1))"  
        using \<open>0 < n\<close> n_exp \<open>p permutes UNIV\<close> length_upt map_eq_conv next_elem_by_p by force
      have 2:"{((support p x)!(n-1)), (p ((support p x)!(n-1)))} \<in> ?m_edges"  
        using 1 by blast
      then have "(p ((support p x)!(n-1))) = y" 
        using \<open>support p x ! n = p (support p x ! (n - 1))\<close> n_exp by presburger
      then show ?thesis 
        using 2 insert_commute by auto

    qed
  qed
  then have "Vs ?m_edges = C" 
    using \<open>set (support p x) = C\<close> by fastforce
  have "matching ?m_edges" unfolding matching_def
  proof
    fix e1 
    assume asme1:"e1 \<in> ?m_edges"
    show "\<forall>e2 \<in> ?m_edges. e1 \<noteq> e2 \<longrightarrow>e1 \<inter> e2 = {}"
    proof
      fix e2
      assume asme2:"e2 \<in> ?m_edges"
      show "e1 \<noteq> e2 \<longrightarrow>e1 \<inter> e2 = {}"
      proof
        assume "e1 \<noteq> e2"
        show "e1 \<inter> e2 = {}"
        proof(rule ccontr)
          assume "e1 \<inter> e2 \<noteq> {}" 
          then obtain t where "t \<in> e1 \<inter> e2" by auto
          obtain u v where uv:"e1 = {u, t} \<and> e2 = {t, v}" 
            proof -
              have te1: "t \<in> e1" and te2: "t \<in> e2"
                using \<open>t \<in> e1 \<inter> e2\<close> by auto
              from asme1 obtain a1 where a1: "e1 = {a1, p a1}" by blast
              from asme2 obtain b1 where b1: "e2 = {b1, p b1}" by blast
              have ex1: "\<exists>u. e1 = {u, t}"
              proof(cases "t = a1")
                case True
                have "e1 = {p a1, t}"
                  using a1 True by (simp add: insert_commute)
                then show ?thesis by blast
              next
                case False
                have "t = p a1"
                  using te1 a1 False by simp
                then have "e1 = {a1, t}"
                  using a1 by simp
                then show ?thesis by blast
              qed
              have ex2: "\<exists>v. e2 = {t, v}"
              proof(cases "t = b1")
                case True
                have "e2 = {t, p b1}"
                  using b1 True by simp
                then show ?thesis by blast
              next
                case False
                have "t = p b1"
                  using te2 b1 False by simp
                then have "e2 = {t, b1}"
                  using b1 by (simp add: insert_commute)
                then show ?thesis by blast
              qed
              show thesis using ex1 ex2 that by blast
            qed
          then have "u \<noteq> v" 
            using \<open>e1 \<noteq> e2\<close> by fastforce
          then obtain a where a_elem:"{a, (p a)} = {u, t}  \<and> a \<in> set ?start_vert" 
            using asme1 uv by blast
          obtain b where b_elem:"{b, (p b)} = {v, t}  \<and> b \<in> set ?start_vert" 
          proof -
            from asme2 obtain b where b1: "e2 = {b, p b}" and b2: "b \<in> set ?start_vert"
              by blast
            have "{b, p b} = e2" using b1 by (rule sym)
            also have "e2 = {t, v}" using uv by simp
            also have "{t, v} = {v, t}" by auto
            finally have b3: "{b, p b} = {v, t}" .
            from b3 b2 have "{b, p b} = {v, t} \<and> b \<in> set ?start_vert" by (rule conjI)
            then show thesis by (rule that)
          qed
          have "even (length (support p x))" 
            using \<open>even (length (support p x))\<close> by blast
          have "a \<in> set (support p x)"  
            using a_elem notin_set_nthsI by fastforce
          then obtain an where an: "a = (support p x)!an \<and> 
                                    an \<in> {j \<in> {0..<length (support p x)}. even j}" 
            using a_elem by (blast elim: nths_obtain_index)
          then have "even an"  
            by blast
          then have 4:"an < (length (support p x)) - 1"
            using `even (length (support p x))` a_elem One_nat_def Suc_leI Suc_pred an 
              \<open>a \<in> set (support p x)\<close> atLeastLessThan_iff even_Suc length_pos_if_in_set 
              linorder_neqE_nat mem_Collect_eq not_le by fastforce
          have "b \<in> set (support p x)"  
            using b_elem notin_set_nthsI by fastforce
          then obtain bn where bn: "b = (support p x)!bn \<and> 
                                    bn \<in> {j \<in> {0..<length (support p x)}. even j}"
            using b_elem  nths_obtain_index 
          proof -
            have bmem: "b \<in> set (nths (support p x) {j \<in> {0..<length (support p x)}. even j})"
              using b_elem by blast
            have "\<exists>bn. b = (support p x)!bn \<and> bn \<in> {j \<in> {0..<length (support p x)}. even j}"
              using bmem[unfolded set_nths] by blast
            then show thesis
              using that by blast
          qed
          then have 5:"bn < (length (support p x)) - 1" 
            using `even (length (support p x))` by fastforce
          have "even bn" 
            using bn by fastforce
          show False
          proof(cases "a = u \<and> (p a) = t")
            case True
            then show ?thesis
            proof(cases "b = v \<and> (p b) = t")
              case True
              have "p a = p b"
                using `a = u \<and> (p a) = t` True 
                by auto
              then have "a = b" 
                by (blast intro: injD permutes_inj \<open>p permutes UNIV\<close>)
              then show ?thesis 
                using True uv \<open>e1 \<noteq> e2\<close> a_elem by blast
            next
              case False
              have "b = t \<and> (p b) = v" 
                by (meson False b_elem doubleton_eq_iff)
              have "p ((support p x)!an) = (support p x)!(an+1)" 
                using  next_elem_by_p'[of p an x] 4 \<open>p permutes UNIV\<close> 
                by presburger
              then have "p a = (support p x)!(an+1)" 
                using an by fastforce
              then have 6:"(support p x)!(an+1) = (support p x)!(bn)" 
                using True bn \<open>b = t \<and> p b = v\<close> by presburger
              have "an + 1 \<noteq> bn" 
                using \<open>even an\<close> \<open>even bn\<close> even_add odd_one by blast
              then have "\<not> distinct (support p x)" 
                proof -
                  have len1: "an + 1 < length (support p x)"
                    using 4 by (simp add: less_diff_conv)
                  have len2: "bn < length (support p x)"
                    using 5 by (meson diff_le_self less_le_trans)
                  show "\<not> distinct (support p x)"
                  proof
                    assume dist: "distinct (support p x)"
                    have "(support p x ! (an + 1) = support p x ! bn) = (an + 1 = bn)"
                      by (rule nth_eq_iff_index_eq[OF dist len1 len2])
                    then have "an + 1 = bn"
                      using 6 by simp
                    then show False
                      using \<open>an + 1 \<noteq> bn\<close> by simp
                  qed
                qed
              then show ?thesis 
                using \<open>p permutes UNIV\<close> perm_support_distinct by force
            qed
          next
            case False
            have "a =  t \<and> (p a) = u" 
              by (meson False a_elem doubleton_eq_iff) 
            have "p ((support p x)!bn) = (support p x)!(bn+1)" 
              using  next_elem_by_p'[of p bn x] 
              using 5 \<open>p permutes UNIV\<close> by presburger
            then have "p b = (support p x)!(bn+1)" 
              using bn by fastforce
            show ?thesis 
            proof(cases "b = v \<and> (p b) = t")
              case True
              have "a = (p b)" 
                using True \<open>a = t \<and> p a = u\<close> by blast
              then have 7:"(support p x)!(bn+1) = (support p x)!(an)" 
                using an \<open>p b = support p x ! (bn + 1)\<close> by presburger
              have "bn + 1 \<noteq> an" 
                using \<open>even an\<close> \<open>even bn\<close> even_add odd_one by blast
              then have "\<not> distinct (support p x)" 
              proof -
                have ean: "even an" using an by auto
                have ebn: "even bn" using bn by auto
                have Bl: "bn + 1 < length (support p x)"
                  using 5 by (simp add: less_diff_conv)
                have Al: "an + 1 < length (support p x)"
                  using 4 by (simp add: less_diff_conv)
                then have Al': "an < length (support p x)" by linarith
                show ?thesis
                proof
                  assume dist: "distinct (support p x)"
                  have eq: "bn + 1 = an"
                    using 7 nth_eq_iff_index_eq[OF dist Bl Al'] by simp
                  show False using ean ebn eq by presburger
                qed
              qed
              then show ?thesis 
                using \<open>p permutes UNIV\<close> perm_support_distinct by force
            next
              case False
              have "b = t \<and> (p b) = v" 
                by (meson False b_elem doubleton_eq_iff) 
              then have "b = a" 
                using \<open>a = t \<and> (p a) = u\<close> by auto
              then have "u = v" 
                using \<open>a = t \<and> (p a) = u\<close> \<open>b = t \<and> (p b) = v\<close> by blast
              then show ?thesis 
                using \<open>u \<noteq> v\<close> by auto
            qed
          qed
        qed
      qed
    qed
  qed
  have 9:"?m_edges \<subseteq> (component_edges (u_edges p) C)"
  proof
    fix e
    assume "e \<in> ?m_edges" 
    then have "e \<in> (u_edges p)"         
      using  \<open>?m_edges \<subseteq> u_edges p\<close> by blast
    have "e \<subseteq> C" 
      using \<open>Vs ?m_edges = set (support p x)\<close> \<open>e \<in> ?m_edges\<close> \<open>set (support p x) = C\<close>
            subset_iff vs_member by blast
    then show "e \<in> (component_edges (u_edges p) C)" 
      unfolding component_edges_def
      using \<open>e \<in> u_edges p\<close> by fastforce
  qed
  have 8:"Vs (component_edges (u_edges p) C) = C" 
    using vs_connected_component[of "u_edges p" C] assms(2)
    by (meson assms(1) u_edges_is_graph)
  then have "graph_invar (component_edges (u_edges p) C)"
    using Connected_Components.component_edges_subset assms(1) u_edges_is_graph
    by force
  then  have " perfect_matching (component_edges (u_edges p) C) ?m_edges"
    unfolding perfect_matching_def 
    using 8 \<open>Vs ?m_edges = C\<close> \<open>matching ?m_edges\<close> 9
    by simp
  then show "\<exists> M'. perfect_matching (component_edges (u_edges p) C) M'" 
    by blast
qed

lemma even_circuits_has_perfect_matching:
  assumes "p \<in> nonzero_perms"
  assumes "\<forall>C \<in> connected_components (u_edges p). even (card C) "
  shows "\<exists> M. perfect_matching (u_edges p) M"
proof -
  have "p permutes (UNIV :: 'a set)" 
    using assms(1) nonzero_perms_def  by auto
  have "finite (u_edges p)" 
    by (simp add: u_edges_finite)
  have "\<forall> C \<in> connected_components (u_edges p). 
        \<exists> M'. perfect_matching (component_edges (u_edges p) C) M'"
    using even_circuit_matching assms by blast
  then  show "\<exists> M. perfect_matching (u_edges p) M" 
    using perfect_matching_union_components[of "u_edges p"] u_edges_is_graph assms(1)
    by presburger
qed

definition least_odd :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "least_odd p = (LEAST a. odd (least_power p a))"

definition rev_p :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  where "rev_p p = (\<lambda> i. if i \<in> set (support p (least_odd p)) then 
        (inv p) i else p i)" 

lemma least_power_same_in_support:
  assumes "permutation p"
  assumes "a \<in> set (support p i)"
  shows "(p^^least_power p i) a = a" 
proof -
  obtain n where n:"(p^^n) i = a \<and> n < least_power p i"
    using assms  by fastforce
  have "(p^^n) i = ((p^^n) \<circ> (p^^least_power p i)) i" 
    by (simp add: assms(1) least_power_of_permutation(1))
  then have "((p^^least_power p i)\<circ>(p^^n)) i = (p^^n) i" 
  proof -
  have fix_i: "(p ^^ least_power p i) i = i"
    by (simp add: assms(1) least_power_of_permutation(1))
  have "(p ^^ least_power p i) \<circ> (p ^^ n) = p ^^ (least_power p i + n)"
    by (simp add: funpow_add)
  also have "\<dots> = p ^^ (n + least_power p i)"
    by (simp add: add.commute)
  also have "\<dots> = (p ^^ n) \<circ> (p ^^ least_power p i)"
    by (simp add: funpow_add)
  finally have comm: "(p ^^ least_power p i) \<circ> (p ^^ n) = (p ^^ n) \<circ> (p ^^ least_power p i)" .
  show ?thesis
    using comm fix_i by simp
  qed
  then have "(p^^least_power p i) ((p^^n) i) = (p^^n) i" 
    by simp
  then show ?thesis 
    using n by blast
qed

lemma inv_in_support:
  assumes "permutation p"
  assumes "a \<in> set (support p i)"
  shows "(inv p) a \<in> set (support p i)" 
proof  -
  have "permutation (inv p)" 
    using assms(1) permutation_inverse by blast
  moreover have "a \<in> set (support (inv p) i)" 
    using assms(1) assms(2) inv_support_same by fastforce
  ultimately have "(inv p) a \<in> set (support (inv p) i)" 
    using elemnets_in_support_expo[where n = 1 and p = "inv p" and x = a and i = i and y = "inv p a"]
    by simp
  then show ?thesis 
    using assms(1) inv_support_same by fastforce
qed

lemma inv_notin_support:
  assumes "permutation p"
  assumes "a \<notin> set (support p i)"
  shows "(inv p) a \<notin> set (support p i)"
proof(rule ccontr)
  assume "\<not> (inv p) a \<notin> set (support p i)"
  then have "(inv p) a \<in> set (support p i)"
    by auto
  then have "p ((inv p) a) = a" 
    by (meson assms(1) bij_inv_eq_iff permutation_bijective)
  have "p ((inv p) a) \<in> set (support p i)" 
  proof -
    have "p (inv p a) = (p ^^ (1::nat)) (inv p a)"
      by simp
    then show ?thesis
      using elemnets_in_support_expo[OF assms(1) \<open>inv p a \<in> set (support p i)\<close>]
      by blast
  qed
  then show False 
    using \<open>p (inv p a) = a\<close> assms(2) by auto
qed

lemma p_rev_p_same:
  assumes "p permutes (UNIV::'a set)"
  assumes "x \<in> set (support p (least_odd p))" 
  shows "p (rev_p p x) = x" 
proof -
  have "rev_p p x = inv p x"
    using assms(2) by (simp add: rev_p_def)
  hence "p (rev_p p x) = p (inv p x)"
    by simp
  also have "\<dots> = x"
    by (rule permutes_inverses(1)[OF assms(1)])
  finally show ?thesis .
qed

lemma p_rev_p_same':
  assumes "p permutes (UNIV::'a set)"
  assumes "x \<notin> set (support p (least_odd p))" 
  shows "(rev_p p x) = p x" 
  using assms(2) rev_p_def by presburger

definition on_odd where
  "on_odd p = (\<lambda> x. if x \<in> set (support p (least_odd p)) then p x else x)" 

definition not_on_odd where
  "not_on_odd p = (\<lambda> x. if x \<notin> set (support p (least_odd p)) then p x else x)" 

lemma on_odd_in:
  assumes "x \<in>  set (support p (least_odd p))"
  shows "on_odd p x = p x" 
  unfolding on_odd_def using assms by auto

lemma on_odd_out:
  assumes "x \<notin>  set (support p (least_odd p))"
  shows "on_odd p x = x" 
  unfolding on_odd_def using assms by auto

lemma not_on_odd_in:
  assumes "x \<notin>  set (support p (least_odd p))"
  shows "not_on_odd p x = p x" 
  unfolding not_on_odd_def using assms by auto

lemma not_on_odd_out:
  assumes "x \<in>  set (support p (least_odd p))"
  shows "not_on_odd p x = x" 
  unfolding not_on_odd_def using assms by auto

lemma on_odd_p_permutes:
  assumes "p permutes (UNIV::'a set)"
  shows "(on_odd p) permutes (set (support p (least_odd p)))" 
proof -
  let ?A = "set (support p  (least_odd p))"
  have "(\<forall>x\<in>?A. \<forall>y\<in>?A. (on_odd p) x = (on_odd p) y \<longrightarrow> x = y)"
  proof (intro ballI impI)
    fix x y
    assume xA: "x \<in> set (support p (least_odd p))"
      and yA: "y \<in> set (support p (least_odd p))"
      and eq: "on_odd p x = on_odd p y"
    have hx: "on_odd p x = p x"
      unfolding on_odd_def using xA by simp
    have hy: "on_odd p y = p y"
      unfolding on_odd_def using yA by simp
    from eq hx hy have "p x = p y" by simp
    moreover have "inj p" using assms by (rule permutes_inj)
    ultimately show "x = y" by (rule injD[rotated])
  qed
  then have "inj_on (on_odd p) ?A" 
    using inj_on_def by blast
  have "(on_odd p) ` ?A = ?A"
    apply safe 
    using assms on_odd_def p_in_same_cycle apply presburger
  proof -
    fix x
    assume "x \<in> ?A" 
    have "(inv p) x \<in> ?A" 
      using \<open>x \<in> ?A\<close> assms inv_in_support p_is_permutation
      by fast
    have "(on_odd p) ((inv p) x) = x" 
    proof -
      have "on_odd p (inv p x) = p (inv p x)"
        using \<open>inv p x \<in> ?A\<close> by (rule on_odd_in)
      also have "\<dots> = x"
        using assms by (rule permutes_inverses(1))
      finally show ?thesis .
    qed
    then show "x \<in> (on_odd p) ` ?A" 
      by (rule image_eqI[OF sym]) fact
  qed
  then have "bij_betw (on_odd p) ?A ?A" 
    unfolding bij_betw_def 
    using \<open>inj_on (on_odd p) ?A\<close> by blast
  have "(\<And>x. x \<notin> ?A \<Longrightarrow> (on_odd p) x = x)" 
    using on_odd_out by presburger
  then show " (on_odd p) permutes ?A" 
    using  Permutations.bij_imp_permutes
    using \<open>bij_betw (on_odd p) ?A ?A\<close> by blast
qed

lemma on_odd_p_permutes_UNIV:
  assumes "p permutes (UNIV::'a set)"
  shows "(on_odd p) permutes UNIV" using on_odd_p_permutes assms 
  by (meson bij_imp_permutes iso_tuple_UNIV_I permutes_bij)

lemma not_on_odd_p_permutes:
  assumes "p permutes (UNIV::'a set)"
  shows "(not_on_odd p) permutes (UNIV::'a set) - (set (support p  (least_odd p)))"
proof -
  let ?A = "(UNIV::'a set) - (set (support p (least_odd p)))"
  have "(\<forall>x\<in>?A. \<forall>y\<in>?A. (not_on_odd p) x = (not_on_odd p) y \<longrightarrow> x = y)"
  proof(rule+) 
    fix x y
    assume "x \<in> ?A" "y \<in> ?A"  "not_on_odd p x = not_on_odd p y" 
    then have "not_on_odd p x = p x" 
      using not_on_odd_in by blast
    then have "not_on_odd p y = p y" 
      using not_on_odd_in  \<open>y \<in> ?A\<close> by blast
    then show "x = y" 
    proof -
      have inj_p: "inj p"
        using assms by (rule permutes_inj)
      have "p x = not_on_odd p y"
        using \<open>not_on_odd p x = not_on_odd p y\<close> \<open>not_on_odd p x = p x\<close>
        by simp
      then have "p x = p y"
        using \<open>not_on_odd p y = p y\<close> by simp
      with inj_p show "x = y"
        by (rule injD)
    qed
  qed
  then have "inj_on (not_on_odd p) ?A" 
    using inj_on_def by blast
  have "(not_on_odd p) ` ?A = ?A"
  proof(rule)+
    show "?A \<subseteq> not_on_odd p ` ?A"
    proof
      fix x
      assume "x \<in> ?A"
      then have "p x \<in> ?A" 
      proof -
        have perm: "permutation p"
          using assms by (rule p_is_permutation)
        have xout: "x \<notin> set (support p (least_odd p))"
          using \<open>x \<in> ?A\<close> by blast
        have "p x \<notin> set (support p (least_odd p))"
        proof
          assume px: "p x \<in> set (support p (least_odd p))"
          have "p x = (p ^^ Suc 0) x" by simp
          then have "x \<in> set (support p (least_odd p))"
            using elemnets_in_support_expo'[OF perm px] by blast
          then show False using xout by blast
        qed
        then show ?thesis by blast
      qed
      then show "x \<in> not_on_odd p ` ?A" 
      proof -
        have perm: "permutation p"
          using assms by (rule p_is_permutation)
        have "x \<notin> set (support p (least_odd p))"
          using \<open>x \<in> ?A\<close> by simp
        with perm have inv_notin: "inv p x \<notin> set (support p (least_odd p))"
          by (rule inv_notin_support)
        then have mem: "inv p x \<in> ?A"
          by simp
        have eq: "not_on_odd p (inv p x) = p (inv p x)"
          using inv_notin by (rule not_on_odd_in)
        have px: "p (inv p x) = x"
          by (rule permutes_inverses(1)[OF assms])
        show ?thesis
        proof (rule image_eqI[where x = "inv p x"])
          show "x = not_on_odd p (inv p x)"
            using eq px by simp
          show "inv p x \<in> ?A"
            by (rule mem)
        qed
      qed
    qed
    fix x
    assume asmx: "x \<in>  not_on_odd p ` ?A"  "x \<in>  set (support p (least_odd p)) " 
    have "(inv p x) \<in> set (support p (least_odd p))" 
      using asmx assms inv_in_support p_is_permutation by fast
    then have "x \<in> ?A" 
      using asmx by (force simp add: not_on_odd_in permutes_inverses(2)[OF assms])
    then show False 
      using \<open>x \<in> set (support p (least_odd p))\<close> by force
  qed
  then have 1:"bij_betw (not_on_odd p) ?A ?A" 
    unfolding bij_betw_def 
    using \<open>inj_on (not_on_odd p) ?A\<close> by blast
  have "(\<And>x. x \<notin> ?A \<Longrightarrow> (not_on_odd p) x = x)" 
    using not_on_odd_out by simp
  then show " (not_on_odd p) permutes ?A" 
    using  Permutations.bij_imp_permutes
    using 1 by blast
qed

lemma not_on_odd_p_permutes_UNIV:
  assumes "p permutes (UNIV::'a set)"
  shows "(not_on_odd p) permutes (UNIV::'a set)"
  using not_on_odd_p_permutes assms permutes_subset by blast

lemma rev_is_composition:
  assumes "p permutes (UNIV::'a set)"
  shows "rev_p p = ((inv (on_odd  p)) \<circ>  not_on_odd p)"
proof
  let ?A = "(set (support p  (least_odd p)))" 
  fix x
  show " rev_p p x = ((inv (on_odd  p)) \<circ>  not_on_odd p) x"
  proof(cases "x \<in> ?A")
    case True
    have "not_on_odd p x = x" 
      using True not_on_odd_out by presburger
    have " (on_odd  p) x = p x" using on_odd_in[of x "inv p"] True 
      using on_odd_def by presburger
    then have "inv (on_odd  p) x = (inv p) x" 
      proof -
  have xA: "inv p x \<in> set (support p (least_odd p))"
    by (rule inv_in_support[OF p_is_permutation[OF assms], OF True])
  have "on_odd p (inv p x) = p (inv p x)"
    using xA by (rule on_odd_in)
  also have "\<dots> = x"
    using assms by (rule permutes_inverses(1))
  finally have qx: "on_odd p (inv p x) = x" .
  have q: "on_odd p permutes UNIV"
    using assms by (rule on_odd_p_permutes_UNIV)
  show "inv (on_odd p) x = inv p x"
    using qx by (rule iffD2[OF permutes_inv_eq[OF q]])
qed
    then have "rev_p p x = (inv p x)" 
      using True by (simp add: rev_p_def)
    then show ?thesis 
      by (simp add: \<open>inv (on_odd p) x = inv p x\<close> \<open>not_on_odd p x = x\<close>)
  next
    case False
    have "rev_p p x = p x"
      using False assms unfolding rev_p_def by presburger
    have "not_on_odd p x = p x" 
      using False not_on_odd_in by presburger
    then have "inv (on_odd  p) (p x) = p x" 
    proof -
      have notin: "p x \<notin> set (support p (least_odd p))"
      proof
        assume "p x \<in> set (support p (least_odd p))"
        then have "inv p (p x) \<in> set (support p (least_odd p))"
          using inv_in_support[OF p_is_permutation[OF assms]] by blast
        moreover have "inv p (p x) = x"
          by (simp add: permutes_inv_eq[OF assms])
        ultimately show False using False by simp
      qed
      have "on_odd p (p x) = p x"
        by (rule on_odd_out[OF notin])
      then show ?thesis
        using permutes_inv_eq[OF on_odd_p_permutes_UNIV[OF assms]] by simp
    qed
    then show ?thesis 
      using \<open>not_on_odd p x = p x\<close> \<open>rev_p p x = p x\<close> by force
  qed
qed

lemma rev_p_permutes:
  assumes "p permutes (UNIV::'a set)"
  shows "(rev_p p) permutes (UNIV::'a set)" 
  using rev_is_composition not_on_odd_p_permutes_UNIV assms 
  by (simp add: on_odd_p_permutes_UNIV permutes_compose permutes_inv)

lemma odd_component_then_odd_circuit:
  assumes "p permutes (UNIV :: 'a set)" 
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) "
  obtains x where "odd (least_power p x)"
proof -
  obtain C where C:"C \<in> connected_components (u_edges p) \<and> odd (card C)"
    using assms by blast
  then obtain x where "x \<in> C" 
proof -
  have "C \<noteq> {}"
  proof
    assume "C = {}"
    then have "card C = 0"
      by simp
    then show False
      using C by simp
  qed
  then obtain y where "y \<in> C"
    by blast
  then show thesis
    by (rule that)
qed
  then have "x \<in> Vs (u_edges p)" 
    by (meson C connected_comp_verts_in_verts)
  have "C = set (support p x)" 
    using support_is_connected_component[of p C x] C \<open>x \<in> C\<close> assms(1) by fastforce
  then have " odd (least_power p x)" 
proof -
  have dist: "distinct (support p x)"
    using assms(1) by (rule cycle_vert_is_distict)
  have "card C = card (set (support p x))"
    using \<open>C = set (support p x)\<close> by simp
  also have "\<dots> = length (support p x)"
    using dist by (rule distinct_card)
  also have "\<dots> = least_power p x"
    by simp
  finally have "card C = least_power p x" .
  moreover have "odd (card C)"
    using C by blast
  ultimately show ?thesis
    by simp
  qed
  show ?thesis 
    using \<open>odd (least_power p x)\<close> that by auto
qed

lemma least_odd_is_odd:
  assumes "p permutes (UNIV :: 'a set)" 
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) "
  shows "odd (least_power p  (least_odd p))" 
proof -
  obtain i where "odd (least_power p i)" 
    using odd_component_then_odd_circuit[of p] assms by blast
  then show ?thesis
    unfolding least_odd_def
    using LeastI[of "\<lambda>a. odd (least_power p a)"] by blast
qed

lemma reverse_for_each_product:
  fixes h :: "'n \<Rightarrow> 'b::comm_ring_1"
  assumes "\<forall>a \<in> A. h a = - (g a)"
  assumes "odd (card A)"
  shows "prod h A = - prod g A" 
  using assms
proof(induct "card A" arbitrary: A rule: less_induct)
  case less
  have "finite A" 
  proof (rule ccontr)
    assume "infinite A"
    then have "card A = 0"
      by (rule card.infinite)
    with less.prems(2) show False by simp
  qed
  then show ?case
  proof(cases "card A = 1")
    case True
    obtain a where "a \<in> A" 
      proof -
        from True obtain b where "A = {b}"
          by (rule card_1_singletonE)
        then have "b \<in> A"
          by simp
        then show thesis
          using that by blast
      qed
    then have "A = {a}" 
      proof -
        obtain b where "A = {b}"
          using True by (rule card_1_singletonE)
        then show "A = {a}"
          using \<open>a \<in> A\<close> by simp
      qed
    then have "prod h A = h a" 
      by simp
    have "prod g A = g a" using `A = {a}` by simp

    then show ?thesis 
      using \<open>a \<in> A\<close> \<open>prod h A = h a\<close> less.prems(1) by force
  next
    case False
    then have "card A > 1" 
      proof -
        have "card A \<noteq> 0"
          using less.prems(2) by presburger
        moreover have "card A \<noteq> 1"
          using False by blast
        ultimately show ?thesis
          by linarith
      qed
    then obtain a b where ab: "a \<in> A \<and> b \<in> A \<and> a \<noteq> b" 
    proof -
      assume gt: "1 < card A"
      then have "A \<noteq> {}" by force
      then obtain x where x: "x \<in> A" by blast
      have "\<exists>y \<in> A. x \<noteq> y"
      proof (rule ccontr)
        assume "\<not> (\<exists>y \<in> A. x \<noteq> y)"
        have sub: "A \<subseteq> {x}"
        proof (rule subsetI)
          fix z
          assume zA: "z \<in> A"
          show "z \<in> {x}"
          proof (rule ccontr)
            assume "z \<notin> {x}"
            then have "x \<noteq> z" by simp
            with zA have "\<exists>y \<in> A. x \<noteq> y" by blast
            with \<open>\<not> (\<exists>y \<in> A. x \<noteq> y)\<close> show False by blast
          qed
        qed
        have "card A \<le> card {x}"
        proof (rule card_mono)
          show "finite {x}" by simp
          show "A \<subseteq> {x}" using sub by blast
        qed
        then have "card A \<le> 1" by simp
        with gt show False by linarith
      qed
      then obtain y where y: "y \<in> A" "x \<noteq> y" by blast
      have "x \<in> A \<and> y \<in> A \<and> x \<noteq> y" using x y by blast
      then show thesis by (rule that)
    qed
    then have "odd (card (A - {a, b}))" 
      proof -
  have aA: "a \<in> A" and bA: "b \<in> A" and neq: "a \<noteq> b"
    using \<open>a \<in> A \<and> b \<in> A \<and> a \<noteq> b\<close> by auto
  have finb: "finite (A - {b})"
    using \<open>finite A\<close> by (rule finite_Diff)
  have amem: "a \<in> A - {b}"
    using aA neq by blast
  have c1: "Suc (card (A - {b} - {a})) = card (A - {b})"
    using finb amem by (rule card_Suc_Diff1)
  have c2: "Suc (card (A - {b})) = card A"
    using \<open>finite A\<close> bA by (rule card_Suc_Diff1)
  have card2: "card {a, b} = 2" using neq by simp
  have fin2: "finite {a, b}" by simp
  have sub: "{a, b} \<subseteq> A" using aA bA by simp
  have "card {a, b} \<le> card A"
    using \<open>finite A\<close> sub by (rule card_mono)
  with card2 have "2 \<le> card A" by simp
  then show "odd (card (A - {a, b}))"
    using card_Diff_subset[OF fin2 sub] card2 less.prems(2) by presburger
      qed
    have "(card (A - {a, b})) < card A" 
      proof -
        have finA: "finite A"
          using \<open>finite A\<close> .
        have aA: "a \<in> A"
          using ab by blast
        have finA': "finite (A - {a})"
          using finA by blast
        have bA': "b \<in> A - {a}"
          using ab by blast
        have less1: "card (A - {a} - {b}) < card (A - {a})"
          by (rule card_Diff1_less[OF finA' bA'])
        have less2: "card (A - {a}) < card A"
          by (rule card_Diff1_less[OF finA aA])
        have eq: "A - {a, b} = A - {a} - {b}"
          by blast
        have "card (A - {a, b}) = card (A - {a} - {b})"
          using eq by simp
        then show ?thesis
          using less1 less2 by linarith
      qed
    have "\<forall>a \<in> (A - {a, b}). h a = - (g a)" 
      by (meson DiffD1 less.prems(1))
    then have "prod h (A - {a, b}) = - prod g (A - {a, b})" 
      using \<open>card (A - {a, b}) < card A\<close> \<open>odd (card (A - {a, b}))\<close> less.hyps by presburger
    moreover have "prod h A = prod h (A - {a, b}) * prod h {a, b}" 
      by (meson \<open>finite A\<close> ab bot.extremum insert_subset prod.subset_diff) 
    moreover have "prod g A = prod g (A - {a, b}) * prod g {a, b}"
      by (meson \<open>finite A\<close> ab bot.extremum insert_subset prod.subset_diff)
    moreover  have "prod h {a, b} = h a * h b" 
      by (simp add: ab)
    moreover have "prod g {a, b} = g a * g b" 
      by (simp add: ab)
    moreover then have "h a * h b = (- g a)*(-g b)" 
      by (simp add: ab less.prems(1))
    moreover have "(- g a)*(-g b) = ((-1) * g a) * ((-1) * g b)" 
      by simp
    ultimately show ?thesis 
      by force
  qed
qed

lemma p_is_composition:
  assumes "p permutes (UNIV::'a set)"
  shows "p = on_odd  p \<circ>  not_on_odd p"
proof
  fix x
  let ?A = "(set (support p  (least_odd p)))" 
  show "p x = (on_odd p \<circ> not_on_odd p) x" 
  proof(cases "x \<in> ?A")
    case True
    have "not_on_odd p x = x" 
      using True not_on_odd_out by presburger
    have "on_odd p x = p x" 
  proof -
    have "x \<in> set (support p (least_odd p))"
      using True by blast
    then show ?thesis
      by (rule on_odd_in)
  qed
    then show ?thesis 
      by (simp add: \<open>not_on_odd p x = x\<close>)
  next
    case False
    have "not_on_odd p x = p x" 
      using False not_on_odd_in by presburger
    then have "on_odd p (p x) = p x" 
      unfolding on_odd_def
      using False
        inv_in_support[OF p_is_permutation[OF assms], where a = "p x" and i = "least_odd p"]
      by (auto simp add: on_odd_def permutes_inverses(2)[OF assms])
    then show ?thesis 
      by (simp add: \<open>not_on_odd p x = p x\<close>)
  qed
qed

lemma rev_p_opposit_tutte_value:
  assumes "p permutes (UNIV::'a set)"
  assumes "i \<in> set (support p  (least_odd p))"
  shows "(tutte_matrix )$i$p i = - (tutte_matrix )$p i$(rev_p p) (p i)"
proof - 
  have "p i \<in> set (support p  (least_odd p))" 
    by (rule p_in_same_cycle[OF assms]) 
  then have "(rev_p p) (p i) = i"  
    unfolding rev_p_def 
    by (simp add: rev_p_def
                   if_P[OF p_in_same_cycle[OF assms(1) assms(2)]]
                   permutes_inv_eq[OF assms(1)])
  note rev_eq = this
  have "tutte_matrix $ i $ p i = - tutte_matrix $ (p i) $ i"
    by (rule tutte_skew_symmetric)
  then show ?thesis
    by (simp only: rev_eq)
qed

lemma least_odd_support_is_odd:
  assumes "p permutes (UNIV::'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)" 
  shows "odd (card (set (support p (least_odd p))))" 
proof -
  have "card (set (support p (least_odd p))) = least_power p (least_odd p)"
    using \<open>p permutes UNIV\<close> distinct_card perm_support_distinct by force
  then show ?thesis 
    using assms(1) assms(2) least_odd_is_odd by presburger
qed   

lemma rev_product_is_minus:
  assumes "p permutes (UNIV::'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows " prod (\<lambda>i. (tutte_matrix )$i$p i) (UNIV :: 'a set) = 
          -  prod (\<lambda>i. (tutte_matrix)$i$(rev_p p) i) (UNIV :: 'a set)" 
proof -
  let ?A = "set (support p  (least_odd p))"
  let ?h = "(\<lambda>i. (tutte_matrix )$i$p i)" 
  let ?g = "(\<lambda>i. (tutte_matrix )$i$(rev_p p) i)" 
  have 3: "prod ?h UNIV =  prod ?h ?A *  prod ?h (UNIV - ?A)" 
  proof -
    have fin: "finite (UNIV :: 'a set)"
      by (rule univ_is_finite)
    have subs: "?A \<subseteq> (UNIV :: 'a set)"
      by (rule subset_UNIV)
    show ?thesis
      by (rule trans[OF prod.subset_diff[OF subs fin] mult.commute])
  qed
  have 4:"prod ?g UNIV =  prod ?g ?A *  prod ?g (UNIV - ?A)"
    by (rule trans[OF prod.subset_diff[OF subset_UNIV univ_is_finite] mult.commute])
  have "\<forall> i\<in> (UNIV - ?A). (rev_p p) i = p i" 
    using assms p_rev_p_same' by auto
  then have 2:" prod ?h (UNIV  - ?A) =  prod ?g (UNIV - ?A)"    
    by force
  have "odd (card ?A)" 
    using assms(1-2) least_odd_support_is_odd by blast
  have "\<forall> i \<in> ?A. (tutte_matrix )$i$p i = - (tutte_matrix )$p i$(rev_p p) (p i)" 
    by (simp add: assms(1-2) rev_p_opposit_tutte_value)
  then have "\<forall> i \<in> ?A. ?h i = - (?g \<circ> (on_odd p)) i" 
    using tutte_matrix.on_odd_def tutte_matrix_axioms by fastforce
  then have 1: "prod ?h ?A = - prod (?g \<circ> (on_odd p)) ?A"
    using reverse_for_each_product[of ?A ?h ] \<open>odd (card ?A)\<close> 
    by blast
  have " prod ?g ?A =  prod (?g \<circ> (on_odd p)) ?A"
    using  Permutations.comm_monoid_mult_class.prod.permute [of "on_odd p" "?A" ?g] 
    using assms(1) on_odd_p_permutes by presburger
  then have "prod ?h ?A = -  prod ?g ?A " 
    using 1 by presburger
  then show ?thesis
    using 2 3 4 by auto
qed

lemma rev_has_same_parity:
  assumes "p permutes (UNIV::'a set)"
  shows "evenperm p = evenperm (rev_p p)"
proof -
  have 1:"permutation (on_odd p)" 
    by (simp add: assms(1) on_odd_p_permutes_UNIV p_is_permutation)
  have 2:"permutation (not_on_odd p)" 
    by (simp add: assms(1) not_on_odd_p_permutes_UNIV p_is_permutation)
  have 3:"p = on_odd  p \<circ>  not_on_odd p" 
    by (simp add: assms(1) p_is_composition)
  have 4:"(rev_p p) = (inv (on_odd  p)) \<circ>  not_on_odd p"
    using rev_is_composition assms(1) by auto
  have 5: "evenperm p \<longleftrightarrow> evenperm (on_odd  p) = evenperm (not_on_odd p)" 
  proof -
    have "evenperm (on_odd p \<circ> not_on_odd p) \<longleftrightarrow>
          (evenperm (on_odd p) = evenperm (not_on_odd p))"
      using 1 2 by (rule evenperm_comp)
    moreover have "on_odd p \<circ> not_on_odd p = p"
      using 3 by (rule sym)
    ultimately show ?thesis by simp
  qed
  have "evenperm (rev_p p) \<longleftrightarrow> evenperm (inv (on_odd  p)) = evenperm (not_on_odd p)"
    by (simp add: 1 2 4 evenperm_comp permutation_inverse)
  then show ?thesis 
    by (simp add: 5 1 evenperm_inv)
qed

lemma rev_same_sign:
  assumes "p permutes (UNIV :: 'a set)" 
  shows "of_int (sign p) = of_int (sign (rev_p p))" 
  by (simp add: assms rev_has_same_parity sign_def)

lemma rev_opposite_value:
  assumes "p permutes (UNIV :: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) " 
  shows "(\<lambda>p. of_int (sign p) * prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV) p = 
 - (\<lambda>p. of_int (sign p) *  prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV) (rev_p p)" 
    (is  " ?g  p = - ?g (rev_p p)")
proof -
  have "of_int (sign p) = of_int (sign (rev_p p))" 
    using assms(1) rev_same_sign by blast
  have " prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV =
  -  prod (\<lambda>i. (tutte_matrix)$i$(rev_p p) i) UNIV"
    using rev_product_is_minus assms   
    by blast
  then show ?thesis 
    by (simp add: \<open>of_int (sign p) = of_int (sign (rev_p p))\<close>)
qed

lemma rev_nonzero_is_nonzero:
  assumes "p \<in> nonzero_perms"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "rev_p p \<in> nonzero_perms" 
proof -
  have "p permutes UNIV" 
    using assms(1) nonzero_perms_def by auto
  have "prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV \<noteq> 0"
    using assms unfolding nonzero_perms_def by force
  then have " prod (\<lambda>i. (tutte_matrix)$i$(rev_p p) i) UNIV \<noteq> 0"
    by (simp add: assms(2) rev_product_is_minus \<open>p permutes UNIV\<close> )
  then show "rev_p p \<in> nonzero_perms" 
    unfolding nonzero_perms_def using \<open>p permutes UNIV\<close> rev_p_permutes by force
qed

lemma pow_rev_p_is_inv:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "a \<in> (set (support p  (least_odd p)))" 
  shows "((inv p)^^n) a = ((rev_p p)^^n) a"
proof (induct n)
  case (Suc n)
  let ?A = "(set (support p  (least_odd p)))"
  have "permutation p" using assms(1) 
    by (simp add: p_is_permutation)
  then have same_support: "set (support p  (least_odd p)) = set (support (inv p) (least_odd p))"
    using inv_support_same by fastforce
  then have "(inv p) a \<in> set (support (inv p) (least_odd p))" 
  proof -
    have "\<forall>n. p (inv p n) = n"
      by (meson assms(1) permutes_inverses(1))
    then show ?thesis 
      proof -
        have pperm: "permutation p"
          by (rule p_is_permutation[OF assms(1)])
        have "inv p a \<in> set (support p (least_odd p))"
          by (rule inv_in_support[OF pperm assms(2)])
        moreover have "set (support p (least_odd p)) = set (support (inv p) (least_odd p))"
          by (rule inv_support_same[OF pperm])
        ultimately show ?thesis by simp
      qed
  qed
  then have "(inv p ^^ n) a \<in> set (support (inv p)  (least_odd p))"
  proof -
    have perm: "permutation p"
      using assms(1) p_is_permutation by blast
    then have perm_inv: "permutation (inv p)"
      using permutation_inverse by blast
    have supp_eq: "set (support p (least_odd p)) = set (support (inv p) (least_odd p))"
      by (rule inv_support_same[OF perm])
    have a_in: "a \<in> set (support (inv p) (least_odd p))"
      using assms(2) supp_eq by simp
    show ?thesis
      by (rule elemnets_in_support_expo[OF perm_inv a_in refl])
  qed
  then have "(inv p ^^ n) a \<in> set (support p (least_odd p))"
    using same_support by blast
  then have "(rev_p p) ((inv p ^^ n) a) = (inv p) ((inv p ^^ n) a)"  
    using rev_p_def by presburger
  then show "(inv p ^^ Suc n) a = (rev_p p ^^ Suc n) a" 
    by (simp add: Suc.hyps)
qed simp

lemma pow_rev_p_is_same:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "a \<notin> (set (support p  (least_odd p)))" 
  shows "(p^^n) a = ((rev_p p)^^n) a"
proof (induct n)
  case (Suc n)
  let ?A = "(set (support p (least_odd p)))" 
  have "(p^^n) a \<notin>  (set (support p  (least_odd p)))" 
  proof (rule ccontr)
    assume "\<not> (p ^^ n) a \<notin> set (support p (least_odd p))"
    then have h1: "(p ^^ n) a \<in> set (support p (least_odd p))" by blast
    have h2: "permutation p" using assms(1) p_is_permutation by blast
    have h3: "(p ^^ n) a = (p ^^ n) a" by (rule refl)
    have "a \<in> set (support p (least_odd p))"
      using elemnets_in_support_expo'[OF h2 h1 h3] .
    then show False using assms(2) by blast
  qed
  then have "(rev_p p) ((p ^^ n) a) = p ((p ^^ n) a)" 
    using assms(1) p_rev_p_same' by presburger
  then show "(p ^^ Suc n) a = (rev_p p ^^ Suc n) a" 
    by (simp add: Suc.hyps)
qed simp

lemma rev_p_support_same:
  assumes "p permutes (UNIV:: 'a set)"
  shows "set (support p i) = set (support (rev_p p) i)" 
proof(safe)
  let ?A = "(set (support p  (least_odd p)))" 
  have 2: "i \<in> set (support (rev_p p) i)" 
    using el_in_own_support assms rev_p_permutes by presburger
  have "i \<in> set (support p  i)" 
    using el_in_own_support assms rev_p_permutes by presburger
  have 3: "permutation ((rev_p p))" 
    by (simp add: assms p_is_permutation rev_p_permutes) 
  have "permutation p" 
    by (simp add: assms p_is_permutation)
  { 
    fix x
    assume "x \<in> set (support p i)"
    then obtain j where j:"x = (p^^j) i \<and> j < least_power p i" 
      by fastforce
    then have "((inv p)^^j) x= i" 
  proof -
    have bij_p: "bij p" using assms permutes_imp_bij by blast
    then have inj_pj: "inj (p ^^ j)" using bij_fn bij_is_inj by blast
    have "inv (p ^^ j) x = i" using j inj_pj inv_f_f by fastforce
    then show "((inv p)^^j) x= i" using inv_fn [OF bij_p, symmetric] by simp
  qed
    have 1: "(least_power p i)-j > 0" 
      by (simp add: j)
    have "(p^^(least_power p i)) x = (p^^((least_power p i) + j)) i" 
      by (simp add: j funpow_add)
    then have "(p^^(((least_power p i)-j)+j)) x = (p^^((least_power p i)+j)) i"
      using 1 by simp
    then have "(p^^(((least_power p i)-j))) x = (p^^((least_power p i))) i"
    proof -
      have j1: "x = (p ^^ j) i" and j2: "j < least_power p i"
        using j by auto
      have j3: "j \<le> least_power p i"
        using j2 by (rule order_less_imp_le)
      have "least_power p i - j + j = least_power p i"
        using j3 by (simp add: le_add_diff_inverse2)
      moreover have "(p ^^ (least_power p i - j)) x = (p ^^ (least_power p i - j + j)) i"
        by (simp add: j1 funpow_add)
      ultimately show "(p ^^ (least_power p i - j)) x = (p ^^ least_power p i) i"
        by simp
    qed
    then have "(p^^((least_power p i)-j)) x = i" 
      by (simp add: assms least_power_of_permutation(1) p_is_permutation)
    show "x \<in>  set (support (rev_p p) i)" 
    proof(cases "x \<in> ?A")
      case True
      then have "((inv p)^^j) x = ((rev_p p)^^j) x" 
        using assms pow_rev_p_is_inv by presburger
      then have "((rev_p p)^^j) x = i" 
        using \<open>(inv p ^^ j) x = i\<close> by presburger
      then show ?thesis 
        using 2 elemnets_in_support_expo'[of "(rev_p p)" i i j x] 3 by fastforce
    next
      case False
      have "(p^^((least_power p i)-j)) x = ((rev_p p)^^((least_power p i)-j)) x" 
        using pow_rev_p_is_same[of p x "(least_power p i)-j"] False assms by blast
      then have "((rev_p p)^^((least_power p i)-j)) x = i" 
        using \<open>(p ^^ (least_power p i - j)) x = i\<close> by presburger
      then show ?thesis 
        using 2  elemnets_in_support_expo'[of "(rev_p p)" i i "(least_power p i - j)" x] 3
        by fastforce
    qed
  }
  let ?lp = "least_power (rev_p p) i" 
  fix x
  assume "x \<in>  set (support (rev_p p) i)"
  then obtain j where j_sup:"x = ((rev_p p)^^j) i \<and> j < least_power (rev_p p) i" 
    by fastforce
  have "?lp-j > 0" 
    by (simp add: j_sup)
  have "((rev_p p)^^?lp) x = ((rev_p p)^^(?lp + j)) i" 
    by (simp add:j_sup funpow_add)
  then have "((rev_p p)^^((?lp-j)+j)) x = ((rev_p p)^^(?lp+j)) i"
    using `?lp-j > 0`  
    by simp
  then have "((rev_p p)^^((?lp-j))) x = ((rev_p p)^^(?lp)) i"
  proof -
    have j_le: "j \<le> ?lp" using j_sup by linarith
    have exp_eq: "(?lp - j) + j = ?lp" using j_le by linarith
    have "((rev_p p)^^(?lp-j)) x = ((rev_p p)^^(?lp-j)) (((rev_p p)^^j) i)"
      using j_sup by simp
    also have "\<dots> = ((rev_p p)^^((?lp-j)+j)) i"
      by (simp add: funpow_add)
    also have "\<dots> = ((rev_p p)^^?lp) i"
      by (simp add: exp_eq)
    finally show ?thesis .
  qed
  then have "((rev_p p)^^(?lp-j)) x = i" 
    by (simp add: \<open>permutation (rev_p p)\<close> least_power_of_permutation(1))
  show "x \<in>  set (support p i)" 
  proof(cases "i \<in> ?A")
    case True
    then have "((inv p)^^j) i = ((rev_p p)^^j) i" 
      using assms pow_rev_p_is_inv by presburger
    then have "((inv p)^^j) i = x" 
      using j_sup by presburger
    then have "i = (p^^j) x" 
    proof -
      assume inv_fact: "(inv p ^^ j) i = x"
      have bij_p: "bij p"
        using assms permutes_imp_bij by blast
      have bij_pow: "bij (p ^^ j)"
        using bij_p by (rule bij_fn)
      have inv_pow: "inv (p ^^ j) = (inv p) ^^ j"
        using bij_p by (rule inv_fn)
      have "inv (p ^^ j) i = x"
        using inv_pow inv_fact by simp
      have id_c: "p ^^ j \<circ> inv p ^^ j = (\<lambda>x::'a. x)"
        using bij_p by (rule fn_o_inv_fn_is_id)
      have "((p ^^ j) o (inv p ^^ j)) i = i"
        using id_c by simp
      then show "i = (p ^^ j) x"
        using inv_fact by simp
    qed
    then show ?thesis using 
        `i \<in> set (support p  i)` 
        elemnets_in_support_expo'[of p i i j x] assms 
      using p_is_permutation by blast 
  next
    case False
    have "(p^^((least_power p i)-j)) i = ((rev_p p)^^((least_power p i)-j)) i" 
      using pow_rev_p_is_same[of p i "(least_power p i)-j"]
      using False assms by blast
    then have "((rev_p p)^^(?lp-j)) x = i" 
      using \<open>(rev_p p ^^ (least_power (rev_p p) i - j)) x = i\<close> by blast 
    show ?thesis
    proof -
      have i_in_supp: "i \<in> set (support p i)"
        using assms el_in_own_support by blast
      have perm_p: "permutation p"
        using assms p_is_permutation by blast
      have eq1: "(p ^^ j) i = (rev_p p ^^ j) i"
        by (rule pow_rev_p_is_same[OF assms False])
      have eq2: "(rev_p p ^^ j) i = x"
        using j_sup by simp
      have eq3: "x = (p ^^ j) i"
        using eq1 eq2 by simp
      show "x \<in> set (support p i)"
        using elemnets_in_support_expo[OF perm_p i_in_supp eq3] .
    qed
  qed
qed

lemma rev_u_edges_same:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "(u_edges p) = (u_edges (rev_p p))" 
proof(safe)
  let ?A = "(set (support p  (least_odd p)))"
  {
    fix e
    assume "e \<in> (u_edges p)"
    then obtain i where "e = {i, p i}" 
      using u_edges_def by fastforce
    show "e \<in> (u_edges (rev_p p))" 
    proof(cases "i \<in> ?A")
      case True
      then have "p i \<in> ?A" 
        by (blast intro: p_in_same_cycle assms(1))
      then have "(rev_p p) (p i) = (inv p) (p i)" 
        using rev_p_def by presburger
      then have "(rev_p p) (p i) = i " 
      proof -
        have "inv p (p i) = i"
          by (rule permutes_inverses(2)[OF assms(1)])
        with \<open>rev_p p (p i) = inv p (p i)\<close> show ?thesis
          by simp
      qed
      have "{(p i), ((rev_p p) (p i))} \<in> (u_edges (rev_p p))"  
        using tutte_matrix.u_edges_def tutte_matrix_axioms by fastforce
      then show ?thesis 
        by (simp add: \<open>e = {i, (p i)}\<close> \<open>rev_p p (p i) = i\<close> insert_commute)
    next
      case False
      then have "(rev_p p) i = p i" 
        using assms(1) p_rev_p_same' by presburger
      have "{i, ((rev_p p) i)} \<in> (u_edges (rev_p p))"  
        using tutte_matrix.u_edges_def tutte_matrix_axioms by fastforce
      then show ?thesis 
        by (simp add: \<open>e = {i, (p i)}\<close> \<open>rev_p p i = p i\<close>)
    qed
  }
  fix e
  assume "e \<in>  u_edges (rev_p p)"
  then obtain i where i: "e = {i, ((rev_p p) i)}" 
    using u_edges_def by fastforce
  show "e \<in> (u_edges p)" 
  proof(cases "i \<in> ?A")
    case True
    have "(rev_p p) i = (inv p) i"   using True rev_p_def by presburger
    have "{((inv p) i), (p ((inv p) i))} \<in> u_edges p" 
      using u_edges_def by auto
    then show ?thesis 
    proof -
      have p_inv: "p (inv p i) = i"
        using permutes_inv_eq[OF assms(1)] by blast
      have mem: "{inv p i, p (inv p i)} \<in> u_edges p"
        using u_edges_def by auto
      have e_eq: "e = {inv p i, p (inv p i)}"
        using i \<open>rev_p p i = inv p i\<close> p_inv by (simp add: insert_commute)
      show ?thesis
        using mem e_eq by simp
    qed
  next
    case False
    have "(rev_p p) i = p i" using False 
      using assms(1) p_rev_p_same' by presburger
    then show ?thesis 
      using \<open>e = {i, (rev_p p i)}\<close> u_edges_def by auto
  qed
qed

lemma least_odd_least:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  assumes "odd (least_power p a)"
  shows "(least_odd p) \<le> a" 
  unfolding least_odd_def
  using assms(3) by (rule Least_le[of _ a])

lemma rev_least_odd_same:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "least_odd p = least_odd (rev_p p)" 
proof -
  have 1: "(rev_p p) permutes  (UNIV:: 'a set)" 
    by (simp add: assms(1) rev_p_permutes)
  have 2: "\<exists>C \<in> connected_components (u_edges (rev_p p)). odd (card C)"
    using assms rev_u_edges_same by presburger
  let ?sup = "(\<lambda> p i. (set (support p i)))" 
  let ?A_rev = "(set (support (rev_p p) ((inv f) (least_odd (rev_p p)))))"
  let ?i = "(least_odd p)"
  let ?i_rev = "(least_odd (rev_p p))"
  have "odd (least_power p ?i)"  
    using assms least_odd_is_odd by presburger
  have 4:"odd (least_power (rev_p p) ?i_rev)"
    using assms least_odd_is_odd "1" "2" by blast
  have "?sup p ?i = ?sup (rev_p p) ?i" 
    using assms(1) rev_p_support_same by presburger
  then have 5: "odd (least_power (rev_p p) ?i)" 
  proof -
    have supp_eq: "set (support p (least_odd p)) = set (support (rev_p p) (least_odd p))"
      using assms(1) rev_p_support_same by presburger
    have dist_p: "distinct (support p (least_odd p))"
      using perm_support_distinct assms(1) by blast
    have dist_rev: "distinct (support (rev_p p) (least_odd p))"
      using perm_support_distinct "1" by blast
    have len_p: "length (support p (least_odd p)) = least_power p (least_odd p)"
      by simp
    have len_rev: "length (support (rev_p p) (least_odd p)) = least_power (rev_p p) (least_odd p)"
      by simp
    have card_p: "card (set (support p (least_odd p))) = least_power p (least_odd p)"
      using dist_p len_p distinct_card by fastforce
    have card_rev: "card (set (support (rev_p p) (least_odd p))) = least_power (rev_p p) (least_odd p)"
      using dist_rev len_rev distinct_card by fastforce
    have card_eq: "card (set (support p (least_odd p))) = card (set (support (rev_p p) (least_odd p)))"
      using supp_eq by simp
    have "least_power p (least_odd p) = least_power (rev_p p) (least_odd p)"
      using card_p card_rev card_eq by simp
    then show ?thesis
      using \<open>odd (least_power p (least_odd p))\<close> by simp
  qed
  have 3: "?sup p ?i_rev = ?sup (rev_p p) ?i_rev" 
    using assms(1) rev_p_support_same by presburger
  then have "odd (least_power p ?i_rev)"  
  proof -
    have f1: "\<forall>n. cycle (support p n)"
      using assms(1) perm_support_distinct by blast
    have "card (set (support p (least_odd (rev_p p)))) = 
          least_power (rev_p p) (least_odd (rev_p p))"
      using 1 3 distinct_card perm_support_distinct by force
    then show ?thesis
    proof -
      have card_eq_p: "card (set (support p (least_odd (rev_p p)))) = 
                    least_power p (least_odd (rev_p p))"
        using assms(1) distinct_card perm_support_distinct by force
      have "least_power p (least_odd (rev_p p)) = card (set (support p (least_odd (rev_p p))))"
        using card_eq_p by simp
      also have "... = least_power (rev_p p) (least_odd (rev_p p))"
        using \<open>card (set (support p (least_odd (rev_p p)))) = 
           least_power (rev_p p) (least_odd (rev_p p))\<close> by simp
      finally have "least_power p (least_odd (rev_p p)) = 
                least_power (rev_p p) (least_odd (rev_p p))" .
      then show ?thesis using 4 by simp
    qed
  qed
  then have "least_odd p \<le> least_odd (rev_p p)" 
    unfolding least_odd_def by (rule Least_le)
  have "least_odd p \<ge> least_odd (rev_p p)"  
    using 5 least_odd_def wellorder_Least_lemma(2) by fastforce
  then show ?thesis 
    using \<open>least_odd p \<le> least_odd (rev_p p)\<close> by auto
qed

lemma p_also_not_in_support:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "x \<notin> set (support p i)"
  shows "(p x) \<notin> set (support p i)" 
proof(rule ccontr)
  have "i \<in> set (support p i)" 
    using assms(1) el_in_own_support by blast 
  assume "\<not> p x \<notin> set (support p i)" 
  then have "p x \<in> set (support p i)" 
    by auto
  then have "p x \<in> set (support (inv p) i)" 
    using assms(1) inv_support_same p_is_permutation by fast
  then have "(inv p) (p x) \<in> set (support (inv p) i)" 
    using assms(1) inv_in_support inv_support_same p_is_permutation by fast
  then have "x \<in> set (support (inv p) i)" 
    using permutes_inverses(2)[OF assms(1)] by simp
  then show False 
    using assms inv_support_same p_is_permutation by fast
qed

lemma rev_rev_same:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "rev_p (rev_p p) = p" 
proof 
  fix x
  let ?A = "(set (support p (least_odd p)))" 
  let ?A' = "(set (support (rev_p p) (least_odd (rev_p p))))" 
  have "?A = ?A'" 
    using assms rev_least_odd_same rev_p_support_same by presburger
  have 1: "rev_p p = ((inv (on_odd  p)) \<circ> not_on_odd p)"
    using assms(1) rev_is_composition by auto
  then have 2:"rev_p (rev_p p) = ((inv (on_odd  (rev_p p))) \<circ> not_on_odd (rev_p p))"
    using assms(1) rev_is_composition rev_p_permutes by blast
  then have "rev_p (rev_p p) = ((inv (on_odd  ((inv (on_odd  p)) \<circ> not_on_odd p))) \<circ>  
          not_on_odd ((inv (on_odd  p)) \<circ> not_on_odd p))" 
    by (simp add: 1)
  show "(rev_p (rev_p p)) x = p x" 
  proof(cases "x \<in> ?A")
    case True
    then have "not_on_odd (rev_p p) x = x" 
      using \<open>?A = ?A'\<close> not_on_odd_out by force
    have "p x \<in> ?A" 
      using p_in_same_cycle[OF assms(1) True] by blast
    then have "(on_odd  (rev_p p)) (p x) = (inv p) (p x)"   
      unfolding on_odd_def using \<open>?A = ?A'\<close> unfolding rev_p_def by presburger 
    then have "(on_odd  (rev_p p)) (p x) = x" 
      by (simp add: permutes_inverses(2)[OF assms(1)])
    then have "inv ((on_odd  (rev_p p))) x = p x" 
      proof -
        assume prev: "on_odd (rev_p p) (p x) = x"
        have "rev_p p permutes UNIV"
          using assms(1) rev_p_permutes by blast
        then have q_perm: "on_odd (rev_p p) permutes UNIV"
          using on_odd_p_permutes_UNIV by blast
        have "inv (on_odd (rev_p p)) x = p x \<longleftrightarrow> on_odd (rev_p p) (p x) = x"
          by (rule permutes_inv_eq[OF q_perm])
        then show ?thesis
          using prev by simp
      qed
    then show "(rev_p (rev_p p)) x = p x" 
      by (simp add: \<open>not_on_odd (rev_p p) x = x\<close> 2)
  next
    case False
    then have 3: "not_on_odd (rev_p p) x = (rev_p p) x" 
      using not_on_odd_in[of x "(rev_p p)"] using \<open>?A = ?A'\<close> by blast 
    have "(rev_p p) x = p x"
      unfolding rev_p_def using False by presburger
    have "p x \<notin> ?A" 
      using False p_also_not_in_support assms(1) by presburger
    then  have "(on_odd  (rev_p p)) (p x) = (p x)" 
    proof -
      have "p x \<notin> set (support (rev_p p) (least_odd (rev_p p)))"
        using \<open>set (support p (least_odd p)) = set (support (rev_p p) (least_odd (rev_p p)))\<close>
              \<open>p x \<notin> set (support p (least_odd p))\<close>
        by blast
      then show ?thesis
        by (rule on_odd_out)
    qed
    then have "inv (on_odd  (rev_p p)) (p x) = (p x)" 
    proof -
      assume E: "on_odd (rev_p p) (p x) = p x"
      have perm: "on_odd (rev_p p) permutes UNIV"
        using assms(1) rev_p_permutes on_odd_p_permutes_UNIV by blast
      have "inv (on_odd (rev_p p)) (p x) = inv (on_odd (rev_p p)) (on_odd (rev_p p) (p x))"
        using E[symmetric] by (rule arg_cong)
      also have "inv (on_odd (rev_p p)) (on_odd (rev_p p) (p x)) = p x"
        by (rule permutes_inverses(2)[OF perm])
      finally show ?thesis .
    qed
    then show "(rev_p (rev_p p)) x = p x"  
      by (simp add: 3 2 \<open>rev_p p x = p x\<close>)
  qed
qed

lemma det_is_sum_nonzero:
  shows "det (tutte_matrix ) = sum (\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix )$i$p i) (UNIV :: 'a set)) nonzero_perms" 
proof -
  let ?g = "(\<lambda>p. of_int (sign p) *  prod (\<lambda>i. (tutte_matrix )$i$p i) (UNIV :: 'a set))" 
  have 2: "finite {p. p permutes (UNIV :: 'a set)}" 
    by simp
  then have 3:  "{p. p permutes (UNIV :: 'a set)} = {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0 } \<union>
                                                {p. p permutes (UNIV :: 'a set) \<and> ?g p = 0}"
    by auto
  have 1: "{p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0 } \<inter> 
        {p. p permutes (UNIV :: 'a set) \<and> ?g p = 0} = {}" by auto
  then have 4: "sum ?g {p. p permutes (UNIV :: 'a set)} = 
                sum ?g  {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0 } + 
                sum ?g  {p. p permutes (UNIV :: 'a set) \<and> ?g p = 0 }"
    by (simp add: 1 2 3  sum.union_disjoint)
  have "sum ?g  {p. p permutes (UNIV :: 'a set) \<and> ?g p = 0 } = 0" 
    by auto
  then have 5: "sum ?g {p. p permutes (UNIV :: 'a set)} = 
                sum ?g {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0}"  
    by (simp add: 4)
  have "det (tutte_matrix) = sum ?g {p. p permutes (UNIV :: 'a set)}" 
    using tutte_matrix_det by force
  then have 6:"det (tutte_matrix) = sum ?g {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0}"
    using 5 by presburger
  let ?A = "nonzero_perms"
  have "{p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0} = ?A" 
  proof(safe)
    {
      fix p
      assume "p permutes (UNIV:: 'a set)" 
      assume " of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix  $ i $ p i) \<noteq> 0"
      then have "(\<Prod>i\<in>UNIV. local.tutte_matrix  $ i $ p i) \<noteq> 0" by force
      then show "p \<in> nonzero_perms"
        unfolding nonzero_perms_def using \<open>p permutes UNIV\<close> by blast
    }
    {
      fix p
      assume "p \<in>  nonzero_perms"
      then show "p permutes UNIV" 
        by (simp add: nonzero_perms_def)
    }
    fix p
    assume "p \<in>  nonzero_perms" "?g p = 0"
    then have 1: "(\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) \<noteq> 0" 
      unfolding nonzero_perms_def  
      by blast
    have "of_int (sign p) \<noteq> 0" 
      by (simp add: sign_def)
    then have "(\<Prod>i\<in>UNIV. local.tutte_matrix  $ i $ p i) = 0"
      using `?g p = 0` unfolding sign_def
    proof -
      have zero: "of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) = 0"
        using `?g p = 0` by simp
      show ?thesis
      proof (cases "evenperm p")
        case True
        then have "sign p = 1"
          by (simp add: sign_def)
        with zero show ?thesis by simp
      next
        case False
        then have "sign p = - 1"
          by (simp add: sign_def)
        with zero show ?thesis by simp
      qed
    qed
    then show False 
      using 1 by blast
  qed
  then show ?thesis 
    using 6 by presburger
qed

lemma zero_det_each_has_odd_circuit:
  assumes "\<forall>p \<in> nonzero_perms. \<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "det tutte_matrix = 0"
proof -
  let ?g = "(\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix )$i$p i) (UNIV :: 'a set))" 
  let ?A = "nonzero_perms"
  let ?h = "rev_p"  
  have "finite ?A" 
    by simp
  have 1: "\<forall>a \<in> ?A.  rev_p a \<in> ?A" 
    using assms rev_nonzero_is_nonzero by blast
  have 2: "\<forall>a \<in> ?A. rev_p (rev_p a) = a" 
    by (simp add: assms nonzero_perms_def rev_rev_same)
  have 3: "\<forall>a \<in> ?A. ?g a + ?g (rev_p a) = 0"
  proof
    fix a
    assume "a \<in> ?A" 
    have "a permutes (UNIV :: 'a set)" 
      using \<open>a \<in> nonzero_perms \<close> nonzero_perms_def by auto
    have " \<exists>C \<in> connected_components (u_edges a). odd (card C)" 
      using assms by (simp add: \<open>a \<in> nonzero_perms \<close>)
    then have "?g a = - ?g (rev_p a)" 
      using rev_opposite_value[of a] \<open>a permutes UNIV\<close> by blast
    then show "?g a + ?g (rev_p a) = 0" by simp
  qed
  have 4: "\<forall>a \<in> ?A. a = (rev_p) a \<longrightarrow> ?g a = 0"
  proof
    fix a
    assume "a \<in> ?A" 
    then have a_perm:"a permutes UNIV" 
      by (simp add: nonzero_perms_def)
    show "a = (rev_p) a \<longrightarrow> ?g a = 0"
    proof
      assume "a = (rev_p) a"
      let ?i = "least_odd a"
      obtain i where i: "i = least_odd a" 
        by auto
      then  have "i \<in> set (support a (least_odd a))"
        using el_in_own_support a_perm by blast
      then have "a ((rev_p a) i) = i" 
        using a_perm p_rev_p_same by presburger
      then have "a (a i) = i" 
        using \<open>a = rev_p a\<close> by auto
      then have "(a^^2) i = i" 
      proof -
        have "(a ^^ 2) i = a (a ((a ^^ 0) i))"
          by (simp add: numeral_2_eq_2 funpow.simps o_apply)
        also have "\<dots> = a (a i)"
          by (simp add: funpow_0)
        finally have "(a ^^ 2) i = a (a i)" .
        then show ?thesis
          using \<open>a (a i) = i\<close> by simp
      qed
      then have "least_power a i \<le> 2" 
        by (simp add: least_power_le)
      have "odd (least_power a i)" 
        using \<open>a \<in> nonzero_perms\<close> a_perm i assms least_odd_is_odd by blast
      then have "(least_power a i) = 1" 
        using \<open>least_power a i \<le> 2\<close> \<open>odd (least_power a i)\<close>
proof -
  assume le: "least_power a i \<le> 2" and odd: "odd (least_power a i)"
  have "least_power a i = 0 \<or> least_power a i = 1 \<or> least_power a i = 2"
    using le by auto
  then show "least_power a i = 1"
    using odd by auto
qed
      then have "(a^^1) i = i" 
      proof -
        have perm: "permutation a"
          by (rule p_is_permutation[OF a_perm])
        have "(a ^^ least_power a i) i = i"
          by (rule least_power_of_permutation(1)[OF perm])
        then show "(a ^^ 1) i = i"
          using \<open>least_power a i = 1\<close> by simp
      qed
      then have "a i = i" 
        by simp
      show "?g a = 0" 
        using \<open>a \<in> nonzero_perms\<close> \<open>a i = i\<close> nonzero_perms_not_id by blast
    qed
  qed
  have "sum ?g ?A = 0" 
    using sum_of_values_cancel_out[of ?A rev_p ?g] `finite ?A` 1 2 3 4 
    by blast
  then show ?thesis using det_is_sum_nonzero 
    by presburger
qed

lemma no_perfect_matching_zero_det:
  assumes "\<nexists> M. perfect_matching G M"
  shows "det (tutte_matrix) = 0" 
proof(cases "\<exists> p \<in> nonzero_perms. \<forall>C \<in> connected_components (u_edges p). even (card C)")
  case True
  then obtain p where p: "p \<in> nonzero_perms \<and> 
                          (\<forall>C \<in> connected_components (u_edges p). even (card C))" 
    by auto
  then have "\<exists> M. perfect_matching (u_edges p) M"
    using even_circuits_has_perfect_matching by meson
  then obtain M where M: "perfect_matching (u_edges p) M" 
    by auto
  have "u_edges p \<subseteq> G" 
    by (simp add: p nonzero_perms_u_edges_in_graph)
  have "Vs (u_edges p) = Vs G" 
    by (meson p perm_verts_eq_all)
  then have "perfect_matching G M" 
    using M unfolding perfect_matching_def using \<open>u_edges p \<subseteq> G\<close> graph by auto
  then show ?thesis 
    using assms by auto
next
  case False
  then have "\<forall>p \<in> nonzero_perms. \<exists>C \<in> connected_components (u_edges p). odd (card C)" 
    by blast
  then show ?thesis 
    using zero_det_each_has_odd_circuit by blast
qed

definition var_sign where
  "var_sign p = (if (prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = 
                     prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV
                then 1
                else -1)" 

lemma product_is_var_product'':
  assumes "p permutes (UNIV::'a set)"
  assumes "finite A" 
  assumes "\<forall>i \<in> A. {i, p i} \<in> G" 
  shows "(prod (\<lambda>i. (tutte_matrix)$i$p i) (A::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A \<or>
     - (prod (\<lambda>i. (tutte_matrix)$i$p i) A) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A" 
  using assms(2) assms(3)
proof(induct A)
  case (insert a F)
  then show ?case 
  proof(cases "(prod (\<lambda>i. (tutte_matrix)$i$p i) F) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) F")
    case True
    have 1:"(prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) =
        (prod (\<lambda>i. (tutte_matrix)$i$p i) F) * (tutte_matrix)$a$p a)" 
      by (simp add: insert.hyps(2))
    have 2: " prod (\<lambda> i. Var\<^sub>0 ({i, p i}))  (insert a F) = 
        prod (\<lambda> i. Var\<^sub>0 ( {i, p i})) F * ( Var\<^sub>0 ( {a, p a}))" 
      by (simp add: insert.hyps(2) mult.commute)
    then show ?thesis
    proof(cases "(a, p a) \<in> oriented_edges")
      case True
      have "(tutte_matrix)$a$p a =  Var\<^sub>0  {a, p a}" 
        by (simp add: True in_oriented)
      then show ?thesis 
        proof -
          assume eq_a: "tutte_matrix $ a $ p a = Var\<^sub>0 {a, p a}"
          have F_sub: "\<forall>i\<in>F. {i, p i} \<in> G"
            using insert.prems by auto
          have F_disj: "(\<Prod>i\<in>F. tutte_matrix $ i $ p i) = (\<Prod>i\<in>F. Var\<^sub>0 {i, p i}) \<or>
                        - (\<Prod>i\<in>F. tutte_matrix $ i $ p i) = (\<Prod>i\<in>F. Var\<^sub>0 {i, p i})"
            using insert.hyps(3) F_sub by blast
          have pt: "(\<Prod>i\<in>insert a F. tutte_matrix $ i $ p i)
                      = Var\<^sub>0 {a, p a} * (\<Prod>i\<in>F. tutte_matrix $ i $ p i)"
            using insert.hyps(1) insert.hyps(2) eq_a by simp
          have pv: "(\<Prod>i\<in>insert a F. Var\<^sub>0 {i, p i})
                      = Var\<^sub>0 {a, p a} * (\<Prod>i\<in>F. Var\<^sub>0 {i, p i})"
            using insert.hyps(1) insert.hyps(2) by simp
          consider (F_pos) "(\<Prod>i\<in>F. tutte_matrix $ i $ p i) = (\<Prod>i\<in>F. Var\<^sub>0 {i, p i})"
            | (F_neg) "- (\<Prod>i\<in>F. tutte_matrix $ i $ p i) = (\<Prod>i\<in>F. Var\<^sub>0 {i, p i})"
            using F_disj by blast
          then show ?thesis
          proof cases
            case F_pos
            have "(\<Prod>i\<in>insert a F. tutte_matrix $ i $ p i)
                    = (\<Prod>i\<in>insert a F. Var\<^sub>0 {i, p i})"
              unfolding pt pv using F_pos by simp
            then show ?thesis by (rule disjI1)
          next
            case F_neg
            have F_neg': "(\<Prod>i\<in>F. tutte_matrix $ i $ p i)
                                 = - (\<Prod>i\<in>F. Var\<^sub>0 {i, p i})"
            proof -
              have "(\<Prod>i\<in>F. Var\<^sub>0 {i, p i})
                      = - (\<Prod>i\<in>F. tutte_matrix $ i $ p i)"
                using F_neg by simp
              then show ?thesis by simp
            qed
            have "- (\<Prod>i\<in>insert a F. tutte_matrix $ i $ p i)
                    = (\<Prod>i\<in>insert a F. Var\<^sub>0 {i, p i})"
              unfolding pt pv using F_neg' by simp
            then show ?thesis by (rule disjI2)
          qed
        qed
    next
      case False
      then have "(p a, a) \<in> oriented_edges"
        by (meson insert.prems insertI1 not_in_both_oriented)
      then have  "(tutte_matrix)$a$p a = -  Var\<^sub>0 ({a, p a})" 
        by (simp add: rev_in_oriented)
      then have "(prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) = 
        - prod (\<lambda> i.  Var\<^sub>0 ({i, p i}))  (insert a F))" 
        by (simp add: True 1 2)
      then show ?thesis 
        by fastforce
    qed
  next
    case False
    then have "(prod (\<lambda>i. (tutte_matrix)$i$p i) F) = - prod (\<lambda> i.  Var\<^sub>0 ({i, p i})) F"
    proof -
      have "\<forall>i\<in>F. {i, p i} \<in> G"
        using insert.prems by blast
      then have "(prod (\<lambda>i. (tutte_matrix)$i$p i) F) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) F \<or>
                 - (prod (\<lambda>i. (tutte_matrix)$i$p i) F) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) F"
        using insert.hyps(3) by blast
      with False have B: "- (prod (\<lambda>i. (tutte_matrix)$i$p i) F) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) F"
        by blast
      have "prod (\<lambda>i. (tutte_matrix)$i$p i) F = - (- (prod (\<lambda>i. (tutte_matrix)$i$p i) F))"
        by simp
      also have "\<dots> = - prod (\<lambda> i. Var\<^sub>0 ({i, p i})) F"
        using B by simp
      finally show ?thesis .
    qed
    have 1:"(prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) =
            (prod (\<lambda>i. (tutte_matrix)$i$p i) F) * (tutte_matrix)$a$p a)" 
      by (simp add: insert.hyps(2))
    have 2:"prod (\<lambda> i.  Var\<^sub>0 ({i, p i}))  (insert a F) = 
            prod (\<lambda> i.  Var\<^sub>0 ({i, p i})) F * (  Var\<^sub>0 ({a, p a}))" 
      by (simp add: insert.hyps(2) mult.commute)
    then show ?thesis
    proof(cases "(a, p a) \<in> oriented_edges")
      case True
      have "(tutte_matrix)$a$p a =  Var\<^sub>0  {a, p a}" 
        by (simp add: True in_oriented)
      then show ?thesis 
      proof -
        have eq_a: "(tutte_matrix)$a$p a = Var\<^sub>0 {a, p a}"
          by (simp add: True in_oriented)
        have F_sub: "\<forall>i\<in>F. {i, p i} \<in> G"
          using insert.prems by auto
        have F_disj: "prod (\<lambda>i. (tutte_matrix)$i$p i) F = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) F \<or>
                      - prod (\<lambda>i. (tutte_matrix)$i$p i) F = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) F"
          using insert.hyps(3) F_sub by blast
        consider (F_pos) "prod (\<lambda>i. (tutte_matrix)$i$p i) F = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) F"
               | (F_neg) "- prod (\<lambda>i. (tutte_matrix)$i$p i) F = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) F"
          using F_disj by blast
        then show ?thesis
        proof cases
          case F_pos
          have "prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) F * (tutte_matrix)$a$p a"
            using "1" F_pos by simp
          also have "... = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) F * Var\<^sub>0 {a, p a}"
            using eq_a by simp
          also have "... = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) (insert a F)"
            by (simp add: "2")
          finally show ?thesis by (rule disjI1)
        next
          case F_neg
          have "- prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F)
                = - (prod (\<lambda>i. (tutte_matrix)$i$p i) F * (tutte_matrix)$a$p a)"
            using "1" by simp
          also have "... = - (prod (\<lambda>i. (tutte_matrix)$i$p i) F * Var\<^sub>0 {a, p a})"
            using eq_a by simp
          also have "... = (- prod (\<lambda>i. (tutte_matrix)$i$p i) F) * Var\<^sub>0 {a, p a}"
            by (simp add: mult_minus_left)
          also have "... = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) F * Var\<^sub>0 {a, p a}"
            using F_neg by simp
          also have "... = prod (\<lambda>i. Var\<^sub>0 ({i, p i})) (insert a F)"
            by (simp add: "2")
          finally show ?thesis by (rule disjI2)
        qed
      qed
    next
      case False
      then have "(p a, a) \<in> oriented_edges"
        by (meson insert.prems insertI1 not_in_both_oriented)
      then have  "(tutte_matrix)$a$p a = -  Var\<^sub>0 ({a, p a})" 
        by (simp add: rev_in_oriented)
      then have "(prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) = 
         prod (\<lambda> i.  Var\<^sub>0 ({i, p i}))  (insert a F))" 
        by (simp add: "1" "2" \<open>(\<Prod>i\<in>F. local.tutte_matrix $ i $ p i) = - (\<Prod>i\<in>F. Var\<^sub>0 {i, p i})\<close>)
      then show ?thesis 
        by fastforce
    qed
  qed
qed auto

(* TODO: 
 clean it out by introduction of new function.*)
lemma product_is_var_product:
  assumes "p \<in> nonzero_perms"
  assumes "finite A" 
  shows "(prod (\<lambda>i. (tutte_matrix)$i$p i) (A::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A
    \<or> - (prod (\<lambda>i. (tutte_matrix)$i$p i) A) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A" 
proof -
  have "\<forall>i. {i, p i} \<in> G" 
    using nonzero_edge_in_graph assms(1) by blast
  then show ?thesis 
    using product_is_var_product''[of p A] assms nonzero_perms_elim(1) by blast
qed

lemma product_is_var_product_sign:
  assumes "p \<in> nonzero_perms"
  shows "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = 
          var_sign p * prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV" 
proof(cases "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV")
  case True
  have "var_sign p = 1" 
    by (meson True var_sign_def)
  then show ?thesis 
    by (simp add: \<open>var_sign p = 1\<close> True)
next
  case False
  have "var_sign p = -1"
    by (meson False var_sign_def)
  have "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = - prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV"
  proof -
    have disj: "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV \<or>
        - (prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV"
      using product_is_var_product[OF assms finite_class.finite_UNIV] .
    show ?thesis
      using disj False
    proof (elim disjE)
      assume "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV"
      then show ?thesis
        using False by simp
    next
      assume "- (prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV"
      then have "- (- (prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set))) = - prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV"
        by (rule arg_cong)
      then show ?thesis
        by simp
    qed
  qed
  then show ?thesis 
    by (simp add: \<open>var_sign p = - 1\<close>)
qed

lemma product_Var_mapping:
  assumes "p permutes (UNIV:: 'a set)" 
  assumes "finite A" 
  shows "prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A = 
         Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) A) (1::real)" 
  using assms(2)
proof(induct A)
  case (insert x F)
  have 1: "prod (\<lambda> i. Var\<^sub>0 ({i, p i})) (insert x F) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) F * Var\<^sub>0 {x, p x}" 
    by (simp add: insert.hyps(2) mult.commute)
  have 2: "Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) (insert x F)) 1 =
           Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F + 
          Poly_Mapping.single {x, p x} 1) 1" 
    by (simp add: add.commute insert.hyps(2))
  have "(Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F) 1) *
         Poly_Mapping.single (Poly_Mapping.single {x, p x} 1) 1 = 
         Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F +
         Poly_Mapping.single {x, p x} 1) (1::real)"
    by (simp add: mult_single[of _ 1 _ 1])
  then have "Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) (insert x F)) (1::real) 
             = 
            (Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F) 1) * Var\<^sub>0 {x, p x}" 
    unfolding Var\<^sub>0_def by (simp add: 2 mult_single insert.hyps(2) sum.insert add.commute)
  then show ?case
    by (simp add:1 insert.hyps(3))
qed simp

lemma all_edges_in_E_prod_nonzero:
  assumes "p permutes (UNIV::'a set)"
  assumes "\<forall>i. {i, p i} \<in> G" 
  shows "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) \<noteq> 0"
proof -
  have "finite (UNIV::'a set)" by simp
  have 1:"prod (\<lambda> i. Var\<^sub>0 ({i, p i})) (UNIV::'a set) = 
         Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) 
                              (UNIV::'a set)) (1::real)" 
    using product_Var_mapping[of p UNIV] assms `finite (UNIV::'a set)`  by blast
  then have "Poly_Mapping.lookup (Poly_Mapping.single 
            (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real))
            (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) \<noteq> 0" 
    by simp
  then have "Poly_Mapping.single 
            (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real) \<noteq> 0" 
  proof -
    assume lookup_neq: "Poly_Mapping.lookup (Poly_Mapping.single 
              (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real))
              (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) \<noteq> 0"
    show "Poly_Mapping.single 
              (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real) \<noteq> 0"
    proof
      assume "Poly_Mapping.single 
              (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real) = 0"
      then have "Poly_Mapping.lookup (Poly_Mapping.single 
                  (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real))
                  (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) = 0"
        by (simp add: lookup_zero)
      with lookup_neq show False by simp
    qed
  qed
  then have "prod (\<lambda> i. Var\<^sub>0 ({i, p i}) ::(_\<Rightarrow>\<^sub>0 real)) (UNIV::'a set) \<noteq> 0" 
    using 1 by presburger
  have "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV \<or>
         - (prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV" 
    using product_is_var_product''[of p UNIV]  assms finite_class.finite_UNIV by blast
  then show ?thesis 
    using \<open>(\<Prod>i\<in>UNIV. Var\<^sub>0 {i, p i}) \<noteq> 0\<close> by force
qed

(* we need the g sign function *)
lemma unique_single_sum:
  assumes "finite A"
  assumes "a \<in> A"
  assumes "\<forall>a' \<in> A - {a}.  f a  \<noteq> f a'" 
  assumes "\<forall>a' \<in> A. g a' \<in> {1::int, -1}"
  shows "Poly_Mapping.lookup (sum (\<lambda> b. of_int (sign b) * of_int (g b) *
      (Poly_Mapping.single (f b) (1::real))) A) (f a) \<noteq> 0" 
  using assms
proof(induct A)
  case (insert x F)
  let ?m = "(\<lambda> b. of_int (sign b) * of_int(g b) * (Poly_Mapping.single (f b) (1::real)))" 
  have 1: "\<forall>a'\<in>F - {a}. f a \<noteq> f a'" 
    by (meson DiffD1 DiffD2 DiffI insert.prems(2) subsetD subset_insertI)
  then show ?case
  proof(cases "a =x")
    case True
    have "a \<notin> F" 
      by (simp add: True insert.hyps(2))
    have 2: "\<forall>a'\<in>F. g a' \<in> {1::int, - 1}" 
      using insert.prems(3) by blast 
    have "finite F" 
      by (simp add: insert.hyps(1))
    then have 4: "poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a) = 0" 
      using  `a \<notin> F` 1 2
    proof(induct F)
      case (insert t T)
      have "a \<notin> T" 
        using insert.prems by auto
      have 3: "poly_mapping.lookup (\<Sum>b\<in>(insert t T). ?m b) (f a) = 
            poly_mapping.lookup (\<Sum>b\<in>T. ?m b) (f a) +
      poly_mapping.lookup (?m t) (f a)" 
      proof -
        have "(\<Sum>b\<in>insert t T. ?m b) = ?m t + (\<Sum>b\<in>T. ?m b)"
          by (simp add: sum.insert insert.hyps(1) insert.hyps(2))
        then show ?thesis
          by (simp add: lookup_add add.commute)
      qed
      have "a \<noteq> t" 
        using insert.prems by auto
      have "\<forall>a'\<in>T - {a}. f a \<noteq> f a'" 
        by (simp add: insert.prems(2))
      then have "f a \<noteq> f t" 
        using insert.prems(1-2) by force
      then have "poly_mapping.lookup (?m t) (f a) = 0" 
      proof -
        have e1: "of_int (sign t) = Poly_Mapping.single 0 (of_int (sign t) :: real)"
          by (simp add: single_of_int)
        have e2: "of_int (g t) = Poly_Mapping.single 0 (of_int (g t) :: real)"
          by (simp add: single_of_int)
        have s2: "(Poly_Mapping.single 0 (of_int (sign t)) * Poly_Mapping.single 0 (of_int (g t)))
                   * Poly_Mapping.single (f t) (1::real)
                 = of_int (sign t) * of_int (g t) * Poly_Mapping.single (f t) (1::real)"
          by (simp add: single_of_int)
        have s3: "(Poly_Mapping.single 0 (of_int (sign t)) * Poly_Mapping.single 0 (of_int (g t)))
                   * Poly_Mapping.single (f t) (1::real)
                 = Poly_Mapping.single (0 + 0 + f t) (of_int (sign t) * of_int (g t) * 1)"
          by (simp only: mult_single)
        then have s4: "(Poly_Mapping.single 0 (of_int (sign t)) * Poly_Mapping.single 0 (of_int (g t)))
                   * Poly_Mapping.single (f t) (1::real)
                 = Poly_Mapping.single (f t) (of_int (sign t) * of_int (g t))"
          by simp
        have mp: "of_int (sign t) * of_int (g t) * Poly_Mapping.single (f t) (1::real)
                 = Poly_Mapping.single (f t) (of_int (sign t) * of_int (g t))"
          by (rule trans [OF s2 [symmetric] s4])
        then show ?thesis
          using \<open>f a \<noteq> f t\<close> by (simp add: lookup_single_not_eq)
      qed
      then have "poly_mapping.lookup (\<Sum>b\<in>(insert t T). ?m b) (f a) =  
                 poly_mapping.lookup (\<Sum>b\<in>T. ?m b) (f a)"
        using 3 by linarith
      then show ?case 
        using \<open>\<forall>a'\<in>T - {a}. f a \<noteq> f a'\<close> \<open>a \<notin> T\<close> using insert.hyps(3) insert.prems(3) by force
    qed auto
    have "(\<Sum>b\<in>(insert x F). ?m b) = (\<Sum>b\<in>F. ?m b) + ?m x" 
      by (simp add: insert.hyps(1-2))
    then have "poly_mapping.lookup (\<Sum>b\<in>(insert x F). ?m b) (f a) =  
               poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a) + poly_mapping.lookup (?m x) (f a)" 
      by (simp add: lookup_add)
    then have 5: "poly_mapping.lookup (\<Sum>b\<in>(insert x F). ?m b) (f a) = 
                  poly_mapping.lookup (?m x) (f a)" 
      using 4 by linarith
    have "poly_mapping.lookup (Poly_Mapping.single (f a) (int 1)) (f a) \<noteq> 0"
      by simp
    have "g a \<in> {1::int, -1}" using assms(2) assms(4) 
      by auto
    then have "poly_mapping.lookup (of_int (sign a) * of_int (g a) * 
              (Poly_Mapping.single (f a) (int 1))) (f a) \<noteq> 0"
    proof -
  have g_ne: "g a \<noteq> (0::int)"
    using assms(2) assms(4) by auto
  have sign_ne: "of_int (sign a) \<noteq> (0::real)"
    by (simp add: sign_def)
  have g_ne': "of_int (g a) \<noteq> (0::real)"
    using g_ne by simp
  have sign_ne_i: "of_int (sign a) \<noteq> (0::int)"
    by (simp add: sign_def)
  have e1: "of_int (sign a) = Poly_Mapping.single 0 (of_int (sign a) :: int)"
    by (simp only: single_of_int)
  have e2: "of_int (g a) = Poly_Mapping.single 0 (of_int (g a) :: int)"
    by (simp only: single_of_int)
  have s2: "(Poly_Mapping.single 0 (of_int (sign a) :: int) * Poly_Mapping.single 0 (of_int (g a) :: int))
             * Poly_Mapping.single (f a) (1::int)
           = of_int (sign a) * of_int (g a) * Poly_Mapping.single (f a) (1::int)"
    by (simp only: single_of_int)
  have s3: "(Poly_Mapping.single 0 (of_int (sign a) :: int) * Poly_Mapping.single 0 (of_int (g a) :: int))
             * Poly_Mapping.single (f a) (1::int)
           = Poly_Mapping.single (0 + 0 + f a) (of_int (sign a) * of_int (g a) * 1)"
    by (simp only: mult_single)
  then have s4: "(Poly_Mapping.single 0 (of_int (sign a) :: int) * Poly_Mapping.single 0 (of_int (g a) :: int))
             * Poly_Mapping.single (f a) (1::int)
           = Poly_Mapping.single (f a) (of_int (sign a) * of_int (g a))"
    by simp
  have mp: "of_int (sign a) * of_int (g a) * Poly_Mapping.single (f a) (1::int)
           = Poly_Mapping.single (f a) (of_int (sign a) * of_int (g a))"
    by (rule trans [OF s2 [symmetric] s4])
  show ?thesis
    using mp g_ne sign_ne_i by (simp add: lookup_single_eq)
qed
    then  have "poly_mapping.lookup (?m x) (f a) \<noteq> 0" 
      using True 
      proof -
        have gx: "g x \<in> {1::int, - 1}"
          using True insert.prems by auto
        have sx: "sign x \<in> {1::int, - 1}"
          by (simp add: sign_def)
        have key: "?m x = Poly_Mapping.single (f x) (of_int (sign x) * of_int (g x) :: real)"
        proof -
          have "?m x = (Poly_Mapping.single 0 (of_int (sign x) :: real)
                          * Poly_Mapping.single 0 (of_int (g x) :: real))
                       * Poly_Mapping.single (f x) (1::real)"
            by (simp add: single_of_int)
          also have "\<dots> = Poly_Mapping.single (0 + 0) (of_int (sign x) * of_int (g x) :: real)
                       * Poly_Mapping.single (f x) (1::real)"
            by (simp add: mult_single del: single_of_int)
          also have "\<dots> = Poly_Mapping.single (0 + 0 + f x)
                            (of_int (sign x) * of_int (g x) * 1 :: real)"
            by (simp add: mult_single del: single_of_int)
          finally show ?thesis by simp
        qed
        have lk: "poly_mapping.lookup (?m x) (f x)
                    = (of_int (sign x) * of_int (g x) :: real)"
          by (simp add: key lookup_single_eq)
        have nz: "(of_int (sign x) * of_int (g x) :: real) \<noteq> 0"
        proof -
          have s0: "sign x \<noteq> (0::int)" using sx by auto
          have g0: "g x \<noteq> (0::int)" using gx by auto
          show ?thesis using s0 g0 by simp
        qed
        have "poly_mapping.lookup (?m x) (f a) = poly_mapping.lookup (?m x) (f x)"
          using True by simp
        then show ?thesis using lk nz by simp
      qed
    then show ?thesis 
      using 5 by presburger
  next 
    case False
    then have "a \<in> F" 
      using insert.prems(1) by auto
    then have 7: "poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a) \<noteq> 0" 
      using insert.hyps 1 insert.prems(3) by blast
    have "(f x ) \<noteq> (f a )" 
      proof -
      have "x \<in> insert x F - {a}"
        using False by simp
      then have "f a \<noteq> f x"
        using insert.prems(2) by blast
      then show ?thesis
        by simp
    qed
    have "(\<Sum>b\<in>(insert x F). ?m b) =  (\<Sum>b\<in>F. ?m b) +  ?m x" 
      by (simp add: insert.hyps(1) insert.hyps(2))
    then have 6: "poly_mapping.lookup (\<Sum>b\<in>(insert x F). ?m b) (f a) = 
                  poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a) + poly_mapping.lookup (?m x) (f a)" 
      by (simp add: lookup_add)
    have " poly_mapping.lookup (?m x) (f a) = 0"
    proof -
      have scalar: "of_int (sign x) * of_int (g x)
          = Poly_Mapping.single 0 (of_int (sign x) * of_int (g x))"
      proof -
        have "of_int (sign x) * of_int (g x)
            = Poly_Mapping.single 0 (of_int (sign x)) * Poly_Mapping.single 0 (of_int (g x))"
          by (simp add: single_of_int)
        also have "\<dots> = Poly_Mapping.single (0 + 0) (of_int (sign x) * of_int (g x))"
          by (rule mult_single)
        then show ?thesis by simp
      qed
      have key: "of_int (sign x) * of_int (g x) * (Poly_Mapping.single (f x) (1::real))
          = Poly_Mapping.single (f x) (of_int (sign x) * of_int (g x))"
      proof -
        have "of_int (sign x) * of_int (g x) * (Poly_Mapping.single (f x) (1::real))
            = Poly_Mapping.single 0 (of_int (sign x) * of_int (g x))
              * Poly_Mapping.single (f x) (1::real)"
          by (simp add: scalar)
        also have "\<dots> = Poly_Mapping.single (0 + f x) (of_int (sign x) * of_int (g x) * 1)"
          by (simp add: mult_single)
        finally show ?thesis by simp
      qed
      show "poly_mapping.lookup (?m x) (f a) = 0"
        using \<open>f x \<noteq> f a\<close> by (simp add: key lookup_single_not_eq)
    qed
    then have "poly_mapping.lookup (\<Sum>b\<in>(insert x F). ?m b) (f a) = 
               poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a)"
      by (simp add: 6)
    then show ?thesis 
      using 7 by presburger
  qed
qed auto

lemma el_in_sum_is_nonzero:
  assumes "finite A"
  assumes "a \<in> A"
  shows "Poly_Mapping.lookup (sum (\<lambda> b. (Poly_Mapping.single (f b) (1::nat))) A) (f a) \<noteq> 0" 
  using assms
proof -
  have lookup_eq: "Poly_Mapping.lookup (sum (\<lambda>b. Poly_Mapping.single (f b) (1::nat)) A) (f a) =
        (\<Sum>b\<in>A. Poly_Mapping.lookup (Poly_Mapping.single (f b) (1::nat)) (f a))"
    by (simp add: lookup_sum)
  have term_a: "Poly_Mapping.lookup (Poly_Mapping.single (f a) (1::nat)) (f a) = 1"
    by (simp add: lookup_single_eq)
  have "(\<Sum>b\<in>A. Poly_Mapping.lookup (Poly_Mapping.single (f b) (1::nat)) (f a)) \<noteq> 0"
  proof (rule notI)
    assume "(\<Sum>b\<in>A. Poly_Mapping.lookup (Poly_Mapping.single (f b) (1::nat)) (f a)) = 0"
    with assms(1) have "\<forall>b\<in>A. Poly_Mapping.lookup (Poly_Mapping.single (f b) (1::nat)) (f a) = 0"
      by (simp add: sum_eq_0_iff)
    with assms(2) have "Poly_Mapping.lookup (Poly_Mapping.single (f a) (1::nat)) (f a) = 0"
      by blast
    with term_a show False
      by linarith
  qed
  then show ?thesis
    using lookup_eq by simp
qed

lemma monom_is_nonzero_for_unique_p:
  assumes "p \<in> nonzero_perms" 
  assumes "\<forall> p' \<in> nonzero_perms - {p}.  
           (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) \<noteq> 
           (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat))"
  shows "Poly_Mapping.lookup (det tutte_matrix) 
        (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV:: 'a set)) \<noteq> 0"   
proof -
  have "p \<in> nonzero_perms" 
    by (simp add: all_perms_def assms(1))
  have "finite nonzero_perms" 
    by simp
  let ?f = "(\<lambda> p'. (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat)))"
  have "\<forall>a' \<in> nonzero_perms - {p}.  ?f p  \<noteq> ?f a'" 
    using assms(2) by blast
  then have 1:"Poly_Mapping.lookup (sum (\<lambda> b. of_int (sign b) * (var_sign b) *
          (Poly_Mapping.single (?f b) (1::real))) nonzero_perms) (?f p) \<noteq> 0" 
    using unique_single_sum[of nonzero_perms p ?f var_sign] 
      \<open>finite nonzero_perms\<close> \<open>p \<in> nonzero_perms\<close> 
    unfolding var_sign_def 
    by (smt (verit) insert_iff of_int_1 of_int_minus sum.cong)
  have "\<forall>b \<in> nonzero_perms. (var_sign b)* (Poly_Mapping.single (?f b) (1::real)) =  
                             var_sign b * prod (\<lambda> i. Var\<^sub>0 ({i, b i})) UNIV" 
    by (simp add: nonzero_perms_def product_Var_mapping)
  then have " \<forall>b \<in> nonzero_perms. (var_sign b)*  (Poly_Mapping.single (?f b) (1::real)) = 
                                  (prod (\<lambda>i. (tutte_matrix)$i$b i) (UNIV::'a set))"
    using product_is_var_product_sign by simp
  then have "(sum (\<lambda> b. of_int (sign b) * 
             (prod (\<lambda>i. (tutte_matrix)$i$b i) (UNIV::'a set))) nonzero_perms) =
             (sum (\<lambda> b. of_int (sign b) * (var_sign b) *
             (Poly_Mapping.single (?f b) (1::nat))) nonzero_perms)"
  proof -
    assume eq: "\<forall>b \<in> nonzero_perms. (var_sign b)*  (Poly_Mapping.single (?f b) (1::real)) = 
                                  (prod (\<lambda>i. (tutte_matrix)$i$b i) (UNIV::'a set))"
    show ?thesis
    proof (intro sum.cong refl)
      fix b
      assume "b \<in> nonzero_perms"
      then have "var_sign b * (Poly_Mapping.single (?f b) 1) =
                 prod (\<lambda> i. tutte_matrix $ i $ b i) (UNIV::'a set)"
        using eq by blast
      then show "of_int (sign b) * (prod (\<lambda>i. (tutte_matrix)$i$b i) (UNIV::'a set)) =
                 of_int (sign b) * (var_sign b) * (Poly_Mapping.single (?f b) (1::nat))"
        by (simp add: algebra_simps)
    qed
  qed
  then have 1:"Poly_Mapping.lookup (sum (\<lambda> b. of_int (sign b) * 
            (prod (\<lambda>i. (tutte_matrix)$i$b i) (UNIV::'a set))) nonzero_perms) (?f p) \<noteq> 0"
    using 1 by force
  have "det tutte_matrix =
        sum (\<lambda>p. of_int (sign p) * prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set)) nonzero_perms" 
    using det_is_sum_nonzero by blast
  then show "Poly_Mapping.lookup (det tutte_matrix) (?f p) \<noteq> 0"
    using 1 by presburger
qed

lemma u_edges_unique_poly_map:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "p' permutes (UNIV:: 'a set)"
  assumes "u_edges p \<noteq> u_edges p'"
  shows " (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) \<noteq> 
    (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat))" 
proof -

  show ?thesis
  proof(cases "u_edges p - u_edges p' \<noteq> {}")
    case True
    obtain e where e: "e \<in> u_edges p - u_edges p'" 
      using True by blast
    then obtain a where a: "e = {a, p a} \<and> a \<in> (UNIV:: 'a set)" 
      using u_edges_def by auto
    have "e \<notin> u_edges p'" 
      using e by auto
    have 1:"Poly_Mapping.lookup (\<Sum>i\<in>UNIV. Poly_Mapping.single {i, p i} (1::nat)) e \<noteq> 0" 
      using el_in_sum_is_nonzero[of UNIV a "\<lambda> j. {j, p j}"] 
            a finite_class.finite_UNIV by blast 
    have "Poly_Mapping.lookup (\<Sum>i\<in>UNIV. Poly_Mapping.single {i, p' i} (1::nat)) e = 0"
      proof -
        have "\<And>i. i \<in> (UNIV::'a set) \<Longrightarrow> 
              Poly_Mapping.lookup (Poly_Mapping.single {i, p' i} (1::nat)) e = 0"
        proof -
          fix i :: 'a
          assume "i \<in> (UNIV::'a set)"
          have "{i, p' i} \<noteq> e" 
            using \<open>e \<notin> u_edges p'\<close> unfolding u_edges_def by blast
          then show "Poly_Mapping.lookup (Poly_Mapping.single {i, p' i} (1::nat)) e = 0"
            by (simp add: lookup_single_not_eq)
        qed
        then have "(\<Sum>i\<in>(UNIV::'a set). 
              Poly_Mapping.lookup (Poly_Mapping.single {i, p' i} (1::nat)) e) = 0"
          by (auto intro: sum.neutral)
        then show ?thesis
          by (simp add: lookup_sum)
      qed
    then show ?thesis 
      using 1 by fastforce
  next
    case False
    have "u_edges p' - u_edges p \<noteq> {}" 
      using False assms(3) by blast
    then obtain e where e: "e \<in> u_edges p'- u_edges p" 
      by blast
    then obtain a where a: "e = {a, p' a} \<and> a \<in> (UNIV:: 'a set)" 
      using u_edges_def by auto
    have "e \<notin> u_edges p" 
      using e by auto
    have 1: "Poly_Mapping.lookup (\<Sum>i\<in>UNIV. Poly_Mapping.single {i, p' i} (1::nat)) e \<noteq> 0" 
      using el_in_sum_is_nonzero[of UNIV a "\<lambda> j. {j, p' j}"] 
            a finite_class.finite_UNIV by blast 
    have "Poly_Mapping.lookup (\<Sum>i\<in>UNIV. Poly_Mapping.single {i, p i} (1::nat)) e = 0" 
    proof -
      have "\<And>i. {i, p i} \<noteq> e"
      proof -
        fix i
        show "{i, p i} \<noteq> e"
        proof
          assume "{i, p i} = e"
          then have "e \<in> u_edges p"
            unfolding u_edges_def by blast
          then show False
            using \<open>e \<notin> u_edges p\<close> by blast
        qed
      qed
      then have "\<And>i. Poly_Mapping.lookup (Poly_Mapping.single {i, p i} (1::nat)) e = 0"
        by (simp add: lookup_single_not_eq)
      then show ?thesis
        by (simp add: lookup_sum)
    qed
    then show ?thesis 
      using 1 by fastforce
  qed
qed

lemma monom_is_nonzero_for_unique_edges:
  assumes "p \<in> nonzero_perms" 
  assumes "\<forall> p' \<in> nonzero_perms - {p}.   u_edges p \<noteq> u_edges p'"
  shows "det tutte_matrix  \<noteq> 0"
proof -
  have "p permutes (UNIV::'a set)" using assms(1) 
    using nonzero_perms_def by auto
  have "\<forall> p' \<in> nonzero_perms - {p}.  
       (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) \<noteq> 
       (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat))"
  proof
    fix p'
    assume "p' \<in> nonzero_perms - {p}" 
    then have "p' permutes UNIV" 
      by (simp add: nonzero_perms_def)
    have "u_edges p \<noteq> u_edges p'" 
      using \<open>p' \<in> nonzero_perms - {p}\<close> assms(2) by blast
    then show "(\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) \<noteq> 
              (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat))" 
      using \<open>p permutes UNIV\<close> \<open>p' permutes UNIV\<close> u_edges_unique_poly_map by presburger
  qed
  then have "Poly_Mapping.lookup (det tutte_matrix) 
            (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV:: 'a set)) \<noteq> 0" 
    using assms(1) monom_is_nonzero_for_unique_p by blast
  then show ?thesis 
    by fastforce
qed

lemma u_edges_nonzero_perms:
  assumes "p permutes (UNIV::'a set)"
  assumes "u_edges p \<subseteq> G"
  shows "p \<in> nonzero_perms" 
proof -
  have "\<forall>i. {i, (p i)} \<in> G" 
    using assms(2) unfolding u_edges_def
    by blast
  then have "\<forall>i. (i, (p i)) \<in> oriented_edges \<or> ((p i), i) \<in> oriented_edges"
    using not_in_both_oriented by blast
  then have "prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV \<noteq> 0" 
    using all_edges_in_E_prod_nonzero[of p] \<open>\<forall>i. {i, p i} \<in> G\<close> assms(1) by fastforce
  then show "p \<in> nonzero_perms" 
    unfolding nonzero_perms_def using assms(1) by blast
qed

lemma perfect_matching_nonzero_det:
  assumes "\<exists> M. perfect_matching G M" "graph_invar G"
  shows "det (tutte_matrix) \<noteq> 0"
proof -
  obtain M where M:"perfect_matching G M" 
    using assms by blast
  then have M_match: "matching M" 
    using perfect_matching_def by blast
  have "Vs M = UNIV" 
  proof -
    have MG: "Vs M = Vs G"
      using \<open>perfect_matching G M\<close>
      unfolding perfect_matching_def by simp
    have GU: "Vs G = (UNIV :: 'a set)"
      by (rule univ[symmetric])
    show ?thesis
      by (rule trans[OF MG GU])
  qed
  have "graph_invar M" 
    by (meson M graph_invar_subset perfect_matchingE assms(2))
  let ?singletons = "(\<lambda> i. {e - {i}| e. e \<in> M \<and> i \<in> e})" 
  have "\<forall> i \<in> Vs M. is_singleton (?singletons i)"
  proof
    fix i
    assume asmi: "i \<in> Vs M" 
    have 1:"\<exists>!e.  e \<in> M \<and> i \<in> e" 
      using M_match asmi unfolding matching_def2 by blast
    then obtain e where e:"e \<in> M \<and> i \<in> e" 
      by auto
    then have "{e . e \<in> M \<and> i \<in> e} =  {e}" 
      using 1 by blast
    then have " (?singletons i) = {e - {i}}" 
      by blast
    then show "is_singleton (?singletons i)" 
      by simp
  qed
  then have 2: "\<forall> i. is_singleton (?singletons i)" 
    by (simp add: \<open>Vs M = UNIV\<close>)
  have "\<forall> i \<in> Vs M. is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})" 
  proof
    fix i
    assume asmi: "i \<in> Vs M" 
    have 1: "\<exists>!e. e \<in> M \<and> i \<in> e" 
      using M_match asmi unfolding matching_def2 by blast
    then obtain e where e: "e \<in> M \<and> i \<in> e" 
      by auto
    then have "{e . e \<in> M \<and> i \<in> e} =  {e}" 
      using 1 by blast
    then have 2:"{e - {i} |e. e \<in> M \<and> i \<in> e} = {e - {i}}" 
      by blast
    then obtain j where j: "e = {i, j}" 
      using `graph_invar M` e
      by blast
    then have "{e - {i} |e. e \<in> M \<and> i \<in> e} = {{j}}" 
      using e \<open>graph_invar M\<close> 2 doubleton_eq_iff singletonD by force
    then show "is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})" 
      by simp
  qed
  then have 1: "\<forall> i. is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})" 
    by (simp add: \<open>Vs M = UNIV\<close>)

  let ?f = "\<lambda> i. the_elem (\<Union> (?singletons i))"
  have "?f permutes (UNIV::'a set)" 
  proof -
    have "bij_betw ?f UNIV UNIV"
      unfolding bij_betw_def
    proof
      show "inj_on ?f UNIV" 
      proof
        fix x y
        assume asm: "x \<in> (UNIV::'a set)" " y \<in> (UNIV::'a set)" "?f x = ?f y"
        then obtain a where a:"?f x = a" 
          by blast
        have "is_singleton (\<Union>{e - {x} |e. e \<in> M \<and> x \<in> e})" 
          using 1 by blast
        then have 3: "\<Union>{e - {x} |e. e \<in> M \<and> x \<in> e} = {a}"
          using 1 a by (simp add: is_singleton_the_elem)
        have "is_singleton {e - {x} |e. e \<in> M \<and> x \<in> e}" 
          using 2 by auto
        then have "{a} \<in> {e - {x} |e. e \<in> M \<and> x \<in> e}" 
          proof -
            from 2 have s: "is_singleton {e - {x} |e. e \<in> M \<and> x \<in> e}" by auto
            then have eq: "{e - {x} |e. e \<in> M \<and> x \<in> e} = {the_elem {e - {x} |e. e \<in> M \<and> x \<in> e}}"
              by (simp add: is_singleton_the_elem)
            from eq 3 have "\<Union> {the_elem {e - {x} |e. e \<in> M \<and> x \<in> e}} = {a}"
              by (rule subst)
            then have u: "the_elem {e - {x} |e. e \<in> M \<and> x \<in> e} = {a}"
              by simp
            from u eq have "{e - {x} |e. e \<in> M \<and> x \<in> e} = {{a}}"
              by (rule subst)
            then show "{a} \<in> {e - {x} |e. e \<in> M \<and> x \<in> e}"
              by simp
          qed
        then have "{x, a} \<in> M" 
          using  insert_Diff by force
        have "is_singleton (\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e})" 
          using 1 by blast
        then have 4:"\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e} = {a}" 
        proof -
          have "is_singleton (\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e})"
            using 1 by blast
          then have singleton_eq: "\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e} =
                     {the_elem (\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e})}"
            by (simp add: is_singleton_the_elem)
          have "the_elem (\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e}) =
                the_elem (\<Union>{e - {x} |e. e \<in> M \<and> x \<in> e})"
            using asm(3) by simp
          also have "\<dots> = a"
            using a by simp
          finally show "\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e} = {a}"
            using singleton_eq by simp
        qed
        have "is_singleton {e - {y} |e. e \<in> M \<and> y \<in> e}" 
          using 2 by auto
        then have "{a} \<in> {e - {y} |e. e \<in> M \<and> y \<in> e}" 
        proof -
          let ?S = "{e - {y} |e. e \<in> M \<and> y \<in> e}"
          have "is_singleton ?S"
            using 2 by auto
          then have S_eq: "?S = {the_elem ?S}"
            by (rule is_singleton_the_elem[THEN iffD1])
          have "the_elem ?S = \<Union>?S"
          proof -
            have "\<Union>?S = \<Union>{the_elem ?S}"
              by (rule arg_cong[OF S_eq])
            also have "\<dots> = the_elem ?S"
              by simp
            finally show "the_elem ?S = \<Union>?S"
              by (rule sym)
          qed
          also have "\<dots> = {a}"
            using 4 by simp
          finally have "the_elem ?S = {a}" .
          with S_eq show "{a} \<in> ?S"
            by simp
        qed
        then have "{y, a} \<in> M" 
          using insert_Diff by force
        then show "x = y"
          by (metis M_match \<open>{x, a} \<in> M\<close> doubleton_eq_iff insertCI matching_unique_match)
      qed
      show "?f ` UNIV = UNIV"
      proof safe
        fix x
        assume "x \<in> (UNIV :: 'a set)"
        obtain e where e: "x \<in> e \<and> e \<in> M" 
          by (metis \<open>Vs M = UNIV\<close> \<open>x \<in> UNIV\<close> vs_member)
        then obtain y where y: "e = {x, y}" 
          using \<open>graph_invar M\<close> by fastforce
        then have "y \<in> e \<and> e \<in> M" 
          using e by fastforce
        then have "y \<in> Vs M" 
          by (simp add: \<open>Vs M = UNIV\<close>)
        have "\<exists>!e. e \<in> M \<and> y \<in> e" 
          using \<open>matching M\<close>[unfolded matching_def2] \<open>y \<in> Vs M\<close> by blast
        then have "{e . e \<in> M \<and> y \<in> e} =  {e}" 
          using `y \<in> e \<and> e \<in> M` by blast
        then have "{e - {y} |e. e \<in> M \<and> y \<in> e} = {e - {y}}" 
          by blast
        then have "{e - {y} |e. e \<in> M \<and> y \<in> e} = {{x}}" 
          using y \<open>graph_invar M\<close> \<open>y \<in> e \<and> e \<in> M\<close> by force
        then have "?f y = x"
          by simp
        then show "x \<in> range ?f" 
          by blast
      qed blast
    qed
    then show "?f permutes UNIV" 
      using bij_imp_permutes by blast
  qed
  have "u_edges ?f = M"
  proof(safe)
    {
      fix e
      assume "e \<in> u_edges ?f" 
      then obtain a where a: "e = {a, ?f a}" 
        unfolding u_edges_def 
        by blast
      then obtain b where b: "b = ?f a" 
        by presburger
      have "is_singleton (\<Union>{e - {a} |e. e \<in> M \<and> a \<in> e})" 
        using 1 by blast
      then have 6: "\<Union>{e - {a} |e. e \<in> M \<and> a \<in> e} = {b}" 
        by (simp add: is_singleton_the_elem b)
      have "is_singleton {e - {a} |e. e \<in> M \<and> a \<in> e}" 
        using 2 by auto
      then have "{b} \<in> {e - {a} |e. e \<in> M \<and> a \<in> e}" 
      proof -
        assume "is_singleton {e - {a} |e. e \<in> M \<and> a \<in> e}"
        then have eq: "{e - {a} |e. e \<in> M \<and> a \<in> e} = {the_elem {e - {a} |e. e \<in> M \<and> a \<in> e}}"
          by (simp add: is_singleton_the_elem)
        then have "\<Union>{the_elem {e - {a} |e. e \<in> M \<and> a \<in> e}} = {b}"
          using 6 by simp
        then have "the_elem {e - {a} |e. e \<in> M \<and> a \<in> e} = {b}"
          by (simp add: ccpo_Sup_singleton)
        with eq show "{b} \<in> {e - {a} |e. e \<in> M \<and> a \<in> e}"
          by simp
      qed
      then have "{a, b} \<in> M"
      proof -
        obtain e' where e': "e' \<in> M" "a \<in> e'" "e' - {a} = {b}"
          using \<open>{b} \<in> {e - {a} |e. e \<in> M \<and> a \<in> e}\<close>
          by blast
        from e'(2) have eq1: "insert a (e' - {a}) = e'"
          by (rule insert_Diff)
        have "e' = {a, b}"
          using e'(2,3) eq1 by simp
        with e'(1) show "{a, b} \<in> M"
          by simp
      qed
      then show "e \<in> M" 
        by (simp add: b a) 
    }
    fix e
    assume asme: "e \<in> M"
    then obtain a b where ab: "e = {a, b}"
      using \<open>graph_invar M\<close>
      by blast
    then have 7: "{b} \<in> {e - {a} |e. e \<in> M \<and> a \<in> e}" 
      using \<open>graph_invar M\<close> asme 
      by(auto simp add: doubleton_eq_iff intro!: exI[of _ "{a, b}"])
    have "is_singleton {e - {a} |e. e \<in> M \<and> a \<in> e}" 
      using 2 by auto
    then have "\<Union>{e - {a} |e. e \<in> M \<and> a \<in> e} = {b}" 
    proof -
      have "is_singleton {e - {a} |e. e \<in> M \<and> a \<in> e}"
        using 2 by auto
      then obtain x where x: "{e - {a} |e. e \<in> M \<and> a \<in> e} = {x}"
        unfolding is_singleton_def by blast
      from 7 x have "{b} = x" by auto
      with x show "\<Union>{e - {a} |e. e \<in> M \<and> a \<in> e} = {b}" by auto
    qed
    then have "?f a = b" 
      by simp   
    have "{a, ?f a} \<in> u_edges ?f"
      unfolding u_edges_def by blast 
    then show "e \<in> u_edges ?f" 
      using ab \<open>?f a = b\<close> by fastforce
  qed
  have "?f \<in> nonzero_perms"
    using u_edges_nonzero_perms[of ?f] M unfolding perfect_matching_def
    using \<open>?f permutes UNIV\<close>  \<open>u_edges ?f = M\<close>
    by simp
  have "\<forall> p' \<in> nonzero_perms - {?f}.  u_edges ?f \<noteq> u_edges p'"
  proof
    fix p
    assume asmp: "p \<in> nonzero_perms - {?f}"
    show "u_edges ?f \<noteq> u_edges p" 
    proof(rule ccontr)
      assume "\<not> u_edges ?f \<noteq> u_edges p"
      then have "u_edges ?f = u_edges p"
        by auto
      have "\<forall>x. ?f x = p x" 
      proof
        fix x
        have 1: "\<exists>!e. e \<in> M \<and> x \<in> e"
          using M_match unfolding matching_def2
          using \<open>Vs M = UNIV\<close> by auto
        then have "\<exists>!e. e \<in> u_edges ?f \<and> x \<in> e" 
          using \<open>u_edges ?f = M\<close> by presburger
        then have "\<exists>!e. e \<in> u_edges p \<and> x \<in> e" 
          by (simp add: \<open>u_edges ?f = u_edges p\<close>)
        obtain e where "e \<in> M \<and> x \<in> e" 
          using 1 by auto
        have "{x, ?f x} \<in> u_edges ?f" 
          unfolding u_edges_def by blast 
        have "{x, p x} \<in> u_edges p"
          unfolding u_edges_def by blast
        then have "{x, ?f x} = {x, p x}" 
          using 1 \<open>u_edges ?f = u_edges p\<close> \<open>{x, ?f x} \<in> u_edges ?f\<close> 
          using \<open>u_edges ?f = M\<close> by force
        then show "?f x = p x" 
          by (fastforce simp: doubleton_eq_iff)
      qed
      then have "?f = p"by auto 
      then show False 
        using asmp by fastforce
    qed
  qed
  then show ?thesis 
    using monom_is_nonzero_for_unique_edges[of ?f]  \<open>?f \<in> nonzero_perms\<close> by blast
qed

theorem perfect_matching_iff_nonzero_det:
  assumes "graph_invar G"
  shows "(\<exists> M. perfect_matching G M) \<longleftrightarrow> det (tutte_matrix) \<noteq> 0"
  using no_perfect_matching_zero_det tutte_matrix.perfect_matching_nonzero_det[OF _ _ assms] 
        tutte_matrix_axioms 
  by blast
end
end