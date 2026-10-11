theory Gammoid_Oracle
  imports
    Gammoid_Max_Flow
    Dinic.Unit_Flows_Impl
    Matroids_Greedy.Best_In_Greedy
    Spanning_Trees.Insertion_Sort_Desc
begin

hide_const (open) RBT_Set.insert

section \<open>An Independence Oracle for Gammoids\<close>

text \<open>We decide independence in a gammoid by augmenting paths. For an independent set \<open>T\<close> we store
a maximum unit flow of the Menger network of \<open>S\<close> and \<open>T\<close> by its residual edges of positive
capacity, as in theory \<open>Unit_Flows_Impl\<close>. An element \<open>x\<close> can be added iff the projection of the
residual edges contains a walk from the source to \<open>x\<close>, which a single depth-first search decides.
Accepting \<open>x\<close> adds the edge from \<open>x\<close> to the sink and augments the stored flow along the walk.\<close>

subsection \<open>Orders on the Nodes of the Network\<close>

text \<open>The residual edges are stored in red-black trees, which need linear orders on the nodes.\<close>

instantiation snode :: (linorder) linorder
begin

definition less_eq_snode :: "'a snode \<Rightarrow> 'a snode \<Rightarrow> bool" where
  "less_eq_snode x y =
    (case x of Vin a \<Rightarrow> (case y of Vin b \<Rightarrow> a \<le> b | Vout b \<Rightarrow> True)
             | Vout a \<Rightarrow> (case y of Vin b \<Rightarrow> False | Vout b \<Rightarrow> a \<le> b))"

definition less_snode :: "'a snode \<Rightarrow> 'a snode \<Rightarrow> bool" where
  "less_snode x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a snode"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (simp add: less_snode_def)
  show "x \<le> x"
    by (cases x) (simp_all add: less_eq_snode_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) (auto simp: less_eq_snode_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) (auto simp: less_eq_snode_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (auto simp: less_eq_snode_def)
qed

end

instantiation mnode :: (linorder) linorder
begin

definition less_eq_mnode :: "'a mnode \<Rightarrow> 'a mnode \<Rightarrow> bool" where
  "less_eq_mnode x y =
    (case x of Src \<Rightarrow> True
             | Nd a \<Rightarrow> (case y of Src \<Rightarrow> False | Nd b \<Rightarrow> a \<le> b | Snk \<Rightarrow> True)
             | Snk \<Rightarrow> (case y of Snk \<Rightarrow> True | _ \<Rightarrow> False))"

definition less_mnode :: "'a mnode \<Rightarrow> 'a mnode \<Rightarrow> bool" where
  "less_mnode x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a mnode"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (simp add: less_mnode_def)
  show "x \<le> x"
    by (cases x) (simp_all add: less_eq_mnode_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) (auto simp: less_eq_mnode_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) (auto simp: less_eq_mnode_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (auto simp: less_eq_mnode_def)
qed

end

text \<open>The networks of a gammoid and their maximum unit flows are in theory \<open>Gammoid_Max_Flow\<close>.\<close>

subsection \<open>The Abstract State of the Oracle\<close>

context gammoid
begin

text \<open>For a nonempty independent set \<open>T\<close> the oracle stores the residual edges of positive capacity
of a maximum unit flow of the network of \<open>T\<close>. For \<open>T = {}\<close> it stores the forward edges of the
network without the sink, i.e.\ the residual edges of the zero flow.\<close>

definition flow_state :: "'a set \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) Redge set \<Rightarrow> bool" where
  "flow_state T RS \<longleftrightarrow> (T = {} \<and> RS = F ` res_init) \<or> (T \<noteq> {} \<and> gammoid_net.ustate G S T RS)"

lemma flow_state_empty: "flow_state {} (F ` res_init)"
  by (simp add: flow_state_def)


lemma indep_insert_props:
  assumes "gammoid_indep (insert x T)"
  shows "S \<noteq> {}" "x \<in> dVs G"
  using assms linked_S_nonempty[of "insert x T"] linked_in_dVs[of G S "insert x T"]
  by (auto simp: gammoid_indep_def)

lemma indep_finite: "gammoid_indep T \<Longrightarrow> finite T"
  using dVs_finite by (auto simp: gammoid_indep_def dest: linked_in_dVs intro: finite_subset)

lemma res_init_tvp:
  "flow_network_spec.to_vertex_pair prod.fst prod.snd ` F ` res_init = res_init"
  by (simp add: image_image flow_network_spec.to_vertex_pair.simps multigraph_spec.make_pair_def)

text \<open>A walk from the source to \<open>Vout x\<close> in the stored edges needs a source and \<open>x\<close> in the graph.\<close>

lemma flow_state_walk:
  assumes st: "flow_state T RS" and ind: "gammoid_indep T"
    and p: "vwalk_bet (flow_network_spec.to_vertex_pair prod.fst prod.snd ` RS) Src p (Nd (Vout x))"
  shows "S \<noteq> {}" "x \<in> dVs G"
proof -
  have "S \<noteq> {} \<and> x \<in> dVs G"
  proof (cases "T = {}")
    case True
    then have R: "flow_network_spec.to_vertex_pair prod.fst prod.snd ` RS = res_init"
      using st res_init_tvp by (simp add: flow_state_def)
    have src: "Src \<in> dVs res_init" and vx: "Nd (Vout x) \<in> dVs res_init"
      using vwalk_bet_endpoints[OF p] unfolding R by simp_all
    obtain e where e: "e \<in> res_init" "Src = fst e \<or> Src = snd e"
      using src by (auto simp: dVs_eq)
    then have S: "S \<noteq> {}"
      by (auto simp: res_init_def)
    obtain d where d: "d \<in> res_init" "Nd (Vout x) = fst d \<or> Nd (Vout x) = snd d"
      using vx by (auto simp: dVs_eq)
    then have "Vout x \<in> dVs net_graph"
      by (auto simp: res_init_def)
    then show ?thesis
      using S by (simp add: net_graph_dVs)
  next
    case False
    have S: "S \<noteq> {}"
      using ind False linked_S_nonempty by (auto simp: gammoid_indep_def)
    have TG: "T \<subseteq> dVs G"
      using ind by (auto simp: gammoid_indep_def dest: linked_in_dVs)
    have Tmeets: "T \<inter> dVs G \<noteq> {}"
      using False TG by (simp add: Int_absorb2)
    interpret N: gammoid_net G S T
      by (intro gammoid_net.intro gammoid_net_axioms.intro gammoid_axioms S Tmeets indep_finite ind)
    obtain f where "RS = {e | e. e \<in> N.U.\<EE> \<and> N.U.rcap f e > 0}"
      using st False by (auto simp: flow_state_def N.ustate_def)
    then have RS: "RS \<subseteq> N.U.\<EE>"
      by blast
    have "Nd (Vout x) \<in> dVs (NEt T)"
      by (rule N.res_vertex[OF RS vwalk_bet_endpoints(2)[OF p]])
    then obtain d where d: "d \<in> NEt T" "Nd (Vout x) = fst d \<or> Nd (Vout x) = snd d"
      by (auto simp: dVs_eq)
    then have "Vout x \<in> dVs net_graph \<or> x \<in> dVs G"
      unfolding NEt_iff[OF S Tmeets] by auto
    then show ?thesis
      using S by (auto simp: net_graph_dVs)
  qed
  then show "S \<noteq> {}" "x \<in> dVs G"
    by simp_all
qed

end

text \<open>One step of the oracle: an independent set \<open>T\<close> and a new element \<open>x\<close> of the graph.\<close>

locale gammoid_step = gammoid +
  fixes T :: "'a set" and x :: 'a
  assumes S_ne: "S \<noteq> {}" and x_in: "x \<in> dVs G" and x_notin: "x \<notin> T"
    and T_indep: "gammoid_indep T"
begin

sublocale N': gammoid_net G S "insert x T"
  using S_ne x_in indep_finite[OF T_indep]
  by (intro gammoid_net.intro gammoid_net_axioms.intro gammoid_axioms) auto

text \<open>The stored edges of \<open>T\<close> together with the forward edge from \<open>x\<close> to the sink are the residual
edges of a unit flow of value \<open>card T\<close> in the network of \<open>insert x T\<close>.\<close>

lemma lift:
  assumes st: "flow_state T RS"
  obtains f where "N'.U.is_s_t_flow f Src Snk" "N'.U.unit_flow f" "N'.U.ex f Snk = card T"
    "\<forall>e. e \<notin> NEt (insert x T) \<longrightarrow> f e = 0"
    "{e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap f e > 0} = insert (F (Nd (Vout x), Snk)) RS"
    "F (Nd (Vout x), Snk) \<notin> RS"
    "\<not> (\<exists>p. vwalk_bet (N'.U.to_vertex_pair ` RS) Src p Snk)"
proof (cases "T = {}")
  case True
  then have RS: "RS = F ` res_init"
    using st by (simp add: flow_state_def)
  have NE: "NEt (insert x T) = insert (Nd (Vout x), Snk) res_init"
    using NEt_single[OF S_ne x_in] True by simp
  have st0: "N'.U.is_s_t_flow (\<lambda>_. 0) Src Snk"
    by (rule N'.U.zero_flow_is_s_t_flow[OF N'.M.Src_Snk_in_V N'.M.Src_neq_Snk])
  have ex0: "N'.U.ex (\<lambda>_. 0) Snk = card T"
    unfolding N'.U.ex_def using True by simp
  have res0: "{e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap (\<lambda>_. 0) e > 0} = insert (F (Nd (Vout x), Snk)) RS"
    using N'.U.zero_unit_flow(2) unfolding NE RS by simp
  have notin: "F (Nd (Vout x), Snk) \<notin> RS"
    unfolding RS by (auto simp: res_init_def)
  have nowalk: "\<not> (\<exists>p. vwalk_bet (N'.U.to_vertex_pair ` RS) Src p Snk)"
  proof
    assume "\<exists>p. vwalk_bet (N'.U.to_vertex_pair ` RS) Src p Snk"
    then obtain p where "vwalk_bet (N'.U.to_vertex_pair ` RS) Src p Snk"
      by blast
    then have "Snk \<in> dVs (N'.U.to_vertex_pair ` RS)"
      by (rule vwalk_bet_endpoints(2))
    then have "Snk \<in> dVs res_init"
      unfolding RS res_init_tvp .
    then show False
      by (auto simp: res_init_def dVs_eq)
  qed
  show ?thesis
    by (rule that[OF st0 N'.U.zero_unit_flow(1) ex0 _ res0 notin nowalk]) simp
next
  case False
  have TG: "T \<subseteq> dVs G"
    using T_indep by (auto simp: gammoid_indep_def dest: linked_in_dVs)
  have Tmeets: "T \<inter> dVs G \<noteq> {}"
    using False TG by (simp add: Int_absorb2)
  interpret N: gammoid_net G S T
    by (intro gammoid_net.intro gammoid_net_axioms.intro gammoid_axioms S_ne Tmeets
        indep_finite T_indep)
  obtain f where f: "N.U.is_s_t_flow f Src Snk" "N.U.unit_flow f" "N.U.ex f Snk = card T"
    "\<forall>e. e \<notin> NEt T \<longrightarrow> f e = 0" "RS = {e | e. e \<in> N.U.\<EE> \<and> N.U.rcap f e > 0}"
    using st False by (auto simp: flow_state_def N.ustate_def)
  let ?e0 = "(Nd (Vout x), Snk)"
  have NE: "NEt (insert x T) = insert ?e0 (NEt T)"
    by (rule NEt_insert[OF S_ne Tmeets x_in])
  have e0: "?e0 \<notin> NEt T"
    using x_notin by (simp add: NEt_iff[OF S_ne Tmeets])
  have f0: "f ?e0 = 0"
    using f(4)[rule_format, OF e0] .
  have sums: "sum f {e \<in> NEt (insert x T). P e} = sum f {e \<in> NEt T. P e}" for P
    unfolding NE using N.M.NE_finite f0 by (rule sum_insert_zero)
  have ex: "N'.U.ex f v = N.U.ex f v" for v
    using N'.M.ex_unfold[of f v] N.M.ex_unfold[of f v] sums by simp
  have vx: "Nd (Vout x) \<in> dVs (NEt T)"
  proof -
    have "(Vin x, Vout x) \<in> net_graph"
      using x_in by (simp add: net_graph_iff)
    then have "(Nd (Vin x), Nd (Vout x)) \<in> NEt T"
      by (simp add: NEt_iff[OF S_ne Tmeets])
    then show ?thesis
      by (blast intro: dVsI')
  qed
  have snk: "Snk \<in> dVs (NEt T)"
    using N.M.Src_Snk_in_V(2) by (simp add: N.M.V_NE)
  have V: "dVs (NEt (insert x T)) = dVs (NEt T)"
    unfolding NE using vx snk by (auto simp: dVs_eq)
  have uf: "N'.U.isuflow f"
  proof -
    have "\<forall>e \<in> NEt (insert x T). 0 \<le> f e \<and> f e \<le> 1"
      using f(1) f0 unfolding N.U.is_s_t_flow_def N.U_isuflow_iff NE by auto
    then show ?thesis
      unfolding N'.U_isuflow_iff .
  qed
  have st': "N'.U.is_s_t_flow f Src Snk"
    using f(1) uf unfolding N'.U.is_s_t_flow_def N.U.is_s_t_flow_def ex N'.M.V_NE N.M.V_NE V
    by simp
  have int': "N'.U.is_integral_flow f"
  proof -
    have "\<exists>n::int. f ?e0 = real_of_int n"
      using f0 by (intro exI[of _ 0]) simp
    then have "\<forall>e \<in> NEt (insert x T). \<exists>n::int. f e = real_of_int n"
      using f(2) unfolding N.U.is_integral_flow_def NE by blast
    then show ?thesis
      unfolding N'.U.is_integral_flow_def .
  qed
  have zero': "\<forall>e. e \<notin> NEt (insert x T) \<longrightarrow> f e = 0"
    using f(4) unfolding NE by blast
  have notin: "F ?e0 \<notin> RS"
  proof
    assume "F ?e0 \<in> RS"
    then have "F ?e0 \<in> N.U.\<EE>"
      using f(5) by blast
    then show False
      using e0 N.U.o_edge_res[of "F ?e0"] by simp
  qed
  have res: "{e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap f e > 0} = insert (F ?e0) RS"
  proof (rule set_eqI)
    fix r
    have E': "r \<in> N'.U.\<EE> \<longleftrightarrow> N'.U.oedge r \<in> insert ?e0 (NEt T)"
      using N'.U.o_edge_res[of r] unfolding NE by simp
    have E: "r \<in> N.U.\<EE> \<longleftrightarrow> N.U.oedge r \<in> NEt T"
      using N.U.o_edge_res[of r] by simp
    show "r \<in> {e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap f e > 0} \<longleftrightarrow> r \<in> insert (F ?e0) RS"
    proof (cases "N.U.oedge r = ?e0")
      case True
      then have "r = F ?e0 \<or> r = Redge.B ?e0"
        by (cases r) simp_all
      then show ?thesis
      proof
        assume r: "r = F ?e0"
        show ?thesis
          using E' f0 unfolding r by (simp add: one_ereal_def)
      next
        assume r: "r = Redge.B ?e0"
        have "Redge.B ?e0 \<notin> RS"
          using f(5) E e0 unfolding r by simp
        then show ?thesis
          using f0 unfolding r by simp
      qed
    next
      case False
      then have "r \<noteq> F ?e0"
        by auto
      then show ?thesis
        using E E' False f(5) by simp
    qed
  qed
  have nowalk: "\<not> (\<exists>p. vwalk_bet (N'.U.to_vertex_pair ` RS) Src p Snk)"
    using N.card_flow_no_walk[OF f(1) f(3)] f(5) by simp
  show ?thesis
    by (rule that[OF st' _ _ zero' res notin nowalk]) (use f(3) ex int' uf in simp_all)
qed

text \<open>Query correctness: \<open>insert x T\<close> is linked iff the stored edges contain a walk from the source
to \<open>Vout x\<close>.\<close>

theorem walk_iff:
  assumes st: "flow_state T RS"
  shows "(\<exists>p. vwalk_bet (N'.U.to_vertex_pair ` RS) Src p (Nd (Vout x))) \<longleftrightarrow> linked G S (insert x T)"
proof -
  obtain f where f: "N'.U.is_s_t_flow f Src Snk" "N'.U.unit_flow f" "N'.U.ex f Snk = card T"
    "\<forall>e. e \<notin> NEt (insert x T) \<longrightarrow> f e = 0"
    "{e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap f e > 0} = insert (F (Nd (Vout x), Snk)) RS"
    "F (Nd (Vout x), Snk) \<notin> RS"
    "\<not> (\<exists>p. vwalk_bet (N'.U.to_vertex_pair ` RS) Src p Snk)"
    by (rule lift[OF st])
  let ?e0 = "(Nd (Vout x), Snk)"
  let ?R = "N'.U.to_vertex_pair ` RS"
  have tvp0: "N'.U.to_vertex_pair (F ?e0) = ?e0"
    by (simp add: N'.M.make_pair_id)
  have R': "N'.U.to_vertex_pair ` {e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap f e > 0} = insert ?e0 ?R"
    unfolding f(5) using tvp0 by simp
  have card: "card (insert x T) - 1 = card T"
    using x_notin indep_finite[OF T_indep] by simp
  have link: "(\<exists>p. vwalk_bet (insert ?e0 ?R) Src p Snk) \<longleftrightarrow> linked G S (insert x T)"
    using N'.walk_Snk_iff_linked[OF f(1)] f(3) card unfolding R' by simp
  have "(\<exists>p. vwalk_bet ?R Src p (Nd (Vout x))) \<longleftrightarrow> (\<exists>p. vwalk_bet (insert ?e0 ?R) Src p Snk)"
  proof
    assume "\<exists>p. vwalk_bet ?R Src p (Nd (Vout x))"
    then obtain p where p: "vwalk_bet ?R Src p (Nd (Vout x))"
      by blast
    have "(Src, Nd (Vout x)) \<in> ?R\<^sup>+"
      using p by (rule walk_trancl) simp
    then have "(Src, Nd (Vout x)) \<in> (insert ?e0 ?R)\<^sup>+"
      by (rule trancl_mono) blast
    then have "(Src, Snk) \<in> (insert ?e0 ?R)\<^sup>+"
      by (rule trancl_into_trancl) simp
    then obtain q where "vwalk_bet (insert ?e0 ?R) Src q Snk"
      by (rule trancl_walk)
    then show "\<exists>p. vwalk_bet (insert ?e0 ?R) Src p Snk"
      by blast
  next
    assume "\<exists>p. vwalk_bet (insert ?e0 ?R) Src p Snk"
    then obtain q where "vwalk_bet (insert ?e0 ?R) Src q Snk"
      by blast
    then have "(Src, Snk) \<in> (insert ?e0 ?R)\<^sup>+"
      by (rule walk_trancl) simp
    then have "\<exists>y. (Src, y) \<in> {e \<in> insert ?e0 ?R. snd e \<noteq> Snk}\<^sup>* \<and> (y, Snk) \<in> insert ?e0 ?R"
      by (rule trancl_first_arrival)
    then obtain y where y: "(Src, y) \<in> {e \<in> insert ?e0 ?R. snd e \<noteq> Snk}\<^sup>*" "(y, Snk) \<in> insert ?e0 ?R"
      by (elim exE conjE)
    have sub: "{e \<in> insert ?e0 ?R. snd e \<noteq> Snk} \<subseteq> ?R"
      by auto
    have ry: "(Src, y) \<in> ?R\<^sup>*"
      using rtrancl_mono[OF sub] y(1) by (rule subsetD)
    show "\<exists>p. vwalk_bet ?R Src p (Nd (Vout x))"
    proof (cases "(y, Snk) = ?e0")
      case True
      then have "(Src, Nd (Vout x)) \<in> ?R\<^sup>*"
        using ry by simp
      then have "(Src, Nd (Vout x)) \<in> ?R\<^sup>+"
        by (auto dest: rtranclD)
      then obtain p where "vwalk_bet ?R Src p (Nd (Vout x))"
        by (rule trancl_walk)
      then show ?thesis
        by blast
    next
      case False
      then have "(y, Snk) \<in> ?R"
        using y(2) by simp
      with ry have "(Src, Snk) \<in> ?R\<^sup>+"
        by (rule rtrancl_into_trancl1)
      then obtain p where "vwalk_bet ?R Src p Snk"
        by (rule trancl_walk)
      then show ?thesis
        using f(7) by blast
    qed
  qed
  then show ?thesis
    using link by simp
qed

end

text \<open>The executable representation of the residual edges needs a linear order on the nodes.\<close>

locale gammoid_step_impl = gammoid_step G S T x for G :: "('a::linorder) dgraph" and S T x
begin

text \<open>Insertion: adding the edge into the sink and flipping the walk extended by the sink gives the
state of \<open>insert x T\<close>.\<close>

theorem insert_flow:
  assumes st: "flow_state T RS" and inv: "unit_invar prod.fst prod.snd RS ust"
    and p: "distinct p" "vwalk_bet (N'.U.to_vertex_pair ` RS) Src p (Nd (Vout x))"
  obtains RS' where "flow_state (insert x T) RS'"
    "unit_invar prod.fst prod.snd RS'
       (unit_flip (edges_of_vwalk (p @ [Snk])) (unit_add prod.fst prod.snd (F (Nd (Vout x), Snk)) ust))"
proof -
  obtain f where f: "N'.U.is_s_t_flow f Src Snk" "N'.U.unit_flow f" "N'.U.ex f Snk = card T"
    "\<forall>e. e \<notin> NEt (insert x T) \<longrightarrow> f e = 0"
    "{e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap f e > 0} = insert (F (Nd (Vout x), Snk)) RS"
    "F (Nd (Vout x), Snk) \<notin> RS"
    "\<not> (\<exists>p. vwalk_bet (N'.U.to_vertex_pair ` RS) Src p Snk)"
    by (rule lift[OF st])
  let ?e0 = "(Nd (Vout x), Snk)"
  let ?R' = "{e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap f e > 0}"
  let ?ust' = "unit_add prod.fst prod.snd (F ?e0) ust"
  have inv': "unit_invar prod.fst prod.snd ?R' ?ust'"
    unfolding f(5) by (rule unit_impl.u_add_correct[OF inv f(6)])
  have Snk_notin: "Snk \<notin> set p"
  proof
    assume "Snk \<in> set p"
    then obtain p1 p2 where p12: "p = p1 @ Snk # p2"
      by (meson split_list)
    have "vwalk_bet (N'.U.to_vertex_pair ` RS) Src ((p1 @ [Snk]) @ p2) (Nd (Vout x))"
      using p(2) p12 by simp
    then have "vwalk_bet (N'.U.to_vertex_pair ` RS) Src (p1 @ [Snk]) Snk"
      using vwalk_bet_prefix_is_vwalk_bet[of "p1 @ [Snk]"] by simp
    then show False
      using f(7) by blast
  qed
  have q: "distinct (p @ [Snk])"
    using p(1) Snk_notin by simp
  have sub: "N'.U.to_vertex_pair ` RS \<subseteq> N'.U.to_vertex_pair ` ?R'"
    unfolding f(5) by blast
  have e0R: "?e0 \<in> N'.U.to_vertex_pair ` ?R'"
    unfolding f(5) by (simp add: N'.M.make_pair_id)
  have "vwalk_bet (N'.U.to_vertex_pair ` ?R') Src (p @ tl [Nd (Vout x), Snk]) Snk"
    by (rule vwalk_bet_transitive[OF vwalk_bet_subset[OF p(2) sub] edges_are_vwalk_bet[OF e0R]])
  then have qw: "vwalk_bet (N'.U.to_vertex_pair ` ?R') Src (p @ [Snk]) Snk"
    by simp
  have fu: "N'.U.isuflow f" "N'.U.is_integral_flow f"
    using f(2) by simp_all
  obtain g where g: "N'.U.is_s_t_flow g Src Snk" "N'.U.isuflow g" "N'.U.is_integral_flow g"
    "N'.U.ex g Snk = N'.U.ex f Snk + 1"
    "unit_invar prod.fst prod.snd {e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap g e > 0}
       (unit_flip (edges_of_vwalk (p @ [Snk])) ?ust')"
    "\<forall>d. d \<notin> N'.M.NE \<longrightarrow> g d = f d"
    by (rule unit_impl.u_flip_augment[OF N'.U_unit_network inv' f(1) fu q qw])
  have card: "card (insert x T) = card T + 1"
    using x_notin indep_finite[OF T_indep] by simp
  have "N'.ustate {e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap g e > 0}"
    unfolding N'.ustate_def
    using g(1,2,3,4,6) f(3,4) card by (intro exI[of _ g]) simp
  then have "flow_state (insert x T) {e | e. e \<in> N'.U.\<EE> \<and> N'.U.rcap g e > 0}"
    by (simp add: flow_state_def)
  then show ?thesis
    by (rule that[OF _ g(5)])
qed

end

section \<open>The Executable Oracle\<close>

subsection \<open>The Initial Residual Edges\<close>

text \<open>The vertices of a list of edges as a red-black tree.\<close>

definition vertex_rbt :: "('a::linorder \<times> 'a) list \<Rightarrow> 'a rbt" where
  "vertex_rbt es = fold (\<lambda>e V. vset_insert (fst e) (vset_insert (snd e) V)) es vset_empty"

lemma vertex_rbt_correct: "vset_inv (vertex_rbt es)" "t_set (vertex_rbt es) = dVs (set es)"
proof -
  have "vset_inv V \<Longrightarrow> vset_inv (fold (\<lambda>e V. vset_insert (fst e) (vset_insert (snd e) V)) es V) \<and>
      t_set (fold (\<lambda>e V. vset_insert (fst e) (vset_insert (snd e) V)) es V) = t_set V \<union> dVs (set es)"
    for V
  proof (induction es arbitrary: V)
    case (Cons e es)
    have "vset_inv (vset_insert (fst e) (vset_insert (snd e) V))"
      "t_set (vset_insert (fst e) (vset_insert (snd e) V)) = insert (fst e) (insert (snd e) (t_set V))"
      using Cons.prems by (simp_all add: dfs.Graph.vset.set.invar_insert dfs.Graph.vset.set.set_insert)
    then show ?case
      using Cons.IH by (auto simp: dVs_eq)
  qed simp
  then show "vset_inv (vertex_rbt es)" "t_set (vertex_rbt es) = dVs (set es)"
    by (simp_all add: vertex_rbt_def dfs.Graph.vset.set.invar_empty dfs.Graph.vset.set.set_empty)
qed


text \<open>The edges of the residual graph of the zero flow, read off the input edges and sources:
  each input edge contributes the two vertex arcs of its endpoints and, unless it is a loop,
  the arc between them.\<close>

definition res_init_block :: "'a \<times> 'a \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) list" where
  "res_init_block e = [(Nd (Vin (fst e)), Nd (Vout (fst e))), (Nd (Vin (snd e)), Nd (Vout (snd e)))] @
     (if fst e = snd e then [] else [(Nd (Vout (fst e)), Nd (Vin (snd e)))])"

definition res_init_list :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) list" where
  "res_init_list es ss = concat (map res_init_block es) @ map (\<lambda>s. (Src, Nd (Vin s))) ss"

lemma set_res_init_list:
  "set (res_init_list es ss) = (\<Union>x \<in> set es. set (res_init_block x)) \<union> (\<lambda>s. (Src, Nd (Vin s))) ` set ss"
  by (simp add: res_init_list_def)

lemma (in gammoid) res_init_blocks:
  "res_init = (\<Union>x \<in> G. set (res_init_block x)) \<union> (\<lambda>s. (Src, Nd (Vin s))) ` S"
proof -
  have "(\<lambda>e. (Nd (fst e), Nd (snd e))) ` net_graph = (\<Union>x \<in> G. set (res_init_block x))"
  proof (rule set_eqI, rule iffI)
    fix e
    assume "e \<in> (\<lambda>e. (Nd (fst e), Nd (snd e))) ` net_graph"
    then obtain y where y: "y \<in> net_graph" "e = (Nd (fst y), Nd (snd y))"
      by (rule imageE) simp
    from y(1) consider (vert) v where "v \<in> dVs G" "y = (Vin v, Vout v)"
      | (arc) u v where "(u, v) \<in> G" "u \<noteq> v" "y = (Vout u, Vin v)"
      unfolding net_graph_iff by (elim disjE exE conjE) simp_all
    then show "e \<in> (\<Union>x \<in> G. set (res_init_block x))"
    proof cases
      case vert
      from vert(1) obtain a b where ab: "(a, b) \<in> G" "v = a \<or> v = b"
        by (auto simp: dVs_def)
      have "e \<in> set (res_init_block (a, b))"
        using ab(2) vert(2) y(2) by (auto simp: res_init_block_def)
      then show ?thesis
        by (rule UN_I[OF ab(1)])
    next
      case arc
      have "e \<in> set (res_init_block (u, v))"
        using arc(2,3) y(2) by (simp add: res_init_block_def)
      then show ?thesis
        by (rule UN_I[OF arc(1)])
    qed
  next
    fix e
    assume "e \<in> (\<Union>x \<in> G. set (res_init_block x))"
    then obtain x where x: "x \<in> G" "e \<in> set (res_init_block x)"
      by (rule UN_E)
    obtain a b where "x = (a, b)"
      by (cases x)
    then have ab: "(a, b) \<in> G" "e \<in> set (res_init_block (a, b))"
      using x by simp_all
    have a: "a \<in> dVs G" and b: "b \<in> dVs G"
      using ab(1) by auto
    have "e = (Nd (Vin a), Nd (Vout a)) \<or> e = (Nd (Vin b), Nd (Vout b)) \<or>
        (a \<noteq> b \<and> e = (Nd (Vout a), Nd (Vin b)))"
      using ab(2) by (simp add: res_init_block_def split: if_splits)
    then show "e \<in> (\<lambda>e. (Nd (fst e), Nd (snd e))) ` net_graph"
    proof (elim disjE conjE)
      assume e: "e = (Nd (Vin a), Nd (Vout a))"
      have "(Vin a, Vout a) \<in> net_graph"
        unfolding net_graph_iff using a by simp
      then show ?thesis
        by (rule image_eqI[rotated]) (simp add: e)
    next
      assume e: "e = (Nd (Vin b), Nd (Vout b))"
      have "(Vin b, Vout b) \<in> net_graph"
        unfolding net_graph_iff using b by simp
      then show ?thesis
        by (rule image_eqI[rotated]) (simp add: e)
    next
      assume ne: "a \<noteq> b" and e: "e = (Nd (Vout a), Nd (Vin b))"
      have "(Vout a, Vin b) \<in> net_graph"
        unfolding net_graph_iff using ab(1) ne by simp
      then show ?thesis
        by (rule image_eqI[rotated]) (simp add: e)
    qed
  qed
  then show ?thesis
    unfolding res_init_def by simp
qed


subsection \<open>The State of the Oracle\<close>

text \<open>The set as a red-black tree, and the stored residual edges with their projection as in
theory \<open>Unit_Flows_Impl\<close>.\<close>

record 'a gstate =
  gs_set :: "'a rbt"
  gs_res :: "(('a snode mnode \<times> 'a snode mnode rbt) rbt,
    (('a snode mnode \<times> 'a snode mnode) \<times> ('a snode mnode \<times> 'a snode mnode) Redge list) rbt) ustate"

locale gammoid_oracle_spec =
  fixes input_G :: "('a::linorder \<times> 'a) rbt" and input_S :: "'a rbt"
begin

definition gs_empty :: "'a gstate" where
  "gs_empty = \<lparr>gs_set = vset_empty,
     gs_res = unit_init fst snd
       (map F (remdups (res_init_list (Tree2.inorder input_G) (Tree2.inorder input_S))))\<rparr>"

text \<open>Is \<open>T + x\<close> independent? One depth-first search in the projection of the stored edges.\<close>

definition gs_query :: "'a \<Rightarrow> 'a gstate \<Rightarrow> bool" where
  "gs_query x st = (unit_search (gs_res st) Src (Nd (Vout x)) \<noteq> None)"

text \<open>Adding \<open>x\<close>: the same search, then the edge from \<open>x\<close> to the sink, and augmentation along the
walk found extended by the sink.\<close>

definition gs_insert :: "'a \<Rightarrow> 'a gstate \<Rightarrow> 'a gstate" where
  "gs_insert x st =
    (if isin (gs_set st) x then st\<lparr>gs_set := vset_insert x (gs_set st)\<rparr>
     else case unit_search (gs_res st) Src (Nd (Vout x)) of
       None \<Rightarrow> st\<lparr>gs_set := vset_insert x (gs_set st)\<rparr>
     | Some p \<Rightarrow> \<lparr>gs_set = vset_insert x (gs_set st),
         gs_res = unit_flip (edges_of_vwalk (p @ [Snk]))
           (unit_add fst snd (F (Nd (Vout x), Snk)) (gs_res st))\<rparr>)"

text \<open>The ground set of the gammoid.\<close>

definition gs_carrier :: "'a rbt" where
  "gs_carrier = vertex_rbt (Tree2.inorder input_G)"

text \<open>The invariant of the state. The flow part is only claimed for well-formed inputs, so that
  the invariant is meaningful for all inputs.\<close>

definition gs_invar :: "'a gstate \<Rightarrow> bool" where
  "gs_invar st \<longleftrightarrow> vset_inv (gs_set st) \<and> unit_wf (gs_res st) \<and>
     (vset_inv input_G \<and> vset_inv input_S \<and> t_set input_S \<subseteq> dVs (t_set input_G) \<longrightarrow>
      gammoid.gammoid_indep (t_set input_G) (t_set input_S) (t_set (gs_set st)) \<longrightarrow>
      (\<exists>RS. unit_invar fst snd RS (gs_res st) \<and>
         gammoid.flow_state (t_set input_G) (t_set input_S) (t_set (gs_set st)) RS))"

lemma gs_set_insert: "gs_set (gs_insert x st) = vset_insert x (gs_set st)"
  by (simp add: gs_insert_def split: option.split)

end

global_interpretation gorcl: gammoid_oracle_spec
  where input_G = input_G and input_S = input_S
  for input_G input_S
  defines gs_empty = gorcl.gs_empty
    and gs_query = gorcl.gs_query
    and gs_insert = gorcl.gs_insert
    and gs_carrier = gorcl.gs_carrier
    and gs_invar = gorcl.gs_invar
  done

locale gammoid_oracle = gammoid_oracle_spec +
  assumes G_inv: "vset_inv input_G" and S_inv: "vset_inv input_S"
    and S_sub: "t_set input_S \<subseteq> dVs (t_set input_G)"
begin

sublocale gammoid "t_set input_G" "t_set input_S"
  by unfold_locales (simp_all add: S_sub)

lemma gs_invar_iff:
  "local.gs_invar st \<longleftrightarrow> vset_inv (gs_set st) \<and> unit_wf (gs_res st) \<and>
     (gammoid_indep (t_set (gs_set st)) \<longrightarrow>
       (\<exists>RS. unit_invar fst snd RS (gs_res st) \<and> flow_state (t_set (gs_set st)) RS))"
  by (simp add: local.gs_invar_def G_inv S_inv S_sub)

lemma res_init_list_input: "set (res_init_list (Tree2.inorder input_G) (Tree2.inorder input_S)) = res_init"
  by (simp only: set_res_init_list res_init_blocks set_inorder)

lemma gs_carrier_correct: "vset_inv local.gs_carrier" "t_set local.gs_carrier = dVs (t_set input_G)"
  using vertex_rbt_correct[of "Tree2.inorder input_G"] by (simp_all add: local.gs_carrier_def)

lemma gs_empty_correct: "local.gs_invar local.gs_empty" "t_set (gs_set local.gs_empty) = {}"
proof -
  let ?rs = "map F (remdups (res_init_list (Tree2.inorder input_G) (Tree2.inorder input_S)))"
  have dist: "distinct ?rs"
    by (simp add: distinct_map inj_on_def)
  have set: "set ?rs = F ` res_init"
    using res_init_list_input by simp
  have inv: "unit_invar fst snd (F ` res_init) (unit_init fst snd ?rs)"
    using unit_impl.u_init_correct[OF dist] unfolding set .
  have wfi: "unit_wf (unit_init fst snd ?rs)"
    by (rule unit_impl.u_invar_wf[OF inv])
  have e: "vset_inv (vset_empty :: 'a rbt)" "t_set (vset_empty :: 'a rbt) = {}"
    by (simp_all add: dfs.Graph.vset.set.invar_empty dfs.Graph.vset.set.set_empty)
  show "local.gs_invar local.gs_empty"
    unfolding gs_invar_iff local.gs_empty_def
    using inv wfi e flow_state_empty by (auto intro!: exI[of _ "F ` res_init"])
  show "t_set (gs_set local.gs_empty) = {}"
    by (simp add: local.gs_empty_def dfs.Graph.vset.set.set_empty)
qed

lemma gs_query_correct:
  assumes inv: "local.gs_invar st" and ind: "gammoid_indep (t_set (gs_set st))"
    and x: "x \<notin> t_set (gs_set st)"
  shows "local.gs_query x st \<longleftrightarrow> gammoid_indep (insert x (t_set (gs_set st)))"
proof -
  let ?T = "t_set (gs_set st)"
  obtain RS where R: "unit_invar fst snd RS (gs_res st)" "flow_state ?T RS"
    using inv ind by (auto simp: gs_invar_iff)
  have "local.gs_query x st \<longleftrightarrow>
      (\<exists>p. vwalk_bet (flow_network_spec.to_vertex_pair fst snd ` RS) Src p (Nd (Vout x)))"
    using unit_impl.u_search_correct(1)[OF R(1), of Src "Nd (Vout x)"]
    by (simp add: local.gs_query_def)
  also have "\<dots> \<longleftrightarrow> gammoid_indep (insert x ?T)"
  proof
    assume w: "\<exists>p. vwalk_bet (flow_network_spec.to_vertex_pair fst snd ` RS) Src p (Nd (Vout x))"
    then obtain p where p: "vwalk_bet (flow_network_spec.to_vertex_pair fst snd ` RS) Src p (Nd (Vout x))"
      by blast
    have S: "t_set input_S \<noteq> {}" and xG: "x \<in> dVs (t_set input_G)"
      using flow_state_walk[OF R(2) ind p] by simp_all
    interpret K: gammoid_step "t_set input_G" "t_set input_S" ?T x
      by (intro gammoid_step.intro gammoid_step_axioms.intro gammoid_axioms S xG x ind)
    show "gammoid_indep (insert x ?T)"
      using K.walk_iff[OF R(2)] w by (simp add: gammoid_indep_def)
  next
    assume ind': "gammoid_indep (insert x ?T)"
    have S: "t_set input_S \<noteq> {}" and xG: "x \<in> dVs (t_set input_G)"
      using indep_insert_props[OF ind'] by simp_all
    interpret K: gammoid_step "t_set input_G" "t_set input_S" ?T x
      by (intro gammoid_step.intro gammoid_step_axioms.intro gammoid_axioms S xG x ind)
    show "\<exists>p. vwalk_bet (flow_network_spec.to_vertex_pair fst snd ` RS) Src p (Nd (Vout x))"
      using K.walk_iff[OF R(2)] ind' by (simp add: gammoid_indep_def)
  qed
  finally show ?thesis .
qed

lemma gs_insert_correct:
  assumes inv: "local.gs_invar st"
  shows "local.gs_invar (local.gs_insert x st)"
proof -
  let ?T = "t_set (gs_set st)"
  have sinv: "vset_inv (gs_set st)" and wf: "unit_wf (gs_res st)"
    and st: "gammoid_indep ?T \<Longrightarrow> \<exists>RS. unit_invar fst snd RS (gs_res st) \<and> flow_state ?T RS"
    using inv by (auto simp: gs_invar_iff)
  have sinv': "vset_inv (vset_insert x (gs_set st))"
    and T': "t_set (vset_insert x (gs_set st)) = insert x ?T"
    using sinv by (simp_all add: dfs.Graph.vset.set.invar_insert dfs.Graph.vset.set.set_insert)
  have sub: "gammoid_indep ?T" if "gammoid_indep (insert x ?T)"
    using that linked_subset[of "t_set input_G" "t_set input_S" "insert x ?T" ?T]
    by (auto simp: gammoid_indep_def)
  show ?thesis
  proof (cases "isin (gs_set st) x")
    case True
    then have "x \<in> ?T"
      using sinv by (simp add: dfs.Graph.vset.set.set_isin)
    then have "insert x ?T = ?T"
      by blast
    then show ?thesis
      using inv True sinv' T' by (simp add: local.gs_insert_def gs_invar_iff)
  next
    case False
    then have x: "x \<notin> ?T"
      using sinv by (simp add: dfs.Graph.vset.set.set_isin)
    show ?thesis
    proof (cases "unit_search (gs_res st) Src (Nd (Vout x))")
      case None
      have res: "local.gs_insert x st = st\<lparr>gs_set := vset_insert x (gs_set st)\<rparr>"
        using False None by (simp add: local.gs_insert_def)
      have "\<not> gammoid_indep (insert x ?T)"
      proof
        assume ind': "gammoid_indep (insert x ?T)"
        then have "local.gs_query x st"
          using gs_query_correct[OF inv sub[OF ind'] x] by simp
        then show False
          using None by (simp add: local.gs_query_def)
      qed
      then show ?thesis
        unfolding res gs_invar_iff using sinv' T' wf by simp
    next
      case (Some p)
      let ?st' = "unit_flip (edges_of_vwalk (p @ [Snk]))
        (unit_add fst snd (F (Nd (Vout x), Snk)) (gs_res st))"
      have res: "local.gs_insert x st = \<lparr>gs_set = vset_insert x (gs_set st), gs_res = ?st'\<rparr>"
        using False Some by (simp add: local.gs_insert_def)
      have wf': "unit_wf ?st'"
        by (rule unit_impl.u_wf_flip[OF unit_impl.u_wf_add[OF wf]])
      have "\<exists>RS'. unit_invar fst snd RS' ?st' \<and> flow_state (insert x ?T) RS'"
        if ind': "gammoid_indep (insert x ?T)"
      proof -
        have ind: "gammoid_indep ?T"
          by (rule sub[OF ind'])
        obtain RS where R: "unit_invar fst snd RS (gs_res st)" "flow_state ?T RS"
          using st[OF ind] by blast
        have p: "distinct p" "vwalk_bet (flow_network_spec.to_vertex_pair fst snd ` RS) Src p (Nd (Vout x))"
          using unit_impl.u_search_correct(2)[OF R(1) _ Some] by simp_all
        have S: "t_set input_S \<noteq> {}" and xG: "x \<in> dVs (t_set input_G)"
          using indep_insert_props[OF ind'] by simp_all
        interpret K: gammoid_step_impl "t_set input_G" "t_set input_S" ?T x
          unfolding gammoid_step_impl_def
          by (intro gammoid_step.intro gammoid_step_axioms.intro gammoid_axioms S xG x ind)
        obtain RS' where "flow_state (insert x ?T) RS'" "unit_invar fst snd RS' ?st'"
          by (rule K.insert_flow[OF R(2) R(1) p])
        then show ?thesis
          by blast
      qed
      then show ?thesis
        unfolding res gs_invar_iff using sinv' T' wf' by simp
    qed
  qed
qed

end

text \<open>Invariant preservation for arbitrary inputs: for ill-formed inputs the invariant only
  concerns the data structures.\<close>

context gammoid_oracle_spec
begin

lemma gs_invar_empty: "gs_invar gs_empty"
proof (cases "vset_inv input_G \<and> vset_inv input_S \<and> t_set input_S \<subseteq> dVs (t_set input_G)")
  case True
  then interpret gammoid_oracle input_G input_S
    by unfold_locales auto
  show ?thesis
    by (rule gs_empty_correct(1))
next
  case False
  have "vset_inv (gs_set gs_empty) \<and> unit_wf (gs_res gs_empty)"
    using unit_impl.u_wf_init by (simp add: gs_empty_def dfs.Graph.vset.set.invar_empty)
  with False show ?thesis
    unfolding gs_invar_def by blast
qed

lemma gs_invar_insert:
  assumes inv: "gs_invar st"
  shows "gs_invar (gs_insert x st)"
proof (cases "vset_inv input_G \<and> vset_inv input_S \<and> t_set input_S \<subseteq> dVs (t_set input_G)")
  case True
  then interpret gammoid_oracle input_G input_S
    by unfold_locales auto
  show ?thesis
    by (rule gs_insert_correct[OF inv])
next
  case False
  have sinv: "vset_inv (gs_set st)" and wfr: "unit_wf (gs_res st)"
    using inv by (simp_all add: gs_invar_def)
  have sinv': "vset_inv (gs_set (gs_insert x st))"
    using sinv by (simp add: gs_set_insert dfs.Graph.vset.set.invar_insert)
  have "unit_wf (gs_res (gs_insert x st))"
    using wfr unit_impl.u_wf_flip[OF unit_impl.u_wf_add[OF wfr]]
    by (simp add: gs_insert_def split: option.split)
  with False sinv' show ?thesis
    unfolding gs_invar_def by blast
qed

end

section \<open>The Best-In-Greedy Algorithm on Gammoids\<close>

text \<open>Red-black trees implement the set specification of the greedy algorithm.\<close>

interpretation rbt_specs: Matroid_Specs
  where set_empty = vset_empty and set_insert = vset_insert and set_delete = vset_delete
    and set_inv = "vset_inv :: ('a::linorder) rbt \<Rightarrow> bool" and set_isin = isin and to_set = t_set
    and union = vset_union and inter = vset_inter and diff = vset_diff and cardinality = size
  apply (unfold Matroid_Specs_def Indep_System_Specs_def Card_Set2_def)
  apply (intro conjI Card_Set2_axioms.intro)
  subgoal
    by (rule dfs.set_ops.Set2_axioms)
  subgoal for X
    by (cases X) (simp_all add: RBT_Set.empty_def)
  subgoal for X
    using rbt_size_correct[of X] by (simp add: t_inv_def vset_inv_def)
  done

text \<open>The greedy algorithm with the gammoid oracle. The independence test of the abstract
  algorithm is the gammoid independence of the set represented.\<close>

global_interpretation Gammoid_Greedy: Best_In_Greedy'
  where set_empty = vset_empty and set_insert = vset_insert and set_delete = vset_delete
    and set_inv = "vset_inv :: 'a rbt \<Rightarrow> bool" and set_isin = isin and to_set = t_set
    and union = vset_union and inter = vset_inter and diff = vset_diff and cardinality = size
    and carrier = "gs_carrier input_G"
    and indep_fn = "\<lambda>X. gammoid.gammoid_indep (t_set input_G) (t_set input_S) (t_set X)"
    and sort_desc = insort_key_desc
    and local_indep_oracle = gs_query
    and wrapper_insert = gs_insert
    and wrapper_invar = "gs_invar input_G input_S"
    and remove_wrapper = gs_set
    and wrapper_empty = "gs_empty input_G input_S"
  for input_G :: "('a::linorder \<times> 'a) rbt" and input_S :: "'a rbt"
  defines gammoid_greedy' = Gammoid_Greedy.BestInGreedy'
    and gammoid_greedy = Gammoid_Greedy.BestInGreedy
    and gammoid_greedy_init = Gammoid_Greedy.initial_state
    and gammoid_greedy_init' = Gammoid_Greedy.initial_state'
    and gammoid_to_ordinary = Gammoid_Greedy.to_ordinary
  apply (subst Best_In_Greedy'_def, subst Best_In_Greedy_def, subst Greedy_Common_def)
  apply (intro conjI Best_In_Greedy'_axioms.intro rbt_specs.Matroid_Specs_axioms)
  subgoal
    by (rule gorcl.gs_invar_insert)
  subgoal
    by (simp add: gorcl.gs_invar_def)
  subgoal
    by (rule gorcl.gs_set_insert)
  subgoal
    by (simp add: gorcl.gs_empty_def)
  subgoal
    by (rule gorcl.gs_invar_empty)
  done

lemma insort_key_desc_axioms:
  "sort_desc_axioms' (insort_key_desc :: ('a::linorder \<Rightarrow> rat) \<Rightarrow> 'a list \<Rightarrow> 'a list)"
  by (simp add: Gammoid_Greedy.sort_desc_axioms_def insort_key_desc_stable length_insort_key_desc
      set_insort_key_desc sorted_desc_f_insort_key_desc)

text \<open>Correctness: the executable algorithm agrees with the abstract one, which returns a basis
  of maximum weight, since gammoids are matroids.\<close>

locale gammoid_greedy_correct = gammoid_oracle input_G input_S
  for input_G :: "('a::linorder \<times> 'a) rbt" and input_S +
  fixes c :: "'a \<Rightarrow> rat" and order :: "'a list"
  assumes c_nonneg: "\<And>x. x \<in> dVs (t_set input_G) \<Longrightarrow> 0 \<le> c x"
    and order_carrier: "set order = dVs (t_set input_G)"
    and order_distinct: "distinct order"
begin

lemma oracle_correct:
  assumes "local.gs_invar S" "gammoid_indep (t_set (gs_set S))" "x \<notin> t_set (gs_set S)"
  shows "local.gs_query x S \<longleftrightarrow> gammoid_indep (t_set (vset_insert x (gs_set S)))"
proof -
  have "vset_inv (gs_set S)"
    using assms(1) by (simp add: gs_invar_iff)
  then show ?thesis
    using gs_query_correct[OF assms] by (simp add: dfs.Graph.vset.set.set_insert)
qed

lemma size_carrier: "size local.gs_carrier = length order"
proof -
  have "size local.gs_carrier = card (t_set local.gs_carrier)"
    using gs_carrier_correct(1) rbt_size_correct[of local.gs_carrier] by (simp add: t_inv_def vset_inv_def)
  then show ?thesis
    using gs_carrier_correct(2) order_carrier distinct_card[OF order_distinct] by simp
qed

theorem gammoid_greedy_corresp:
  "gammoid_to_ordinary (gammoid_greedy' (gammoid_greedy_init' input_G input_S c order)) =
   gammoid_greedy input_G input_S (gammoid_greedy_init c order)"
  apply (rule Gammoid_Greedy.BestInGreedy'_corresp)
  apply (unfold Gammoid_Oracle.gs_carrier_def Gammoid_Oracle.gs_invar_def Gammoid_Oracle.gs_query_def)
  subgoal for S x
    using oracle_correct[of S x] by simp
  subgoal
    by (rule gs_carrier_correct(1))
  subgoal
    unfolding Greedy_Common.greedy_axioms_def[OF Gammoid_Greedy.Greedy_Common_axioms]
    by (intro conjI rbt_specs.invarI rbt_specs.finite_setsI) (simp_all add: gs_carrier_correct(1))
  subgoal
    by (rule insort_key_desc_axioms)
  subgoal
    unfolding rbt_specs.indep_system_axioms_def
  proof (intro conjI allI impI)
    fix X :: "'a rbt"
    assume "vset_inv X" "gammoid_indep (t_set X)"
    then show "rbt_specs.subseteq X local.gs_carrier"
      using indep_system.indep_subset_carrier[OF gammoid_indep_system]
      by (simp add: rbt_specs.set.set_subseteq gs_carrier_correct)
  next
    show "\<exists>X. vset_inv X \<and> gammoid_indep (t_set X)"
      using indep_system.indep_empty[OF gammoid_indep_system]
      by (intro exI[of _ vset_empty]) (simp add: dfs.Graph.vset.set.invar_empty dfs.Graph.vset.set.set_empty)
  next
    fix X Y :: "'a rbt"
    assume "vset_inv X" "vset_inv Y" "gammoid_indep (t_set X)" "rbt_specs.subseteq Y X"
    then show "gammoid_indep (t_set Y)"
      using indep_system.indep_subset[OF gammoid_indep_system]
      by (simp add: rbt_specs.set.set_subseteq)
  qed
  subgoal
    by (simp add: Greedy_Common.nonnegative_def[OF Gammoid_Greedy.Greedy_Common_axioms]
        dfs.Graph.vset.set.set_isin gs_carrier_correct c_nonneg)
  subgoal
    by (simp add: Greedy_Common.valid_order_def[OF Gammoid_Greedy.Greedy_Common_axioms]
        gs_carrier_correct order_carrier size_carrier)
  done

interpretation use_greedy: Use_Greedy_Thms vset_empty vset_insert vset_delete isin t_set vset_inv
  vset_union vset_inter vset_diff size gammoid_indep local.gs_carrier c order
  "insort_key_desc :: ('a \<Rightarrow> rat) \<Rightarrow> 'a list \<Rightarrow> 'a list"
proof (intro Use_Greedy_Thms.intro Use_Greedy_Thms_axioms.intro)
  show "Indep_System_Specs vset_empty vset_insert vset_delete isin t_set vset_inv vset_union
      vset_inter vset_diff size"
    using rbt_specs.Matroid_Specs_axioms by (simp add: Matroid_Specs_def)
  show "indep_system (t_set local.gs_carrier) gammoid_indep"
    using gammoid_indep_system by (simp add: gs_carrier_correct(2))
  show "finite X" if "gammoid_indep X" for X
    using that by (rule indep_finite)
  show "X \<subseteq> t_set local.gs_carrier" if "gammoid_indep X" for X
    using indep_system.indep_subset_carrier[OF gammoid_indep_system that]
    by (simp add: gs_carrier_correct(2))
  show "vset_inv local.gs_carrier"
    by (rule gs_carrier_correct(1))
  show "0 \<le> c e" if "e \<in> t_set local.gs_carrier" for e
    using that c_nonneg by (simp add: gs_carrier_correct(2))
  show "t_set local.gs_carrier = set order"
    by (simp add: gs_carrier_correct(2) order_carrier)
  show "distinct order"
    by (rule order_distinct)
  show "finite (t_set X)" for X :: "'a rbt"
    by simp
  show "sort_desc_axioms' (insort_key_desc :: ('a \<Rightarrow> rat) \<Rightarrow> 'a list \<Rightarrow> 'a list)"
    by (rule insort_key_desc_axioms)
qed

lemma result_exec:
  "t_set (gs_set (result (gammoid_greedy' (gammoid_greedy_init' input_G input_S c order)))) =
   t_set (result (gammoid_greedy input_G input_S (gammoid_greedy_init c order)))"
  using arg_cong[OF gammoid_greedy_corresp, of "\<lambda>st. t_set (result st)"]
  by (simp add: Gammoid_Greedy.to_ordinary_def)

theorem gammoid_greedy_basis:
  "indep_system.basis (dVs (t_set input_G)) gammoid_indep
     (t_set (gs_set (result (gammoid_greedy' (gammoid_greedy_init' input_G input_S c order)))))"
  using use_greedy.algo_gives_basis
  by (simp add: result_exec gammoid_greedy_def gammoid_greedy_init_def Gammoid_Oracle.gs_carrier_def
      gs_carrier_correct(2))

theorem gammoid_greedy_max:
  assumes "gammoid_indep X"
  shows "sum c X \<le> sum c (t_set (gs_set (result (gammoid_greedy' (gammoid_greedy_init' input_G input_S c order)))))"
proof -
  have "indep_system.rank_quotient (t_set local.gs_carrier) gammoid_indep = 1"
    using indep_system.matroid_iff_rq_eq_1[OF use_greedy.indep_system] gammoid_matroid
    by (simp add: gs_carrier_correct(2))
  then show ?thesis
    using use_greedy.indep_predicate_greedy_correct[OF assms]
    by (simp add: result_exec gammoid_greedy_def gammoid_greedy_init_def Gammoid_Oracle.gs_carrier_def)
qed

end

text \<open>A small test: sources \<open>1\<close> and \<open>4\<close>, weights equal to the vertex names. The maximum-weight
  independent set is \<open>{4, 5}\<close>, linked by \<open>[4]\<close> and \<open>[1, 3, 5]\<close>.\<close>

value "let G = foldr vset_insert [(1::nat, 2), (2, 3), (1, 3), (4, 3), (3, 5)] vset_empty;
           S = foldr vset_insert [1::nat, 4] vset_empty
       in Tree2.inorder (gs_set (result (gammoid_greedy' (gammoid_greedy_init' G S of_nat [1, 2, 3, 4, 5]))))"

end

