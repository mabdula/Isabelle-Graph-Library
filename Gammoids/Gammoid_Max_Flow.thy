theory Gammoid_Max_Flow
  imports
    Gammoids
    Flow_Theory.Unit_Flows
begin

section \<open>Maximum Unit Flows in the Network of a Gammoid\<close>

text \<open>The network of a gammoid \<open>(G, S)\<close> and a set \<open>T\<close> splits every vertex of \<open>G\<close> into an in- and an
out-copy joined by a unit edge, and connects a source to the in-copies of \<open>S\<close> and the out-copies
of \<open>T\<close> to a sink. \<open>T\<close> is independent iff a maximum unit flow saturates all edges into the sink.
This theory provides the facts an independence oracle needs to maintain such a flow while \<open>T\<close>
changes.\<close>

subsection \<open>Menger Networks\<close>

context menger_edge_network
begin

lemma ex_unfold: "N.ex f v = sum f {e \<in> NE. snd e = v} - sum f {e \<in> NE. fst e = v}"
  by (simp add: N.ex_def N.delta_minus_def N.delta_plus_def)

lemma GE_iff_inner:
  assumes "e \<in> NE"
  shows "e \<in> GE \<longleftrightarrow> fst e \<noteq> Src \<and> snd e \<noteq> Snk"
  using assms
proof (cases rule: NE_cases)
  case (G x y)
  then have "e \<in> GE"
    unfolding GE_def by (auto intro: rev_image_eqI[of "(x, y)"] simp: lift_edge_def)
  then show ?thesis
    using G(2) by simp
qed (auto simp: GE_def lift_edge_def)

end


subsection \<open>The Network of a Gammoid\<close>

context gammoid
begin

text \<open>The split graph without the edges \<open>(Vout v, Vin v)\<close> that come from self-loops: a distinct
walk never needs them.\<close>

definition net_graph :: "'a snode dgraph" where
  "net_graph = split_graph G - range (\<lambda>v. (Vout v, Vin v))"

lemma net_graph_iff:
  "e \<in> net_graph \<longleftrightarrow>
    (\<exists>v. v \<in> dVs G \<and> e = (Vin v, Vout v)) \<or> (\<exists>u v. (u, v) \<in> G \<and> u \<noteq> v \<and> e = (Vout u, Vin v))"
proof
  assume "e \<in> net_graph"
  then show "(\<exists>v. v \<in> dVs G \<and> e = (Vin v, Vout v)) \<or>
    (\<exists>u v. (u, v) \<in> G \<and> u \<noteq> v \<and> e = (Vout u, Vin v))"
    by (auto simp: net_graph_def split_graph_def)
next
  assume "(\<exists>v. v \<in> dVs G \<and> e = (Vin v, Vout v)) \<or>
    (\<exists>u v. (u, v) \<in> G \<and> u \<noteq> v \<and> e = (Vout u, Vin v))"
  then show "e \<in> net_graph"
  proof (elim disjE exE conjE)
    fix v
    assume "v \<in> dVs G" "e = (Vin v, Vout v)"
    then show ?thesis
      by (auto simp: net_graph_def split_graph_def)
  next
    fix u v
    assume uv: "(u, v) \<in> G" "u \<noteq> v" "e = (Vout u, Vin v)"
    then have "e \<in> (\<lambda>e. (Vout (fst e), Vin (snd e))) ` G"
      by (auto intro: rev_image_eqI[of "(u, v)"])
    then show ?thesis
      using uv by (auto simp: net_graph_def split_graph_def)
  qed
qed

lemma net_graph_subset: "net_graph \<subseteq> split_graph G"
  by (auto simp: net_graph_def)

lemma finite_net_graph: "finite net_graph"
  using finite_split_graph[OF G_finite] net_graph_subset by (rule finite_subset[rotated])


lemma net_graph_dVs:
  "Vin v \<in> dVs net_graph \<longleftrightarrow> v \<in> dVs G"
  "Vout v \<in> dVs net_graph \<longleftrightarrow> v \<in> dVs G"
proof -
  have edge: "v \<in> dVs G \<Longrightarrow> (Vin v, Vout v) \<in> net_graph"
    by (simp add: net_graph_iff)
  have from_net: "v \<in> dVs G" if w: "w \<in> dVs net_graph" "w = Vin v \<or> w = Vout v" for w
  proof -
    obtain a b where ab: "(a, b) \<in> net_graph" "w = a \<or> w = b"
      using w(1) unfolding dVs_def by blast
    from ab(1) consider (split) u where "u \<in> dVs G" "a = Vin u" "b = Vout u"
      | (arc) u' v' where "(u', v') \<in> G" "a = Vout u'" "b = Vin v'"
      by (auto simp: net_graph_iff)
    then show ?thesis
    proof cases
      case split
      then show ?thesis
        using ab(2) w(2) by auto
    next
      case arc
      then have "u' \<in> dVs G" "v' \<in> dVs G"
        by auto
      then show ?thesis
        using arc(2,3) ab(2) w(2) by auto
    qed
  qed
  show "Vin v \<in> dVs net_graph \<longleftrightarrow> v \<in> dVs G" "Vout v \<in> dVs net_graph \<longleftrightarrow> v \<in> dVs G"
    using from_net edge by auto
qed

lemma net_network:
  assumes "S \<noteq> {}" "T \<inter> dVs G \<noteq> {}"
  shows "menger_edge_network net_graph (Vin ` S) (Vout ` T)"
proof
  show "finite net_graph"
    by (rule finite_net_graph)
  show "Vin ` S \<inter> Vout ` T = {}"
    by auto
  obtain s where "s \<in> S"
    using assms(1) by blast
  then show "Vin ` S \<inter> dVs net_graph \<noteq> {}"
    using S_in_dVs net_graph_dVs(1)[of s] by blast
  obtain t where "t \<in> T" "t \<in> dVs G"
    using assms(2) by blast
  then show "Vout ` T \<inter> dVs net_graph \<noteq> {}"
    using net_graph_dVs(2)[of t] by blast
qed

text \<open>The edges of the Menger network for a sink set \<open>T\<close>.\<close>

abbreviation "NEt T \<equiv> menger_edge_network.NE net_graph (Vin ` S) (Vout ` T)"

lemma NEt_iff:
  assumes "S \<noteq> {}" "T \<inter> dVs G \<noteq> {}"
  shows "e \<in> NEt T \<longleftrightarrow>
    (\<exists>x y. (x, y) \<in> net_graph \<and> e = (Nd x, Nd y)) \<or> (\<exists>s \<in> S. e = (Src, Nd (Vin s))) \<or>
    (\<exists>t. t \<in> T \<and> t \<in> dVs G \<and> e = (Nd (Vout t), Snk))"
proof -
  interpret N: menger_edge_network net_graph "Vin ` S" "Vout ` T"
    using assms by (rule net_network)
  show ?thesis
  proof
    assume "e \<in> NEt T"
    then show "(\<exists>x y. (x, y) \<in> net_graph \<and> e = (Nd x, Nd y)) \<or> (\<exists>s \<in> S. e = (Src, Nd (Vin s))) \<or>
      (\<exists>t. t \<in> T \<and> t \<in> dVs G \<and> e = (Nd (Vout t), Snk))"
      unfolding N.NE_def N.GE_def N.SE_def N.TE_def lift_edge_def
      using S_in_dVs by (auto simp: net_graph_dVs)
  next
    assume "(\<exists>x y. (x, y) \<in> net_graph \<and> e = (Nd x, Nd y)) \<or> (\<exists>s \<in> S. e = (Src, Nd (Vin s))) \<or>
      (\<exists>t. t \<in> T \<and> t \<in> dVs G \<and> e = (Nd (Vout t), Snk))"
    then show "e \<in> NEt T"
    proof (elim disjE exE conjE bexE)
      fix x y
      assume "(x, y) \<in> net_graph" "e = (Nd x, Nd y)"
      then show ?thesis
        unfolding N.NE_def N.GE_def lift_edge_def by (auto intro: rev_image_eqI[of "(x, y)"])
    next
      fix s
      assume "s \<in> S" "e = (Src, Nd (Vin s))"
      then show ?thesis
        unfolding N.NE_def N.SE_def using S_in_dVs net_graph_dVs(1)[of s]
        by (auto intro: rev_image_eqI[of "Vin s"])
    next
      fix t
      assume "t \<in> T" "t \<in> dVs G" "e = (Nd (Vout t), Snk)"
      then show ?thesis
        unfolding N.NE_def N.TE_def using net_graph_dVs(2)[of t]
        by (auto intro: rev_image_eqI[of "Vout t"])
    qed
  qed
qed

lemma NEt_insert:
  assumes "S \<noteq> {}" "T \<inter> dVs G \<noteq> {}" "x \<in> dVs G"
  shows "NEt (insert x T) = insert (Nd (Vout x), Snk) (NEt T)"
proof -
  have T': "insert x T \<inter> dVs G \<noteq> {}"
    using assms(3) by blast
  show ?thesis
    by (rule set_eqI)
      (unfold NEt_iff[OF assms(1) T'] insert_iff NEt_iff[OF assms(1,2)], use assms(3) in auto)
qed

text \<open>The edges of the network of the empty set without the sink. Its residual edges of the zero
flow are the forward edges.\<close>

definition res_init :: "'a snode mnode dgraph" where
  "res_init = (\<lambda>e. (Nd (fst e), Nd (snd e))) ` net_graph \<union> (\<lambda>s. (Src, Nd (Vin s))) ` S"

lemma NEt_single:
  assumes S: "S \<noteq> {}" and x: "x \<in> dVs G"
  shows "NEt {x} = insert (Nd (Vout x), Snk) res_init"
proof (rule set_eqI)
  fix e
  have x': "{x} \<inter> dVs G \<noteq> {}"
    using x by blast
  show "e \<in> NEt {x} \<longleftrightarrow> e \<in> insert (Nd (Vout x), Snk) res_init"
    unfolding NEt_iff[OF S x'] insert_iff res_init_def using x by (auto intro: rev_image_eqI)
qed

lemma sum_insert_zero:
  "\<lbrakk>finite A; f n = 0\<rbrakk> \<Longrightarrow> sum f {e \<in> insert n A. P e} = sum f {e \<in> A. P e}"
  by (rule sum.mono_neutral_right) auto

end

context gammoid
begin

text \<open>A distinct walk of the split graph that ends in some \<open>Vout t\<close> uses no edge
\<open>(Vout w, Vin w)\<close>, since the only edge leaving \<open>Vin w\<close> returns to \<open>Vout w\<close>.\<close>

lemma distinct_split_walk_net:
  assumes q: "distinct q" "vwalk_bet (split_graph G) u q (Vout t)"
  shows "set (edges_of_vwalk q) \<subseteq> net_graph"
proof
  fix e
  assume e: "e \<in> set (edges_of_vwalk q)"
  then have e_split: "e \<in> split_graph G"
    using q(2) by (auto dest: vwalk_bet_edges_in_edges)
  show "e \<in> net_graph"
  proof (rule ccontr)
    assume "e \<notin> net_graph"
    then obtain w where w: "e = (Vout w, Vin w)"
      using e_split by (auto simp: net_graph_def)
    then obtain q1 q2 where q12: "q = q1 @ [Vout w, Vin w] @ q2"
      using e edges_in_vwalk_split by fastforce
    have "q2 \<noteq> []"
      using q(2) q12 by (auto simp: vwalk_bet_def)
    then obtain y q3 where q2: "q2 = y # q3"
      by (cases q2) auto
    have "Vwalk.vwalk (split_graph G) ((q1 @ [Vout w, Vin w]) @ q2)"
      using q(2) q12 by (simp add: vwalk_bet_def)
    then have "(Vin w, y) \<in> split_graph G"
      using vwalk_append_edge[of _ "q1 @ [Vout w, Vin w]" q2] q2 by simp
    then have "y = Vout w"
      by (simp add: split_graph_edge_iff)
    then show False
      using q(1) q12 q2 by simp
  qed
qed

lemma separator_split:
  assumes sep: "edge_separator net_graph (Vin ` S) (Vout ` T) Fs"
  shows "edge_separator (split_graph G) (Vin ` S) (Vout ` T) Fs"
proof (rule edge_separatorI)
  show "Fs \<subseteq> split_graph G"
    using edge_separatorD(1)[OF sep] net_graph_subset by blast
  fix u p v
  assume u: "u \<in> Vin ` S" and v: "v \<in> Vout ` T" and p: "vwalk_bet (split_graph G) u p v"
  define q where "q = vwalk_bet_to_distinct (split_graph G) p"
  have "distinct_vwalk_bet (split_graph G) u q v"
    unfolding q_def using p by (rule vwalk_bet_to_distinct_is_distinct_vwalk_bet)
  then have qv: "vwalk_bet (split_graph G) u q v" and qd: "distinct q"
    by (auto elim: distinct_vwalk_betE)
  obtain t where t: "v = Vout t"
    using v by blast
  have q_net: "set (edges_of_vwalk q) \<subseteq> net_graph"
    using qd qv unfolding t by (rule distinct_split_walk_net)
  have "u \<noteq> v"
    using u v by auto
  have "2 \<le> length q"
  proof (rule ccontr)
    assume "\<not> 2 \<le> length q"
    then obtain w where "q = [w]"
      using qv by (cases q rule: edges_of_vwalk.cases) (auto simp: vwalk_bet_def)
    then show False
      using qv \<open>u \<noteq> v\<close> by (auto simp: vwalk_bet_def)
  qed
  then have "vwalk_bet (set (edges_of_vwalk q)) u q v"
    using qv by (intro vwalk_bet_in_its_own_edges)
  then have "vwalk_bet net_graph u q v"
    using q_net by (rule vwalk_bet_subset)
  then have q_F: "set (edges_of_vwalk q) \<inter> Fs \<noteq> {}"
    by (rule edge_separatorD(2)[OF sep u v])
  have "set (edges_of_vwalk q) \<subseteq> set (edges_of_vwalk p)"
    unfolding q_def by (rule edges_of_vwalk_bet_to_distinct_subset[OF p])
  then show "set (edges_of_vwalk p) \<inter> Fs \<noteq> {}"
    using q_F by auto
qed

end

subsection \<open>The Network of an Independent Set\<close>

locale gammoid_net = gammoid +
  fixes T :: "'a set"
  assumes S_nonempty: "S \<noteq> {}" and T_meets: "T \<inter> dVs G \<noteq> {}" and T_finite: "finite T"
begin

sublocale M: menger_edge_network net_graph "Vin ` S" "Vout ` T"
  using S_nonempty T_meets by (rule net_network)

text \<open>Cutting off the sink and the vertices \<open>Vout t\<close> leaves one unit edge per element of \<open>T\<close>.\<close>

definition "sink_cut = dVs M.NE - insert Snk (Nd ` Vout ` T)"

lemma sink_cut:
  shows "M.N.is_s_t_cut Src Snk sink_cut" and "M.N.Cap sink_cut \<le> ereal (card T)"
proof -
  show cut: "M.N.is_s_t_cut Src Snk sink_cut"
    using M.Src_Snk_in_V by (auto simp: M.N.is_s_t_cut_def sink_cut_def M.V_NE)
  have D: "M.N.Delta_plus sink_cut \<subseteq> (\<lambda>t. (Nd (Vin t), Nd (Vout t))) ` T"
  proof
    fix e
    assume "e \<in> M.N.Delta_plus sink_cut"
    then have e: "e \<in> M.NE" "fst e \<in> sink_cut" "snd e \<notin> sink_cut"
      by (auto simp: M.N.Delta_plus_def)
    have "snd e \<in> dVs M.NE"
      using e(1) by (rule dVsI'(2))
    then have snd_e: "snd e = Snk \<or> snd e \<in> Nd ` Vout ` T"
      using e(3) by (auto simp: sink_cut_def)
    from e(1) show "e \<in> (\<lambda>t. (Nd (Vin t), Nd (Vout t))) ` T"
    proof (cases rule: M.NE_cases)
      case (G a b)
      then obtain t where t: "t \<in> T" "b = Vout t"
        using snd_e by auto
      then have "a = Vin t"
        using G(1) by (auto simp: net_graph_iff)
      then show ?thesis
        using G(2) t by auto
    next
      case (S a)
      then show ?thesis
        using snd_e by auto
    next
      case (T b)
      then show ?thesis
        using e(2) by (auto simp: sink_cut_def)
    qed
  qed
  have fin_D: "finite (M.N.Delta_plus sink_cut)"
    using M.NE_finite by (auto intro: finite_subset simp: M.N.Delta_plus_def)
  have GE: "M.N.Delta_plus sink_cut \<subseteq> M.GE"
  proof
    fix e
    assume e: "e \<in> M.N.Delta_plus sink_cut"
    then have "e \<in> M.NE"
      by (simp add: M.N.Delta_plus_def)
    moreover have "fst e \<noteq> Src \<and> snd e \<noteq> Snk"
      using D e by auto
    ultimately show "e \<in> M.GE"
      using M.GE_iff_inner by blast
  qed
  have "M.N.Cap sink_cut = (\<Sum>e \<in> M.N.Delta_plus sink_cut. ereal 1)"
    unfolding M.N.Cap_def by (rule sum.cong) (use GE in \<open>auto simp: M.cap_def one_ereal_def\<close>)
  also have "\<dots> = ereal (real (card (M.N.Delta_plus sink_cut)))"
    by (simp only: sum_ereal) simp
  also have "\<dots> \<le> ereal (card T)"
  proof -
    have "card (M.N.Delta_plus sink_cut) \<le> card T"
      using card_mono[OF finite_imageI[OF T_finite] D]
        card_image_le[OF T_finite, of "\<lambda>t. (Nd (Vin t), Nd (Vout t))"] by (rule le_trans)
    then show ?thesis
      by simp
  qed
  finally show "M.N.Cap sink_cut \<le> ereal (card T)" .
qed

lemma flow_value_le:
  assumes "M.N.is_s_t_flow g Src Snk"
  shows "M.N.ex g Snk \<le> card T"
proof -
  have "ereal (M.N.ex g Snk) \<le> M.N.Cap sink_cut"
    using M.N.ex_less_cut_cap[OF M.Src_Snk_in_V M.Src_neq_Snk sink_cut(1) assms] .
  also have "\<dots> \<le> ereal (card T)"
    by (rule sink_cut(2))
  finally show ?thesis
    by simp
qed

lemma integral_max_flow:
  obtains h where "M.N.is_max_flow Src Snk h" "M.N.is_integral_flow h"
proof -
  have caps: "\<And>e. e \<in> M.NE \<Longrightarrow> M.cap e = PInfty \<or> (\<exists>r \<in> \<int>. M.cap e = ereal r)"
    by (auto simp: M.cap_def one_ereal_def)
  have "ereal (card T) < PInfty"
    by simp
  with sink_cut(2) have fin: "M.N.Cap sink_cut < PInfty"
    by (rule le_less_trans)
  obtain h where "M.N.is_max_flow Src Snk h" "M.N.is_integral_flow h"
    using M.N.integral_max_flow_exists[OF M.Src_Snk_in_V M.Src_neq_Snk caps sink_cut(1) fin] by blast
  then show ?thesis
    by (rule that)
qed

lemma flow_linked:
  assumes h: "M.N.is_s_t_flow h Src Snk" "M.N.is_integral_flow h" and le: "card T \<le> M.N.ex h Snk"
  shows "linked G S T"
proof -
  obtain P where P: "edge_linkage net_graph (Vin ` S) (Vout ` T) P" "real (card P) = M.N.ex h Snk"
    by (rule M.paths_from_flow[OF h])
  have "edge_linkage (split_graph G) (Vin ` S) (Vout ` T) P"
    using P(1) net_graph_subset by (rule edge_linkage_mono)
  then obtain T' where T': "T' \<subseteq> T" "card T' = card P" "linked G S T'"
    using split_edge_linkage_linked[of G S T P] by blast
  have "card T \<le> card T'"
    using le P(2) T'(2) by simp
  with card_mono[OF T_finite T'(1)] have "card T' = card T"
    by (rule le_antisym)
  then have eq: "T' = T"
    by (rule card_subset_eq[OF T_finite T'(1)])
  show ?thesis
    using T'(3) unfolding eq .
qed

lemma linked_le_max_flow:
  assumes h: "M.N.is_max_flow Src Snk h" and link: "linked G S T"
  shows "card T \<le> M.N.ex h Snk"
proof -
  obtain Fs where Fs: "edge_separator net_graph (Vin ` S) (Vout ` T) Fs" "real (card Fs) = M.N.ex h Snk"
    by (rule M.separator_from_max_flow[OF h])
  obtain X where X: "separator G S T X" "finite X" "card X \<le> card Fs"
    using split_edge_separator_separator[OF G_finite separator_split[OF Fs(1)]] by blast
  from link obtain p where "linkage G S T p"
    by (rule linkedE)
  then have "card T \<le> card X"
    using X(1) subset_refl X(2) by (rule linkage_card_le_separator)
  then show ?thesis
    using X(3) Fs(2) by simp
qed
text \<open>Every edge carries at most one unit: the edges at the source and the sink are the only edges
at \<open>Vin s\<close> and \<open>Vout t\<close> besides the unit edge \<open>(Vin v, Vout v)\<close>.\<close>

lemma flow_le_one:
  assumes g: "M.N.isuflow g"
    and cons: "\<And>v. \<lbrakk>v \<noteq> Src; v \<noteq> Snk\<rbrakk> \<Longrightarrow>
      sum g {e \<in> M.NE. snd e = v} = sum g {e \<in> M.NE. fst e = v}"
    and e: "e \<in> M.NE"
  shows "g e \<le> 1"
proof -
  have nonneg: "0 \<le> g d" if "d \<in> M.NE" for d
    using g that by (auto simp: M.N.isuflow_def)
  have unit_cap: "g d \<le> 1" if d: "d \<in> M.GE" for d
  proof -
    have "d \<in> M.NE"
      using d by (simp add: M.NE_def)
    then have "ereal (g d) \<le> M.cap d"
      using g by (simp add: M.N.isuflow_def)
    then show ?thesis
      using d by (simp add: M.cap_def one_ereal_def)
  qed
  have split_GE: "(Nd (Vin v), Nd (Vout v)) \<in> M.GE" if "v \<in> dVs G" for v
    unfolding M.GE_def lift_edge_def
    using that by (auto simp: net_graph_iff intro!: rev_image_eqI[of "(Vin v, Vout v)"])
  have split_NE: "(Nd (Vin v), Nd (Vout v)) \<in> M.NE" if "v \<in> dVs G" for v
    using split_GE[OF that] by (simp add: M.NE_def)
  have le_sum: "g d \<le> sum g {e \<in> M.NE. P e}" if "d \<in> M.NE" "P d" for d P
    by (rule member_le_sum) (use that nonneg M.NE_finite in auto)
  from e show ?thesis
  proof (cases rule: M.NE_cases)
    case (G x y)
    then have "e \<in> M.GE"
      unfolding M.GE_def lift_edge_def by (auto intro!: rev_image_eqI[of "(x, y)"])
    then show ?thesis
      by (rule unit_cap)
  next
    case (S a)
    then obtain s where s: "s \<in> S" "a = Vin s"
      by blast
    then have sG: "s \<in> dVs G"
      using S_in_dVs by blast
    have out: "{d \<in> M.NE. fst d = Nd (Vin s)} = {(Nd (Vin s), Nd (Vout s))}"
    proof
      show "{d \<in> M.NE. fst d = Nd (Vin s)} \<subseteq> {(Nd (Vin s), Nd (Vout s))}"
      proof
        fix d
        assume "d \<in> {d \<in> M.NE. fst d = Nd (Vin s)}"
        then have d: "d \<in> M.NE" "fst d = Nd (Vin s)"
          by auto
        from d(1) show "d \<in> {(Nd (Vin s), Nd (Vout s))}"
          by (cases rule: M.NE_cases) (use d(2) in \<open>auto simp: net_graph_iff\<close>)
      qed
      show "{(Nd (Vin s), Nd (Vout s))} \<subseteq> {d \<in> M.NE. fst d = Nd (Vin s)}"
        using split_NE[OF sG] by simp
    qed
    have "g e \<le> sum g {d \<in> M.NE. snd d = Nd (Vin s)}"
      using e S(3) s(2) by (intro le_sum) auto
    also have "\<dots> = sum g {d \<in> M.NE. fst d = Nd (Vin s)}"
      by (rule cons) auto
    also have "\<dots> = g (Nd (Vin s), Nd (Vout s))"
      unfolding out by simp
    also have "\<dots> \<le> 1"
      using split_GE[OF sG] by (rule unit_cap)
    finally show ?thesis .
  next
    case (T b)
    then obtain t where t: "t \<in> T" "b = Vout t"
      by blast
    then have tG: "t \<in> dVs G"
      using T(2) net_graph_dVs(2) by simp
    have inn: "{d \<in> M.NE. snd d = Nd (Vout t)} = {(Nd (Vin t), Nd (Vout t))}"
    proof
      show "{d \<in> M.NE. snd d = Nd (Vout t)} \<subseteq> {(Nd (Vin t), Nd (Vout t))}"
      proof
        fix d
        assume "d \<in> {d \<in> M.NE. snd d = Nd (Vout t)}"
        then have d: "d \<in> M.NE" "snd d = Nd (Vout t)"
          by auto
        from d(1) show "d \<in> {(Nd (Vin t), Nd (Vout t))}"
          by (cases rule: M.NE_cases) (use d(2) in \<open>auto simp: net_graph_iff\<close>)
      qed
      show "{(Nd (Vin t), Nd (Vout t))} \<subseteq> {d \<in> M.NE. snd d = Nd (Vout t)}"
        using split_NE[OF tG] by simp
    qed
    have "g e \<le> sum g {d \<in> M.NE. fst d = Nd (Vout t)}"
      using e T(3) t(2) by (intro le_sum) auto
    also have "\<dots> = sum g {d \<in> M.NE. snd d = Nd (Vout t)}"
      by (rule cons[symmetric]) auto
    also have "\<dots> = g (Nd (Vin t), Nd (Vout t))"
      unfolding inn by simp
    also have "\<dots> \<le> 1"
      using split_GE[OF tG] by (rule unit_cap)
    finally show ?thesis .
  qed
qed

text \<open>The unit network on the edges of the Menger network.\<close>

lemma U_unit_network: "unit_network prod.fst prod.snd Pair (\<lambda>_. 1) M.NE"
  by unfold_locales (auto simp: M.NE_finite M.NE_nonempty)

sublocale U: unit_network prod.fst prod.snd Pair "\<lambda>_. 1" M.NE
  by (rule U_unit_network)

lemma U_isuflow_iff: "U.isuflow f \<longleftrightarrow> (\<forall>e \<in> M.NE. 0 \<le> f e \<and> f e \<le> 1)"
  unfolding U.isuflow_def by (auto simp: one_ereal_def)

text \<open>The unit network and the Menger network have the same \<open>s\<close>-\<open>t\<close> flows: every edge at the source
or the sink is the only edge at its other end besides a unit edge.\<close>

lemma st_flow_iff: "U.is_s_t_flow f Src Snk \<longleftrightarrow> M.N.is_s_t_flow f Src Snk"
proof
  assume f: "U.is_s_t_flow f Src Snk"
  have "M.N.isuflow f"
  proof (rule M.N.isuflowI)
    fix e
    assume e: "e \<in> M.NE"
    have "0 \<le> f e" "f e \<le> 1"
      using f e by (auto simp: U.is_s_t_flow_def U_isuflow_iff)
    then show "ereal (f e) \<le> M.cap e" "0 \<le> f e"
      by (auto simp: M.cap_def one_ereal_def)
  qed
  then show "M.N.is_s_t_flow f Src Snk"
    using f by (simp add: U.is_s_t_flow_def M.N.is_s_t_flow_def)
next
  assume f: "M.N.is_s_t_flow f Src Snk"
  have g: "M.N.isuflow f"
    using f by (simp add: M.N.is_s_t_flow_def)
  have cons: "sum f {e \<in> M.NE. snd e = v} = sum f {e \<in> M.NE. fst e = v}"
    if v: "v \<noteq> Src" "v \<noteq> Snk" for v
  proof (cases "v \<in> dVs M.NE")
    case True
    then have "M.N.ex f v = 0"
      using f v by (simp add: M.N.is_s_t_flow_def M.V_NE)
    then show ?thesis
      by (simp add: M.ex_unfold)
  next
    case False
    have A: "{e \<in> M.NE. snd e = v} = {}" and B: "{e \<in> M.NE. fst e = v} = {}"
      using False dVsI' by blast+
    show ?thesis
      unfolding A B ..
  qed
  have "U.isuflow f"
    unfolding U_isuflow_iff
  proof
    fix e
    assume e: "e \<in> M.NE"
    show "0 \<le> f e \<and> f e \<le> 1"
      using flow_le_one[OF g cons e] g e by (simp add: M.N.isuflow_def)
  qed
  then show "U.is_s_t_flow f Src Snk"
    using f by (simp add: U.is_s_t_flow_def M.N.is_s_t_flow_def)
qed

lemma max_flow_iff: "U.is_max_flow Src Snk f \<longleftrightarrow> M.N.is_max_flow Src Snk f"
  unfolding U.is_max_flow_def M.N.is_max_flow_def st_flow_iff ..

text \<open>A flow of value \<open>card T\<close> is maximum, so the projection of its residual edges contains no walk
from the source to the sink.\<close>

lemma card_flow_max:
  assumes f: "U.is_s_t_flow f Src Snk" and val: "U.ex f Snk = card T"
  shows "U.is_max_flow Src Snk f"
  unfolding max_flow_iff
  using f val flow_value_le st_flow_iff by (auto intro: M.N.is_max_flowI)

lemma card_flow_no_walk:
  assumes f: "U.is_s_t_flow f Src Snk" and val: "U.ex f Snk = card T"
  shows "\<not> (\<exists>p. vwalk_bet (U.to_vertex_pair ` {e | e. e \<in> U.\<EE> \<and> U.rcap f e > 0}) Src p Snk)"
  using U.max_flow_iff_no_vwalk[OF f] card_flow_max[OF f val] by simp

text \<open>For a flow of value \<open>card T - 1\<close>, a walk from the source to the sink exists iff \<open>T\<close> is
linked.\<close>

lemma walk_Snk_iff_linked:
  assumes f: "U.is_s_t_flow f Src Snk" and val: "U.ex f Snk = card T - 1"
  shows "(\<exists>p. vwalk_bet (U.to_vertex_pair ` {e | e. e \<in> U.\<EE> \<and> U.rcap f e > 0}) Src p Snk)
    \<longleftrightarrow> linked G S T"
proof -
  have st: "M.N.is_s_t_flow f Src Snk"
    using f st_flow_iff by simp
  have cardT: "1 \<le> card T"
    using T_meets T_finite by (auto simp: Suc_le_eq card_gt_0_iff)
  have walk_iff: "(\<exists>p. vwalk_bet (U.to_vertex_pair ` {e | e. e \<in> U.\<EE> \<and> U.rcap f e > 0}) Src p Snk)
      \<longleftrightarrow> \<not> M.N.is_max_flow Src Snk f"
    using U.max_flow_iff_no_vwalk[OF f] max_flow_iff by simp
  show ?thesis
    unfolding walk_iff
  proof
    assume "\<not> M.N.is_max_flow Src Snk f"
    then obtain g where g: "M.N.is_s_t_flow g Src Snk" "M.N.ex f Snk < M.N.ex g Snk"
      using st by (auto simp: M.N.is_max_flow_def not_le)
    obtain h where h: "M.N.is_max_flow Src Snk h" "M.N.is_integral_flow h"
      by (rule integral_max_flow)
    have hst: "M.N.is_s_t_flow h Src Snk"
      using h(1) by (simp add: M.N.is_max_flow_def)
    have "M.N.ex g Snk \<le> M.N.ex h Snk"
      using h(1) g(1) by (simp add: M.N.is_max_flow_def)
    then have lt: "real (card T - 1) < M.N.ex h Snk"
      using g(2) val by simp
    obtain k where k: "M.N.ex h Snk = of_int k"
      using M.N.integral_ex[OF h(2)] by (auto elim: Ints_cases)
    have "real_of_int (int (card T - 1)) < real_of_int k"
      using lt k by simp
    then have "int (card T - 1) < k"
      by (simp only: of_int_less_iff)
    moreover have "int (card T - 1) = int (card T) - 1"
      using cardT by simp
    ultimately have "int (card T) \<le> k"
      by linarith
    then have "real_of_int (int (card T)) \<le> real_of_int k"
      by (simp only: of_int_le_iff)
    then have "card T \<le> M.N.ex h Snk"
      using k by simp
    then show "linked G S T"
      by (rule flow_linked[OF hst h(2)])
  next
    assume linkT: "linked G S T"
    show "\<not> M.N.is_max_flow Src Snk f"
    proof
      assume "M.N.is_max_flow Src Snk f"
      then have "card T \<le> M.N.ex f Snk"
        using linkT by (rule linked_le_max_flow)
      then show False
        using val cardT by simp
    qed
  qed
qed

text \<open>The residual edges stored for \<open>T\<close>: those of a maximum unit flow that vanishes outside the
network.\<close>

definition ustate :: "('a snode mnode \<times> 'a snode mnode) Redge set \<Rightarrow> bool" where
  "ustate RS \<longleftrightarrow> (\<exists>f. U.is_s_t_flow f Src Snk \<and> U.unit_flow f \<and> U.ex f Snk = card T \<and>
     (\<forall>e. e \<notin> M.NE \<longrightarrow> f e = 0) \<and> RS = {e | e. e \<in> U.\<EE> \<and> U.rcap f e > 0})"

lemma res_vertex:
  assumes RS: "RS \<subseteq> U.\<EE>" and v: "v \<in> dVs (U.to_vertex_pair ` RS)"
  shows "v \<in> dVs M.NE"
proof -
  obtain r where r: "r \<in> RS" "v = prod.fst (U.to_vertex_pair r) \<or> v = prod.snd (U.to_vertex_pair r)"
    using v by (auto simp: dVs_eq)
  have "U.oedge r \<in> M.NE"
    using RS r(1) U.o_edge_res by blast
  then show ?thesis
    using r(2) dVsI'[of "U.oedge r" M.NE] by (cases r) (auto simp: M.make_pair_id)
qed

end

subsection \<open>The Network as a Total Function of the Sink Set\<close>

context gammoid
begin

text \<open>The edges \<open>NEt T\<close> of the Menger network are only specified when \<open>S\<close> is nonempty and \<open>T\<close> meets
the graph. The oracle also passes through the degenerate states, so it works with the following
edge set, which agrees with \<open>NEt T\<close> whenever the latter is specified.\<close>

definition net :: "'a set \<Rightarrow> 'a snode mnode dgraph" where
  "net T = res_init \<union> (\<lambda>t. (Nd (Vout t), Snk)) ` (T \<inter> dVs G)"

lemma net_iff:
  "e \<in> net T \<longleftrightarrow>
    (\<exists>x y. (x, y) \<in> net_graph \<and> e = (Nd x, Nd y)) \<or> (\<exists>s \<in> S. e = (Src, Nd (Vin s))) \<or>
    (\<exists>t. t \<in> T \<and> t \<in> dVs G \<and> e = (Nd (Vout t), Snk))"
  by (auto simp: net_def res_init_def intro: rev_image_eqI)

lemma NEt_net:
  assumes "S \<noteq> {}" "T \<inter> dVs G \<noteq> {}"
  shows "NEt T = net T"
  by (rule set_eqI) (simp only: NEt_iff[OF assms] net_iff)

lemma net_insert: "x \<in> dVs G \<Longrightarrow> net (insert x T) = insert (Nd (Vout x), Snk) (net T)"
  by (auto simp: net_def)

lemma net_remove: "net (T - {x}) = net T - {(Nd (Vout x), Snk)}"
  by (auto simp: net_def res_init_def)

lemma net_mono: "T \<subseteq> T' \<Longrightarrow> net T \<subseteq> net T'"
  by (auto simp: net_def)

lemma finite_net: "finite (net T)"
  using finite_net_graph finite_subset[OF S_in_dVs dVs_finite] dVs_finite
  by (simp add: net_def res_init_def)

text \<open>No two nodes are joined in both directions.\<close>

lemma net_antisym: "(a, b) \<in> net T \<Longrightarrow> (b, a) \<notin> net T'"
  by (auto simp: net_iff net_graph_iff)

lemma node_arc_net: "x \<in> dVs G \<Longrightarrow> (Nd (Vin x), Nd (Vout x)) \<in> net T"
  by (simp add: net_iff net_graph_iff)

lemma Snk_out: "{e \<in> net T. fst e = Snk} = {}" and Src_in: "{e \<in> net T. snd e = Src} = {}"
  by (auto simp: net_iff)

lemma net_unit_network:
  assumes "G \<noteq> {}"
  shows "unit_network prod.fst prod.snd Pair (\<lambda>_. 1) (net T)"
proof -
  obtain x where "x \<in> dVs G"
    using assms by (auto simp: dVs_def)
  then have "net T \<noteq> {}"
    using node_arc_net by blast
  then show ?thesis
    using finite_net by unfold_locales auto
qed

subsection \<open>Unit Flows of the Network\<close>

text \<open>Excess, residual edges, residual node pairs and augmentation in the network of \<open>T\<close>. Only
\<open>nres_iff\<close>, \<open>nresE_cases\<close>, \<open>EE_net_iff\<close>, \<open>nresE_iff\<close>, \<open>ntvp_simps\<close> and \<open>nex_unfold\<close> look
into the definitions of the flow library.\<close>

abbreviation "nex T \<equiv> flow_network_spec.ex prod.fst prod.snd (net T)"

abbreviation "ntvp \<equiv> flow_network_spec.to_vertex_pair prod.fst prod.snd"

abbreviation "nresE T f \<equiv>
  {e | e. e \<in> flow_network_spec.\<EE> (net T) \<and> flow_network_spec.rcap (\<lambda>_. 1) f e > 0}"

abbreviation "nres T f \<equiv> ntvp ` nresE T f"

abbreviation "naug f rs \<equiv> flow_network_spec.augment_edges f 1 rs"

lemmas nres_simps = flow_network_spec.\<EE>_def multigraph_spec.make_pair_def
  flow_network_spec.rcap.simps flow_network_spec.to_vertex_pair.simps prod.swap_def

lemma nres_iff:
  "(u, v) \<in> nres T f \<longleftrightarrow> ((u, v) \<in> net T \<and> f (u, v) < 1) \<or> ((v, u) \<in> net T \<and> 0 < f (v, u))"
proof
  assume "(u, v) \<in> nres T f"
  then obtain r where r: "r \<in> flow_network_spec.\<EE> (net T)" "0 < flow_network_spec.rcap (\<lambda>_. 1) f r"
    "(u, v) = flow_network_spec.to_vertex_pair prod.fst prod.snd r"
    by (rule imageE) (simp only: mem_Collect_eq, blast)
  then show "((u, v) \<in> net T \<and> f (u, v) < 1) \<or> ((v, u) \<in> net T \<and> 0 < f (v, u))"
    by (cases r) (simp_all add: nres_simps one_ereal_def, force+)
next
  assume "((u, v) \<in> net T \<and> f (u, v) < 1) \<or> ((v, u) \<in> net T \<and> 0 < f (v, u))"
  then show "(u, v) \<in> nres T f"
  proof
    assume a: "(u, v) \<in> net T \<and> f (u, v) < 1"
    show ?thesis
      by (rule image_eqI[of _ _ "F (u, v)"]) (use a in \<open>simp_all add: nres_simps one_ereal_def\<close>)
  next
    assume a: "(v, u) \<in> net T \<and> 0 < f (v, u)"
    show ?thesis
      by (rule image_eqI[of _ _ "B (v, u)"]) (use a in \<open>simp_all add: nres_simps\<close>)
  qed
qed

lemma nex_unfold: "nex T f v = sum f {e \<in> net T. snd e = v} - sum f {e \<in> net T. fst e = v}"
  by (simp add: flow_network_spec.ex_def multigraph_spec.delta_minus_def multigraph_spec.delta_plus_def)

lemma nex_cong:
  assumes "net T \<subseteq> net T'" "\<And>e. e \<in> net T' - net T \<Longrightarrow> f e = 0"
  shows "nex T' f v = nex T f v"
proof -
  have "sum f {e \<in> net T'. P e} = sum f {e \<in> net T. P e}" for P
    using assms finite_net by (intro sum.mono_neutral_right) auto
  then show ?thesis
    by (simp add: nex_unfold)
qed

lemma Src_nres: "Src \<in> dVs (nres T f) \<Longrightarrow> S \<noteq> {}"
  by (erule in_dVsE(1)) (simp_all only: nres_iff, auto simp: net_iff)

lemma Snk_nres: "Snk \<in> dVs (nres T f) \<Longrightarrow> T \<inter> dVs G \<noteq> {}"
  by (erule in_dVsE(1)) (simp_all only: nres_iff, auto simp: net_iff)

text \<open>The state of the oracle for a set \<open>T\<close>: a unit flow of the network of \<open>T\<close> from the source to
the sink, and a maximum one. The value of the flow is the excess at the sink. The flow conserves at
all other nodes, and the source loses exactly the value; this also holds in the degenerate cases,
where \<open>Src\<close> or \<open>Snk\<close> is not a node of the network.\<close>

definition uflow :: "'a set \<Rightarrow> ('a snode mnode \<times> 'a snode mnode \<Rightarrow> real) \<Rightarrow> bool" where
  "uflow T f \<longleftrightarrow> (\<forall>e. e \<notin> net T \<longrightarrow> f e = 0) \<and> (\<forall>e. f e = 0 \<or> f e = 1) \<and>
     (\<forall>v. v \<noteq> Src \<longrightarrow> v \<noteq> Snk \<longrightarrow> nex T f v = 0) \<and> nex T f Src + nex T f Snk = 0"

definition mstate :: "'a set \<Rightarrow> ('a snode mnode \<times> 'a snode mnode \<Rightarrow> real) \<Rightarrow> bool" where
  "mstate T f \<longleftrightarrow> uflow T f \<and> \<not> (\<exists>p. vwalk_bet (nres T f) Src p Snk)"

lemma mstate_empty: "mstate {} (\<lambda>_. 0)"
proof -
  have "\<not> vwalk_bet (nres {} (\<lambda>_. 0)) Src p Snk" for p
    using Snk_nres[of "{}" "\<lambda>_. 0"] vwalk_bet_endpoints(2)[of "nres {} (\<lambda>_. 0)" Src p Snk] by blast
  then show ?thesis
    unfolding mstate_def uflow_def nex_unfold by simp
qed

lemma uflow_range: "uflow T f \<Longrightarrow> 0 \<le> f e \<and> f e \<le> 1"
  unfolding uflow_def by (metis order.refl zero_le_one)

lemma uflow_val_nonneg: "uflow T f \<Longrightarrow> 0 \<le> nex T f Snk"
  using uflow_range by (simp add: nex_unfold Snk_out sum_nonneg)

lemma uflow_val_le:
  assumes f: "uflow T f" and T: "T \<subseteq> dVs G"
  shows "nex T f Snk \<le> card T"
proof -
  let ?I = "{e \<in> net T. snd e = Snk}"
  have I: "?I \<subseteq> (\<lambda>t. (Nd (Vout t), Snk)) ` T"
    by (auto simp: net_iff)
  have finT: "finite T"
    using T dVs_finite by (rule finite_subset)
  have "card ?I \<le> card T"
    using card_mono[OF finite_imageI[OF finT] I] card_image_le[OF finT, of "\<lambda>t. (Nd (Vout t), Snk)"]
    by (rule le_trans)
  moreover have "sum f ?I \<le> of_nat (card ?I) * 1"
    using uflow_range[OF f] by (intro sum_bounded_above) auto
  ultimately show ?thesis
    by (simp add: nex_unfold Snk_out)
qed

lemma net_G: "e \<in> net T \<Longrightarrow> G \<noteq> {}"
  using S_in_dVs by (auto simp: net_iff net_graph_iff dVs_def)

lemma V_net: "multigraph_spec.make_pair prod.fst prod.snd ` net T = net T"
  by (simp add: multigraph_spec.make_pair_def)

lemma nex_outside:
  assumes "v \<notin> dVs (net T)"
  shows "nex T h v = 0"
proof -
  have I: "{e \<in> net T. snd e = v} = {}" and O: "{e \<in> net T. fst e = v} = {}"
    using assms by (auto dest: dVsI')
  show ?thesis
    unfolding nex_unfold I O by simp
qed

lemma nres_net: "(u, v) \<in> nres T f \<Longrightarrow> (u, v) \<in> net T \<or> (v, u) \<in> net T"
  by (simp only: nres_iff) blast

lemma nres_G:
  assumes "u \<in> dVs (nres T f)"
  shows "G \<noteq> {}"
proof -
  obtain a b where "(a, b) \<in> nres T f"
    using assms by (rule in_dVsE(1)) blast+
  then show ?thesis
    using nres_net net_G by blast
qed

lemma dVs_nres:
  assumes "u \<in> dVs (nres T f)"
  shows "u \<in> dVs (net T)"
proof -
  obtain w where "(u, w) \<in> nres T f \<or> (w, u) \<in> nres T f"
    using assms by (rule in_dVsE(1)) blast+
  then have "(u, w) \<in> net T \<or> (w, u) \<in> net T"
    using nres_net by blast
  then show ?thesis
    by blast
qed

text \<open>A residual edge is determined by its node pair.\<close>

lemma nresE_cases:
  assumes "r \<in> nresE T f" "ntvp r = (u, v)"
  shows "(r = F (u, v) \<and> (u, v) \<in> net T \<and> f (u, v) < 1) \<or>
    (r = B (v, u) \<and> (v, u) \<in> net T \<and> 0 < f (v, u))"
  using assms by (cases r) (simp_all add: nres_simps one_ereal_def, force+)

text \<open>Residual edges by their kind.\<close>

lemma EE_net_iff:
  "r \<in> flow_network_spec.\<EE> (net T) \<longleftrightarrow> (case r of F e \<Rightarrow> e \<in> net T | B e \<Rightarrow> e \<in> net T)"
  by (cases r) (auto simp: nres_simps)

lemma nresE_iff:
  "r \<in> nresE T f \<longleftrightarrow> (case r of F e \<Rightarrow> e \<in> net T \<and> f e < 1 | B e \<Rightarrow> e \<in> net T \<and> 0 < f e)"
  by (cases r) (auto simp: nres_simps one_ereal_def)

lemma ntvp_simps: "ntvp (F e) = e" "ntvp (B e) = prod.swap e"
  by (simp_all add: nres_simps)

lemma nres_lift:
  assumes "vwalk_bet (nres T f) u p v"
  obtains rs where "map ntvp rs = edges_of_vwalk p" "set rs \<subseteq> nresE T f"
  using list_in_image_map[OF vwalk_bet_edges_in_edges[OF assms]] by blast

lemma linked_S_nonempty:
  assumes "linked G S T" "T \<noteq> {}"
  shows "S \<noteq> {}"
proof -
  obtain t where t: "t \<in> T"
    using assms(2) by blast
  from assms(1) obtain p where "linkage G S T p"
    by (rule linkedE)
  then have "hd (p t) \<in> S"
    using t by (rule linkageD(1))
  then show ?thesis
    by blast
qed

end

subsection \<open>Unit Flows of Non-Degenerate Networks\<close>

context gammoid_net
begin

lemma NE_net: "M.NE = net T"
  by (rule NEt_net[OF S_nonempty T_meets])

lemma U_nres: "U.to_vertex_pair ` {e | e. e \<in> U.\<EE> \<and> U.rcap f e > 0} = nres T f"
  unfolding NE_net ..

lemma U_ex: "U.ex f v = nex T f v"
  unfolding NE_net ..

lemma uflow_U:
  assumes f: "uflow T f"
  shows "U.is_s_t_flow f Src Snk" "U.unit_flow f"
proof -
  have vals: "f e = 0 \<or> f e = 1" for e
    using f unfolding uflow_def by blast
  have uf: "U.isuflow f"
    unfolding U_isuflow_iff using vals by (metis order.refl zero_le_one)
  have "nex T f Src \<le> 0"
    using f uflow_val_nonneg[OF f] by (simp add: uflow_def)
  then show "U.is_s_t_flow f Src Snk"
    by (intro U.is_s_t_flowI) (use uf f M.Src_Snk_in_V M.Src_neq_Snk in \<open>auto simp: uflow_def NE_net\<close>)
  have "\<exists>n::int. f e = real_of_int n" for e
    using vals[of e] by (metis of_int_0 of_int_1)
  then show "U.unit_flow f"
    using uf by (simp add: U.is_integral_flow_def)
qed

lemma mstate_max:
  assumes "mstate T f"
  shows "M.N.is_max_flow Src Snk f"
  using assms U.max_flow_iff_no_vwalk[OF uflow_U(1)] max_flow_iff
  unfolding mstate_def U_nres by blast

end

subsection \<open>Walks, and Flows of Unit Shape\<close>

text \<open>A set of node pairs has unit shape if every node other than the source has at most one
outgoing pair, and every node other than the sink at most one incoming pair. The support of a unit
flow has unit shape, which lets implementations store a flow by successors and predecessors.\<close>

definition unit_shape :: "('a mnode \<times> 'a mnode) set \<Rightarrow> bool" where
  "unit_shape P \<longleftrightarrow> (\<forall>u v w. (u, v) \<in> P \<longrightarrow> (u, w) \<in> P \<longrightarrow> u \<noteq> Src \<longrightarrow> v = w) \<and>
     (\<forall>u v w. (v, u) \<in> P \<longrightarrow> (w, u) \<in> P \<longrightarrow> u \<noteq> Snk \<longrightarrow> v = w)"

lemma unit_shape_mono: "\<lbrakk>unit_shape P'; P \<subseteq> P'\<rbrakk> \<Longrightarrow> unit_shape P"
  unfolding unit_shape_def by blast

subsection \<open>The Operations of the Oracle on the Abstract State\<close>

context gammoid
begin

text \<open>Independence of the stored set.\<close>

lemma mstate_indep:
  assumes T: "T \<subseteq> dVs G" and f: "mstate T f"
  shows "gammoid_indep T \<longleftrightarrow> nex T f Snk = card T"
proof (cases "T = {}")
  case True
  have I: "{e \<in> net T. snd e = Snk} = {}"
    using True by (auto simp: net_iff)
  have "nex T f Snk = 0"
    unfolding nex_unfold Snk_out I by simp
  then show ?thesis
    using True by (simp add: gammoid_indep_def linked_empty)
next
  case Tne: False
  have finT: "finite T"
    using T dVs_finite by (rule finite_subset)
  show ?thesis
  proof (cases "S = {}")
    case True
    have O: "{e \<in> net T. fst e = Src} = {}"
      unfolding net_iff using True by auto
    have "nex T f Src = 0"
      unfolding nex_unfold Src_in O by simp
    then have "nex T f Snk = 0"
      using f by (simp add: mstate_def uflow_def)
    moreover have "card T \<noteq> 0"
      using Tne finT by simp
    moreover have "\<not> gammoid_indep T"
      unfolding gammoid_indep_def using linked_S_nonempty[of T] True Tne by blast
    ultimately show ?thesis
      by simp
  next
    case False
    interpret N: gammoid_net G S T
      using False Tne T finT by unfold_locales auto
    have max: "N.M.N.is_max_flow Src Snk f"
      by (rule N.mstate_max[OF f])
    have st: "N.M.N.is_s_t_flow f Src Snk"
      using max by (simp add: N.M.N.is_max_flow_def)
    have int: "N.M.N.is_integral_flow f"
      using N.uflow_U(2) f by (simp add: mstate_def)
    show ?thesis
    proof
      assume "gammoid_indep T"
      then have "card T \<le> N.U.ex f Snk"
        using N.linked_le_max_flow[OF max] by (simp add: gammoid_indep_def)
      then show "nex T f Snk = card T"
        using N.flow_value_le[OF st] by (simp add: N.U_ex)
    next
      assume "nex T f Snk = card T"
      then show "gammoid_indep T"
        using N.flow_linked[OF st int] by (simp add: gammoid_indep_def N.U_ex)
    qed
  qed
qed

text \<open>Inserting an element keeps the flow; the edge into the sink becomes residual.\<close>

lemma uflow_insert:
  assumes f: "uflow T f" and x: "x \<in> dVs G" "x \<notin> T"
  shows "nex (insert x T) f v = nex T f v" "uflow (insert x T) f"
    "nres (insert x T) f = insert (Nd (Vout x), Snk) (nres T f)"
proof -
  let ?a = "(Nd (Vout x), Snk)"
  have a: "?a \<notin> net T"
    using x(2) by (simp add: net_iff)
  then have fa: "f ?a = 0"
    using f by (simp add: uflow_def)
  have N: "net (insert x T) = insert ?a (net T)"
    by (rule net_insert[OF x(1)])
  show ex: "nex (insert x T) f v = nex T f v" for v
    using fa by (intro nex_cong) (auto simp: N)
  have "\<forall>e. e \<notin> net (insert x T) \<longrightarrow> f e = 0"
    using f unfolding N uflow_def by blast
  then show "uflow (insert x T) f"
    using f unfolding uflow_def ex by blast
  show "nres (insert x T) f = insert ?a (nres T f)"
    by (rule set_eqI, simp only: split_paired_all nres_iff insert_iff, simp only: N insert_iff)
      (use fa a net_antisym[of _ _ T] in auto)
qed

text \<open>The insertion query: \<open>insert y T\<close> is independent iff \<open>T\<close> is and the source reaches \<open>y\<close>.\<close>

lemma mstate_query:
  assumes T: "T \<subseteq> dVs G" and f: "mstate T f" and y: "y \<in> dVs G" "y \<notin> T"
  shows "gammoid_indep (insert y T) \<longleftrightarrow>
    nex T f Snk = card T \<and> (\<exists>p. vwalk_bet (nres T f) Src p (Nd (Vout y)))"
proof (cases "S = {}")
  case True
  have "\<not> vwalk_bet (nres T f) Src p (Nd (Vout y))" for p
    using Src_nres[of T f] vwalk_bet_endpoints(1)[of "nres T f" Src p] True by blast
  moreover have "\<not> gammoid_indep (insert y T)"
    unfolding gammoid_indep_def using linked_S_nonempty[of "insert y T"] True by blast
  ultimately show ?thesis
    by blast
next
  case False
  let ?T = "insert y T"
  let ?a = "(Nd (Vout y), Snk)"
  have u: "uflow T f" and no: "\<not> (\<exists>p. vwalk_bet (nres T f) Src p Snk)"
    using f by (simp_all add: mstate_def)
  have finT: "finite T"
    using T dVs_finite by (rule finite_subset)
  interpret N: gammoid_net G S ?T
    using False y finT by unfold_locales auto
  show ?thesis
  proof (cases "nex T f Snk = card T")
    case True
    have st: "N.U.is_s_t_flow f Src Snk"
      by (rule N.uflow_U(1)[OF uflow_insert(2)[OF u y]])
    have val: "N.U.ex f Snk = card ?T - 1"
      unfolding N.U_ex uflow_insert(1)[OF u y] using True y(2) finT by simp
    have "linked G S ?T \<longleftrightarrow> (\<exists>p. vwalk_bet (insert ?a (nres T f)) Src p Snk)"
      using N.walk_Snk_iff_linked[OF st val, symmetric] unfolding N.U_nres uflow_insert(3)[OF u y] .
    also have "\<dots> \<longleftrightarrow> (\<exists>p. vwalk_bet (nres T f) Src p (Nd (Vout y)))"
      by (rule walk_insert_target[OF no]) simp_all
    finally show ?thesis
      using True by (simp add: gammoid_indep_def)
  next
    case False
    then have "\<not> gammoid_indep T"
      using mstate_indep[OF T f] by simp
    then have "\<not> gammoid_indep ?T"
      unfolding gammoid_indep_def using linked_subset[of G S ?T T] by blast
    then show ?thesis
      using False by simp
  qed
qed

text \<open>Augmenting along a distinct residual walk keeps a unit flow and moves one unit of excess from
the end of the walk to its start.\<close>

lemma augment_net:
  assumes f: "\<forall>e. e \<notin> net T \<longrightarrow> f e = 0" "\<forall>e. f e = 0 \<or> f e = 1"
    and p: "distinct p" "vwalk_bet (nres T f) s p t" "s \<noteq> t"
    and rs: "map ntvp rs = edges_of_vwalk p" "set rs \<subseteq> nresE T f"
  shows "\<forall>e. e \<notin> net T \<longrightarrow> naug f rs e = 0" "\<forall>e. naug f rs e = 0 \<or> naug f rs e = 1"
    "nex T (naug f rs) v =
       (if v = s then nex T f v - 1 else if v = t then nex T f v + 1 else nex T f v)"
proof -
  interpret U: unit_network prod.fst prod.snd Pair "\<lambda>_. 1" "net T"
    by (rule net_unit_network[OF nres_G[OF vwalk_bet_endpoints(1)[OF p(2)]]])
  have r: "0 \<le> f e \<and> f e \<le> 1" for e
    using f(2) by (metis order.refl zero_le_one)
  have uf: "U.isuflow f"
    using r by (intro U.isuflowI) (auto simp: one_ereal_def)
  have "\<exists>n::int. f e = real_of_int n" for e
    using f(2) by (metis of_int_0 of_int_1)
  then have int: "U.is_integral_flow f"
    by (simp add: U.is_integral_flow_def)
  have bf: "U.isbflow f (\<lambda>v. - U.ex f v)"
    using uf by (intro U.isbflowI) simp_all
  note aug = U.augment_unit_walk[OF bf conjI[OF uf int] p rs]
  show zero: "\<forall>e. e \<notin> net T \<longrightarrow> naug f rs e = 0"
    using aug(4) f(1) by simp
  show "\<forall>e. naug f rs e = 0 \<or> naug f rs e = 1"
    using U.unit_flow_values[OF aug(2)] zero by blast
  have V: "U.\<V> = dVs (net T)"
    by (simp only: V_net)
  have st: "s \<in> dVs (net T)" "t \<in> dVs (net T)"
    using dVs_nres vwalk_bet_endpoints[OF p(2)] by blast+
  show "nex T (naug f rs) v =
       (if v = s then nex T f v - 1 else if v = t then nex T f v + 1 else nex T f v)"
  proof (cases "v \<in> dVs (net T)")
    case True
    have "- nex T (naug f rs) v =
        (if v = s then - nex T f v + 1 else if v = t then - nex T f v - 1 else - nex T f v)"
      using aug(1) by (rule U.isbflowE) (simp add: V True)
    then show ?thesis
      using p(3) by (auto split: if_splits)
  next
    case False
    then show ?thesis
      using st nex_outside[OF False] by auto
  qed
qed

text \<open>Restoring maximality: augmenting from the source to the sink raises the value by one.\<close>

lemma uflow_augment:
  assumes f: "uflow T f" and p: "distinct p" "vwalk_bet (nres T f) Src p Snk"
    and rs: "map ntvp rs = edges_of_vwalk p" "set rs \<subseteq> nresE T f"
  shows "uflow T (naug f rs)" "nex T (naug f rs) Snk = nex T f Snk + 1"
proof -
  have f': "\<forall>e. e \<notin> net T \<longrightarrow> f e = 0" "\<forall>e. f e = 0 \<or> f e = 1"
    using f by (simp_all add: uflow_def)
  note a = augment_net[OF f' p _ rs, simplified]
  show "nex T (naug f rs) Snk = nex T f Snk + 1"
    using a(3)[of Snk] by simp
  show "uflow T (naug f rs)"
    using a f unfolding uflow_def by auto
qed

text \<open>Deletion. If the edge of \<open>x\<close> into the sink carries no flow, the flow is kept. Otherwise this
edge is cancelled, which leaves one unit of excess at \<open>Vout x\<close>; it is returned to the source along
a residual walk, which exists by @{thm [source] flow_network.neg_balance_resreach}.\<close>

lemma uflow_delete_free:
  assumes f: "uflow T f" and fa: "f (Nd (Vout x), Snk) = 0"
  shows "nex (T - {x}) f v = nex T f v" "uflow (T - {x}) f"
proof -
  have N: "net (T - {x}) = net T - {(Nd (Vout x), Snk)}"
    by (rule net_remove)
  show ex: "nex (T - {x}) f v = nex T f v" for v
    by (rule nex_cong[symmetric]) (use fa in \<open>auto simp: N\<close>)
  have "f e = 0" if "e \<notin> net (T - {x})" for e
    using f fa that unfolding N uflow_def by blast
  then show "uflow (T - {x}) f"
    using f unfolding uflow_def ex by blast
qed

lemma delete_cancel_walk:
  assumes f: "uflow T f" and x: "x \<in> T" "x \<in> dVs G" and fa: "f (Nd (Vout x), Snk) \<noteq> 0"
  shows "vwalk_bet (nres T f) Snk [Snk, Nd (Vout x)] (Nd (Vout x))"
proof -
  have "f (Nd (Vout x), Snk) = 1"
    using f fa unfolding uflow_def by blast
  moreover have "(Nd (Vout x), Snk) \<in> net T"
    using x by (simp add: net_iff)
  ultimately have "(Snk, Nd (Vout x)) \<in> nres T f"
    by (simp only: nres_iff) simp
  then show ?thesis
    by (rule edges_are_vwalk_bet)
qed

lemma delete_cancel:
  assumes f: "uflow T f" and x: "x \<in> T" "x \<in> dVs G" and fa: "f (Nd (Vout x), Snk) \<noteq> 0"
    and rs: "map ntvp rs = [(Snk, Nd (Vout x))]" "set rs \<subseteq> nresE T f"
  defines "g \<equiv> naug f rs"
  shows "g = f((Nd (Vout x), Snk) := 0)"
    "\<forall>e. e \<notin> net (T - {x}) \<longrightarrow> g e = 0" "\<forall>e. g e = 0 \<or> g e = 1"
    "nex (T - {x}) g v =
       (if v = Snk then nex T f Snk - 1 else if v = Nd (Vout x) then 1 else nex T f v)"
proof -
  let ?a = "(Nd (Vout x), Snk)"
  have f': "\<forall>e. e \<notin> net T \<longrightarrow> f e = 0" "\<forall>e. f e = 0 \<or> f e = 1"
    and cons: "\<And>v. \<lbrakk>v \<noteq> Src; v \<noteq> Snk\<rbrakk> \<Longrightarrow> nex T f v = 0"
    using f by (simp_all add: uflow_def)
  have fa1: "f ?a = 1"
    using f'(2) fa by blast
  have p: "distinct [Snk, Nd (Vout x)]" "Snk \<noteq> Nd (Vout x)"
    by simp_all
  have ew: "edges_of_vwalk [Snk, Nd (Vout x)] = [(Snk, Nd (Vout x))]"
    by simp
  note a = augment_net[OF f' p(1) delete_cancel_walk[OF f x fa] p(2) rs(1)[folded ew] rs(2),
      folded g_def]
  obtain r where r: "rs = [r]" "ntvp r = (Snk, Nd (Vout x))" "r \<in> nresE T f"
    using rs by (cases rs) auto
  have "r = B ?a"
    using nresE_cases[OF r(3,2)] Snk_out[of T] by auto
  then show g: "g = f(?a := 0)"
    using fa1 unfolding g_def r(1) by (auto simp: flow_network_spec.augment_edges_distinct)
  then have ga: "g ?a = 0"
    by simp
  have N: "net (T - {x}) = net T - {?a}"
    by (rule net_remove)
  show "\<forall>e. e \<notin> net (T - {x}) \<longrightarrow> g e = 0"
    using a(1) ga unfolding N by blast
  show "\<forall>e. g e = 0 \<or> g e = 1"
    by (rule a(2))
  have "nex (T - {x}) g v = nex T g v"
    by (rule nex_cong[symmetric]) (use ga in \<open>auto simp: N\<close>)
  then show "nex (T - {x}) g v =
       (if v = Snk then nex T f Snk - 1 else if v = Nd (Vout x) then 1 else nex T f v)"
    using a(3)[of v] cons[of "Nd (Vout x)"] by simp
qed

lemma excess_walk:
  assumes g: "\<forall>e. e \<notin> net T \<longrightarrow> g e = 0" "\<forall>e. g e = 0 \<or> g e = 1"
    and ex: "\<And>v. \<lbrakk>v \<noteq> Src; v \<noteq> Snk; v \<noteq> w\<rbrakk> \<Longrightarrow> nex T g v = 0" "nex T g w = 1"
    and w: "w \<in> dVs (net T)" "w \<noteq> Src" "w \<noteq> Snk"
  obtains p where "distinct p" "vwalk_bet (nres T g) w p Src"
proof -
  obtain e where "e \<in> net T"
    using w(1) by (auto simp: dVs_eq)
  interpret U: unit_network prod.fst prod.snd Pair "\<lambda>_. 1" "net T"
    by (rule net_unit_network[OF net_G[OF \<open>e \<in> net T\<close>]])
  have r: "0 \<le> g e \<and> g e \<le> 1" for e
    using g(2) by (metis order.refl zero_le_one)
  have uf: "U.isuflow g"
    using r by (intro U.isuflowI) (auto simp: one_ereal_def)
  have bf: "U.isbflow g (\<lambda>v. - U.ex g v)"
    using uf by (intro U.isbflowI) simp_all
  have V: "U.\<V> = dVs (net T)"
    by (simp only: V_net)
  have "0 \<le> nex T g Snk"
    using r by (simp add: nex_unfold Snk_out sum_nonneg)
  then have nn: "0 \<le> nex T g v" if "v \<noteq> Src" "v \<noteq> w" for v
    using ex(1)[OF that(1) _ that(2)] by (cases "v = Snk") auto
  have "U.resreach g w Src"
    using ex(2) w nn by (intro U.neg_balance_resreach[OF bf]) (auto simp: V)
  then obtain q where "vwalk_bet (nres T g) w q Src"
    using U.resreach_iff_vwalk[of w Src g] w(2) by blast
  then have "distinct_vwalk_bet (nres T g) w (vwalk_bet_to_distinct (nres T g) q) Src"
    by (rule vwalk_bet_to_distinct_is_distinct_vwalk_bet)
  then show ?thesis
    by (blast intro: that dest: distinct_vwalk_betD)
qed

lemma delete_return:
  assumes g: "\<forall>e. e \<notin> net T \<longrightarrow> g e = 0" "\<forall>e. g e = 0 \<or> g e = 1"
    and ex: "\<And>v. \<lbrakk>v \<noteq> Src; v \<noteq> Snk; v \<noteq> w\<rbrakk> \<Longrightarrow> nex T g v = 0" "nex T g w = 1"
      "nex T g Src + nex T g Snk = -1"
    and w: "w \<noteq> Src" "w \<noteq> Snk"
    and p: "distinct p" "vwalk_bet (nres T g) w p Src"
    and rs: "map ntvp rs = edges_of_vwalk p" "set rs \<subseteq> nresE T g"
  shows "uflow T (naug g rs)" "nex T (naug g rs) Snk = nex T g Snk"
proof -
  note a = augment_net[OF g p w(1) rs]
  show "nex T (naug g rs) Snk = nex T g Snk"
    using a(3)[of Snk] w by simp
  have "nex T (naug g rs) v = 0" if "v \<noteq> Src" "v \<noteq> Snk" for v
    using a(3)[of v] ex(1)[of v] ex(2) that by (cases "v = w") auto
  moreover have "nex T (naug g rs) Src + nex T (naug g rs) Snk = 0"
    using a(3)[of Src] a(3)[of Snk] ex(3) w by simp
  ultimately show "uflow T (naug g rs)"
    using a(1,2) unfolding uflow_def by blast
qed

text \<open>Every unit flow has unit shape: the edge \<open>(Vin a, Vout a)\<close> is the only edge into \<open>Vout a\<close>
and the only edge out of \<open>Vin a\<close>.\<close>

lemma uflow_unit_shape:
  assumes f: "uflow T f"
  shows "unit_shape {e. f e \<noteq> 0}"
proof -
  have zero: "e \<in> net T" if "f e \<noteq> 0" for e
    using f that unfolding uflow_def by blast
  have one: "f e = 1" if "f e \<noteq> 0" for e
    using f that unfolding uflow_def by blast
  have nn: "0 \<le> f e" for e
    using uflow_range[OF f] by blast
  have cons: "sum f {e \<in> net T. snd e = v} = sum f {e \<in> net T. fst e = v}"
    if "v \<noteq> Src" "v \<noteq> Snk" for v
    using f that by (simp add: uflow_def nex_unfold)
  have le_one: "sum f A \<le> 1" if "A \<subseteq> {d}" for A d
  proof -
    have "sum f A \<le> sum f {d}"
      using that nn by (intro sum_mono2) auto
    then show ?thesis
      using uflow_range[OF f, of d] by simp
  qed
  have in_Vout: "sum f {e \<in> net T. snd e = Nd (Vout a)} \<le> 1" for a
    by (rule le_one[of _ "(Nd (Vin a), Nd (Vout a))"]) (auto simp: net_iff net_graph_iff)
  have out_Vin: "sum f {e \<in> net T. fst e = Nd (Vin a)} \<le> 1" for a
    by (rule le_one[of _ "(Nd (Vin a), Nd (Vout a))"]) (auto simp: net_iff net_graph_iff)
  have fin: "finite {e \<in> net T. P e}" for P
    using finite_net by simp
  show ?thesis
    unfolding unit_shape_def
  proof (intro conjI allI impI)
    fix u v w
    assume uv: "(u, v) \<in> {e. f e \<noteq> 0}" and uw: "(u, w) \<in> {e. f e \<noteq> 0}" and u: "u \<noteq> Src"
    show "v = w"
    proof (rule ccontr)
      assume vw: "v \<noteq> w"
      have mem: "(u, v) \<in> net T" "(u, w) \<in> net T" "f (u, v) = 1" "f (u, w) = 1"
        using uv uw zero one by auto
      have two: "2 \<le> sum f {e \<in> net T. fst e = u}"
        by (rule two_le_sum[where d = "(u, v)" and d' = "(u, w)"]) (use mem vw fin nn in auto)
      show False
      proof (cases u)
        case Snk
        then show ?thesis
          using mem(1) by (simp add: net_iff)
      next
        case (Nd x)
        show ?thesis
        proof (cases x)
          case (Vin a)
          then show ?thesis
            using mem(1,2) vw Nd by (auto simp: net_iff net_graph_iff)
        next
          case (Vout a)
          then show ?thesis
            using two cons[of u] in_Vout[of a] Nd by simp
        qed
      qed (use u in simp)
    qed
  next
    fix u v w
    assume vu: "(v, u) \<in> {e. f e \<noteq> 0}" and wu: "(w, u) \<in> {e. f e \<noteq> 0}" and u: "u \<noteq> Snk"
    show "v = w"
    proof (rule ccontr)
      assume vw: "v \<noteq> w"
      have mem: "(v, u) \<in> net T" "(w, u) \<in> net T" "f (v, u) = 1" "f (w, u) = 1"
        using vu wu zero one by auto
      have two: "2 \<le> sum f {e \<in> net T. snd e = u}"
        by (rule two_le_sum[where d = "(v, u)" and d' = "(w, u)"]) (use mem vw fin nn in auto)
      show False
      proof (cases u)
        case Src
        then show ?thesis
          using mem(1) by (simp add: net_iff)
      next
        case (Nd x)
        show ?thesis
        proof (cases x)
          case (Vout a)
          then show ?thesis
            using mem(1,2) vw Nd by (auto simp: net_iff net_graph_iff)
        next
          case (Vin a)
          then show ?thesis
            using two cons[of u] out_Vin[of a] Nd by simp
        qed
      qed (use u in simp)
    qed
  qed
qed

end

end
