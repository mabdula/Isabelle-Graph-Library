theory Menger_Edge
  imports
    Directed_Set_Graphs.Vwalk
    Flow_Theory.STFlow
begin

section \<open>Integral Maximum Flows\<close>

text \<open>If all capacities are natural numbers or infinite, and some \<open>s\<close>-\<open>t\<close> cut has finite capacity,
then there is an integral maximum flow. We obtain this from a generalisation of
@{thm flow_network.max_flow_no_augpath}: a flow that is maximal within a class of flows closed under
augmentation along augmenting paths admits no augmenting path.\<close>

context flow_network_spec
begin

text \<open>The amount by which the proof of @{thm flow_network.max_flow_no_augpath} augments.\<close>

definition aug_amount :: "('edge \<Rightarrow> real) \<Rightarrow> 'edge Redge list \<Rightarrow> real" where
  "aug_amount f q = (if Rcap f (set q) < PInfty then real_of_ereal (Rcap f (set q)) else 1)"

end

context flow_network
begin

lemma max_in_class_no_augpath:
  assumes "f is s -- t flow" "Q f"
    "\<And>g. \<lbrakk>g is s -- t flow; Q g\<rbrakk> \<Longrightarrow> ex g t \<le> ex f t"
    "\<And>q. \<lbrakk>augpath f q; distinct q; set q \<subseteq> \<EE>; fstv (hd q) = s; sndv (last q) = t\<rbrakk> \<Longrightarrow>
       Q (augment_edges f (aug_amount f q) q)"
  shows "\<not> resreach f s t"
proof
  assume reach: "resreach f s t"
  have props: "isuflow f" "ex f s \<le> 0" "s \<in> \<V>" "t \<in> \<V>" "s \<noteq> t"
    "\<And>x. \<lbrakk>x \<in> \<V>; x \<noteq> s; x \<noteq> t\<rbrakk> \<Longrightarrow> ex f x = 0"
    using assms(1) by (auto simp add: is_s_t_flow_def)
  hence bflow: "isbflow f (\<lambda>v. - ex f v)"
    by (auto simp add: isbflow_def)
  obtain p where p_prop: "augpath f p" "fstv (hd p) = s" "sndv (last p) = t" "set p \<subseteq> \<EE>"
    "p \<noteq> []"
    using resreach_imp_augpath[of f s t] reach
    by (auto simp add: augpath_def prepath_def)
  then obtain q where q_prop: "augpath f q" "fstv (hd q) = s" "sndv (last q) = t" "set q \<subseteq> \<EE>"
    "distinct q" "q \<noteq> []"
    by (cases "distinct p")
      (fastforce elim!: prepath_drop_cycles[of p "set p"] intro!: Min_antimono
        simp add: Rcap_def augpath_def)+
  define \<gamma> where "\<gamma> = aug_amount f q"
  have gamma_geq_0: "0 \<le> \<gamma>"
    using augpath_def order.order_iff_strict q_prop(1)
    by (auto intro: real_of_ereal_pos simp add: \<gamma>_def aug_amount_def)
  moreover hence gamma_soft: "ereal \<gamma> \<le> Rcap f (set q)"
    using augpath_def order.order_iff_strict q_prop(1)
    by (auto simp add: ereal_real \<gamma>_def aug_amount_def)
  ultimately have bflow': "(augment_edges f \<gamma> q) is (\<lambda>v. if v = s then - ex f v + \<gamma>
                             else if v = t then - ex f v - \<gamma> else - ex f v) flow"
    using q_prop(4) q_prop(5) props(5)
    by (auto intro!: augment_path_validness_b_pres_source_target_distinct[OF bflow _ q_prop(1),
          simplified q_prop(2,3)])
  moreover have "\<gamma> > 0"
    using gamma_soft gamma_geq_0
    by (auto simp add: augpath_rcap q_prop(1) \<gamma>_def aug_amount_def zero_less_real_of_ereal)
  ultimately have "ex (augment_edges f \<gamma> q) t > ex f t"
    using props(4,5) by (fastforce simp add: isbflow_def)
  moreover have "(augment_edges f \<gamma> q) is s -- t flow"
    using bflow' \<open>0 < \<gamma>\<close> props by (auto simp add: is_s_t_flow_def isbflow_def)
  moreover have "Q (augment_edges f \<gamma> q)"
    using assms(4)[OF q_prop(1,5,4,2,3)] by (simp add: \<gamma>_def)
  ultimately show False
    using assms(3) by fastforce
qed


lemma Rcap_integral:
  assumes "is_integral_flow f" "\<And>e. e \<in> \<E> \<Longrightarrow> \<u> e = PInfty \<or> (\<exists>r \<in> \<int>. \<u> e = ereal r)"
    "set q \<subseteq> \<EE>" "Rcap f (set q) < PInfty"
  obtains r where "Rcap f (set q) = ereal r" "r \<in> \<int>"
proof -
  have fin: "finite {rc. \<exists>e. rc = rcap f e \<and> e \<in> set q}"
    by (rule finite_subset[of _ "rcap f ` set q"]) auto
  have "Rcap f (set q) \<in> insert PInfty {rc. \<exists>e. rc = rcap f e \<and> e \<in> set q}"
    unfolding Rcap_def by (rule Min_in) (use fin in auto)
  then obtain e where e: "e \<in> set q" "Rcap f (set q) = rcap f e"
    using assms(4) by auto
  hence oe: "oedge e \<in> \<E>"
    using assms(3) o_edge_res by auto
  show ?thesis
  proof (cases e)
    case (F d)
    hence "\<u> d \<noteq> PInfty"
      using e assms(4) by auto
    then obtain r where "r \<in> \<int>" "\<u> d = ereal r"
      using assms(2) oe F by auto
    thus ?thesis
      using that[of "r - f d"] e F assms(1) oe by (auto simp add: is_integral_flow_Ints)
  next
    case (B d)
    thus ?thesis
      using that[of "f d"] e assms(1) oe by (auto simp add: is_integral_flow_Ints)
  qed
qed

lemma integral_max_flow_exists:
  assumes "s \<in> \<V>" "t \<in> \<V>" "s \<noteq> t"
    "\<And>e. e \<in> \<E> \<Longrightarrow> \<u> e = PInfty \<or> (\<exists>r \<in> \<int>. \<u> e = ereal r)"
    "is_s_t_cut s t Y" "Cap Y < PInfty"
  obtains f where "is_max_flow s t f" "is_integral_flow f"
proof -
  have "0 \<le> Cap Y"
    by (auto intro: sum_nonneg simp add: Cap_def u_non_neg)
  then obtain c where c: "Cap Y = ereal c"
    using assms(6) by (cases "Cap Y") auto
  define Vals where
    "Vals = {n::int. \<exists>f. (f is s -- t flow) \<and> is_integral_flow f \<and> ex f t = of_int n}"
  have ex_bound: "0 \<le> ex f t \<and> ex f t \<le> c" if "f is s -- t flow" for f
    using s_t_flow_excess_s_t[OF that] ex_less_cut_cap[OF assms(1-3,5) that] c that
    by (auto simp add: is_s_t_flow_def)
  hence "Vals \<subseteq> {0..\<lfloor>c\<rfloor>}"
    by (fastforce simp add: Vals_def le_floor_iff)
  hence fin: "finite Vals"
    by (rule finite_subset) simp
  have "0 \<in> Vals"
    using zero_flow_is_s_t_flow[OF assms(1-3)]
    by (auto simp add: Vals_def is_integral_flow_def ex_def intro!: exI[of _ "\<lambda>e. 0"])
  then obtain f where f: "f is s -- t flow" "is_integral_flow f" "ex f t = of_int (Max Vals)"
    using Max_in[OF fin] by (fastforce simp add: Vals_def)
  have max: "ex g t \<le> ex f t" if g: "g is s -- t flow" "is_integral_flow g" for g
  proof -
    obtain n where n: "ex g t = of_int n"
      using integral_ex[OF g(2)] Ints_cases by metis
    hence "n \<in> Vals"
      using g by (auto simp add: Vals_def)
    thus ?thesis
      using fin f(3) n by simp
  qed
  have closed: "is_integral_flow (augment_edges f (aug_amount f q) q)" if q: "set q \<subseteq> \<EE>" for q
  proof (rule augment_edges_integral[OF f(2) _ q])
    show "aug_amount f q \<in> \<int>"
    proof (cases "Rcap f (set q) < PInfty")
      case True
      then obtain r where "Rcap f (set q) = ereal r" "r \<in> \<int>"
        using Rcap_integral[OF f(2) assms(4) q] by blast
      thus ?thesis
        using True by (simp add: aug_amount_def)
    qed (simp add: aug_amount_def)
  qed
  have "\<not> resreach f s t"
    using max_in_class_no_augpath[of f s t is_integral_flow] f(1,2) max closed by blast
  hence "is_max_flow s t f"
    using no_max_flow_resreach[OF assms(1-3) f(1)] by simp
  thus ?thesis
    using that f(2) by blast
qed

end

text \<open>The residual-edge constructors would clash with the usual names for sets of vertices
and edges.\<close>

hide_const (open) Redge.F Redge.B

section \<open>Edge-Disjoint Paths and Edge Separators\<close>

text \<open>A family \<open>P\<close> of pairwise edge-disjoint paths from \<open>A\<close> to \<open>B\<close>, and a set of edges \<open>F\<close>
separating \<open>A\<close> from \<open>B\<close>, i.e.\ every walk from \<open>A\<close> to \<open>B\<close> uses an edge of \<open>F\<close>.\<close>

definition edge_linkage :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a list set \<Rightarrow> bool" where
  "edge_linkage G A B P =
    ((\<forall>p \<in> P. hd p \<in> A \<and> last p \<in> B \<and> distinct_vwalk_bet G (hd p) p (last p)) \<and>
     (\<forall>p1 \<in> P. \<forall>p2 \<in> P. p1 \<noteq> p2 \<longrightarrow> set (edges_of_vwalk p1) \<inter> set (edges_of_vwalk p2) = {}))"

lemma edge_linkageE:
  "edge_linkage G A B P \<Longrightarrow>
    (\<lbrakk>\<And>p. p \<in> P \<Longrightarrow> hd p \<in> A;
      \<And>p. p \<in> P \<Longrightarrow> last p \<in> B;
      \<And>p. p \<in> P \<Longrightarrow> distinct_vwalk_bet G (hd p) p (last p);
      \<And>p1 p2. \<lbrakk>p1 \<in> P; p2 \<in> P; p1 \<noteq> p2\<rbrakk> \<Longrightarrow> set (edges_of_vwalk p1) \<inter> set (edges_of_vwalk p2) = {}\<rbrakk>
      \<Longrightarrow> Q) \<Longrightarrow>
    Q"
and edge_linkageI:
  "\<lbrakk>\<And>p. p \<in> P \<Longrightarrow> hd p \<in> A;
    \<And>p. p \<in> P \<Longrightarrow> last p \<in> B;
    \<And>p. p \<in> P \<Longrightarrow> distinct_vwalk_bet G (hd p) p (last p);
    \<And>p1 p2. \<lbrakk>p1 \<in> P; p2 \<in> P; p1 \<noteq> p2\<rbrakk> \<Longrightarrow> set (edges_of_vwalk p1) \<inter> set (edges_of_vwalk p2) = {}\<rbrakk>
    \<Longrightarrow> edge_linkage G A B P"
and edge_linkageD:
  "\<lbrakk>edge_linkage G A B P; p \<in> P\<rbrakk> \<Longrightarrow> hd p \<in> A"
  "\<lbrakk>edge_linkage G A B P; p \<in> P\<rbrakk> \<Longrightarrow> last p \<in> B"
  "\<lbrakk>edge_linkage G A B P; p \<in> P\<rbrakk> \<Longrightarrow> distinct_vwalk_bet G (hd p) p (last p)"
  "\<lbrakk>edge_linkage G A B P; p1 \<in> P; p2 \<in> P; p1 \<noteq> p2\<rbrakk> \<Longrightarrow>
     set (edges_of_vwalk p1) \<inter> set (edges_of_vwalk p2) = {}"
  by (auto simp: edge_linkage_def)

definition edge_separator :: "'a dgraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "edge_separator G A B F =
    (F \<subseteq> G \<and>
     (\<forall>u p v. u \<in> A \<longrightarrow> v \<in> B \<longrightarrow> vwalk_bet G u p v \<longrightarrow> set (edges_of_vwalk p) \<inter> F \<noteq> {}))"

lemma edge_separatorE:
  "edge_separator G A B F \<Longrightarrow>
    (\<lbrakk>F \<subseteq> G;
      \<And>u p v. \<lbrakk>u \<in> A; v \<in> B; vwalk_bet G u p v\<rbrakk> \<Longrightarrow> set (edges_of_vwalk p) \<inter> F \<noteq> {}\<rbrakk> \<Longrightarrow> Q) \<Longrightarrow>
    Q"
and edge_separatorI:
  "\<lbrakk>F \<subseteq> G;
    \<And>u p v. \<lbrakk>u \<in> A; v \<in> B; vwalk_bet G u p v\<rbrakk> \<Longrightarrow> set (edges_of_vwalk p) \<inter> F \<noteq> {}\<rbrakk> \<Longrightarrow>
    edge_separator G A B F"
and edge_separatorD:
  "edge_separator G A B F \<Longrightarrow> F \<subseteq> G"
  "\<lbrakk>edge_separator G A B F; u \<in> A; v \<in> B; vwalk_bet G u p v\<rbrakk> \<Longrightarrow> set (edges_of_vwalk p) \<inter> F \<noteq> {}"
  by (auto simp: edge_separator_def)

section \<open>Auxiliary Lemmas on Walks\<close>

lemma edges_of_vwalk_bet_to_distinct_subset:
  assumes "vwalk_bet E u p v"
  shows "set (edges_of_vwalk (vwalk_bet_to_distinct E p)) \<subseteq> set (edges_of_vwalk p)"
  using assms
proof (induction rule: vwalk_bet_to_distinct_induct)
  case (path p)
  thus ?case
    by (simp only: vwalk_bet_to_distinct.simps[of E p]) (simp del: vwalk_bet_to_distinct.simps)
next
  case (decomp p q r s)
  obtain w where q: "vwalk_bet E u q w" and r: "vwalk_bet E w r w" "Suc 0 < length r"
    and s: "vwalk_bet E w s v" and p: "p = q @ tl r @ tl s"
    using closed_vwalk_bet_decompE_2[OF decomp(1,2,3)] by blast
  have eq: "vwalk_bet_to_distinct E p = vwalk_bet_to_distinct E (q @ tl s)"
    using decomp(1,2,3)
    by (simp only: vwalk_bet_to_distinct.simps[of E p]) (auto simp del: vwalk_bet_to_distinct.simps)
  have q_props: "q \<noteq> []" "last q = w"
    using q by (auto simp add: vwalk_bet_def)
  obtain s' where s': "s = w # s'"
    using s by (cases s) (auto simp add: vwalk_bet_def)
  obtain r' where r': "r = w # r'"
    using r by (cases r) (auto simp add: vwalk_bet_def)
  have last_r: "last r = w"
    using r by (simp add: vwalk_bet_def)
  have "edges_of_vwalk (q @ tl s) = edges_of_vwalk q @ edges_of_vwalk s"
    using edges_of_vwalk_append_3[of q s'] q_props s' by simp
  moreover have "edges_of_vwalk p = edges_of_vwalk q @ edges_of_vwalk r @ edges_of_vwalk s"
  proof -
    have "edges_of_vwalk p = edges_of_vwalk q @ edges_of_vwalk (r @ s')"
      using p r' s' edges_of_vwalk_append_3[of q "r' @ s'"] q_props by simp
    also have "\<dots> = edges_of_vwalk q @ edges_of_vwalk r @ edges_of_vwalk s"
      using edges_of_vwalk_append_3[of r s'] last_r r' s' by simp
    finally show ?thesis .
  qed
  ultimately show ?case
    using decomp(4) unfolding eq by (auto simp del: vwalk_bet_to_distinct.simps)
qed

lemma cas_crossing:
  "\<lbrakk>cas x es y; x \<in> X; y \<notin> X\<rbrakk> \<Longrightarrow> \<exists>e \<in> set es. fst e \<in> X \<and> snd e \<notin> X"
proof (induction es arbitrary: x)
  case (Cons e es)
  thus ?case
    by (cases e) (auto simp add: cas_simp)
qed simp

lemma cas_awlast: "cas u p v \<Longrightarrow> awlast u p = v"
  by (induction u p v rule: cas.induct) auto

lemma cas_closed_successor:
  "\<lbrakk>cas u es v; e \<in> set es\<rbrakk> \<Longrightarrow> snd e = v \<or> (\<exists>e' \<in> set es. fst e' = snd e)"
proof (induction es arbitrary: u)
  case (Cons e' es)
  obtain t h where e': "e' = (t, h)"
    by fastforce
  hence cas_es: "cas h es v"
    using Cons.prems(1) by simp
  show ?case
  proof (cases "e = e'")
    case True
    show ?thesis
    proof (cases es)
      case Nil
      thus ?thesis
        using cas_es True e' by simp
    next
      case (Cons e'' es')
      thus ?thesis
        using cas_es True e' by (cases e'') auto
    qed
  next
    case False
    thus ?thesis
      using Cons.IH[OF cas_es] Cons.prems(2) by auto
  qed
qed simp

section \<open>The Flow Network\<close>

text \<open>We add a source \<open>Src\<close> with infinite-capacity edges into \<open>A\<close>, and a sink \<open>Snk\<close> with
infinite-capacity edges from \<open>B\<close>. The edges of \<open>G\<close> get capacity 1.\<close>

datatype 'a mnode = Src | Snk | Nd 'a

fun unNd :: "'a mnode \<Rightarrow> 'a" where
  "unNd (Nd x) = x"
| "unNd _ = undefined"

definition lift_edge :: "'a \<times> 'a \<Rightarrow> 'a mnode \<times> 'a mnode" where
  "lift_edge e = (Nd (fst e), Nd (snd e))"

definition unlift_edge :: "'a mnode \<times> 'a mnode \<Rightarrow> 'a \<times> 'a" where
  "unlift_edge e = (unNd (fst e), unNd (snd e))"

lemma unlift_lift_edge[simp]: "unlift_edge (lift_edge e) = e"
  by (simp add: lift_edge_def unlift_edge_def)

lemma lift_edge_simps[simp]:
  "fst (lift_edge e) = Nd (fst e)" "snd (lift_edge e) = Nd (snd e)"
  by (simp_all add: lift_edge_def)

lemma inj_lift_edge: "inj lift_edge"
  by (metis injI unlift_lift_edge)

locale menger_edge_network =
  fixes G :: "'a dgraph" and A B :: "'a set"
  assumes finite_G: "finite G"
    and AB_disj: "A \<inter> B = {}"
    and A_meets: "A \<inter> dVs G \<noteq> {}"
    and B_meets: "B \<inter> dVs G \<noteq> {}"
begin

definition "GE = lift_edge ` G"
definition "SE = (\<lambda>a. (Src, Nd a)) ` (A \<inter> dVs G)"
definition "TE = (\<lambda>b. (Nd b, Snk)) ` (B \<inter> dVs G)"
definition "NE = GE \<union> SE \<union> TE"
definition "cap e = (if e \<in> GE then (1::ereal) else PInfty)"

lemma NE_finite: "finite NE"
  using finite_G finite_vertices_iff[of G]
  by (auto simp add: NE_def GE_def SE_def TE_def)

lemma NE_nonempty: "NE \<noteq> {}"
  using A_meets by (auto simp add: NE_def SE_def)

sublocale N: flow_network prod.fst prod.snd Pair cap NE
  by unfold_locales (auto simp add: NE_finite NE_nonempty cap_def)

lemma make_pair_id: "N.make_pair e = e"
  by (simp add: N.make_pair_def)

lemma V_NE: "dVs (N.make_pair ` NE) = dVs NE"
  by (simp add: make_pair_id)

lemma NE_cases:
  assumes "e \<in> NE"
  obtains (G) x y where "(x, y) \<in> G" "e = (Nd x, Nd y)"
    | (S) a where "a \<in> A" "a \<in> dVs G" "e = (Src, Nd a)"
    | (T) b where "b \<in> B" "b \<in> dVs G" "e = (Nd b, Snk)"
  using assms by (auto simp add: NE_def GE_def SE_def TE_def lift_edge_def)

lemma NE_not_into_Src: "e \<in> NE \<Longrightarrow> snd e \<noteq> Src"
  by (erule NE_cases) auto

lemma NE_not_out_of_Snk: "e \<in> NE \<Longrightarrow> fst e \<noteq> Snk"
  by (erule NE_cases) auto

lemma Src_Snk_in_V: "Src \<in> dVs (N.make_pair ` NE)" "Snk \<in> dVs (N.make_pair ` NE)"
proof -
  obtain a b where "a \<in> A \<inter> dVs G" "b \<in> B \<inter> dVs G"
    using A_meets B_meets by blast
  hence "(Src, Nd a) \<in> NE" "(Nd b, Snk) \<in> NE"
    by (auto simp add: NE_def SE_def TE_def)
  thus "Src \<in> dVs (N.make_pair ` NE)" "Snk \<in> dVs (N.make_pair ` NE)"
    by (auto simp add: V_NE)
qed

lemma path_to_Snk:
  assumes "cas (Nd x) ps Snk" "set ps \<subseteq> NE"
  shows "\<exists>es b. ps = map lift_edge es @ [(Nd b, Snk)] \<and> b \<in> B \<and> b \<in> dVs G \<and> set es \<subseteq> G \<and>
           cas x es b"
  using assms
proof (induction ps arbitrary: x)
  case (Cons e ps)
  have e_NE: "e \<in> NE" and ps_NE: "set ps \<subseteq> NE"
    using Cons.prems(2) by auto
  have fst_e: "fst e = Nd x" and cas_ps: "cas (snd e) ps Snk"
    using Cons.prems(1) by (cases e; simp)+
  from e_NE show ?case
  proof (cases rule: NE_cases)
    case (G x' y)
    obtain es b where IH: "ps = map lift_edge es @ [(Nd b, Snk)]" "b \<in> B" "b \<in> dVs G"
      "set es \<subseteq> G" "cas y es b"
      using Cons.IH[of y] cas_ps ps_NE G(2) by auto
    show ?thesis
      using IH G fst_e by (auto intro!: exI[of _ "(x, y) # es"] exI[of _ b] simp add: lift_edge_def)
  next
    case (S a)
    thus ?thesis
      using fst_e by simp
  next
    case (T b)
    have "ps = []"
    proof (rule ccontr)
      assume "ps \<noteq> []"
      then obtain e' ps' where "ps = e' # ps'"
        by (cases ps) auto
      hence "fst e' = Snk" "e' \<in> NE"
        using cas_ps T(3) ps_NE by (cases e'; auto)+
      thus False
        using NE_not_out_of_Snk by blast
    qed
    thus ?thesis
      using T fst_e by (auto intro!: exI[of _ "[]"])
  qed
qed simp

lemma path_shape:
  assumes "cas Src ps Snk" "set ps \<subseteq> NE"
  obtains a es b where "ps = (Src, Nd a) # map lift_edge es @ [(Nd b, Snk)]"
    "a \<in> A" "b \<in> B" "awalk G a es b" "es \<noteq> []"
proof -
  obtain e ps' where ps: "ps = e # ps'"
    using assms(1) by (cases ps) auto
  have e: "fst e = Src" "e \<in> NE" and ps': "cas (snd e) ps' Snk" "set ps' \<subseteq> NE"
    using assms ps by (cases e; auto)+
  from e(2) obtain a where a: "a \<in> A" "a \<in> dVs G" "e = (Src, Nd a)"
    using e(1) by (cases rule: NE_cases) auto
  obtain es b where es: "ps' = map lift_edge es @ [(Nd b, Snk)]" "b \<in> B" "set es \<subseteq> G"
    "cas a es b"
    using path_to_Snk[of a ps'] ps' a(3) by auto
  have "a \<noteq> b"
    using a(1) es(2) AB_disj by auto
  hence "es \<noteq> []"
    using es(4) by auto
  moreover have "awalk G a es b"
    using a(2) es(3,4) by (simp add: awalk_def)
  ultimately show ?thesis
    using that ps a(1,3) es(1,2) by blast
qed

definition proj :: "('a mnode \<times> 'a mnode) list \<Rightarrow> 'a list" where
  "proj ps = vwalk_bet_to_distinct G
     (awalk_verts (unNd (snd (hd ps))) (map unlift_edge (butlast (tl ps))))"

lemma proj_props:
  assumes "cas Src ps Snk" "set ps \<subseteq> NE"
  shows "hd (proj ps) \<in> A" "last (proj ps) \<in> B"
    "distinct_vwalk_bet G (hd (proj ps)) (proj ps) (last (proj ps))"
    "set (edges_of_vwalk (proj ps)) \<subseteq> unlift_edge ` (set ps \<inter> GE)"
    "edges_of_vwalk (proj ps) \<noteq> []"
proof -
  obtain a es b where ps: "ps = (Src, Nd a) # map lift_edge es @ [(Nd b, Snk)]"
    and ab: "a \<in> A" "b \<in> B" and aw: "awalk G a es b"
    using path_shape[OF assms] by blast
  have proj_eq: "proj ps = vwalk_bet_to_distinct G (awalk_verts a es)"
    by (simp add: proj_def ps comp_def)
  have vw: "vwalk_bet G a (awalk_verts a es) b"
    using awalk_imp_vwalk[OF aw] .
  have dv: "distinct_vwalk_bet G a (proj ps) b"
    unfolding proj_eq by (rule vwalk_bet_to_distinct_is_distinct_vwalk_bet[OF vw])
  hence hd_last: "hd (proj ps) = a" "last (proj ps) = b"
    by (auto simp add: distinct_vwalk_bet_def vwalk_bet_def)
  have "set (edges_of_vwalk (proj ps)) \<subseteq> set es"
    using edges_of_vwalk_bet_to_distinct_subset[OF vw] vwalk_awalk_id[of a es b] aw
    unfolding proj_eq by (auto simp add: awalk_def)
  moreover have "set es \<subseteq> unlift_edge ` (set ps \<inter> GE)"
  proof
    fix e
    assume "e \<in> set es"
    hence "lift_edge e \<in> set ps \<inter> GE"
      using ps aw by (auto simp add: GE_def awalk_def)
    thus "e \<in> unlift_edge ` (set ps \<inter> GE)"
      by (auto intro!: image_eqI[where x = "lift_edge e"])
  qed
  moreover have "edges_of_vwalk (proj ps) \<noteq> []"
  proof
    assume "edges_of_vwalk (proj ps) = []"
    hence "length (proj ps) \<le> 1"
      using edges_of_vwalk_length[of "proj ps"] by simp
    hence "hd (proj ps) = last (proj ps)"
      using dv by (cases "proj ps") (auto simp add: distinct_vwalk_bet_def vwalk_bet_def)
    thus False
      using hd_last ab AB_disj by auto
  qed
  ultimately show "hd (proj ps) \<in> A" "last (proj ps) \<in> B"
    "distinct_vwalk_bet G (hd (proj ps)) (proj ps) (last (proj ps))"
    "set (edges_of_vwalk (proj ps)) \<subseteq> unlift_edge ` (set ps \<inter> GE)"
    "edges_of_vwalk (proj ps) \<noteq> []"
    using hd_last ab dv by auto
qed

lemma cas_lift: "cas u es v \<Longrightarrow> cas (Nd u) (map lift_edge es) (Nd v)"
  by (induction es arbitrary: u) (auto simp add: cas_simp lift_edge_def)

lemma inj_on_unlift_GE: "inj_on unlift_edge GE"
  by (auto simp add: GE_def inj_on_def)

lemma unlift_GE: "unlift_edge ` GE = G"
  by (simp add: GE_def image_comp comp_def)

lemma Src_neq_Snk: "Src \<noteq> Snk"
  by simp

lemma make_pair_fun: "N.make_pair = (\<lambda>e. e)"
  by (rule ext) (simp add: make_pair_id)

lemma flowpath_cas:
  assumes "N.flowpath f ps" "ps \<noteq> []"
  shows "cas (fst (hd ps)) ps (snd (last ps))"
  using assms by (simp add: N.flowpath_def N.multigraph_path_def awalk_def make_pair_fun)

lemma path_last_TE:
  assumes "cas Src ps Snk" "set ps \<subseteq> NE"
  shows "{e \<in> set ps. snd e = Snk} = {last ps}" "\<exists>e \<in> set ps. e \<in> GE"
proof -
  obtain a es b where ps: "ps = (Src, Nd a) # map lift_edge es @ [(Nd b, Snk)]"
    and aw: "awalk G a es b" and es: "es \<noteq> []"
    using path_shape[OF assms] by blast
  show "{e \<in> set ps. snd e = Snk} = {last ps}"
    using ps by auto
  have "lift_edge (hd es) \<in> set ps" "hd es \<in> G"
    using ps es aw by (auto simp add: awalk_def)
  thus "\<exists>e \<in> set ps. e \<in> GE"
    by (auto simp add: GE_def)
qed

lemma cycle_avoids_Snk:
  assumes "N.flowcycle f cs" "set cs \<subseteq> NE" "e \<in> set cs"
  shows "snd e \<noteq> Snk"
proof
  assume snk: "snd e = Snk"
  have ne: "cs \<noteq> []" and cas: "cas (fst (hd cs)) cs (fst (hd cs))"
    using assms(1) flowpath_cas[of f cs] by (auto simp add: N.flowcycle_def)
  have "hd cs \<in> NE"
    using ne assms(2) by auto
  hence "snd e \<noteq> fst (hd cs)"
    using snk NE_not_out_of_Snk[of "hd cs"] by simp
  moreover have "fst e' \<noteq> snd e" if "e' \<in> set cs" for e'
    using snk assms(2) NE_not_out_of_Snk[of e'] that by auto
  ultimately show False
    using cas_closed_successor[OF cas assms(3)] by auto
qed

lemma paths_from_flow:
  assumes flow: "N.is_s_t_flow f Src Snk" and integral: "N.is_integral_flow f"
  obtains P where "edge_linkage G A B P" "real (card P) = N.ex f Snk"
proof -
  obtain css cws pss pws where
    len: "length css = length cws" "length pss = length pws" and
    pos: "\<And>w. w \<in> set cws \<union> set pws \<Longrightarrow> 0 < w" and
    cyc: "\<And>cs. cs \<in> set css \<Longrightarrow> N.flowcycle f cs \<and> set cs \<subseteq> N.support f \<and> distinct cs" and
    pth: "\<And>ps. ps \<in> set pss \<Longrightarrow> N.flowpath f ps \<and> set ps \<subseteq> N.support f \<and> distinct ps
                  \<and> fst (hd ps) = Src \<and> snd (last ps) = Snk" and
    dec: "\<And>e. e \<in> NE \<Longrightarrow> f e = (\<Sum>i<length css. if e \<in> set (css ! i) then cws ! i else 0) +
                  (\<Sum>i<length pss. if e \<in> set (pss ! i) then pws ! i else 0)" and
    int: "N.is_integral_flow f \<Longrightarrow> (\<forall>w\<in>set cws \<union> set pws. \<exists>n. w = real n)"
    by (rule N.s_t_flow_decomposition[OF flow]) blast
  have supp: "N.support f \<subseteq> NE"
    by (auto simp add: N.support_def)
  define I where "I = {i. i < length pss \<and> pss ! i \<noteq> []}"
  have path_i: "cas Src (pss ! i) Snk" "set (pss ! i) \<subseteq> NE" if "i \<in> I" for i
  proof -
    have "pss ! i \<in> set pss" "pss ! i \<noteq> []"
      using that by (auto simp add: I_def)
    thus "cas Src (pss ! i) Snk" "set (pss ! i) \<subseteq> NE"
      using pth[of "pss ! i"] flowpath_cas[of f "pss ! i"] supp by auto
  qed
  have w_pos: "0 < pws ! i" if "i < length pss" for i
    using pos len that by auto
  have w_nat: "\<exists>n::nat. pws ! i = real n" if "i < length pss" for i
    using int[OF integral] len that by auto
  have cyc_nonneg: "0 \<le> (\<Sum>i<length css. if e \<in> set (css ! i) then cws ! i else 0)" for e
  proof (rule sum_nonneg)
    fix i
    assume "i \<in> {..<length css}"
    hence "0 < cws ! i"
      using pos len by auto
    thus "0 \<le> (if e \<in> set (css ! i) then cws ! i else 0)"
      by simp
  qed
  have term_le: "pws ! i \<le> f e" if "e \<in> NE" "i < length pss" "e \<in> set (pss ! i)" for e i
  proof -
    have "pws ! i = (if e \<in> set (pss ! i) then pws ! i else 0)"
      using that by simp
    also have "\<dots> \<le> (\<Sum>k<length pss. if e \<in> set (pss ! k) then pws ! k else 0)"
      by (rule member_le_sum) (use that w_pos in \<open>auto intro: less_imp_le\<close>)
    also have "\<dots> \<le> f e"
      using dec[OF that(1)] cyc_nonneg[of e] by simp
    finally show ?thesis .
  qed
  have two_le: "pws ! i + pws ! j \<le> f e"
    if "e \<in> NE" "i < length pss" "j < length pss" "i \<noteq> j" "e \<in> set (pss ! i)" "e \<in> set (pss ! j)"
    for e i j
  proof -
    have "pws ! i + pws ! j = (\<Sum>k \<in> {i, j}. if e \<in> set (pss ! k) then pws ! k else 0)"
      using that by simp
    also have "\<dots> \<le> (\<Sum>k<length pss. if e \<in> set (pss ! k) then pws ! k else 0)"
      by (rule sum_mono2) (use that w_pos in \<open>auto intro: less_imp_le\<close>)
    also have "\<dots> \<le> f e"
      using dec[OF that(1)] cyc_nonneg[of e] by simp
    finally show ?thesis .
  qed
  have cap_le: "f e \<le> 1" if "e \<in> GE" for e
  proof -
    have "e \<in> NE"
      using that by (simp add: NE_def)
    hence "ereal (f e) \<le> cap e"
      using flow by (auto simp add: N.is_s_t_flow_def N.isuflow_def)
    thus ?thesis
      using that by (simp add: cap_def)
  qed
  have w_one: "pws ! i = 1" if iI: "i \<in> I" for i
  proof -
    have i: "i < length pss"
      using iI by (simp add: I_def)
    obtain e where e: "e \<in> set (pss ! i)" "e \<in> GE"
      using path_last_TE(2)[OF path_i[OF iI]] by blast
    have "e \<in> NE"
      using e(2) by (simp add: NE_def)
    hence le1: "pws ! i \<le> 1"
      using term_le[OF _ i e(1)] cap_le[OF e(2)] by fastforce
    obtain n :: nat where n: "pws ! i = real n"
      using w_nat[OF i] by blast
    have "n \<le> 1" "0 < n"
      using le1 w_pos[OF i] n by simp_all
    hence "n = 1"
      by simp
    thus ?thesis
      using n by simp
  qed
  have disj_GE: "set (pss ! i) \<inter> set (pss ! j) \<inter> GE = {}" if "i \<in> I" "j \<in> I" "i \<noteq> j" for i j
  proof (rule ccontr)
    assume "set (pss ! i) \<inter> set (pss ! j) \<inter> GE \<noteq> {}"
    then obtain e where e: "e \<in> set (pss ! i)" "e \<in> set (pss ! j)" "e \<in> GE"
      by blast
    have "e \<in> NE"
      using e(3) by (simp add: NE_def)
    hence "pws ! i + pws ! j \<le> f e"
      using two_le that e by (auto simp add: I_def)
    thus False
      using cap_le[OF e(3)] w_one that by simp
  qed
  define pr where "pr i = proj (pss ! i)" for i
  have edges_disj: "set (edges_of_vwalk (pr i)) \<inter> set (edges_of_vwalk (pr j)) = {}"
    if ij: "i \<in> I" "j \<in> I" "i \<noteq> j" for i j
  proof -
    have "set (edges_of_vwalk (pr i)) \<subseteq> unlift_edge ` (set (pss ! i) \<inter> GE)"
      "set (edges_of_vwalk (pr j)) \<subseteq> unlift_edge ` (set (pss ! j) \<inter> GE)"
      using proj_props(4)[OF path_i[OF ij(1)]] proj_props(4)[OF path_i[OF ij(2)]]
      by (simp_all add: pr_def)
    moreover have "unlift_edge ` (set (pss ! i) \<inter> GE) \<inter> unlift_edge ` (set (pss ! j) \<inter> GE) = {}"
    proof (rule ccontr)
      assume "unlift_edge ` (set (pss ! i) \<inter> GE) \<inter> unlift_edge ` (set (pss ! j) \<inter> GE) \<noteq> {}"
      then obtain x y where x: "x \<in> set (pss ! i)" "x \<in> GE" and y: "y \<in> set (pss ! j)" "y \<in> GE"
        and xy: "unlift_edge x = unlift_edge y"
        by blast
      have "x = y"
        using inj_onD[OF inj_on_unlift_GE xy x(2) y(2)] .
      thus False
        using disj_GE[OF ij] x y by blast
    qed
    ultimately show ?thesis
      by blast
  qed
  have inj: "inj_on pr I"
  proof (rule inj_onI)
    fix i j
    assume ij: "i \<in> I" "j \<in> I" "pr i = pr j"
    show "i = j"
    proof (rule ccontr)
      assume "i \<noteq> j"
      hence "set (edges_of_vwalk (pr i)) = {}"
        using edges_disj[OF ij(1,2)] ij(3) by simp
      thus False
        using proj_props(5)[OF path_i[OF ij(1)]] by (simp add: pr_def)
    qed
  qed
  define P where "P = pr ` I"
  have link: "edge_linkage G A B P"
  proof (rule edge_linkageI)
    fix p
    assume "p \<in> P"
    then obtain i where i: "i \<in> I" "p = pr i"
      by (auto simp add: P_def)
    show "hd p \<in> A"
      using proj_props(1)[OF path_i[OF i(1)]] i(2) by (simp add: pr_def)
  next
    fix p
    assume "p \<in> P"
    then obtain i where i: "i \<in> I" "p = pr i"
      by (auto simp add: P_def)
    show "last p \<in> B"
      using proj_props(2)[OF path_i[OF i(1)]] i(2) by (simp add: pr_def)
  next
    fix p
    assume "p \<in> P"
    then obtain i where i: "i \<in> I" "p = pr i"
      by (auto simp add: P_def)
    show "distinct_vwalk_bet G (hd p) p (last p)"
      using proj_props(3)[OF path_i[OF i(1)]] i(2) by (simp add: pr_def)
  next
    fix p1 p2
    assume "p1 \<in> P" "p2 \<in> P" "p1 \<noteq> p2"
    then obtain i j where "i \<in> I" "j \<in> I" "p1 = pr i" "p2 = pr j" "i \<noteq> j"
      by (auto simp add: P_def)
    thus "set (edges_of_vwalk p1) \<inter> set (edges_of_vwalk p2) = {}"
      using edges_disj by blast
  qed
  have card_P: "card P = card I"
    unfolding P_def using inj by (rule card_image)
  define TS where "TS = {e \<in> NE. snd e = Snk}"
  have fin_TS: "finite TS"
    using NE_finite by (simp add: TS_def)
  have dp: "N.delta_plus Snk = {}"
    using NE_not_out_of_Snk by (auto simp add: N.delta_plus_def)
  have dm: "N.delta_minus Snk = TS"
    by (auto simp add: N.delta_minus_def TS_def)
  have "N.ex f Snk = (\<Sum>e \<in> TS. f e)"
    by (simp add: N.ex_def dp dm)
  also have "\<dots> = (\<Sum>e \<in> TS. \<Sum>k<length pss. if e \<in> set (pss ! k) then pws ! k else 0)"
  proof (rule sum.cong[OF refl])
    fix e
    assume e: "e \<in> TS"
    have "(\<Sum>i<length css. if e \<in> set (css ! i) then cws ! i else 0) = 0"
    proof (rule sum.neutral, rule ballI)
      fix i
      assume "i \<in> {..<length css}"
      hence "css ! i \<in> set css"
        by simp
      hence "e \<notin> set (css ! i)"
        using cyc[of "css ! i"] cycle_avoids_Snk[of f "css ! i" e] supp e by (auto simp add: TS_def)
      thus "(if e \<in> set (css ! i) then cws ! i else 0) = 0"
        by simp
    qed
    thus "f e = (\<Sum>k<length pss. if e \<in> set (pss ! k) then pws ! k else 0)"
      using dec[of e] e by (simp add: TS_def)
  qed
  also have "\<dots> = (\<Sum>k<length pss. \<Sum>e \<in> TS. if e \<in> set (pss ! k) then pws ! k else 0)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>k<length pss. if k \<in> I then 1 else 0)"
  proof (rule sum.cong[OF refl])
    fix k
    assume k: "k \<in> {..<length pss}"
    show "(\<Sum>e \<in> TS. if e \<in> set (pss ! k) then pws ! k else 0) = (if k \<in> I then 1 else 0)"
    proof (cases "k \<in> I")
      case True
      have TE_ps: "{e \<in> set (pss ! k). snd e = Snk} = {last (pss ! k)}"
        using path_last_TE(1)[OF path_i[OF True]] .
      have last_TS: "last (pss ! k) \<in> TS"
        using TE_ps path_i(2)[OF True] by (auto simp add: TS_def)
      have "(\<Sum>e \<in> TS. if e \<in> set (pss ! k) then pws ! k else 0) =
            (\<Sum>e \<in> TS. if e = last (pss ! k) then pws ! k else 0)"
      proof (rule sum.cong[OF refl])
        fix e
        assume "e \<in> TS"
        hence "e \<in> set (pss ! k) \<longleftrightarrow> e = last (pss ! k)"
          using TE_ps by (auto simp add: TS_def)
        thus "(if e \<in> set (pss ! k) then pws ! k else 0) = (if e = last (pss ! k) then pws ! k else 0)"
          by simp
      qed
      also have "\<dots> = pws ! k"
        using fin_TS last_TS by simp
      finally show ?thesis
        using w_one[OF True] True by simp
    next
      case False
      hence "pss ! k = []"
        using k by (simp add: I_def)
      thus ?thesis
        using False by simp
    qed
  qed
  also have "\<dots> = (\<Sum>k \<in> {k \<in> {..<length pss}. k \<in> I}. (1::real))"
    by (rule sum.inter_filter[symmetric]) simp
  also have "{k \<in> {..<length pss}. k \<in> I} = I"
    by (auto simp add: I_def)
  finally have "real (card P) = N.ex f Snk"
    using card_P by simp
  with link show ?thesis
    by (rule that)
qed

lemma separator_from_max_flow:
  assumes "N.is_max_flow Src Snk f"
  obtains F where "edge_separator G A B F" "real (card F) = N.ex f Snk"
proof -
  define C where "C = N.Rescut f Src"
  note st = Src_Snk_in_V Src_neq_Snk
  have min_cut: "N.is_min_cut Src Snk C"
    unfolding C_def using N.Rescut_of_max_flow_is_min_cut[OF st assms] .
  have val: "ereal (N.ex f Snk) = N.Cap C"
    using N.max_flow_min_cut(1)[OF st assms min_cut] .
  have C_cut: "Src \<in> C" "Snk \<notin> C"
    using N.max_flow_Rescut_s_t_cut[OF st assms] by (auto simp add: C_def N.is_s_t_cut_def)
  have fin_D: "finite (N.Delta_plus C)"
    using NE_finite by (auto intro: finite_subset simp add: N.Delta_plus_def)
  have D_GE: "N.Delta_plus C \<subseteq> GE"
  proof
    fix e
    assume e: "e \<in> N.Delta_plus C"
    show "e \<in> GE"
    proof (rule ccontr)
      assume "e \<notin> GE"
      hence "N.Cap C = PInfty"
        using e fin_D by (auto simp add: N.Cap_def sum_Pinfty cap_def)
      thus False
        using val by simp
    qed
  qed
  define F where "F = unlift_edge ` N.Delta_plus C"
  have card_F: "card F = card (N.Delta_plus C)"
    unfolding F_def using inj_on_subset[OF inj_on_unlift_GE D_GE] by (rule card_image)
  have "N.Cap C = (\<Sum>e \<in> N.Delta_plus C. ereal 1)"
    unfolding N.Cap_def by (rule sum.cong) (use D_GE in \<open>auto simp add: cap_def one_ereal_def\<close>)
  also have "\<dots> = ereal (real (card (N.Delta_plus C)))"
    by (simp only: sum_ereal) simp
  finally have real_card: "real (card F) = N.ex f Snk"
    using val card_F by simp
  have sep: "edge_separator G A B F"
  proof (rule edge_separatorI)
    show "F \<subseteq> G"
      using D_GE unlift_GE by (auto simp add: F_def)
  next
    fix u p v
    assume uv: "u \<in> A" "v \<in> B" "vwalk_bet G u p v"
    define es where "es = edges_of_vwalk p"
    have aw: "awalk G u es v"
      unfolding es_def by (rule vwalk_imp_awalk[OF uv(3)])
    have u_v: "u \<in> dVs G" "v \<in> dVs G"
      using vwalk_bet_endpoints[OF uv(3)] by auto
    define W where "W = (Src, Nd u) # map lift_edge es @ [(Nd v, Snk)]"
    have cas_mid: "cas (Nd u) (map lift_edge es) (Nd v)"
      using cas_lift[of u es v] aw by (simp add: awalk_def)
    have cas_W: "cas Src W Snk"
      using cas_mid cas_awlast[OF cas_mid] by (simp add: W_def)
    have W_NE: "set W \<subseteq> NE"
      using aw u_v uv(1,2) by (auto simp add: W_def NE_def SE_def TE_def GE_def awalk_def)
    obtain e where e: "e \<in> set W" "fst e \<in> C" "snd e \<notin> C"
      using cas_crossing[OF cas_W C_cut] by auto
    hence e_D: "e \<in> N.Delta_plus C"
      using W_NE by (auto simp add: N.Delta_plus_def)
    hence "e \<in> GE"
      by (rule subsetD[OF D_GE])
    hence "e \<in> set (map lift_edge es)"
      using e(1) by (auto simp add: W_def GE_def lift_edge_def)
    then obtain e' where e': "e' \<in> set es" "e = lift_edge e'"
      by auto
    hence "e' \<in> F"
      using e_D by (auto simp add: F_def intro!: image_eqI[where x = e])
    thus "set (edges_of_vwalk p) \<inter> F \<noteq> {}"
      using e'(1) by (auto simp add: es_def)
  qed
  show ?thesis
    using that sep real_card by blast
qed

lemma menger_edge_network:
  "\<exists>P F. edge_linkage G A B P \<and> edge_separator G A B F \<and> card F = card P"
proof -
  have caps: "\<And>e. e \<in> NE \<Longrightarrow> cap e = PInfty \<or> (\<exists>r \<in> \<int>. cap e = ereal r)"
    by (auto simp add: cap_def one_ereal_def)
  define Y0 where "Y0 = insert Src (Nd ` (A \<inter> dVs G))"
  have "Nd a \<in> dVs NE" if "a \<in> A \<inter> dVs G" for a
  proof -
    have "(Src, Nd a) \<in> NE"
      using that by (auto simp add: NE_def SE_def)
    thus ?thesis
      by (rule dVsI(2))
  qed
  hence "Y0 \<subseteq> dVs (N.make_pair ` NE)"
    using Src_Snk_in_V(1) by (auto simp add: Y0_def V_NE)
  hence cut: "N.is_s_t_cut Src Snk Y0"
    using Src_Snk_in_V(2) by (auto simp add: N.is_s_t_cut_def Y0_def)
  have D: "N.Delta_plus Y0 \<subseteq> GE"
  proof
    fix e
    assume "e \<in> N.Delta_plus Y0"
    hence e: "e \<in> NE" "fst e \<in> Y0" "snd e \<notin> Y0"
      by (auto simp add: N.Delta_plus_def)
    from e(1) show "e \<in> GE"
    proof (cases rule: NE_cases)
      case (G x y)
      thus ?thesis
        by (auto simp add: GE_def lift_edge_def intro!: image_eqI[where x = "(x, y)"])
    next
      case (S a)
      thus ?thesis
        using e by (auto simp add: Y0_def)
    next
      case (T b)
      thus ?thesis
        using e AB_disj by (auto simp add: Y0_def)
    qed
  qed
  have "N.Cap Y0 = (\<Sum>e \<in> N.Delta_plus Y0. ereal 1)"
    unfolding N.Cap_def by (rule sum.cong) (use D in \<open>auto simp add: cap_def one_ereal_def\<close>)
  also have "\<dots> = ereal (real (card (N.Delta_plus Y0)))"
    by (simp only: sum_ereal) simp
  finally have fin: "N.Cap Y0 < PInfty"
    by simp
  obtain f where max: "N.is_max_flow Src Snk f" and int: "N.is_integral_flow f"
    using N.integral_max_flow_exists[OF Src_Snk_in_V Src_neq_Snk caps cut fin] by blast
  have flow: "N.is_s_t_flow f Src Snk"
    using max by (simp add: N.is_max_flow_def)
  obtain P where P: "edge_linkage G A B P" "real (card P) = N.ex f Snk"
    using paths_from_flow[OF flow int] by blast
  obtain F where F: "edge_separator G A B F" "real (card F) = N.ex f Snk"
    using separator_from_max_flow[OF max] by blast
  have "card F = card P"
    using P(2) F(2) by simp
  thus ?thesis
    using P(1) F(1) by blast
qed

end

section \<open>Menger's Theorem for Edge-Disjoint Paths\<close>

theorem menger_edge:
  assumes "finite G" "A \<inter> B = {}"
  shows "\<exists>P F. edge_linkage G A B P \<and> edge_separator G A B F \<and> card F = card P"
proof (cases "A \<inter> dVs G = {} \<or> B \<inter> dVs G = {}")
  case True
  have "edge_linkage G A B {}"
    by (rule edge_linkageI) auto
  moreover have "edge_separator G A B {}"
  proof (rule edge_separatorI)
    fix u p v
    assume uv: "u \<in> A" "v \<in> B" "vwalk_bet G u p v"
    hence "u \<in> dVs G" "v \<in> dVs G"
      using vwalk_bet_endpoints[OF uv(3)] by auto
    thus "set (edges_of_vwalk p) \<inter> {} \<noteq> {}"
      using True uv(1,2) by blast
  qed simp
  ultimately have "edge_linkage G A B {} \<and> edge_separator G A B {} \<and>
                   card ({} :: ('a \<times> 'a) set) = card ({} :: 'a list set)"
    by simp
  thus ?thesis
    by blast
next
  case False
  interpret menger_edge_network G A B
    using assms False by unfold_locales auto
  show ?thesis
    by (rule menger_edge_network)
qed
end
