theory Gammoid_Oracle_Generic
  imports
    Gammoid_Max_Flow
    Dinic.Residual_Buckets
    "HOL-Data_Structures.Set_Specs"
begin

section \<open>A Generic Independence Oracle for Gammoids\<close>

text \<open>The oracle maintains a set \<open>X\<close> of elements of a gammoid together with a maximum unit flow of the
network of \<open>X\<close>, and answers for every set, independent or not:
\<^item> whether \<open>insert y X\<close> is independent (one search);
\<^item> whether \<open>insert y (X - {x})\<close> is independent (a deletion and one search).
Insertion and deletion re-establish a maximum flow by augmenting paths.

Nothing in this theory is fixed beyond the mathematics. The flow and the set \<open>X\<close> are abstract data
types. Paths are searched by a parameter on an abstract data type for a simple graph, the symmetric
hull of the network of all elements, and the search is told by a predicate which pairs it may use.
From a path of nodes, the residual edges are lifted through the buckets of realising edges, and
the flow is augmented along them.\<close>

subsection \<open>Walks along an Injection\<close>

lemma vwalk_map:
  assumes "Vwalk.vwalk {(u, v). (h u, h v) \<in> R} p"
  shows "Vwalk.vwalk R (map h p)"
  using assms by (induction p rule: induct_list012) (auto elim!: in_dVsE(1))

lemma vwalk_bet_map:
  assumes "vwalk_bet {(u, v). (h u, h v) \<in> R} s p t"
  shows "vwalk_bet R (h s) (map h p) (h t)"
  using assms vwalk_map unfolding vwalk_bet_def by (auto simp: hd_map last_map)

lemma vwalk_unmap:
  assumes h: "inj h" "dVs R \<subseteq> range h" and q: "Vwalk.vwalk R q"
  shows "Vwalk.vwalk {(u, v). (h u, h v) \<in> R} (map (inv h) q)"
  using q
proof (induction q rule: induct_list012)
  case (2 x)
  then obtain w where w: "(x, w) \<in> R \<or> (w, x) \<in> R"
    by (auto elim: in_dVsE(1))
  then have rng: "x \<in> range h" "w \<in> range h"
    using h(2) by auto
  show ?case
    using w
  proof
    assume "(x, w) \<in> R"
    then have "(inv h x, inv h w) \<in> {(u, v). (h u, h v) \<in> R}"
      using rng by (simp add: f_inv_into_f)
    then show ?thesis
      by (simp add: dVsI(1))
  next
    assume "(w, x) \<in> R"
    then have "(inv h w, inv h x) \<in> {(u, v). (h u, h v) \<in> R}"
      using rng by (simp add: f_inv_into_f)
    then show ?thesis
      by (simp add: dVsI(2))
  qed
next
  case (3 x y zs)
  then have xy: "(x, y) \<in> R" "Vwalk.vwalk R (y # zs)"
    by simp_all
  then have "x \<in> range h" "y \<in> range h"
    using h(2) by auto
  then show ?case
    using 3(2)[OF xy(2)] xy(1) by (simp add: f_inv_into_f)
qed simp

lemma vwalk_bet_unmap:
  assumes h: "inj h" "dVs R \<subseteq> range h" and q: "vwalk_bet R (h s) q (h t)"
  shows "vwalk_bet {(u, v). (h u, h v) \<in> R} s (map (inv h) q) t"
  using q vwalk_unmap[OF h] h(1) unfolding vwalk_bet_def by (auto simp: hd_map last_map)

subsection \<open>The Operations\<close>

text \<open>The state: the flow, the set, the hull graph, the buckets and two counters.\<close>

record ('f, 'm, 'g, 'r) ostate =
  o_flow :: 'f
  o_memb :: 'm
  o_hull :: 'g
  o_bkt :: 'r
  o_cnt :: nat
  o_val :: nat

text \<open>Vertices are the nodes of the networks, edges are pairs of them. A flow is read on edges by
\<open>flow_lookup\<close> and augmented along a list of residual edges. The element set is a set ADT. A graph
of the ADT \<open>'g\<close> stands for the set of pairs \<open>graph_abs g\<close>, and \<open>path_search g al s t\<close> searches
a walk through its pairs allowed by \<open>al\<close>. The buckets are a map from pairs of vertices to lists of
residual edges, read by \<open>realising_lookup\<close>.\<close>

locale gammoid_oracle_spec =
  fixes flow_empty :: 'f and flow_invar :: "'f \<Rightarrow> bool"
    and flow_lookup :: "'f \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow> real"
    and augment :: "'f \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) Redge list \<Rightarrow> 'f"
    and memb_empty :: 'm and memb_ins :: "'a \<Rightarrow> 'm \<Rightarrow> 'm" and memb_del :: "'a \<Rightarrow> 'm \<Rightarrow> 'm"
    and memb_isin :: "'m \<Rightarrow> 'a \<Rightarrow> bool" and memb_set :: "'m \<Rightarrow> 'a set"
    and memb_invar :: "'m \<Rightarrow> bool"
    and graph_inv :: "'g \<Rightarrow> bool" and graph_abs :: "'g \<Rightarrow> 'a snode mnode dgraph"
    and path_search :: "'g \<Rightarrow> ('a snode mnode \<Rightarrow> 'a snode mnode \<Rightarrow> bool) \<Rightarrow> 'a snode mnode \<Rightarrow>
      'a snode mnode \<Rightarrow> 'a snode mnode list option"
    and realising_lookup :: "'r \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow>
      ('a snode mnode \<times> 'a snode mnode) Redge list option"
begin

abbreviation "res_bucket \<equiv> residual_buckets_spec.bucket realising_lookup"

text \<open>An edge of the network of all elements lies in the network of the set iff it is no edge into
the sink, or the edge of an element of the set into the sink.\<close>

definition sink_ok :: "'m \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow> bool" where
  "sink_ok mb e \<longleftrightarrow>
    (snd e = Snk \<longrightarrow> (case fst e of Nd (Vout x) \<Rightarrow> memb_isin mb x | _ \<Rightarrow> False))"

text \<open>Residual edges: a forward edge of the network of the set that carries no flow, or the
reverse of an edge that carries flow.\<close>

definition res_ok :: "'f \<Rightarrow> 'm \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) Redge \<Rightarrow> bool" where
  "res_ok fl mb r =
    (case r of F e \<Rightarrow> flow_lookup fl e < 1 \<and> sink_ok mb e | B e \<Rightarrow> 0 < flow_lookup fl e)"

text \<open>A pair is allowed if its bucket contains a residual edge; a path is lifted by choosing, for
every pair, the first residual edge of its bucket.\<close>

definition res_allowed :: "'r \<Rightarrow> 'f \<Rightarrow> 'm \<Rightarrow> 'a snode mnode \<Rightarrow> 'a snode mnode \<Rightarrow> bool" where
  "res_allowed bk fl mb u v = list_ex (res_ok fl mb) (res_bucket bk (u, v))"

definition res_lift :: "'r \<Rightarrow> 'f \<Rightarrow> 'm \<Rightarrow> 'a snode mnode list \<Rightarrow>
    ('a snode mnode \<times> 'a snode mnode) Redge list" where
  "res_lift bk fl mb p = map (\<lambda>d. the (find (res_ok fl mb) (res_bucket bk d))) (edges_of_vwalk p)"

abbreviation "o_search st \<equiv> path_search (o_hull st) (res_allowed (o_bkt st) (o_flow st) (o_memb st))"

abbreviation "o_augment st p \<equiv> augment (o_flow st) (res_lift (o_bkt st) (o_flow st) (o_memb st) p)"

text \<open>Augmenting until no path from the source to the sink is left, at most \<open>k\<close> times.\<close>

fun o_restore :: "nat \<Rightarrow> ('f, 'm, 'g, 'r) ostate \<Rightarrow> ('f, 'm, 'g, 'r) ostate" where
  "o_restore 0 st = st"
| "o_restore (Suc k) st =
    (case o_search st Src Snk of
      None \<Rightarrow> st
    | Some p \<Rightarrow> o_restore k (st\<lparr>o_flow := o_augment st p, o_val := Suc (o_val st)\<rparr>))"

definition o_init :: "'g \<Rightarrow> 'r \<Rightarrow> ('f, 'm, 'g, 'r) ostate" where
  "o_init g bk = \<lparr>o_flow = flow_empty, o_memb = memb_empty, o_hull = g, o_bkt = bk, o_cnt = 0,
     o_val = 0\<rparr>"

definition o_member :: "('f, 'm, 'g, 'r) ostate \<Rightarrow> 'a \<Rightarrow> bool" where
  "o_member st x = memb_isin (o_memb st) x"

definition o_query :: "('f, 'm, 'g, 'r) ostate \<Rightarrow> 'a \<Rightarrow> bool" where
  "o_query st y \<longleftrightarrow> o_val st = o_cnt st \<and>
     (memb_isin (o_memb st) y \<or> o_search st Src (Nd (Vout y)) \<noteq> None)"

definition o_insert :: "'a \<Rightarrow> ('f, 'm, 'g, 'r) ostate \<Rightarrow> ('f, 'm, 'g, 'r) ostate" where
  "o_insert x st = (if memb_isin (o_memb st) x then st
     else o_restore (Suc (Suc (o_cnt st) - o_val st))
       (st\<lparr>o_memb := memb_ins x (o_memb st), o_cnt := Suc (o_cnt st)\<rparr>))"

text \<open>Deletion cancels the flow on the edge of \<open>x\<close> into the sink, if any, and returns the unit to the
source along a residual path; then maximality is restored.\<close>

definition o_delete :: "'a \<Rightarrow> ('f, 'm, 'g, 'r) ostate \<Rightarrow> ('f, 'm, 'g, 'r) ostate" where
  "o_delete x st = (if \<not> memb_isin (o_memb st) x then st
     else let st1 = st\<lparr>o_memb := memb_del x (o_memb st), o_cnt := o_cnt st - 1\<rparr> in
       if 0 < flow_lookup (o_flow st) (Nd (Vout x), Snk) then
         let st2 = st1\<lparr>o_flow := augment (o_flow st) [B (Nd (Vout x), Snk)],
           o_val := o_val st - 1\<rparr> in
         (case o_search st2 (Nd (Vout x)) Src of
           None \<Rightarrow> st2
         | Some p \<Rightarrow> o_restore (Suc (o_cnt st2 - o_val st2)) (st2\<lparr>o_flow := o_augment st2 p\<rparr>))
       else st1)"

definition o_exch :: "('f, 'm, 'g, 'r) ostate \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "o_exch st x y = (if memb_isin (o_memb st) x then o_query (o_delete x st) y else o_query st y)"

end

subsection \<open>Correctness\<close>

text \<open>The assumptions. Augmenting must agree with augmentation in the flow library along residual
edges, at least when the result has unit shape. The search may return any distinct walk through
the allowed pairs of the graph, for every graph and every predicate.\<close>

locale gammoid_oracle =
  gammoid_oracle_spec flow_empty flow_invar flow_lookup augment
    memb_empty memb_ins memb_del memb_isin memb_set memb_invar
    graph_inv graph_abs path_search realising_lookup +
  gammoid G S +
  memb: Set memb_empty memb_ins memb_del memb_isin memb_set memb_invar
  for flow_empty :: 'f and flow_invar
    and flow_lookup :: "'f \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow> real"
    and augment and memb_empty :: 'm
    and memb_ins memb_del memb_isin memb_set memb_invar and graph_inv :: "'g \<Rightarrow> bool"
    and graph_abs path_search and realising_lookup :: "'r \<Rightarrow> _"
    and G :: "'a dgraph" and S +
  assumes flow_empty: "flow_invar flow_empty" "flow_lookup flow_empty = (\<lambda>_. 0)"
    and augment: "\<lbrakk>flow_invar fl; set rs \<subseteq> nresE T (flow_lookup fl); distinct (map ntvp rs);
      unit_shape {e. naug (flow_lookup fl) rs e \<noteq> 0}\<rbrakk> \<Longrightarrow>
      flow_invar (augment fl rs) \<and> flow_lookup (augment fl rs) = naug (flow_lookup fl) rs"
    and search_some: "\<lbrakk>graph_inv g; s \<noteq> t; path_search g al s t = Some p\<rbrakk> \<Longrightarrow>
      distinct p \<and> vwalk_bet {(u, v). (u, v) \<in> graph_abs g \<and> al u v} s p t"
    and search_none: "\<lbrakk>graph_inv g; s \<noteq> t; path_search g al s t = None\<rbrakk> \<Longrightarrow>
      \<not> (\<exists>p. vwalk_bet {(u, v). (u, v) \<in> graph_abs g \<and> al u v} s p t)"
begin

text \<open>The graph of the state is the symmetric hull of the network of all elements, and its
buckets hold the residual edges of that network.\<close>

definition hull_ok :: "'g \<Rightarrow> bool" where
  "hull_ok g \<longleftrightarrow> graph_inv g \<and>
     graph_abs g = {(u, v). (u, v) \<in> net (dVs G) \<or> (v, u) \<in> net (dVs G)}"

definition bkt_ok :: "'r \<Rightarrow> bool" where
  "bkt_ok bk \<longleftrightarrow>
     (\<forall>d. set (res_bucket bk d) = {r. r \<in> flow_network_spec.\<EE> (net (dVs G)) \<and> ntvp r = d})"

lemma EE_hull:
  "r \<in> flow_network_spec.\<EE> (net X) \<Longrightarrow> ntvp r \<in> {(u, v). (u, v) \<in> net X \<or> (v, u) \<in> net X}"
  by (cases r) (auto simp: EE_net_iff ntvp_simps)

lemma nresE_EE:
  assumes "T \<subseteq> dVs G" "r \<in> nresE T f"
  shows "r \<in> flow_network_spec.\<EE> (net (dVs G))"
  using assms(2) net_mono[OF assms(1)] by (cases r) (auto simp: nresE_iff EE_net_iff)

text \<open>The network of the set is cut out of the network of all elements by \<open>sink_ok\<close>.\<close>

lemma net_sink_ok:
  assumes T: "T \<subseteq> dVs G" and mb: "memb_invar mb" "memb_set mb = T"
    and e: "e \<in> net (dVs G)"
  shows "e \<in> net T \<longleftrightarrow> sink_ok mb e"
proof -
  obtain a b where ab: "e = (a, b)"
    by (cases e)
  show ?thesis
  proof (cases "b = Snk")
    case True
    then obtain t where t: "t \<in> dVs G" "a = Nd (Vout t)"
      using e unfolding ab by (auto simp: net_iff)
    have "(Nd (Vout t), Snk) \<in> net T \<longleftrightarrow> t \<in> T"
      using t(1) by (auto simp: net_iff)
    then show ?thesis
      using mb memb.set_isin unfolding ab True t(2) sink_ok_def by simp
  next
    case False
    then show ?thesis
      using e unfolding ab sink_ok_def by (auto simp: net_iff)
  qed
qed

text \<open>The residual edges of the network of all elements that \<open>res_ok\<close> accepts are the residual
edges of the network of the set, as long as the flow lies in the latter.\<close>

lemma res_ok_iff:
  assumes T: "T \<subseteq> dVs G" and mb: "memb_invar mb" "memb_set mb = T"
    and f: "\<forall>e. e \<notin> net T \<longrightarrow> flow_lookup fl e = 0"
    and r: "r \<in> flow_network_spec.\<EE> (net (dVs G))"
  shows "res_ok fl mb r \<longleftrightarrow> r \<in> nresE T (flow_lookup fl)"
proof (cases r)
  case (F e)
  then have "e \<in> net (dVs G)"
    using r by (simp add: EE_net_iff)
  then show ?thesis
    using net_sink_ok[OF T mb] unfolding F nresE_iff by (auto simp: res_ok_def)
next
  case (B e)
  have "e \<in> net T" if "0 < flow_lookup fl e"
  proof (rule ccontr)
    assume "e \<notin> net T"
    then have "flow_lookup fl e = 0"
      using f by blast
    then show False
      using that by simp
  qed
  then show ?thesis
    unfolding B nresE_iff by (auto simp: res_ok_def)
qed

lemma res_allowed_iff:
  assumes T: "T \<subseteq> dVs G" and mb: "memb_invar mb" "memb_set mb = T"
    and f: "\<forall>e. e \<notin> net T \<longrightarrow> flow_lookup fl e = 0" and bk: "bkt_ok bk"
  shows "res_allowed bk fl mb u v \<longleftrightarrow> (u, v) \<in> nres T (flow_lookup fl)"
proof -
  have "res_allowed bk fl mb u v \<longleftrightarrow>
      (\<exists>r. r \<in> flow_network_spec.\<EE> (net (dVs G)) \<and> ntvp r = (u, v) \<and> res_ok fl mb r)"
    using bk by (auto simp: res_allowed_def list_ex_iff bkt_ok_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>r. r \<in> nresE T (flow_lookup fl) \<and> ntvp r = (u, v))"
    using res_ok_iff[OF T mb f] nresE_EE[OF T] by blast
  also have "\<dots> \<longleftrightarrow> (u, v) \<in> nres T (flow_lookup fl)"
    unfolding image_iff Bex_def by (rule ex_cong1) (rule conj_cong[OF refl eq_commute])
  finally show ?thesis .
qed

text \<open>The allowed pairs of the hull are the residual pairs.\<close>

lemma res_hull:
  assumes T: "T \<subseteq> dVs G" and mb: "memb_invar mb" "memb_set mb = T"
    and f: "\<forall>e. e \<notin> net T \<longrightarrow> flow_lookup fl e = 0" and bk: "bkt_ok bk" and g: "hull_ok g"
  shows "{(u, v). (u, v) \<in> graph_abs g \<and> res_allowed bk fl mb u v} = nres T (flow_lookup fl)"
proof -
  have "nres T (flow_lookup fl) \<subseteq> graph_abs g"
  proof
    fix d
    assume "d \<in> nres T (flow_lookup fl)"
    then obtain r where "r \<in> nresE T (flow_lookup fl)" "d = ntvp r"
      by blast
    then show "d \<in> graph_abs g"
      using g EE_hull[OF nresE_EE[OF T]] by (simp add: hull_ok_def)
  qed
  then show ?thesis
    using res_allowed_iff[OF T mb f bk] by auto
qed

text \<open>The lifted residual edges realise the path.\<close>

lemma res_lift_correct:
  assumes T: "T \<subseteq> dVs G" and mb: "memb_invar mb" "memb_set mb = T"
    and f: "\<forall>e. e \<notin> net T \<longrightarrow> flow_lookup fl e = 0" and bk: "bkt_ok bk"
    and p: "vwalk_bet (nres T (flow_lookup fl)) s p t"
  shows "map ntvp (res_lift bk fl mb p) = edges_of_vwalk p"
    "set (res_lift bk fl mb p) \<subseteq> nresE T (flow_lookup fl)"
proof -
  let ?pk = "\<lambda>d. the (find (res_ok fl mb) (res_bucket bk d))"
  have pk: "ntvp (?pk d) = d \<and> ?pk d \<in> nresE T (flow_lookup fl)"
    if "d \<in> set (edges_of_vwalk p)" for d
  proof -
    obtain u v where d: "d = (u, v)"
      by (cases d)
    have "res_allowed bk fl mb u v"
      using res_allowed_iff[OF T mb f bk] vwalk_bet_edges_in_edges[OF p] that d by blast
    then obtain r where r: "find (res_ok fl mb) (res_bucket bk d) = Some r"
      unfolding res_allowed_def list_ex_iff d by (metis find_None_iff not_None_eq)
    then have "r \<in> set (res_bucket bk d)" "res_ok fl mb r"
      by (auto simp: find_Some_iff)
    then show ?thesis
      using bk res_ok_iff[OF T mb f] r d by (auto simp: bkt_ok_def)
  qed
  show "map ntvp (res_lift bk fl mb p) = edges_of_vwalk p"
    unfolding res_lift_def map_map by (rule map_idI) (simp add: pk)
  show "set (res_lift bk fl mb p) \<subseteq> nresE T (flow_lookup fl)"
    unfolding res_lift_def using pk by auto
qed

text \<open>The search on the residual pairs.\<close>

lemma search_res:
  assumes T: "T \<subseteq> dVs G" and mb: "memb_invar mb" "memb_set mb = T"
    and f: "\<forall>e. e \<notin> net T \<longrightarrow> flow_lookup fl e = 0" and bk: "bkt_ok bk" and g: "hull_ok g"
    and st: "s \<noteq> t"
  shows "path_search g (res_allowed bk fl mb) s t = Some p \<Longrightarrow>
      distinct p \<and> vwalk_bet (nres T (flow_lookup fl)) s p t"
    "path_search g (res_allowed bk fl mb) s t = None \<longleftrightarrow>
      \<not> (\<exists>q. vwalk_bet (nres T (flow_lookup fl)) s q t)"
proof -
  have gi: "graph_inv g"
    using g by (simp add: hull_ok_def)
  note hull = res_hull[OF T mb f bk g]
  note some = search_some[OF gi st, where al = "res_allowed bk fl mb", unfolded hull]
  note none = search_none[OF gi st, where al = "res_allowed bk fl mb", unfolded hull]
  show "path_search g (res_allowed bk fl mb) s t = Some p \<Longrightarrow>
      distinct p \<and> vwalk_bet (nres T (flow_lookup fl)) s p t"
    by (rule some)
  show "path_search g (res_allowed bk fl mb) s t = None \<longleftrightarrow>
      \<not> (\<exists>q. vwalk_bet (nres T (flow_lookup fl)) s q t)"
  proof (cases "path_search g (res_allowed bk fl mb) s t")
    case None
    then show ?thesis
      using none by simp
  next
    case (Some p)
    then show ?thesis
      using some[OF Some] by auto
  qed
qed

text \<open>Augmenting along the lifted residual edges of a path.\<close>

lemma augment_res:
  assumes T: "T \<subseteq> dVs G" and mb: "memb_invar mb" "memb_set mb = T"
    and f: "\<forall>e. e \<notin> net T \<longrightarrow> flow_lookup fl e = 0" and bk: "bkt_ok bk"
    and fl: "flow_invar fl" and p: "distinct p" "vwalk_bet (nres T (flow_lookup fl)) s p t"
  defines "rs \<equiv> res_lift bk fl mb p"
  shows "map ntvp rs = edges_of_vwalk p" "set rs \<subseteq> nresE T (flow_lookup fl)"
    "unit_shape {e. naug (flow_lookup fl) rs e \<noteq> 0} \<Longrightarrow>
       flow_invar (augment fl rs) \<and> flow_lookup (augment fl rs) = naug (flow_lookup fl) rs"
proof -
  show rs: "map ntvp rs = edges_of_vwalk p" "set rs \<subseteq> nresE T (flow_lookup fl)"
    unfolding rs_def by (rule res_lift_correct[OF T mb f bk p(2)])+
  have "distinct (map ntvp rs)"
    unfolding rs(1) by (rule distinct_edges_of_vwalk[OF p(1)])
  then show "unit_shape {e. naug (flow_lookup fl) rs e \<noteq> 0} \<Longrightarrow>
      flow_invar (augment fl rs) \<and> flow_lookup (augment fl rs) = naug (flow_lookup fl) rs"
    using augment[OF fl rs(2)] by blast
qed

subsection \<open>The Invariant\<close>

text \<open>The stored set is \<open>T\<close>, and the stored flow is a unit flow of its network, of value \<open>o_val\<close>;
\<open>o_invar\<close> also requires it to be maximum.\<close>

definition o_inv :: "'a set \<Rightarrow> ('f, 'm, 'g, 'r) ostate \<Rightarrow> bool" where
  "o_inv T st \<longleftrightarrow> flow_invar (o_flow st) \<and> memb_invar (o_memb st) \<and> memb_set (o_memb st) = T \<and>
     T \<subseteq> dVs G \<and> uflow T (flow_lookup (o_flow st)) \<and> o_cnt st = card T \<and>
     real (o_val st) = nex T (flow_lookup (o_flow st)) Snk \<and> hull_ok (o_hull st) \<and> bkt_ok (o_bkt st)"

definition o_invar :: "'a set \<Rightarrow> ('f, 'm, 'g, 'r) ostate \<Rightarrow> bool" where
  "o_invar T st \<longleftrightarrow> o_inv T st \<and> mstate T (flow_lookup (o_flow st))"

lemma o_inv_flow:
  assumes "o_inv T st"
  shows "\<forall>e. e \<notin> net T \<longrightarrow> flow_lookup (o_flow st) e = 0"
  using assms by (simp add: o_inv_def uflow_def)

lemma o_restore_correct:
  assumes "o_inv T st" "card T - o_val st < k"
  shows "o_invar T (o_restore k st)"
  using assms
proof (induction k arbitrary: st)
  case (Suc k)
  let ?fl = "o_flow st" and ?mb = "o_memb st" and ?bk = "o_bkt st"
  have inv: "flow_invar ?fl" "memb_invar ?mb" "memb_set ?mb = T" "T \<subseteq> dVs G"
    "uflow T (flow_lookup ?fl)" "o_cnt st = card T" "real (o_val st) = nex T (flow_lookup ?fl) Snk"
    "hull_ok (o_hull st)" "bkt_ok ?bk"
    using Suc.prems(1) by (simp_all add: o_inv_def)
  note f = o_inv_flow[OF Suc.prems(1)]
  note search = search_res[OF inv(4,2,3) f inv(9,8), of Src Snk]
  show ?case
  proof (cases "o_search st Src Snk")
    case None
    then show ?thesis
      using search(2) Suc.prems(1) by (simp add: o_invar_def mstate_def inv(5))
  next
    case (Some p)
    then have p: "distinct p" "vwalk_bet (nres T (flow_lookup ?fl)) Src p Snk"
      using search(1) by blast+
    let ?rs = "res_lift ?bk ?fl ?mb p"
    note rs = augment_res[OF inv(4,2,3) f inv(9,1) p]
    note aug = uflow_augment[OF inv(5) p rs(1,2)]
    have new: "flow_invar (o_augment st p)" "flow_lookup (o_augment st p) = naug (flow_lookup ?fl) ?rs"
      using rs(3) uflow_unit_shape[OF aug(1)] by blast+
    let ?st = "st\<lparr>o_flow := o_augment st p, o_val := Suc (o_val st)\<rparr>"
    have "o_inv T ?st"
      using inv new aug by (simp add: o_inv_def)
    moreover have "Suc (o_val st) \<le> card T"
      using uflow_val_le[OF aug(1) inv(4)] aug(2) inv(7) by simp
    then have "card T - o_val ?st < k"
      using Suc.prems(2) by simp
    ultimately show ?thesis
      using Some Suc.IH by simp
  qed
qed simp

subsection \<open>Correctness of the Operations\<close>

theorem o_invar_init:
  assumes "hull_ok g" "bkt_ok bk"
  shows "o_invar {} (o_init g bk)"
  using assms flow_empty memb.invar_empty memb.set_empty mstate_empty
  by (simp add: o_init_def o_invar_def o_inv_def mstate_def nex_unfold)

theorem o_member_correct: "o_invar T st \<Longrightarrow> o_member st x \<longleftrightarrow> x \<in> T"
  by (simp add: o_invar_def o_inv_def o_member_def memb.set_isin)

theorem o_query_correct:
  assumes I: "o_invar T st" and y: "y \<in> dVs G"
  shows "o_query st y \<longleftrightarrow> gammoid_indep (insert y T)"
proof -
  let ?fl = "o_flow st" and ?mb = "o_memb st"
  have inv: "flow_invar ?fl" "memb_invar ?mb" "memb_set ?mb = T" "T \<subseteq> dVs G"
    "o_cnt st = card T" "real (o_val st) = nex T (flow_lookup ?fl) Snk" "mstate T (flow_lookup ?fl)"
    "hull_ok (o_hull st)" "bkt_ok (o_bkt st)"
    using I by (simp_all add: o_invar_def o_inv_def)
  have val: "o_val st = o_cnt st \<longleftrightarrow> nex T (flow_lookup ?fl) Snk = card T"
    using inv(5,6) by (metis of_nat_eq_iff)
  show ?thesis
  proof (cases "y \<in> T")
    case True
    then show ?thesis
      using inv(2,3) val mstate_indep[OF inv(4,7)]
      by (simp add: o_query_def memb.set_isin insert_absorb)
  next
    case False
    have "Src \<noteq> Nd (Vout y)"
      by simp
    then have "o_search st Src (Nd (Vout y)) \<noteq> None \<longleftrightarrow>
        (\<exists>q. vwalk_bet (nres T (flow_lookup ?fl)) Src q (Nd (Vout y)))"
      using search_res(2)[OF inv(4,2,3) o_inv_flow[OF I[unfolded o_invar_def, THEN conjunct1]]
          inv(9,8)]
      by simp
    then show ?thesis
      using False inv(2,3) val mstate_query[OF inv(4,7) y False]
      by (simp add: o_query_def memb.set_isin)
  qed
qed

theorem o_invar_insert:
  assumes I: "o_invar T st" and x: "x \<in> dVs G"
  shows "o_invar (insert x T) (o_insert x st)"
proof (cases "x \<in> T")
  case True
  then show ?thesis
    using I by (simp add: o_insert_def o_invar_def o_inv_def memb.set_isin insert_absorb)
next
  case False
  let ?fl = "o_flow st" and ?mb = "o_memb st"
  have inv: "flow_invar ?fl" "memb_invar ?mb" "memb_set ?mb = T" "T \<subseteq> dVs G"
    "uflow T (flow_lookup ?fl)" "o_cnt st = card T" "real (o_val st) = nex T (flow_lookup ?fl) Snk"
    "hull_ok (o_hull st)" "bkt_ok (o_bkt st)"
    using I by (simp_all add: o_invar_def o_inv_def)
  have finT: "finite T"
    using inv(4) dVs_finite by (rule finite_subset)
  let ?st = "st\<lparr>o_memb := memb_ins x ?mb, o_cnt := Suc (o_cnt st)\<rparr>"
  have "o_inv (insert x T) ?st"
    using inv x False finT uflow_insert[OF inv(5) x False] memb.invar_insert memb.set_insert
    by (simp add: o_inv_def)
  moreover have "card (insert x T) - o_val ?st < Suc (Suc (o_cnt st) - o_val st)"
    using False finT inv(6) by simp
  ultimately have "o_invar (insert x T) (o_restore (Suc (Suc (o_cnt st) - o_val st)) ?st)"
    by (rule o_restore_correct)
  moreover have "o_insert x st = o_restore (Suc (Suc (o_cnt st) - o_val st)) ?st"
    using False inv(2,3) by (simp add: o_insert_def memb.set_isin del: o_restore.simps)
  ultimately show ?thesis
    by simp
qed

theorem o_invar_delete:
  assumes I: "o_invar T st"
  shows "o_invar (T - {x}) (o_delete x st)"
proof (cases "x \<in> T")
  case False
  then show ?thesis
    using I by (simp add: o_delete_def o_invar_def o_inv_def memb.set_isin)
next
  case True
  let ?fl = "o_flow st" and ?mb = "o_memb st" and ?f = "flow_lookup (o_flow st)"
  let ?T = "T - {x}" and ?a = "(Nd (Vout x), Snk)"
  have inv: "flow_invar ?fl" "memb_invar ?mb" "memb_set ?mb = T" "T \<subseteq> dVs G"
    "uflow T ?f" "o_cnt st = card T" "real (o_val st) = nex T ?f Snk" "mstate T ?f"
    "hull_ok (o_hull st)" "bkt_ok (o_bkt st)"
    using I by (simp_all add: o_invar_def o_inv_def)
  have x: "x \<in> dVs G"
    using True inv(4) by blast
  have T': "?T \<subseteq> dVs G"
    using inv(4) by blast
  have finT: "finite T"
    using inv(4) dVs_finite by (rule finite_subset)
  have mb': "memb_invar (memb_del x ?mb)" "memb_set (memb_del x ?mb) = ?T"
    using inv(2,3) memb.invar_delete memb.set_delete by simp_all
  have cnt': "o_cnt st - 1 = card ?T"
    using True finT inv(6) by simp
  have car: "0 < ?f ?a \<longleftrightarrow> ?f ?a \<noteq> 0"
    using uflow_range[OF inv(5), of ?a] by auto
  let ?st1 = "st\<lparr>o_memb := memb_del x ?mb, o_cnt := o_cnt st - 1\<rparr>"
  show ?thesis
  proof (cases "?f ?a = 0")
    case True
    have free: "uflow ?T ?f" "nex ?T ?f Snk = nex T ?f Snk"
      using uflow_delete_free[OF inv(5) True] by simp_all
    have "nres ?T ?f \<subseteq> nres T ?f"
    proof (rule subrelI)
      fix a b
      assume "(a, b) \<in> nres ?T ?f"
      then show "(a, b) \<in> nres T ?f"
        using net_mono[of ?T T] unfolding nres_iff by blast
    qed
    then have "mstate ?T ?f"
      using inv(8) free(1) unfolding mstate_def by (meson vwalk_bet_subset)
    then have "o_invar ?T ?st1"
      using inv mb' cnt' free T' by (simp add: o_invar_def o_inv_def)
    moreover have "o_delete x st = ?st1"
      using \<open>x \<in> T\<close> True inv(2,3) by (simp add: o_delete_def memb.set_isin)
    ultimately show ?thesis
      by simp
  next
    case False
    have fa: "?f ?a = 1" "?a \<in> net T"
      using False uflow_range[OF inv(5), of ?a] inv(5) by (auto simp: uflow_def)
    let ?rs = "[B ?a]"
    have "B ?a \<in> nresE T ?f"
      unfolding nresE_iff using fa by simp
    then have rs: "map ntvp ?rs = [(Snk, Nd (Vout x))]" "set ?rs \<subseteq> nresE T ?f"
      by (simp_all add: ntvp_simps)
    note can = delete_cancel[OF inv(5) \<open>x \<in> T\<close> x False rs]
    let ?fl1 = "augment ?fl ?rs" and ?g = "naug ?f ?rs"
    have "{e. ?g e \<noteq> 0} \<subseteq> {e. ?f e \<noteq> 0}"
      unfolding can(1) by auto
    then have "unit_shape {e. ?g e \<noteq> 0}"
      by (rule unit_shape_mono[OF uflow_unit_shape[OF inv(5)]])
    then have fl1: "flow_invar ?fl1" "flow_lookup ?fl1 = ?g"
      using augment[OF inv(1) rs(2)] by simp_all
    have cons: "nex T ?f v = 0" if "v \<noteq> Src" "v \<noteq> Snk" for v
      using inv(5) that by (simp add: uflow_def)
    have sum0: "nex T ?f Src + nex T ?f Snk = 0"
      using inv(5) by (simp add: uflow_def)
    have g_ex: "\<And>v. \<lbrakk>v \<noteq> Src; v \<noteq> Snk; v \<noteq> Nd (Vout x)\<rbrakk> \<Longrightarrow> nex ?T ?g v = 0"
      "nex ?T ?g (Nd (Vout x)) = 1" "nex ?T ?g Src + nex ?T ?g Snk = -1"
    proof -
      fix v
      assume "v \<noteq> Src" "v \<noteq> Snk" "v \<noteq> Nd (Vout x)"
      then show "nex ?T ?g v = 0"
        using can(4)[of v] cons by simp
    next
      show "nex ?T ?g (Nd (Vout x)) = 1"
        using can(4)[of "Nd (Vout x)"] by simp
    next
      show "nex ?T ?g Src + nex ?T ?g Snk = -1"
        using can(4)[of Src] can(4)[of Snk] sum0 by simp
    qed
    have g_flow: "\<forall>e. e \<notin> net ?T \<longrightarrow> flow_lookup ?fl1 e = 0"
      "\<forall>e. flow_lookup ?fl1 e = 0 \<or> flow_lookup ?fl1 e = 1"
      using can(2,3) unfolding fl1(2) by simp_all
    let ?st2 = "?st1\<lparr>o_flow := ?fl1, o_val := o_val st - 1\<rparr>"
    have sv: "Nd (Vout x) \<noteq> Src"
      by simp
    note search = search_res[OF T' mb' g_flow(1) inv(10,9) sv]
    have wV: "Nd (Vout x) \<in> dVs (net ?T)"
      by (rule dVsI(2)[OF node_arc_net[OF x]])
    obtain q where "distinct q" "vwalk_bet (nres ?T ?g) (Nd (Vout x)) q Src"
      by (rule excess_walk[OF can(2,3) g_ex(1,2) wV]) simp_all
    then have "o_search ?st2 (Nd (Vout x)) Src \<noteq> None"
      using search(2) unfolding fl1(2) by simp blast
    then obtain p where p: "o_search ?st2 (Nd (Vout x)) Src = Some p"
      by blast
    then have pw: "distinct p" "vwalk_bet (nres ?T (flow_lookup ?fl1)) (Nd (Vout x)) p Src"
      using search(1) by simp_all
    let ?rs' = "res_lift (o_bkt st) ?fl1 (memb_del x ?mb) p"
    note rs' = augment_res[OF T' mb' g_flow(1) inv(10) fl1(1) pw]
    note ret = delete_return[OF g_flow g_ex[folded fl1(2)] _ _ pw rs'(1,2)]
    have ret': "uflow ?T (naug (flow_lookup ?fl1) ?rs')"
      "nex ?T (naug (flow_lookup ?fl1) ?rs') Snk = nex T ?f Snk - 1"
      using ret can(4)[of Snk] fl1(2) by simp_all
    have fl2: "flow_invar (augment ?fl1 ?rs')"
      "flow_lookup (augment ?fl1 ?rs') = naug (flow_lookup ?fl1) ?rs'"
      using rs'(3) uflow_unit_shape[OF ret'(1)] by simp_all
    have "1 \<le> nex T ?f Snk"
      using uflow_val_nonneg[OF ret'(1)] ret'(2) by simp
    then have val: "real (o_val st - 1) = nex ?T (flow_lookup (augment ?fl1 ?rs')) Snk"
      using inv(7) fl2(2) ret'(2) by simp
    let ?st3 = "?st2\<lparr>o_flow := augment ?fl1 ?rs'\<rparr>"
    have "o_inv ?T ?st3"
      using fl2 mb' T' ret'(1) cnt' val inv(9,10) by (simp add: o_inv_def)
    moreover have "card ?T - o_val ?st3 < Suc (o_cnt ?st2 - o_val ?st2)"
      using cnt' by simp
    ultimately have "o_invar ?T (o_restore (Suc (o_cnt ?st2 - o_val ?st2)) ?st3)"
      by (rule o_restore_correct)
    moreover have "o_delete x st = o_restore (Suc (o_cnt ?st2 - o_val ?st2)) ?st3"
      using \<open>x \<in> T\<close> False car inv(2,3) p
      by (simp add: o_delete_def memb.set_isin Let_def del: o_restore.simps)
    ultimately show ?thesis
      by simp
  qed
qed

theorem o_exch_correct:
  assumes I: "o_invar T st" and y: "y \<in> dVs G"
  shows "o_exch st x y \<longleftrightarrow> gammoid_indep (insert y (T - {x}))"
  using o_query_correct[OF o_invar_delete[OF I] y] o_query_correct[OF I y] I
  by (auto simp: o_exch_def o_invar_def o_inv_def memb.set_isin)

theorem o_exch_state:
  assumes I: "o_invar T st" and x: "x \<in> T"
  shows "o_invar T (o_insert x (o_delete x st))"
proof -
  have "x \<in> dVs G"
    using I x by (auto simp: o_invar_def o_inv_def)
  then have "o_invar (insert x (T - {x})) (o_insert x (o_delete x st))"
    by (rule o_invar_insert[OF o_invar_delete[OF I]])
  then show ?thesis
    by (simp only: insert_Diff[OF x])
qed

end

end

