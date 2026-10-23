theory Gammoid_Oracle
  imports
    Gammoid_Oracle_Generic
    Graph_Algorithms_Dev.DFS
    Data_Structures.Fixed_Univ_Map_Specs
    Matroids_Greedy.Best_In_Greedy
begin

section \<open>An Independence Oracle for Gammoids\<close>

text \<open>We instantiate the generic oracle. The hull is a list of node pairs, built once from the
input. Every search builds the residual graph of the current flow from the hull and runs a
depth-first search on it. The flow is a map with a fixed universe from the edges of the network of
all elements to Booleans.\<close>

subsection \<open>The Hull as a List\<close>

text \<open>The edges of the network of all elements, given the edges of \<open>G\<close> and the elements of \<open>S\<close>
as lists. Every edge of \<open>G\<close> contributes a block of node pairs; pairs may occur several times.\<close>

definition net_block :: "'a \<Rightarrow> 'a \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) list" where
  "net_block u v = [(Nd (Vin u), Nd (Vout u)), (Nd (Vout u), Snk),
     (Nd (Vin v), Nd (Vout v)), (Nd (Vout v), Snk)] @
     (if u = v then [] else [(Nd (Vout u), Nd (Vin v))])"

definition net_list :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) list" where
  "net_list es ss = concat (map (case_prod net_block) es) @ map (\<lambda>s. (Src, Nd (Vin s))) ss"

definition hull_list :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) list" where
  "hull_list es ss = (let N = net_list es ss in N @ map prod.swap N)"

lemma set_hull_list:
  "set (hull_list es ss) = {(u, v). (u, v) \<in> set (net_list es ss) \<or> (v, u) \<in> set (net_list es ss)}"
  by (auto simp: hull_list_def Let_def)

lemma set_net_block:
  "e \<in> set (net_block u v) \<longleftrightarrow>
    e = (Nd (Vin u), Nd (Vout u)) \<or> e = (Nd (Vout u), Snk) \<or>
    e = (Nd (Vin v), Nd (Vout v)) \<or> e = (Nd (Vout v), Snk) \<or> (u \<noteq> v \<and> e = (Nd (Vout u), Nd (Vin v)))"
  by (simp add: net_block_def)

context gammoid
begin

lemma net_dVs_iff:
  "e \<in> net (dVs G) \<longleftrightarrow>
    (\<exists>w \<in> dVs G. e = (Nd (Vin w), Nd (Vout w)) \<or> e = (Nd (Vout w), Snk)) \<or>
    (\<exists>(u, v) \<in> G. u \<noteq> v \<and> e = (Nd (Vout u), Nd (Vin v))) \<or> (\<exists>s \<in> S. e = (Src, Nd (Vin s)))"
  by (auto simp: net_iff net_graph_iff)

lemma set_net_list:
  assumes es: "set es = G" and ss: "set ss = S"
  shows "set (net_list es ss) = net (dVs G)"
proof (rule set_eqI, rule iffI)
  fix e
  assume "e \<in> set (net_list es ss)"
  then consider (blk) u v where "(u, v) \<in> G" "e \<in> set (net_block u v)"
    | (src) s where "s \<in> S" "e = (Src, Nd (Vin s))"
    by (auto simp: net_list_def es[symmetric] ss[symmetric])
  then show "e \<in> net (dVs G)"
  proof cases
    case blk
    then have "u \<in> dVs G" "v \<in> dVs G"
      by auto
    then show ?thesis
      using blk unfolding net_dVs_iff set_net_block by auto
  next
    case src
    then show ?thesis
      unfolding net_dVs_iff by auto
  qed
next
  fix e
  have blk: "e \<in> set (net_list es ss)" if "(u, v) \<in> G" "e \<in> set (net_block u v)" for u v
    using that by (auto simp: net_list_def es[symmetric] intro!: bexI[of _ "(u, v)"])
  assume "e \<in> net (dVs G)"
  then consider (w) w where "w \<in> dVs G" "e = (Nd (Vin w), Nd (Vout w)) \<or> e = (Nd (Vout w), Snk)"
    | (uv) u v where "(u, v) \<in> G" "u \<noteq> v" "e = (Nd (Vout u), Nd (Vin v))"
    | (src) s where "s \<in> S" "e = (Src, Nd (Vin s))"
    unfolding net_dVs_iff by blast
  then show "e \<in> set (net_list es ss)"
  proof cases
    case w
    then obtain u v where uv: "(u, v) \<in> G" "w = u \<or> w = v"
      by (auto simp: dVs_def)
    then show ?thesis
      using w(2) by (intro blk[OF uv(1)]) (auto simp: set_net_block)
  next
    case uv
    then show ?thesis
      by (intro blk[OF uv(1)]) (simp add: set_net_block)
  next
    case src
    then show ?thesis
      by (simp add: net_list_def ss[symmetric])
  qed
qed

end

subsection \<open>Searching in the Residual Graph\<close>

text \<open>The residual graph is built from a list of pairs and a predicate telling which pairs are
allowed. It is an adjacency map of the graph ADT of the depth-first search.\<close>

locale gammoid_search =
  Graph: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
  for lookup :: "'adj \<Rightarrow> 'a snode mnode \<Rightarrow> 'vset option"
begin

sublocale dfs: DFS where insert = insert and sel = sel and vset_empty = vset_empty
  and diff = diff and lookup = lookup and empty = empty and delete = delete and isin = isin
  and t_set = t_set and update = update and adjmap_inv = adjmap_inv
  and vset_delete = vset_delete and vset_inv = vset_inv and union = union and inter = inter
  and G = R and s = s and t = t
  for R s t
  by unfold_locales

definition res_graph :: "('a snode mnode \<times> 'a snode mnode) list \<Rightarrow>
    ('a snode mnode \<Rightarrow> 'a snode mnode \<Rightarrow> bool) \<Rightarrow> 'adj" where
  "res_graph hs al = fold (\<lambda>(u, v) R. if al u v then Graph.add_edge R u v else R) hs empty"

definition path_search :: "('a snode mnode \<times> 'a snode mnode) list \<Rightarrow>
    ('a snode mnode \<Rightarrow> 'a snode mnode \<Rightarrow> bool) \<Rightarrow> 'a snode mnode \<Rightarrow> 'a snode mnode \<Rightarrow>
    'a snode mnode list option" where
  "path_search hs al s t =
     (let st = dfs.DFS_impl (res_graph hs al) t (dfs.initial_state s) in
      if return st = Reachable then Some (rev (stack st)) else None)"

lemma res_graph_from_list: "res_graph hs al = Graph.from_list (filter (case_prod al) hs)"
  unfolding res_graph_def Graph.from_list_def' fold_filter
  by (rule fold_cong) (auto split: prod.splits)

lemma res_graph:
  "Graph.graph_inv (res_graph hs al)" "Graph.finite_graph (res_graph hs al)"
  "Graph.finite_vsets (res_graph hs al)"
  "Graph.digraph_abs (res_graph hs al) = {(u, v). (u, v) \<in> set hs \<and> al u v}"
  unfolding res_graph_from_list by (auto simp: Graph.from_list_correct(2,3))

text \<open>If the start is no vertex of the graph, the search stops at once.\<close>

lemma DFS_impl_no_vertex:
  assumes "Graph.graph_inv R" "s \<notin> dVs (Graph.digraph_abs R)" "s \<noteq> t"
  shows "return (dfs.DFS_impl R t (dfs.initial_state s)) = NotReachable"
proof -
  have "diff (Graph.neighbourhood R s) (insert s vset_empty) = vset_empty"
    using Graph.s_non_in_dVs_neighb_empty[OF assms(2)] dfs.subtract_from_empty
      Graph.vset.set.invar_insert Graph.vset.set.invar_empty by simp
  then have "dfs.DFS_impl R t (dfs.initial_state s) =
      dfs.DFS_impl R t ((dfs.initial_state s)\<lparr>stack := []\<rparr>)"
    using assms(3) by (subst dfs.DFS_impl.simps) (simp add: dfs.initial_state_def)
  also have "\<dots> = (dfs.initial_state s)\<lparr>stack := [], return := NotReachable\<rparr>"
    by (subst dfs.DFS_impl.simps) simp
  finally show ?thesis
    by simp
qed

theorem path_search_correct:
  assumes "s \<noteq> t"
  shows "path_search hs al s t = Some p \<Longrightarrow>
      distinct p \<and> vwalk_bet {(u, v). (u, v) \<in> set hs \<and> al u v} s p t"
    "path_search hs al s t = None \<Longrightarrow>
      \<not> (\<exists>p. vwalk_bet {(u, v). (u, v) \<in> set hs \<and> al u v} s p t)"
proof -
  let ?R = "res_graph hs al"
  let ?st = "dfs.DFS_impl ?R t (dfs.initial_state s)"
  have "(return ?st = Reachable \<longrightarrow> distinct (rev (stack ?st)) \<and>
        vwalk_bet (Graph.digraph_abs ?R) s (rev (stack ?st)) t) \<and>
      (return ?st = NotReachable \<longrightarrow> \<not> (\<exists>p. vwalk_bet (Graph.digraph_abs ?R) s p t))"
  proof (cases "s \<in> dVs (Graph.digraph_abs ?R)")
    case True
    interpret D: DFS_thms where insert = insert and sel = sel and vset_empty = vset_empty
      and diff = diff and lookup = lookup and empty = empty and delete = delete and isin = isin
      and t_set = t_set and update = update and adjmap_inv = adjmap_inv
      and vset_delete = vset_delete and vset_inv = vset_inv and union = union and inter = inter
      and G = ?R and s = s and t = t
      by unfold_locales (use res_graph True in \<open>simp add: dfs.DFS_axioms_def\<close>)
    show ?thesis
      using D.DFS_correct_1_strong D.DFS_correct_2 by (simp add: D.DFS_impl_to_DFS)
  next
    case False
    then show ?thesis
      using DFS_impl_no_vertex[OF res_graph(1) False assms] vwalk_bet_endpoints(1) by fastforce
  qed
  moreover have "return ?st = Reachable \<or> return ?st = NotReachable"
    by (cases "return ?st") simp_all
  ultimately show "path_search hs al s t = Some p \<Longrightarrow>
      distinct p \<and> vwalk_bet {(u, v). (u, v) \<in> set hs \<and> al u v} s p t"
    "path_search hs al s t = None \<Longrightarrow>
      \<not> (\<exists>p. vwalk_bet {(u, v). (u, v) \<in> set hs \<and> al u v} s p t)"
    by (auto simp: path_search_def res_graph(4) Let_def split: if_splits return.splits)
qed

end

subsection \<open>The Flow\<close>

text \<open>A unit flow is stored as a map with a fixed universe from the edges of the network of all
elements to Booleans. Augmenting sets the edges of forward residual edges and clears those of
backward ones.\<close>

locale gammoid_flow_spec =
  fixes flow_invar :: "'f \<Rightarrow> bool"
    and flow_upd :: "'f \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow> bool \<Rightarrow> 'f"
    and flow_lkp :: "'f \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow> bool"
begin

definition flow_val :: "'f \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow> real" where
  "flow_val fl e = (if flow_lkp fl e then 1 else 0)"

definition flow_aug :: "'f \<Rightarrow> ('a snode mnode \<times> 'a snode mnode) Redge list \<Rightarrow> 'f" where
  "flow_aug fl rs =
     fold (\<lambda>r fl. case r of F e \<Rightarrow> flow_upd fl e True | B e \<Rightarrow> flow_upd fl e False) rs fl"

end

locale gammoid_flow = gammoid_flow_spec flow_invar flow_upd flow_lkp + gammoid G S +
  flow: fixed_univ_map "net (dVs G)" flow_invar flow_upd flow_lkp
  for flow_invar :: "'f \<Rightarrow> bool"
    and flow_upd :: "'f \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow> bool \<Rightarrow> 'f"
    and flow_lkp and G :: "'a dgraph" and S
begin

lemma flow_aug_lkp:
  assumes "flow_invar fl" "flow_network_spec.oedge ` set rs \<subseteq> net (dVs G)"
    "distinct (map flow_network_spec.oedge rs)"
  shows "flow_invar (flow_aug fl rs) \<and> flow_lkp (flow_aug fl rs) =
    (\<lambda>e. if F e \<in> set rs then True else if B e \<in> set rs then False else flow_lkp fl e)"
  using assms
proof (induction rs arbitrary: fl)
  case (Cons r rs)
  let ?fl = "case r of F e \<Rightarrow> flow_upd fl e True | B e \<Rightarrow> flow_upd fl e False"
  define e where "e = flow_network_spec.oedge r"
  define b where "b = (case r of F _ \<Rightarrow> True | B _ \<Rightarrow> False)"
  have fle: "?fl = flow_upd fl e b"
    by (cases r) (simp_all add: e_def b_def flow_network_spec.oedge.simps)
  have k: "e \<in> net (dVs G)" and new: "e \<notin> flow_network_spec.oedge ` set rs"
    using Cons.prems(2,3) by (auto simp: e_def)
  have fl: "flow_invar ?fl" "flow_lkp ?fl = (flow_lkp fl)(e := b)"
    unfolding fle by (rule flow.fixed_univ_map_upd_invar[OF Cons.prems(1) k]
      flow.fixed_univ_map_upd[OF Cons.prems(1) k])+
  have rs: "F e \<notin> set rs" "B e \<notin> set rs"
    using new image_eqI[of e flow_network_spec.oedge "F e" "set rs"]
      image_eqI[of e flow_network_spec.oedge "B e" "set rs"]
    by (auto simp: flow_network_spec.oedge.simps)
  have IH: "flow_invar (flow_aug ?fl rs) \<and> flow_lkp (flow_aug ?fl rs) =
      (\<lambda>x. if F x \<in> set rs then True else if B x \<in> set rs then False else flow_lkp ?fl x)"
    using Cons.prems(2,3) by (intro Cons.IH[OF fl(1)]) auto
  have "flow_aug fl (r # rs) = flow_aug ?fl rs"
    by (simp add: flow_aug_def)
  then show ?case 
    using IH fl(2) rs by (cases r) (auto simp: fun_eq_iff e_def b_def flow_network_spec.oedge.simps)
qed (simp add: flow_aug_def)

lemma net_dVs_mono: "net T \<subseteq> net (dVs G)"
  by (auto simp: net_def)

text \<open>Augmenting along residual edges with distinct node pairs agrees with augmentation in the flow
library.\<close>

theorem flow_aug_naug:
  assumes fl: "flow_invar fl" and rs: "set rs \<subseteq> nresE T (flow_val fl)" "distinct (map ntvp rs)"
  shows "flow_invar (flow_aug fl rs) \<and> flow_val (flow_aug fl rs) = naug (flow_val fl) rs"
proof -
  have res: "flow_network_spec.oedge r \<in> net (dVs G)"
    "case r of F e \<Rightarrow> \<not> flow_lkp fl e | B e \<Rightarrow> flow_lkp fl e" if "r \<in> set rs" for r
  proof -
    have "r \<in> nresE T (flow_val fl)"
      by (rule subsetD[OF rs(1) that])
    then have r: "case r of F e \<Rightarrow> e \<in> net T \<and> flow_val fl e < 1
        | B e \<Rightarrow> e \<in> net T \<and> 0 < flow_val fl e"
      by (simp only: nresE_iff)
    have "flow_network_spec.oedge r \<in> net T"
      using r by (cases r) (simp_all add: flow_network_spec.oedge.simps)
    then show "flow_network_spec.oedge r \<in> net (dVs G)"
      by (rule subsetD[OF net_dVs_mono])
    show "case r of F e \<Rightarrow> \<not> flow_lkp fl e | B e \<Rightarrow> flow_lkp fl e"
      using r by (cases r) (simp_all add: flow_val_def split: if_splits)
  qed
  have "inj_on flow_network_spec.oedge (set rs)"
  proof (rule inj_onI)
    fix x y
    assume xy: "x \<in> set rs" "y \<in> set rs" "flow_network_spec.oedge x = flow_network_spec.oedge y"
    show "x = y"
      using xy(3) res(2)[OF xy(1)] res(2)[OF xy(2)]
      by (cases x; cases y) (simp_all add: flow_network_spec.oedge.simps)
  qed
  then have dist: "distinct (map flow_network_spec.oedge rs)"
    using rs(2) by (simp add: distinct_map)
  have sub: "flow_network_spec.oedge ` set rs \<subseteq> net (dVs G)"
    by (rule image_subsetI) (rule res(1))
  note lkp = flow_aug_lkp[OF fl sub dist]
  have "flow_val (flow_aug fl rs) e = naug (flow_val fl) rs e" for e
    using res(2)[of "F e"] res(2)[of "B e"] lkp
    by (auto simp: flow_val_def flow_network_spec.augment_edges_distinct[OF dist])
  then show ?thesis
    using lkp by auto
qed

end

subsection \<open>The Oracle\<close>

text \<open>The hull is the list of pairs above, the search runs on residual graphs of the graph ADT, the
flow is a fixed-universe map, and the stored set is a set ADT.\<close>

locale gammoid_impl_spec = gammoid_search where lookup = lookup +
  gammoid_flow_spec flow_invar flow_upd flow_lkp
  for lookup :: "'adj \<Rightarrow> 'a snode mnode \<Rightarrow> 'vset option"
    and flow_invar :: "'f \<Rightarrow> bool"
    and flow_upd :: "'f \<Rightarrow> 'a snode mnode \<times> 'a snode mnode \<Rightarrow> bool \<Rightarrow> 'f" and flow_lkp +
  fixes flow_init :: 'f
    and memb_empty :: 'm and memb_ins :: "'a \<Rightarrow> 'm \<Rightarrow> 'm" and memb_del :: "'a \<Rightarrow> 'm \<Rightarrow> 'm"
    and memb_isin :: "'m \<Rightarrow> 'a \<Rightarrow> bool" and memb_set :: "'m \<Rightarrow> 'a set"
    and memb_invar :: "'m \<Rightarrow> bool"
begin

sublocale orc: gammoid_oracle_spec flow_init flow_invar flow_val flow_aug
  memb_empty memb_ins memb_del memb_isin memb_set memb_invar "\<lambda>_. True" set path_search .

end

locale gammoid_impl = gammoid_impl_spec where lookup = lookup and flow_invar = flow_invar
    and flow_upd = flow_upd and flow_lkp = flow_lkp +
  gammoid_flow flow_invar flow_upd flow_lkp G S +
  memb: Set memb_empty memb_ins memb_del memb_isin memb_set memb_invar
  for lookup :: "'adj \<Rightarrow> 'a snode mnode \<Rightarrow> 'vset option"
    and flow_invar :: "'f \<Rightarrow> bool" and flow_upd flow_lkp and G :: "'a dgraph" and S +
  assumes flow_init: "flow_invar flow_init" "flow_lkp flow_init = (\<lambda>_. False)"
begin

sublocale orc: gammoid_oracle flow_init flow_invar flow_val flow_aug
  memb_empty memb_ins memb_del memb_isin memb_set memb_invar "\<lambda>_. True" set path_search G S
proof unfold_locales
  show "flow_invar flow_init" "flow_val flow_init = (\<lambda>_. 0)"
    using flow_init by (simp_all add: flow_val_def fun_eq_iff)
  show "flow_invar (flow_aug fl rs) \<and> flow_val (flow_aug fl rs) = naug (flow_val fl) rs"
    if "flow_invar fl" "set rs \<subseteq> nresE T (flow_val fl)" "distinct (map ntvp rs)" for fl rs T
    using that by (rule flow_aug_naug)
  show "distinct p \<and> vwalk_bet {(u, v). (u, v) \<in> set g \<and> al u v} s p t"
    if "s \<noteq> t" "path_search g al s t = Some p" for g al s t p
    using that by (rule path_search_correct(1))
  show "\<not> (\<exists>p. vwalk_bet {(u, v). (u, v) \<in> set g \<and> al u v} s p t)"
    if "s \<noteq> t" "path_search g al s t = None" for g al s t
    using that by (rule path_search_correct(2))
qed

lemma hull_ok_hull_list:
  assumes "set es = G" "set ss = S"
  shows "orc.hull_ok (hull_list es ss)"
  by (simp add: orc.hull_ok_def set_hull_list set_net_list[OF assms])

theorem o_invar_init: "\<lbrakk>set es = G; set ss = S\<rbrakk> \<Longrightarrow> orc.o_invar {} (orc.o_init (hull_list es ss))"
  by (rule orc.o_invar_init[OF hull_ok_hull_list])

end

section \<open>The Best-In Greedy Algorithm on Gammoids\<close>

text \<open>The set of the greedy algorithm is the stored set of the oracle. The carrier is collected from
the edges of \<open>G\<close>. Outside the graph, the invariant of the greedy only asks for a valid set.\<close>

locale gammoid_greedy = gammoid_impl where lookup = lookup and flow_invar = flow_invar
    and flow_upd = flow_upd and flow_lkp = flow_lkp and memb_empty = set_empty
    and memb_ins = set_insert and memb_del = set_delete and memb_isin = set_isin
    and memb_set = to_set and memb_invar = set_inv +
  matroid: Matroid_Specs where set_empty = set_empty and set_insert = set_insert
    and set_delete = set_delete and set_isin = set_isin and to_set = to_set and set_inv = set_inv
    and union = s_union and inter = s_inter and diff = s_diff and cardinality = cardinality
  for lookup :: "'adj \<Rightarrow> 'a::linorder snode mnode \<Rightarrow> 'vset option" and flow_invar :: "'f \<Rightarrow> bool"
    and flow_upd flow_lkp and set_empty :: 's
    and set_insert set_delete set_isin to_set set_inv s_union s_inter s_diff cardinality +
  fixes es :: "('a \<times> 'a) list" and ss :: "'a list"
    and sort_desc :: "('a \<Rightarrow> rat) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  assumes es: "set es = G" and ss: "set ss = S" and sort_desc: "sort_desc_axioms' sort_desc"
    and finite_sets: "matroid.finite_sets"
begin

definition g_carrier :: 's where
  "g_carrier = fold (\<lambda>(u, v) X. set_insert u (set_insert v X)) es set_empty"

lemma g_carrier: "set_inv g_carrier" "to_set g_carrier = dVs G"
proof -
  have "set_inv (fold (\<lambda>(u, v) X. set_insert u (set_insert v X)) xs X) \<and>
      to_set (fold (\<lambda>(u, v) X. set_insert u (set_insert v X)) xs X) = to_set X \<union> dVs (set xs)"
    if "set_inv X" for xs X
    using that
    by (induction xs arbitrary: X) (auto simp: memb.invar_insert memb.set_insert insert_edge_dVs)
  then show "set_inv g_carrier" "to_set g_carrier = dVs G"
    using memb.invar_empty memb.set_empty by (simp_all add: g_carrier_def es[symmetric])
qed

definition g_invar :: "('f, 's, ('a snode mnode \<times> 'a snode mnode) list) ostate \<Rightarrow> bool" where
  "g_invar st \<longleftrightarrow> set_inv (o_memb st) \<and>
     (to_set (o_memb st) \<subseteq> dVs G \<longrightarrow> orc.o_invar (to_set (o_memb st)) st)"

lemma g_invar_insert:
  assumes I: "g_invar st"
  shows "g_invar (orc.o_insert x st)"
proof -
  let ?T = "to_set (o_memb st)"
  have "orc.o_invar (Set.insert x ?T) (orc.o_insert x st)" if "Set.insert x ?T \<subseteq> dVs G"
    using that I by (intro orc.o_invar_insert) (simp_all add: g_invar_def)
  then show ?thesis
    using I by (simp add: g_invar_def orc.o_memb_insert memb.invar_insert memb.set_insert)
qed

lemma g_invar_init: "g_invar (orc.o_init (hull_list es ss))"
  using o_invar_init[OF es ss] memb.invar_empty memb.set_empty
  by (simp add: g_invar_def orc.o_init_def)

sublocale greedy: Best_In_Greedy' where set_empty = set_empty and set_insert = set_insert
  and set_delete = set_delete and set_inv = set_inv and set_isin = set_isin and to_set = to_set
  and union = s_union and inter = s_inter and diff = s_diff and cardinality = cardinality
  and carrier = g_carrier and indep_fn = "\<lambda>X. gammoid_indep (to_set X)" and sort_desc = sort_desc
  and local_indep_oracle = "\<lambda>x st. orc.o_query st x" and wrapper_insert = orc.o_insert
  and wrapper_invar = g_invar and remove_wrapper = o_memb
  and wrapper_empty = "orc.o_init (hull_list es ss)"
proof unfold_locales
  show "g_invar (orc.o_insert x S)" if "g_invar S" for S x
    using that by (rule g_invar_insert)
  show "set_inv (o_memb S)" if "g_invar S" for S
    using that by (simp add: g_invar_def)
  show "o_memb (orc.o_insert x S) = set_insert x (o_memb S)" for S x
    by (rule orc.o_memb_insert)
  show "set_empty = o_memb (orc.o_init (hull_list es ss))"
    by (simp add: orc.o_init_def)
  show "g_invar (orc.o_init (hull_list es ss))"
    by (rule g_invar_init)
qed

text \<open>For an independent stored set, the oracle answers whether inserting an element keeps it
independent.\<close>

lemma g_query:
  assumes "g_invar st" "gammoid_indep (to_set (o_memb st))"
  shows "orc.o_query st x \<longleftrightarrow> gammoid_indep (to_set (set_insert x (o_memb st)))"
proof -
  have "to_set (o_memb st) \<subseteq> dVs G"
    using assms(2) by (rule indep_system.indep_subset_carrier[OF gammoid_indep_system])
  then have "orc.o_invar (to_set (o_memb st)) st"
    using assms(1) by (simp add: g_invar_def)
  then show ?thesis
    using assms(1) by (simp add: orc.o_query_correct g_invar_def memb.set_insert)
qed

lemma g_indep_system_axioms:
  "matroid.indep_system_axioms g_carrier (\<lambda>X. gammoid_indep (to_set X))"
  unfolding matroid.indep_system_axioms_def
proof (intro conjI allI impI)
  fix X
  assume "set_inv X" "gammoid_indep (to_set X)"
  then show "matroid.subseteq X g_carrier"
    using indep_system.indep_subset_carrier[OF gammoid_indep_system]
    by (simp add: matroid.set.set_subseteq g_carrier)
next
  show "\<exists>X. set_inv X \<and> gammoid_indep (to_set X)"
    using indep_system.indep_empty[OF gammoid_indep_system]
    by (intro exI[of _ set_empty]) (simp add: memb.invar_empty memb.set_empty)
next
  fix X Y
  assume "set_inv X" "set_inv Y" "gammoid_indep (to_set X)" "matroid.subseteq Y X"
  then show "gammoid_indep (to_set Y)"
    using indep_system.indep_subset[OF gammoid_indep_system]
    by (simp add: matroid.set.set_subseteq)
qed

context
  fixes c :: "'a \<Rightarrow> rat" and order :: "'a list"
  assumes c_nonneg: "\<And>x. x \<in> dVs G \<Longrightarrow> 0 \<le> c x"
    and order: "set order = dVs G" "distinct order"
begin

lemma cardinality_carrier: "cardinality g_carrier = length order"
  using matroid.set.set_cardinality[OF g_carrier(1)] distinct_card[OF order(2)]
  by (simp add: g_carrier(2) order(1))

text \<open>The greedy algorithm with the oracle agrees with the abstract one.\<close>

theorem greedy_corresp:
  "greedy.to_ordinary (greedy.BestInGreedy' (greedy.initial_state' c order)) =
   greedy.BestInGreedy (greedy.initial_state c order)"
  apply (rule greedy.BestInGreedy'_corresp)
  subgoal for S x
    by (rule g_query)
  subgoal
    by (rule g_carrier(1))
  subgoal
    unfolding greedy.greedy_axioms_def
    by (intro conjI matroid.invarI g_carrier(1) finite_sets) simp
  subgoal
    by (rule sort_desc)
  subgoal
    by (rule g_indep_system_axioms)
  subgoal
    using c_nonneg by (simp add: greedy.nonnegative_def memb.set_isin[OF g_carrier(1)] g_carrier(2))
  subgoal
    by (simp add: greedy.valid_order_def g_carrier(2) order(1) cardinality_carrier)
  done

interpretation use_greedy: Use_Greedy_Thms set_empty set_insert set_delete set_isin to_set set_inv
  s_union s_inter s_diff cardinality gammoid_indep g_carrier c order sort_desc
proof (intro Use_Greedy_Thms.intro Use_Greedy_Thms_axioms.intro)
  show "Indep_System_Specs set_empty set_insert set_delete set_isin to_set set_inv s_union s_inter
      s_diff cardinality"
    using matroid.Matroid_Specs_axioms by (simp add: Matroid_Specs_def)
  show "indep_system (to_set g_carrier) gammoid_indep"
    using gammoid_indep_system by (simp add: g_carrier(2))
  show "finite X" if "gammoid_indep X" for X
    by (rule finite_subset[OF indep_system.indep_subset_carrier[OF gammoid_indep_system that]
        dVs_finite])
  show "X \<subseteq> to_set g_carrier" if "gammoid_indep X" for X
    using indep_system.indep_subset_carrier[OF gammoid_indep_system that] by (simp add: g_carrier(2))
  show "set_inv g_carrier"
    by (rule g_carrier(1))
  show "0 \<le> c e" if "e \<in> to_set g_carrier" for e
    using that c_nonneg by (simp add: g_carrier(2))
  show "to_set g_carrier = set order"
    by (simp add: g_carrier(2) order(1))
  show "distinct order"
    by (rule order(2))
  show "finite (to_set X)" for X
    using finite_sets by (simp add: matroid.finite_sets_def)
  show "sort_desc_axioms' sort_desc"
    by (rule sort_desc)
qed

lemma result_exec:
  "to_set (o_memb (result (greedy.BestInGreedy' (greedy.initial_state' c order)))) =
   to_set (result (greedy.BestInGreedy (greedy.initial_state c order)))"
  using arg_cong[OF greedy_corresp, of "\<lambda>st. to_set (result st)"]
  by (simp add: greedy.to_ordinary_def)

text \<open>The greedy algorithm with the oracle returns a basis of maximum weight.\<close>

theorem gammoid_greedy_basis:
  "indep_system.basis (dVs G) gammoid_indep
     (to_set (o_memb (result (greedy.BestInGreedy' (greedy.initial_state' c order)))))"
  using use_greedy.algo_gives_basis by (simp add: result_exec g_carrier(2))

theorem gammoid_greedy_max:
  assumes "gammoid_indep X"
  shows "sum c X \<le> sum c (to_set (o_memb (result (greedy.BestInGreedy' (greedy.initial_state' c order)))))"
proof -
  have "indep_system.rank_quotient (to_set g_carrier) gammoid_indep = 1"
    using indep_system.matroid_iff_rq_eq_1[OF use_greedy.indep_system] gammoid_matroid
    by (simp add: g_carrier(2))
  then show ?thesis
    using use_greedy.indep_predicate_greedy_correct[OF assms] by (simp add: result_exec)
qed

end

end

end

