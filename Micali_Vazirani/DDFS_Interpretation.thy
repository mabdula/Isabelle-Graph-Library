theory DDFS_Interpretation
  imports DDFS IDFS
begin

text \<open>
Re-export theory for the DDFS/IDFS connection.

The heavy lifting happens in the first section below (moved here from IDFS.thy,
so that IDFS does not depend on DDFS): the sublocale
  DDFS_layered \<subseteq> DDFS ... where IDFS = IDFS_impl and succ = sel o neighbourhood
is PROVEN there (READT-TODO-20 closed 2026-07-12), so inside
\<open>context DDFS_layered\<close> every DDFS locale assumption is available at the
executable witness IDFS_impl. This theory re-exports the clauses in explicit,
individually-named form, mirroring the DDFS clause list.

All clauses carry the four input preconditions (the IDFS_pre conjuncts:
vset_inv of avoid/vis and their t_set-images inside dVs) plus dpath+distinct
of the stack; the inner context below fixes them once.

Historical note: the previous version of this file stated these lemmas over a
free function variable \<open>IDFS\<close> in plain-set types (a leftover of the
pre-ADT architecture; the sorried sublocale meant the name did not resolve),
which made them unprovable as stated. READT-TODO-21..36 are closed by this
rewrite; TODO-39's SOME-based successor is superseded by the executable
sel-based successor (succ_works_aux, IDFS.thy).
\<close>

section \<open>Layered-digraph locale and the DDFS interpretation\<close>

text \<open>DDFS_layered is the ops-generic witness locale itself (no extra
assumptions): it fixes the executable ADT, the graph G, the level function
lev, and the layeredness/wf facts wf_graph/L1/L2/L3.
The DDFS interface is then realised by IDFS_impl with the executable successor
succ = sel \<circ> N_G (NEVER SOME --- not executable).\<close>

locale DDFS_layered = IDFS_witness

context DDFS_layered
begin

text \<open>The executable successor picks an element of the (non-empty) neighbourhood via the
Set2 sel operation. For a non-zero-level vertex L3 supplies an outgoing edge, so
the neighbourhood is non-empty and sel picks a member, which is an edge target under
graph_inv.\<close>

lemma succ_works_aux:
  assumes "v \<in> dVs (Graph.digraph_abs G)" "lev v \<noteq> 0" shows "(v, sel (Graph.neighbourhood G v)) \<in> Graph.digraph_abs G"
proof -
  from L3 assms(1) obtain p v' where p: "p \<noteq> []" "dpath_bet (Graph.digraph_abs G) p v v'" and lv: "lev v' = 0"
    by blast
  have neq: "v \<noteq> v'" using assms(2) lv by auto
  from path_then_edge[OF p(2) p(1) neq] obtain u where u: "(v, u) \<in> Graph.digraph_abs G" by auto
  hence "u \<in> t_set (Graph.neighbourhood G v)"
    using wf_graph(1) Graph.are_connected_abs by auto
  then have nempty: "t_set (Graph.neighbourhood G v) \<noteq> {}" by auto
  have inv: "vset_inv (Graph.neighbourhood G v)"
    using wf_graph(1) Graph.neighbourhood_invars' by simp
  have ne: "Graph.neighbourhood G v \<noteq> vset_empty"
  proof
    assume "Graph.neighbourhood G v = vset_empty"
    hence "t_set (Graph.neighbourhood G v) = {}"
      by (simp add: Graph.vset.set.set_empty)
    with nempty show False by simp
  qed
  have "sel (Graph.neighbourhood G v) \<in> t_set (Graph.neighbourhood G v)"
    using ne inv Graph.vset.choose' by auto
  with wf_graph(1) Graph.are_connected_abs show ?thesis by auto
qed

end

sublocale DDFS_layered \<subseteq>
    DDFS where update = update and adjmap_inv = adjmap_inv
      and vset_empty = vset_empty and vset_delete = vset_delete and vset_inv = vset_inv
      and empty = empty and delete = delete and lookup = lookup
      and insert = insert and isin = isin and t_set = t_set and sel = sel
      and union = union and inter = inter and diff = diff
      and G = G and level = lev
      and IDFS = IDFS_impl
      and succ = "\<lambda>v. sel (Graph.neighbourhood G v)"
proof (unfold_locales)
  show "Graph.layered_graph_input G lev"
    using layered_input .
next
  fix v assume hv: "v \<in> dVs (Graph.digraph_abs G)" "lev v \<noteq> 0"
  show "(v, (\<lambda>v. sel (Graph.neighbourhood G v)) v) \<in> Graph.digraph_abs G"
    using succ_works_aux[OF hv] by simp
next
  fix P avoid vis p ret_p vis' v
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (ret_p, vis')"
     and vin: "v \<in> t_set vis' - t_set vis"
  show "\<not> P v" using IDFS_vis_works_1[OF pw dst ivA ivV dA dV eq vin] .
next
  fix P avoid vis p ret_p vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (ret_p, vis')"
  show "(t_set vis' - t_set vis) \<inter> t_set avoid = {}"
    using IDFS_vis_works_2[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p ret_p vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (ret_p, vis')"
  show "t_set vis \<subseteq> t_set vis'"
    using IDFS_vis_works_3[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p ret_p vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (ret_p, vis')"
  show "vset_inv vis'"
    using IDFS_vis_works_4[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p vis' v w
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (None, vis')"
     and vnew: "v \<in> t_set vis' - t_set vis"
     and edge: "(v, w) \<in> Graph.digraph_abs G"
  show "w \<in> t_set avoid \<union> t_set vis'"
    using IDFS_closed_None[OF pw dst ivA ivV dA dV eq vnew edge] .
next
  fix P avoid vis p p' vis' v w
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
     and vnew: "v \<in> t_set vis' - t_set vis"
     and edge: "(v, w) \<in> Graph.digraph_abs G"
  show "w \<in> t_set avoid \<union> t_set vis' \<union> set p'"
    using IDFS_closed_Some[OF pw dst ivA ivV dA dV eq vnew edge] .
next
  fix P avoid vis p vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (None, vis')"
  show "set p - t_set avoid \<subseteq> t_set vis'"
    using IDFS_complete_w[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p p' vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
  have dst: "distinct p"
  proof (rule ccontr)
    assume nd: "\<not> distinct p"
    from not_distinct_decomp[OF nd]
    obtain xs ys zs y where split: "p = xs @ [y] @ ys @ [y] @ zs" by auto
    have revp: "rev p = (rev zs) @ [y] @ (rev ys) @ [y] @ (rev xs)"
      using split by simp
    have suf: "dpath (Graph.digraph_abs G) (y # (rev ys @ [y] @ rev xs))"
      using pw revp by (auto intro: append_dpath_suff)
    have yin: "y \<in> set (rev ys @ [y] @ rev xs)" by simp
    have "lev y < lev y"
      using dpath_transitive_rel[where R = "\<lambda>a b. lev b < lev a", OF _ _ suf yin]
      by (auto intro: L1)
    thus False by simp
  qed
  show "dpath (Graph.digraph_abs G) (rev p')"
    using IDFS_sound_1[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p p' vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
  show "distinct p'"
    using IDFS_sound_2[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p p' vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
  show "(set p' - set (tl p)) \<inter> (t_set avoid \<union> t_set vis') = {}"
    using IDFS_sound_3[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p p' vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
  show "set p - set p' - t_set avoid \<subseteq> t_set vis'"
    using IDFS_sound_4[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p p' vis' v
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
     and tlP: "\<And>v. v \<in> set (tl p) \<Longrightarrow> \<not> P v"
     and vin: "v \<in> set (tl p')"
  show "\<not> P v"
    using IDFS_sound_5[OF pw dst ivA ivV dA dV eq tlP vin] .
next
  fix P avoid vis p p' vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
     and pne: "p \<noteq> []"
  show "last p = last p'"
    using IDFS_sound_6[OF pw dst ivA ivV dA dV eq pne] .
next
  fix P avoid vis p p' vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
  show "p' \<noteq> []"
    using IDFS_sound_7[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p p' vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (Some p', vis')"
  show "P (hd p')"
    using IDFS_sound_8[OF pw dst ivA ivV dA dV eq] .
next
  fix P avoid vis p ret_p vis'
  assume ivA: "vset_inv avoid" and ivV: "vset_inv vis"
     and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
     and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
     and pw: "dpath (Graph.digraph_abs G) (rev p)"
     and dst: "distinct p"
     and eq: "IDFS_impl P avoid p vis = (ret_p, vis')"
  show "t_set vis' \<subseteq> dVs (Graph.digraph_abs G)"
    using IDFS_dVs_bound[OF pw dst ivA ivV dA dV eq] .
qed

section \<open>Re-exported IDFS properties inside DDFS_layered\<close>

context DDFS_layered begin

context
  fixes avoid vis p
  assumes ivA: "vset_inv avoid"
      and ivV: "vset_inv vis"
      and dA: "t_set avoid \<subseteq> dVs (Graph.digraph_abs G)"
      and dV: "t_set vis \<subseteq> dVs (Graph.digraph_abs G)"
      and path: "dpath (Graph.digraph_abs G) (rev p)"
      and dist: "distinct p"
begin

lemma IDFS_notP:
  assumes ic: "IDFS_impl P avoid p vis = (ret_p, vis')" and vm: "v \<in> t_set vis' - t_set vis"
  shows "\<not> P v"
  using IDFS_vis_works(1)[OF ivA ivV dA dV path dist ic vm] .

lemma IDFS_newvis_avoid_disj:
  assumes ic: "IDFS_impl P avoid p vis = (ret_p, vis')"
  shows "(t_set vis' - t_set vis) \<inter> t_set avoid = {}"
  using IDFS_vis_works(2)[OF ivA ivV dA dV path dist ic] .

lemma IDFS_vis_works_mono:
  assumes ic: "IDFS_impl P avoid p vis = (ret_p, vis')"
  shows "t_set vis \<subseteq> t_set vis'"
  using IDFS_vis_works(3)[OF ivA ivV dA dV path dist ic] .

lemma IDFS_vis_inv:
  assumes ic: "IDFS_impl P avoid p vis = (ret_p, vis')"
  shows "vset_inv vis'"
  using IDFS_vis_works(4)[OF ivA ivV dA dV path dist ic] .

lemma IDFS_closed_None_cond:
  assumes ic: "IDFS_impl P avoid p vis = (None, vis')" and vm: "v \<in> t_set vis' - t_set vis"
      and ew: "(v, w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set avoid \<union> t_set vis'"
  using IDFS_closed(1)[OF ivA ivV dA dV path dist ic vm ew] .

lemma IDFS_closed_Some_cond:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')" and vm: "v \<in> t_set vis' - t_set vis"
      and ew: "(v, w) \<in> Graph.digraph_abs G"
  shows "w \<in> t_set avoid \<union> t_set vis' \<union> set p'"
  using IDFS_closed(2)[OF ivA ivV dA dV path dist ic vm ew] .

lemma IDFS_complete_cond:
  assumes ic: "IDFS_impl P avoid p vis = (None, vis')"
  shows "set p - t_set avoid \<subseteq> t_set vis'"
  using IDFS_complete[OF ivA ivV dA dV path dist ic] .

lemma IDFS_sound_dpath:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "dpath (Graph.digraph_abs G) (rev p')"
  using IDFS_sound(1)[OF ivA ivV dA dV path ic] .

lemma IDFS_sound_distinct:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "distinct p'"
  using IDFS_sound(2)[OF ivA ivV dA dV path dist ic] .

lemma IDFS_sound_newvis_disjoint:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "(set p' - set (tl p)) \<inter> (t_set avoid \<union> t_set vis') = {}"
  using IDFS_sound(3)[OF ivA ivV dA dV path dist ic] .

lemma IDFS_sound_prefix_vis:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "set p - set p' - t_set avoid \<subseteq> t_set vis'"
  using IDFS_sound(4)[OF ivA ivV dA dV path dist ic] .

lemma IDFS_sound_tl_notP:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')"
      and tlP: "\<And>u. u \<in> set (tl p) \<Longrightarrow> \<not> P u"
      and uv: "v \<in> set (tl p')"
  shows "\<not> P v"
  using IDFS_sound(5)[OF ivA ivV dA dV path dist ic tlP uv] .

lemma IDFS_sound_last:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')" and ne: "p \<noteq> []"
  shows "last p = last p'"
  using IDFS_sound(6)[OF ivA ivV dA dV path dist ic ne] .

lemma IDFS_sound_nonempty:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "p' \<noteq> []"
  using IDFS_sound(7)[OF ivA ivV dA dV path dist ic] .

lemma IDFS_sound_hdP:
  assumes ic: "IDFS_impl P avoid p vis = (Some p', vis')"
  shows "P (hd p')"
  using IDFS_sound(8)[OF ivA ivV dA dV path dist ic] .

lemma IDFS_vis_dVs:
  assumes ic: "IDFS_impl P avoid p vis = (ret_p, vis')"
  shows "t_set vis' \<subseteq> dVs (Graph.digraph_abs G)"
  using IDFS_dVs[OF ivA ivV dA dV path dist ic] .

end (* inner context: the four IDFS_pre conjuncts + path + dist *)

section \<open>Successor witness\<close>

text \<open>The executable successor (sel of the neighbourhood) leaves every
non-zero-level vertex along a real edge; this is succ_works_aux from IDFS.thy,
re-exported here together with its existential corollary.\<close>

lemma layered_succ_works:
  assumes "v \<in> dVs (Graph.digraph_abs G)" and "lev v \<noteq> 0"
  shows "(v, sel (Graph.neighbourhood G v)) \<in> Graph.digraph_abs G"
  using succ_works_aux[OF assms] .

lemma layered_succ_exists:
  assumes "v \<in> dVs (Graph.digraph_abs G)" and "lev v \<noteq> 0"
  shows "\<exists>v0. (v, v0) \<in> Graph.digraph_abs G"
  using layered_succ_works[OF assms] by blast

end (* DDFS_layered *)

end
