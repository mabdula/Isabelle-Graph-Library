theory DDFS_Interpretation
  imports DDFS IDFS
begin

text \<open>
Re-export theory for the DDFS/IDFS connection.

The heavy lifting happens in IDFS.thy: the sublocale
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
