(*Author: Christoph Madlener, Mohammad Abdulziz *)
theory Pair_Graph_Library_Adaptor
  imports
    "../Pair_Graph"
    "../Vwalk"
    Graph_Theory.Graph_Theory
begin

subsection \<open>Digraph to DDFS\<close>
text \<open>lemmas from DDFS to Noschinski\<close>
context pre_digraph
begin

abbreviation "D \<equiv> arcs_ends G"

lemma dominates_iff:
  "u \<rightarrow>\<^bsub>G\<^esub> v \<longleftrightarrow> (u,v) \<in> D"
  by simp

lemma reachable1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+\<^bsub>D\<^esub> v"
  by simp

lemma arc_iff: "(u,v) \<in> D \<longleftrightarrow> (\<exists>b \<in> arcs G. tail G b = u \<and> head G b = v)"
  unfolding arcs_ends_def arc_to_ends_def by blast

fun is_arc_for_pair where
  "is_arc_for_pair a (u,v) = (a \<in> arcs G \<and> tail G a = u \<and> head G a = v)"

text \<open>We cannot reconstruct the arc from its ends without the choice operator.\<close>
definition arc_from_ends :: "('a \<times> 'a) \<Rightarrow> 'b" where
  "arc_from_ends uv \<equiv> (SOME a. is_arc_for_pair a uv)"

lemma pair_has_arc: 
  assumes "(u,v) \<in> D"
    shows "is_arc_for_pair (arc_from_ends (u,v)) (u, v)"
proof -
  obtain a where "a \<in> arcs G \<and> tail G a = u \<and> head G a = v" 
    using arc_iff assms by blast
  hence "\<exists>a. is_arc_for_pair a (u, v)" by fastforce
  thus ?thesis unfolding arc_from_ends_def ..
qed

end

context wf_digraph
begin

lemma dVs_subset_verts:
  "v \<in> dVs D \<Longrightarrow> v \<in> verts G"
  unfolding arcs_ends_def dVs_def arc_to_ends_def 
  by auto

text \<open>
  Vertices without an edge are not in \<^term>\<open>dVs D\<close> - hence also not in \<^term>\<open>rtrancl_on (dVs D) D\<close>
  Thus we can only prove the converse direction with an additional assumption.
\<close>
lemma reachable_imp:
  "u \<rightarrow>\<^sup>*\<^bsub>D\<^esub> v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  unfolding reachable_def Pair_Graph.reachable_def
  by (rule rtrancl_on_mono[of D])
     (auto simp add: dVs_subset_verts dominates_iff)

lemma reachable_imp':
  "u \<in> dVs D \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>D\<^esub> v"
  unfolding reachable_def Pair_Graph.reachable_def
  by (auto dest!: rtrancl_on_rtranclI 
           elim: rtrancl.cases 
           intro!: rtrancl_consistent_rtrancl_on 
           simp: dVsI)

lemma reachable_iff:
  "u \<in> dVs D \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>D\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  using reachable_imp reachable_imp' by blast
(*
lemma cas_imp_map_arc_to_ends_cas: 
  "cas u p v \<Longrightarrow> Noschinski_to_DDFS.cas u (map (arc_to_ends G) p) v"
  by (induction p arbitrary: u)
     (auto simp: arc_to_ends_def)
*)
(*
lemma cas_map_arc_to_ends_imp_cas: 
  "Noschinski_to_DDFS.cas u (map (arc_to_ends G) p) v \<Longrightarrow> cas u p v"
  by (induction p arbitrary: u)
     (auto simp: arc_to_ends_def)
*)
(*lemma cas_iff_cas: "Noschinski_to_DDFS.cas u (map (arc_to_ends G) p) v \<longleftrightarrow> cas u p v"
  using cas_imp_map_arc_to_ends_cas cas_map_arc_to_ends_imp_cas by blast
*)
(*lemma awalk_imp_awalk_map_arc_to_ends:
  assumes "u \<in> dVs D"
  assumes "awalk u p v"
  shows "Noschinski_to_DDFS.awalk D u (map (arc_to_ends G) p) v"
  using assms
  unfolding awalk_def Noschinski_to_DDFS.awalk_def
  by (auto intro: dominatesI cas_imp_map_arc_to_ends_cas)
*)
(*lemma awalk_map_arc_to_ends_imp_awalk:
  assumes "set p \<subseteq> arcs G"
  assumes "Noschinski_to_DDFS.awalk D u (map (arc_to_ends G) p) v"
  shows "awalk u p v"
  using assms
  unfolding awalk_def Noschinski_to_DDFS.awalk_def
  by (auto simp: dVs_subset_verts cas_iff_cas)
*)
(*lemma awalk_iff_awalk:
  assumes "u \<in> dVs D"
  assumes "set p \<subseteq> arcs G"
  shows "Noschinski_to_DDFS.awalk D u (map (arc_to_ends G) p) v \<longleftrightarrow> awalk u p v"
  using assms awalk_imp_awalk_map_arc_to_ends awalk_map_arc_to_ends_imp_awalk
  by blast
*)
(*lemma cas_imp_map_arc_from_ends_cas:
  assumes "set p \<subseteq> D"
  shows "Noschinski_to_DDFS.cas u p v \<Longrightarrow> cas u (map arc_from_ends p) v"
  using assms arc_from_ends_def pair_has_arc
  by (induction p arbitrary: u) auto
*)
(*lemma cas_map_arc_from_ends_imp_cas:
  assumes "set p \<subseteq> D"
  shows "cas u (map arc_from_ends p) v \<Longrightarrow> Noschinski_to_DDFS.cas u p v"
  using assms arc_from_ends_def pair_has_arc
  by (induction p arbitrary: u) auto
*)
(*lemma cas_iff_cas':
  assumes "set p \<subseteq> D"
  shows "Noschinski_to_DDFS.cas u p v \<longleftrightarrow> cas u (map arc_from_ends p) v"
  using assms cas_imp_map_arc_from_ends_cas cas_map_arc_from_ends_imp_cas by blast
*)
(*lemma awalk_imp_awalk_map_arc_from_ends:
  assumes "Noschinski_to_DDFS.awalk D u p v"
  shows "awalk u (map arc_from_ends p) v"
  using assms pair_has_arc cas_imp_map_arc_from_ends_cas
  unfolding Noschinski_to_DDFS.awalk_def awalk_def
  by (auto simp: dVs_subset_verts)
*)
(*lemma awalk_map_arc_from_ends_imp_awalk:
  assumes "u \<in> dVs D"
  assumes "set p \<subseteq> D"
  assumes "awalk u (map arc_from_ends p) v"
  shows "Noschinski_to_DDFS.awalk D u p v"
  using assms
  unfolding Noschinski_to_DDFS.awalk_def awalk_def
  by (auto simp add: cas_iff_cas')
*)
(*lemma awalk_iff_awalk':
  assumes "u \<in> dVs D"
  assumes "set p \<subseteq> D"
  shows "awalk u (map arc_from_ends p) v \<longleftrightarrow> Noschinski_to_DDFS.awalk D u p v"
  using assms awalk_imp_awalk_map_arc_from_ends awalk_map_arc_from_ends_imp_awalk by blast
*)
text \<open>
  \<^term>\<open>vwalk\<close> requires non-emptiness.
\<close>
lemma dpath_imp_vwalk:
  "Vwalk.vwalk D (u # xs) \<Longrightarrow> vwalk (u # xs) G"
  by (induction xs arbitrary: u)
     (auto simp: dVs_subset_verts)

text \<open>
  Singleton \<^term>\<open>[u]\<close> with a disconnected vertex is also a \<^term>\<open>vwalk\<close>.
\<close>
lemma vwalk_imp_dpath:
  assumes "u \<in> dVs D"
  shows "vwalk (u # xs) G \<Longrightarrow> Vwalk.vwalk D (u # xs)"
  using assms
  by (induction xs arbitrary: u)
     (auto simp: dVsI)

lemma vwalk_iff:
  assumes "u \<in> dVs D"
  shows "vwalk (u # xs) G \<longleftrightarrow> Vwalk.vwalk D (u # xs)"
  using assms vwalk_imp_dpath dpath_imp_vwalk by blast

end

context nomulti_digraph
begin

lemma arc_from_ends_arc_to_ends_eq:
  assumes "a \<in> arcs G"
  shows "arc_from_ends (arc_to_ends G a) = a"
  using assms
  by (intro no_multi_arcs)
     (auto simp: arc_to_ends_def dominates_iff dest!: in_arcs_imp_in_arcs_ends pair_has_arc)

lemma arc_to_ends_arc_from_ends_eq:
  assumes "(u,v) \<in> D"
  shows "arc_to_ends G (arc_from_ends (u,v)) = (u,v)"
  using assms
  by (auto dest!: pair_has_arc simp: arc_to_ends_def)

end


subsection \<open>From Pair-Graph to Digraph\<close>
text \<open>Allows moving lemmas from Digraph to DDFS.\<close>
locale ddfs =
  fixes E :: "'a dgraph"
begin

definition "digraph_of \<equiv> \<lparr>verts = dVs E, arcs = E, tail = fst, head = snd\<rparr>"
definition "pair_digraph_of = \<lparr>pverts = dVs E, arcs = E\<rparr>"

lemma digraph_of_pair_conv:
  "with_proj pair_digraph_of = digraph_of"
  unfolding pair_digraph_of_def digraph_of_def with_proj_def by simp

sublocale ddfs_digraph: nomulti_digraph digraph_of
  by standard (auto simp: digraph_of_def arc_to_ends_def dVsI)

lemma nomulti_digraph_digraph_of: "nomulti_digraph digraph_of" ..
lemma wf_digraph_digraph_of: "wf_digraph digraph_of" ..

interpretation ddfs_pdigraph: pair_wf_digraph pair_digraph_of
  using digraph_of_pair_conv ddfs_digraph.wf_digraph_axioms wf_digraph_wp_iff by fastforce

lemma pair_wf_digraph_pair_digraph_of: "pair_wf_digraph pair_digraph_of" ..

lemma arc_to_ends_eq[simp]:
  "arc_to_ends digraph_of = id"
  by (auto simp add: digraph_of_def arc_to_ends_def)

lemma arcs_ends_eq[simp]:
  "arcs_ends digraph_of = E"
  unfolding arcs_ends_def arc_to_ends_eq by (simp add: digraph_of_def)

lemma dominates_iff:
  "(u,v) \<in> E \<longleftrightarrow> u \<rightarrow>\<^bsub>digraph_of\<^esub> v"
  by simp

lemma verts_eq[simp]:
  "verts digraph_of = dVs E"
  unfolding digraph_of_def by simp

lemma arcs_eq[simp]:
  "arcs digraph_of = E"
  unfolding digraph_of_def by simp

lemma tail_eq[simp]:
  "tail digraph_of = fst"
  unfolding digraph_of_def by simp

lemma head_eq[simp]:
  "head digraph_of = snd"
  unfolding digraph_of_def by simp

lemma reachable_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>digraph_of\<^esub> v"
  unfolding reachable_def Pair_Graph.reachable_def
  by simp

lemma reachable1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+\<^bsub>digraph_of\<^esub> v"
  by simp

lemma vwalk_iff:
  "p \<noteq> [] \<and> Vwalk.vwalk E p \<longleftrightarrow> vwalk p digraph_of"
  by (induction p rule: induct_list012)
     (auto)

lemma symmetric_iff:
  "sym E \<longleftrightarrow> symmetric digraph_of"
  by (simp add: symmetric_def)

end


lemmas ddfs_library_adaptor_simps[simp] = ddfs.arc_to_ends_eq ddfs.arcs_ends_eq ddfs.dominates_iff[symmetric]
  ddfs.verts_eq ddfs.arcs_eq ddfs.tail_eq ddfs.head_eq ddfs.nomulti_digraph_digraph_of
  ddfs.wf_digraph_digraph_of ddfs.pair_wf_digraph_pair_digraph_of

lemma digraph_of_eq_imp_eq: "ddfs.digraph_of G = ddfs.digraph_of H \<Longrightarrow> G = H"
  by (metis ddfs.arcs_eq)

lemma eq_iff_digraph_of_eq: "ddfs.digraph_of G = ddfs.digraph_of H \<longleftrightarrow> G = H"
  using digraph_of_eq_imp_eq
  by auto


context pre_digraph
begin

definition add_verts :: "'a set \<Rightarrow> ('a,'b) pre_digraph" where
  "add_verts V = \<lparr> verts = V \<union> verts G, arcs = arcs G, tail = tail G, head = head G \<rparr>"

lemma
  verts_add_verts: "verts (pre_digraph.add_verts G V) = V \<union> verts G" and
  arcs_add_verts: "arcs (pre_digraph.add_verts G V) = arcs G" and
  tail_add_verts: "tail (pre_digraph.add_verts G V) = tail G" and
  head_add_verts: "head (pre_digraph.add_verts G V) = head G"
  by (auto simp: pre_digraph.add_verts_def)

lemmas add_verts_simps = verts_add_verts arcs_add_verts tail_add_verts head_add_verts

definition del_verts :: "'a set \<Rightarrow> ('a,'b) pre_digraph" where
  "del_verts V = \<lparr> verts = verts G - V, arcs = {a \<in> arcs G. tail G a \<notin> V \<and> head G a \<notin> V}, tail = tail G, head = head G \<rparr>"

lemma
  verts_del_verts: "verts (pre_digraph.del_verts G V) = verts G - V" and
  arcs_del_verts: "arcs (pre_digraph.del_verts G V) = {a \<in> arcs G. tail G a \<notin> V \<and> head G a \<notin> V}" and
  tail_del_verts: "tail (pre_digraph.del_verts G V) = tail G" and
  head_del_verts: "head (pre_digraph.del_verts G V) = head G"
  by (auto simp: pre_digraph.del_verts_def)

lemmas del_verts_simps = verts_del_verts arcs_del_verts tail_del_verts head_del_verts
end

context wf_digraph
begin

lemma wf_digraph_add_verts: "wf_digraph (add_verts V)"
  by standard (auto simp: add_verts_simps)

lemma wf_digraph_del_verts: "wf_digraph (del_verts V)"
  by standard (auto simp: del_verts_simps)

end
end