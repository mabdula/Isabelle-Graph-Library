(*Author: Christoph Madlener *)
theory Pair_Graph_Library_Component_Adaptor
  imports
    Pair_Graph_Library_Adaptor
    Pair_Graph_Library_Awalk_Adaptor
    "../Component_Defs"
    Digraph_Component_More
begin

abbreviation "subgraph_digraph \<equiv> Digraph_Component.subgraph"
abbreviation "induced_subgraph_digraph \<equiv> Digraph_Component.induced_subgraph"
abbreviation "spanning_digraph \<equiv> Digraph_Component.spanning"
abbreviation "strongly_connected_digraph \<equiv> Digraph_Component.strongly_connected"
abbreviation "mk_symmetric_digraph \<equiv> Digraph_Component.mk_symmetric"
abbreviation "connected_digraph \<equiv> Digraph_Component.connected"

lemma compatible_digraph_of[simp]:
  "compatible (ddfs.digraph_of G) (ddfs.digraph_of H)"
  by (simp add: compatible_def)

lemma compatible_digraph_of_compatible_digraph_of_arcs:
  "compatible H (ddfs.digraph_of G) \<Longrightarrow> compatible H (ddfs.digraph_of (arcs H))"
  unfolding compatible_def
  by auto

lemma compatible_sym: "compatible H G \<Longrightarrow> compatible G H"
  unfolding compatible_def
  by simp

lemma compatible_digraph_of_arcs_ends:
  "compatible H (ddfs.digraph_of G) \<Longrightarrow> arcs_ends H = arcs H"
  by (auto simp: compatible_def arcs_ends_def arc_to_ends_def)

lemma subgraph_digraph_of_dVs_arcs_subset:
  assumes "subgraph_digraph H (ddfs.digraph_of G)"
  shows "dVs (arcs H) \<subseteq> verts H"
  using assms
  unfolding Digraph_Component.subgraph_def dVs_def compatible_def
  by (auto dest: wf_digraph.wellformed)

lemma subgraph_digraph_of_dVs_arcs_subset':
  "subgraph_digraph H (ddfs.digraph_of G) \<Longrightarrow> x \<in> dVs (arcs H) \<Longrightarrow> x \<in> verts H"
  using subgraph_digraph_of_dVs_arcs_subset by blast

definition digraph_of_all_verts where
  "digraph_of_all_verts H G \<equiv> pre_digraph.add_verts (ddfs.digraph_of H) (dVs G)"

lemma "dVs G \<subseteq> verts (digraph_of_all_verts H G)"
  by (auto simp: digraph_of_all_verts_def pre_digraph.add_verts_simps)

lemma subgraph_iff:
  "subgraph H G \<longleftrightarrow> subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  by (auto simp: Digraph_Component.subgraph_def)

lemma subgraph_digraph_ofE[elim]:
  assumes "subgraph_digraph H (ddfs.digraph_of G)"
  obtains H' where "H' = arcs H" "subgraph H' G"
  using assms
  by (simp add: Component_Defs.subgraph_def Digraph_Component.subgraph_def)

lemma subgraph_digraph_ofD:
  assumes "subgraph_digraph H (ddfs.digraph_of G)"
  shows "subgraph_digraph (ddfs.digraph_of (arcs H)) (ddfs.digraph_of G)"
  using assms by (auto simp: subgraph_iff)

lemma subgraph_digraph_of_arcs:
  "subgraph_digraph H (ddfs.digraph_of G) \<Longrightarrow> subgraph_digraph (ddfs.digraph_of (arcs H)) H"
  by (auto intro!: Digraph_Component.subgraphI compatible_digraph_of_compatible_digraph_of_arcs 
           simp: subgraph_digraph_of_dVs_arcs_subset' 
           dest: compatible_digraph_of_compatible_digraph_of_arcs compatible_sym)

lemma induced_imp_induced:
  "induced_subgraph H G \<Longrightarrow> induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  unfolding Digraph_Component.induced_subgraph_def
  by (auto dest: induced_subgraphD simp flip: subgraph_iff simp: dVsI)

lemma induced_imp_induced':
  "induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G) \<Longrightarrow> induced_subgraph H G"
  by (auto intro!: induced_subgraphI elim!: Digraph_Component.induced_subgraphE simp: subgraph_iff)

lemma induced_subgraph_iff:
  "induced_subgraph H G \<longleftrightarrow> induced_subgraph_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  using induced_imp_induced induced_imp_induced'
  by blast

lemma induced_subgraph_digraph_of_arcs:
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  shows "induced_subgraph (arcs H) G"
  using assms
  by (auto dest: subgraph_digraph_of_dVs_arcs_subset'
           intro!: subgraph_digraph_of_dVs_arcs_subset' induced_subgraphI
           elim!: Digraph_Component.induced_subgraphE)

lemma induced_subgraph_digraph_ofE:
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  obtains H' where "H' = arcs H" "induced_subgraph H' G"
  using assms induced_subgraph_digraph_of_arcs
  by auto

lemma spanning_iff:
  "spanning H G \<longleftrightarrow> spanning_digraph (ddfs.digraph_of H) (ddfs.digraph_of G)"
  by (auto elim!: spanningE simp: subgraph_iff Digraph_Component.spanning_def)

lemma strongly_connected_iff:
  "strongly_connected G \<longleftrightarrow> strongly_connected_digraph (ddfs.digraph_of G)"
  unfolding Digraph_Component.strongly_connected_def
  by (auto simp: ddfs.reachable_iff strongly_connected_def dest: dVsI)

lemma mk_symmetric_eq: "ddfs.digraph_of (mk_symmetric G) \<equiv> mk_symmetric_digraph (ddfs.digraph_of G)"
  unfolding Digraph_Component.mk_symmetric_def with_proj_def
  by (clarsimp simp: ddfs.digraph_of_def dVs_mk_symmetric)
     (simp add: mk_symmetric_conv case_prod_beta)

lemma connected_iff: "connected G \<longleftrightarrow> connected_digraph (ddfs.digraph_of G)"
  by (auto elim: connectedE 
           simp: Digraph_Component.connected_def strongly_connected_iff mk_symmetric_eq)

lemma max_subgraph_imp_max_subgraph:
  assumes "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) (ddfs.digraph_of H)"
  shows "max_subgraph G P H"
  using assms
  unfolding max_subgraph_def pre_digraph.max_subgraph_def
  by (metis comp_apply ddfs.arcs_eq subgraph_iff)

lemma max_subgraph_imp_max_subgraph_all_verts:
  assumes "max_subgraph G P H"
  shows "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) (digraph_of_all_verts H G)"
proof-
  have G_max_sg_H: "subgraph H G" "P H" "\<And>H'. \<lbrakk>H' \<noteq> H; subgraph H H'; subgraph H' G; P H'\<rbrakk> \<Longrightarrow> False"
    using assms(1)
    by (auto simp: max_subgraph_def)

  have "subgraph_digraph (digraph_of_all_verts H G) (ddfs.digraph_of G)"
    using \<open>subgraph H G\<close>
    by (auto simp: Digraph_Component.subgraph_def compatible_def pre_digraph.add_verts_simps 
                   wf_digraph.wf_digraph_add_verts digraph_of_all_verts_def)

  moreover have "P (arcs (digraph_of_all_verts H G))"    
    by (simp add: G_max_sg_H(2) digraph_of_all_verts_def pre_digraph.arcs_add_verts)


  

  moreover have False
    if "H' \<noteq> digraph_of_all_verts H G" "subgraph_digraph (digraph_of_all_verts H G) H'"
       "subgraph_digraph H' (ddfs.digraph_of G)" "P (arcs H')"
    for H'
    proof(cases "arcs H' = H")
      case True
      hence "arcs H' = arcs (digraph_of_all_verts H G)"
        by (simp add: pre_digraph.arcs_add_verts digraph_of_all_verts_def)
      moreover have "dVs G \<subseteq> verts (digraph_of_all_verts H G)"
        by (simp add: digraph_of_all_verts_def pre_digraph.verts_add_verts)
      moreover have "verts (digraph_of_all_verts H G) \<subseteq> dVs G"
        using \<open>subgraph_digraph (digraph_of_all_verts H G) (ddfs.digraph_of G)\<close>
        by fastforce
      ultimately have "\<not> verts H' \<subseteq> dVs G"
        using \<open>H' \<noteq> digraph_of_all_verts H G\<close> \<open>subgraph_digraph (digraph_of_all_verts H G) H'\<close>
              compatible_head compatible_tail 
        by fastforce
      moreover have " verts H' \<subseteq> dVs G"
        using \<open>subgraph_digraph H' (ddfs.digraph_of G)\<close>
        by fastforce
      ultimately show ?thesis
        by auto
    next
      case False
      show ?thesis
        using Digraph_Component.subgraphE G_max_sg_H(3)[OF False] Component_Defs.subgraphI
              ddfs.arcs_eq digraph_of_all_verts_def pre_digraph.arcs_add_verts that(2-4)
        by metis
    qed
  ultimately show ?thesis
    unfolding pre_digraph.max_subgraph_def
    by auto
qed

lemma max_subgraph_arcs_eq:
  assumes "max_subgraph G P H"
  assumes "H \<subseteq> arcs H'"
  assumes max_digraph_of: "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) H'"
  shows "arcs H' = H"
  using assms pre_digraph.subgraphI_max_subgraph[OF max_digraph_of]
        pre_digraph.max_subgraph_prop[OF max_digraph_of]
  by (auto dest: max_subgraphD)

lemma max_subgraph_arcs_eq':
  assumes "max_subgraph G P H"
  assumes "arcs H' \<subseteq> H"
  assumes "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) H'"
  shows "arcs H' = H"
  using assms pre_digraph.subgraphI_max_subgraph[OF assms(3)] pre_digraph.max_subgraph_prop[OF assms(3)]
  by (metis (no_types, lifting) Digraph_Component.subgraphE Digraph_Component.subgraphI
            compatible_def ddfs.arcs_eq digraph_of_all_verts_def max_subgraph_P_arcs_verts
            max_subgraph_imp_max_subgraph_all_verts pre_digraph.arcs_add_verts
            pre_digraph.max_subgraph_subg_eq pre_digraph.subgraphI_max_subgraph)

lemma max_subgraph_digraph_of_additional_verts_disconnected:
  fixes H' :: "('a, 'a \<times> 'a) pre_digraph"
  assumes "max_subgraph G P H"
  assumes "pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) H'"
  assumes "u \<in> verts H'" "u \<notin> dVs H"
  assumes "H \<subseteq> arcs H'" \<comment> \<open>a max subgraph is not unique, therefore we have to enforce that we are talking about the "same" max subgraph in both worlds\<close>
  shows "\<nexists>v. (u \<rightarrow>\<^bsub>H'\<^esub> v \<or> v \<rightarrow>\<^bsub>H'\<^esub> u)"
  using assms
  by (auto dest!: max_subgraph_arcs_eq;
      metis Digraph_Component.subgraphE compatible_digraph_of_arcs_ends dVsI pre_digraph.subgraphI_max_subgraph subgraph_digraph_of_arcs)+


text \<open>
  The assumption in this lemma is pretty strong, however, it is necessary due to 
  @{thm max_subgraph_P_arcs_verts}.\<close>
lemma max_subgraph_iff:
  assumes "ddfs.digraph_of H = digraph_of_all_verts H G"
  shows "max_subgraph G P H \<longleftrightarrow> pre_digraph.max_subgraph (ddfs.digraph_of G) (P \<circ> arcs) (ddfs.digraph_of H)"
  using assms max_subgraph_imp_max_subgraph max_subgraph_imp_max_subgraph_all_verts
  by metis

lemma dVs_arcs_subset_verts: 
  "wf_digraph H \<Longrightarrow> compatible H (ddfs.digraph_of G)\<Longrightarrow> dVs (arcs H) \<subseteq> verts H"
  by (auto simp: dVs_def wf_digraph_def compatible_head compatible_tail)


lemma strongly_connected_induced_is_digraph_of_verts:
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)" "u \<in> verts H" "strongly_connected_digraph H" "verts H \<noteq> {u}"
  shows "verts H = dVs (arcs H)"
  using assms
  unfolding dVs_def
  apply (auto elim!: Digraph_Component.induced_subgraphE Digraph_Component.strongly_connectedE)
  by (metis (no_types, lifting) Digraph_Component.subgraph_def compatible_digraph_of_arcs_ends
            insertI1 mem_Collect_eq pre_digraph.converse_reachable_cases snd_conv
            subgraph_digraph_of_arcs)

lemma strongly_connected_induced_is_digraph_of:
  assumes "strongly_connected_digraph H"
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  assumes "u \<in> verts H" "verts H \<noteq> {u}"
  shows "ddfs.digraph_of (arcs H) = H"
  using assms
  by (metis ddfs.verts_eq induced_eq_verts_imp_eq induced_subgraph_digraph_ofE induced_subgraph_iff
            strongly_connected_induced_is_digraph_of_verts)

lemma nexistsI: "(\<And>x. P x \<Longrightarrow> False) \<Longrightarrow> (\<nexists>x. P x)"
  by auto

lemma induced_subgraph_digraph_then_arc:
  assumes "induced_subgraph_digraph H (ddfs.digraph_of G)"
  obtains H' where "induced_subgraph H' G" "arcs (ddfs.digraph_of H') = arcs H"
  using assms
  by (force simp add: induced_subgraph_digraph_of_arcs)

text \<open>The third assumption in the following lemma guarantees that we don't have situations of 
      vertices that are not connected to any edge.\<close>

lemma strongly_connected_digraph_then_strongly_connected:
  assumes "arcs H' \<noteq> {}"
    "strongly_connected_digraph H'"
    "induced_subgraph_digraph H' (ddfs.digraph_of G)"
  shows "strongly_connected (arcs H')"
proof-
  have "verts H' \<noteq> {}"
    using assms(2)
    by (simp add: Digraph_Component.strongly_connected_def)
  then obtain u where "u \<in> verts H'"
    by auto

  have "v1 \<rightarrow>\<^sup>*\<^bsub>arcs H'\<^esub> v2" if "v1 \<in> dVs (arcs H')" "v2 \<in> dVs (arcs H')" for v1 v2 
  proof(cases "verts H' \<noteq> {u}")
    case True
    show ?thesis 
      using strongly_connectedD(2)
               [OF iffD2[OF strongly_connected_iff], where G = "arcs H'",
                unfolded strongly_connected_induced_is_digraph_of[OF assms(2,3) \<open>u \<in> verts H'\<close> True],
                OF assms(2) that] .
  next
    case False
    then show ?thesis
      using that
      by (metis assms(3) induced_imp_subgraph reachable_vwalk_iff2 singletonD
                subgraph_digraph_of_dVs_arcs_subset')
  qed
  thus ?thesis
    using assms(1)
    by(simp add: strongly_connected_def)
qed

lemma in_sccs_imp_in_sccs_digraph_of:
  assumes "c \<in> sccs G"
  shows "ddfs.digraph_of c \<in> pre_digraph.sccs (ddfs.digraph_of G)"
proof-

  have G_in_sccs: "induced_subgraph c G" "strongly_connected c"
       "(\<nexists>H'. induced_subgraph H' G \<and> strongly_connected H' \<and>  c \<subset> H')"
    using assms
    by(auto simp: sccs_def)

  hence "induced_subgraph_digraph (ddfs.digraph_of c) (ddfs.digraph_of G)"
        "strongly_connected_digraph (ddfs.digraph_of c)"
    by (simp add: induced_subgraph_iff strongly_connected_iff)+

  have False if
    "induced_subgraph_digraph H' (ddfs.digraph_of G)"
    "verts (ddfs.digraph_of c) \<subset> verts H'"
    "strongly_connected_digraph H'"
  for H'
  proof-
    have "induced_subgraph (arcs H') G"
      using that(1)
      by (simp add: induced_subgraph_digraph_of_arcs)

    moreover have "arcs (ddfs.digraph_of c) \<subset> arcs H'"
    proof(cases "\<exists>v. verts H' = {v}")
      case True
      then show ?thesis
        using that(2) strongly_connectedD(1)[OF G_in_sccs(2), simplified dVs_empty_iff[symmetric]]
        by (auto simp: subset_insert)
    next
      case False
      then show ?thesis
        using that induced_subgraph_dVs_subset_iff[OF G_in_sccs(1) induced_subgraph_digraph_of_arcs[OF that(1)]]
        by (auto simp: induced_subgraph_def dest!: strongly_connected_induced_is_digraph_of_verts)
    qed
    hence "c \<subset> arcs H'"
      using G_in_sccs(1) G_in_sccs(2) that(1) that(2) that(3)
      by auto

    moreover hence "arcs H' \<noteq> {}"
      by auto

    hence "strongly_connected (arcs H')"
      apply (intro strongly_connected_digraph_then_strongly_connected[where G = G] that) .
    ultimately show False
      using G_in_sccs(3)
      using that(1)
      by auto
  qed
  moreover have "verts (ddfs.digraph_of c) \<subseteq> verts (ddfs.digraph_of G)"
    using \<open>induced_subgraph_digraph (ddfs.digraph_of c) (ddfs.digraph_of G)\<close>
    by blast
  ultimately show ?thesis
    apply(intro pre_digraph.in_sccsI[OF induced_imp_induced] in_sccsD(1)[OF assms])
    by (auto simp: strongly_connected_iff[symmetric] in_sccsD(2)[OF assms])
qed

lemma in_sccs_digraph_of_imp_in_sccs:
  "(ddfs.digraph_of c) \<in> pre_digraph.sccs (ddfs.digraph_of G) \<Longrightarrow> c \<in> sccs G"
  unfolding sccs_def pre_digraph.sccs_def
  by (simp add: induced_subgraph_iff strongly_connected_iff)
     (metis ddfs.verts_eq induced_imp_induced' induced_subgraph_dVs_subset_iff)

lemma in_sccs_iff:
  shows "c \<in> sccs G \<longleftrightarrow> ddfs.digraph_of c \<in> pre_digraph.sccs (ddfs.digraph_of G)"
  using in_sccs_digraph_of_imp_in_sccs in_sccs_imp_in_sccs_digraph_of by metis

lemma sccs_dVs_eq: "sccs_dVs G = pre_digraph.sccs_verts (ddfs.digraph_of G)"
  by (auto simp: sccs_dVs_def pre_digraph.sccs_verts_def ddfs.reachable_iff)

lemma scc_of_eq: "scc_of G u = pre_digraph.scc_of (ddfs.digraph_of G) u"
  by (auto simp: scc_of_def pre_digraph.scc_of_def ddfs.reachable_iff)

lemma union_eq: "ddfs.digraph_of (G \<union> H) = union (ddfs.digraph_of G) (ddfs.digraph_of H)"
  by (auto simp: dVs_union_distr)


lemma in_digraph_of_sccs_imp_in_sccs_image:
  assumes "c \<in> pre_digraph.sccs (ddfs.digraph_of G)"
  assumes "u \<in> verts c" "verts c \<noteq> {u}"
  shows "c \<in> ddfs.digraph_of ` sccs G"
  using assms
  by (fastforce simp add: assms(1) in_sccs_digraph_of_imp_in_sccs
                intro: image_eqI[where x = "(arcs c)"]
                dest!: strongly_connected_induced_is_digraph_of[where G = G and u = u]
                elim: pre_digraph.in_sccsE)+

end
