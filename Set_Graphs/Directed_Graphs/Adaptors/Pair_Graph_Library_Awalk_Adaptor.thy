(*Author: Christoph Madlener *)
theory Pair_Graph_Library_Awalk_Adaptor
  imports
    "../Awalk_Defs"
    Pair_Graph_Library_Adaptor
begin

context ddfs
begin

lemma awalk_verts_eq: 
  "awalk_verts u p = ddfs_digraph.awalk_verts u p"
  by (induction p arbitrary: u)
     auto

lemma
  shows awhd_eq: "awhd u p = ddfs_digraph.awhd u p"
  and awlast_eq: "awlast u p = ddfs_digraph.awlast u p"
  by (simp_all add: awalk_verts_eq)

lemma cas_iff_cas:
  "cas u p v \<longleftrightarrow> ddfs_digraph.cas u p v"
  by (induction p arbitrary: u; fastforce simp add: ddfs_digraph.cas.simps)

lemma awalk_iff_awalk:
  "awalk E u p v \<longleftrightarrow> ddfs_digraph.awalk u p v"
  unfolding awalk_def ddfs_digraph.awalk_def
  by (simp add: cas_iff_cas)

lemma trail_iff_trail:
  "trail E u p v \<longleftrightarrow> ddfs_digraph.trail u p v"
  unfolding trail_def ddfs_digraph.trail_def
  by (simp add: awalk_iff_awalk)

lemma apath_iff_apath:
  "apath E u p v \<longleftrightarrow> ddfs_digraph.apath u p v"
  unfolding apath_def ddfs_digraph.apath_def
  by (simp add: awalk_iff_awalk awalk_verts_eq)

lemma closed_w_iff_closed_w:
  "closed_w E p \<longleftrightarrow> ddfs_digraph.closed_w p"
  unfolding closed_w_def
  by (simp add: ddfs_digraph.closed_w_def awalk_iff_awalk)

lemma cycle_iff_cycle:
  "cycle E c \<longleftrightarrow> ddfs_digraph.cycle c"
  unfolding cycle_def ddfs_digraph.cycle_def
  by (simp add: awalk_iff_awalk awalk_verts_eq)

lemma is_awalk_cyc_decomp_iff:
  "is_awalk_cyc_decomp E p (q,r,s) \<longleftrightarrow> ddfs_digraph.is_awalk_cyc_decomp p (q,r,s)"
  by (auto simp: awalk_iff_awalk awalk_verts_eq)

lemma is_awalk_cyc_decomp_iff':
  "is_awalk_cyc_decomp E p qrs \<longleftrightarrow> ddfs_digraph.is_awalk_cyc_decomp p qrs"
  using is_awalk_cyc_decomp_iff by (cases qrs) blast

lemma awalk_cyc_decomp_eq:
  "awalk_cyc_decomp E p = ddfs_digraph.awalk_cyc_decomp p"
  unfolding awalk_cyc_decomp_def ddfs_digraph.awalk_cyc_decomp_def
  by (intro Eps_cong) (simp add: is_awalk_cyc_decomp_iff')

end

termination awalk_to_apath
proof (relation "measure (length \<circ> snd)")
  fix E p qrs rs q r s
  interpret d: "ddfs" E .

  have X: "\<And>x y. closed_w E r \<Longrightarrow> awalk E x r y \<Longrightarrow> x = y"
    by (auto simp: d.closed_w_iff_closed_w d.awalk_iff_awalk d.ddfs_digraph.closed_w_def)
       (blast dest: d.ddfs_digraph.awalk_ends)

  assume "\<not>(\<exists>u. distinct (awalk_verts u p)) \<and> (\<exists>u v. awalk E u p v)"
    and **: "qrs = awalk_cyc_decomp E p" "(q, rs) = qrs" "(r, s) = rs"
  then obtain u v where *: "awalk E u p v" "\<not>distinct (awalk_verts u p)"
    by (cases p) auto
  then have "awalk_cyc_decomp E p = (q, r, s)" using ** by simp
  then have "is_awalk_cyc_decomp E p (q, r, s)" using *
    unfolding d.is_awalk_cyc_decomp_iff d.awalk_cyc_decomp_eq d.awalk_iff_awalk d.awalk_verts_eq
    by (auto intro: d.ddfs_digraph.awalk_cyc_decomp_has_prop elim!: d.ddfs_digraph.awalk_cyc_decompE simp: d.ddfs_digraph.closed_w_def)
  then show "((E, q @ s), E, p) \<in> measure (length \<circ> snd)"
    by (auto simp flip: ddfs.dominates_iff)
qed simp
declare awalk_to_apath.simps[simp del]

context ddfs
begin

lemma awalk_to_apath_eq:
  assumes "ddfs_digraph.awalk u p v"
  shows "awalk_to_apath E p = ddfs_digraph.awalk_to_apath p"
  using assms
proof (induction rule: ddfs_digraph.awalk_to_apath_induct)
  case (path p)
  with path[simplified awalk_verts_eq[symmetric] awalk_iff_awalk[symmetric]] 
  show ?case
    by (auto simp add: awalk_to_apath.simps ddfs_digraph.awalk_to_apath.simps)
next
  case (decomp p q r s)
  with decomp[simplified awalk_verts_eq[symmetric] awalk_iff_awalk[symmetric] awalk_cyc_decomp_eq[symmetric]]
  show ?case
    by (auto simp: awalk_to_apath.simps[of _ p] ddfs_digraph.awalk_to_apath.simps[of p] awalk_verts_eq)
qed
  
end


end