theory Find_Aug_Path_Subprocedures
  imports Graph_Matching_Specs Blossom_Prefixes
begin

provenance ai

section \<open>Finding an augmenting path or a blossom\<close>

text \<open>The alternating forest search returns two alternating paths, from the endpoints of an edge
  between two even vertices to the roots of their trees. If the two paths are vertex-disjoint,
  they form an augmenting path together with that edge. Otherwise they share a suffix, and their
  longest disjoint prefixes form a blossom with the remainder of either path as its stem. In the
  original formalisation, the procedure has a special case for an edge between two free
  vertices; it is not needed here, as the forest search returns such an edge itself. Both the
  test for disjointness and the computation of the prefixes take time linear in the lengths of
  the paths.\<close>

subsection \<open>The longest disjoint prefixes in linear time\<close>

text \<open>The function @{const longest_disj_pfx} searches the first path for each vertex of the
  second path, which takes time quadratic in the lengths of the paths. When the paths end at the
  same root and a common vertex is followed on both paths by the same suffix, the longest
  disjoint prefixes end at the first vertex of the longest common suffix, the base of the
  blossom. The reversed paths start at the root, and the following function finds the base on
  them in linear time: it strips their longest common prefix except its last vertex. It thus
  returns the reversed longest disjoint prefixes.\<close>

fun longest_disj_sfx where
  "longest_disj_sfx (x1 # y1 # r1) (x2 # y2 # r2) =
     (if y1 = y2 then longest_disj_sfx (y1 # r1) (y2 # r2) else (x1 # y1 # r1, x2 # y2 # r2))"
| "longest_disj_sfx r1 r2 = (r1, r2)"

lemma longest_disj_sfx_split:
  "\<lbrakk>r1 \<noteq> []; r2 \<noteq> []; hd r1 = hd r2\<rbrakk> \<Longrightarrow>
     \<exists>c b s1 s2. r1 = c @ b # s1 \<and> r2 = c @ b # s2 \<and> longest_disj_sfx r1 r2 = (b # s1, b # s2) \<and>
                 (s1 = [] \<or> s2 = [] \<or> hd s1 \<noteq> hd s2)"
proof(induction r1 r2 rule: longest_disj_sfx.induct)
  case (1 x1 y1 r1 x2 y2 r2)
  show ?case
  proof(cases "y1 = y2")
    case True
    then obtain c b s1 s2 where IH: "y1 # r1 = c @ b # s1" "y2 # r2 = c @ b # s2"
        "longest_disj_sfx (y1 # r1) (y2 # r2) = (b # s1, b # s2)" "s1 = [] \<or> s2 = [] \<or> hd s1 \<noteq> hd s2"
      using "1.IH"
      by auto
    have "longest_disj_sfx (x1 # y1 # r1) (x2 # y2 # r2) = (b # s1, b # s2)"
      using True IH(3)
      by simp
    thus ?thesis
      using IH(1,2,4) "1.prems"(3)
      by (intro exI[of _ "x1 # c"] exI[of _ b] exI[of _ s1] exI[of _ s2]) auto
  next
    case False
    thus ?thesis
      using "1.prems"(3)
      by (intro exI[of _ "[]"]) auto
  qed
qed (auto simp: neq_Nil_conv)

lemma last_find_pfx_in_set:
  "l \<noteq> [] \<Longrightarrow> last (find_pfx Q l) \<in> set l"
proof(induction l)
  case (Cons a l)
  then show ?case
    by (cases l) auto
qed simp

lemma find_pfx_first:
  "b \<notin> set q \<Longrightarrow> find_pfx ((=) b) (q @ b # s) = q @ [b]"
  by (induction q) auto

lemma longest_disj_pfx_first_common:
  assumes "set u \<inter> set l1 = {}" "h \<in> set l1"
  shows "longest_disj_pfx l1 (u @ h # l2) = (Some (find_pfx ((=) h) l1), Some (u @ [h]))"
  using assms
proof(induction u)
  case Nil
  then show ?case
    using find_pfx_works_1[of h l1 "(=) h"]
    by (cases l1) (auto simp: Let_def)
next
  case (Cons x u)
  have "l1 \<noteq> []"
    using Cons.prems(2)
    by auto
  hence "last (find_pfx ((=) x) l1) \<noteq> x"
    using last_find_pfx_in_set[of l1 "(=) x"] Cons.prems(1)
    by auto
  then show ?case
    using Cons
    by (cases l1) (auto simp: Let_def)
qed

lemma longest_disj_pfx_common_sfx:
  assumes from_tree: "\<And>pref1 x post1 pref2 post2. \<lbrakk>p1 = pref1 @ x # post1; p2 = pref2 @ x # post2\<rbrakk>
                        \<Longrightarrow> post1 = post2"
      and p1: "p1 = q1 @ b # s" and p2: "p2 = q2 @ b # s"
      and lasts: "q1 = [] \<or> q2 = [] \<or> last q1 \<noteq> last q2"
  shows "longest_disj_pfx p1 p2 = (Some (q1 @ [b]), Some (q2 @ [b]))"
proof-
  have "b \<notin> set q1"
  proof
    assume "b \<in> set q1"
    then obtain u v where "q1 = u @ b # v"
      by (blast dest: split_list)
    hence "v @ b # s = s"
      using from_tree[of u b "v @ b # s" q2 s] p1 p2
      by simp
    thus False
      using arg_cong[of "v @ b # s" s length]
      by simp
  qed
  hence pfx1: "find_pfx ((=) b) p1 = q1 @ [b]"
    using p1 find_pfx_first
    by simp
  have "set q2 \<inter> set p1 = {}"
  proof(rule ccontr)
    assume "set q2 \<inter> set p1 \<noteq> {}"
    then obtain y where y: "y \<in> set q2" "y \<in> set p1"
      by blast
    obtain u2 v2 where q2: "q2 = u2 @ y # v2"
      using y(1)
      by (blast dest: split_list)
    obtain u1 w1 where p1': "p1 = u1 @ y # w1"
      using y(2)
      by (blast dest: split_list)
    have "w1 = v2 @ b # s"
      using from_tree[of u1 y w1 u2 "v2 @ b # s"] p1' p2 q2
      by simp
    hence "(u1 @ y # v2) @ b # s = q1 @ b # s"
      using p1 p1'
      by simp
    hence "q1 = u1 @ y # v2"
      by simp
    hence "q1 \<noteq> [] \<and> q2 \<noteq> [] \<and> last q1 = last q2"
      using q2
      by simp
    thus False
      using lasts
      by blast
  qed
  moreover have "b \<in> set p1"
    using p1
    by simp
  ultimately show ?thesis
    using longest_disj_pfx_first_common[of q2 p1 b s] p2 pfx1
    by (simp add: Int_commute)
qed

subsection \<open>The procedure\<close>

lemma \<^marker>\<open>provenance human\<close> compute_alt_path_specD:
  assumes "compute_alt_path_spec G M (Some (p1, p2))"
  shows "\<And>pref1 x post1 pref2 post2. \<lbrakk>p1 = pref1 @ x # post1; p2 = pref2 @ x # post2\<rbrakk>
           \<Longrightarrow> post1 = post2"
        "alt_path M (hd p1 # p2)" "alt_path M (hd p2 # p1)" "last p1 \<notin> Vs M" "last p2 \<notin> Vs M"
        "hd p1 \<noteq> hd p2" "odd (length p1)" "odd (length p2)" "distinct p1" "distinct p2"
        "path G p1" "path G p2" "{hd p1, hd p2} \<in> G"
  by (insert assms[unfolded compute_alt_path_spec_def, simplified], blast)+

lemma \<^marker>\<open>provenance human\<close> common_suffix:
  assumes "compute_alt_path_spec G M (Some (p1, p2))"
          "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2"
  obtains p where "p1 = pfx1 @ p" "p2 = pfx2 @ p"
proof \<^marker>\<open>provenance ai\<close>-
  obtain p1' p2' where pp: "p1 = pfx1 @ p1'" "p2 = pfx2 @ p2'"
    using disj_pref_append1[OF assms(2)] disj_pref_append2[OF assms(2)]
    by blast
  obtain ys1 y1 where s1: "pfx1 = ys1 @ [y1]"
    using first_pfx_nempty[OF assms(2)]
    by (cases pfx1 rule: rev_cases) auto
  obtain ys2 y2 where s2: "pfx2 = ys2 @ [y2]"
    using snd_pfx_nempty[OF assms(2)]
    by (cases pfx2 rule: rev_cases) auto
  have "y1 = y2"
    using pfx_common_end[OF assms(2)] s1 s2
    by simp
  hence "p1' = p2'"
    using compute_alt_path_specD(1)[OF assms(1), of ys1 y1 p1' ys2 p2'] pp s1 s2
    by simp
  thus ?thesis
    using that pp
    by blast
qed

text \<open>On the paths returned by the forest search, a common vertex is followed by the same suffix
  on both paths. Hence the paths are disjoint if and only if their last vertices differ, and the
  longest disjoint prefixes are the reversals of the results of @{const longest_disj_sfx} on the
  reversed paths.\<close>

lemma common_suffix_disj_iff:
  assumes "compute_alt_path_spec G M (Some (p1, p2))"
  shows "set p1 \<inter> set p2 = {} \<longleftrightarrow> last p1 \<noteq> last p2"
proof
  note S = compute_alt_path_specD[OF assms]
  have ne: "p1 \<noteq> []" "p2 \<noteq> []"
    using S(7,8)
    by auto
  show "set p1 \<inter> set p2 = {}" if "last p1 \<noteq> last p2"
  proof(rule ccontr)
    assume "set p1 \<inter> set p2 \<noteq> {}"
    then obtain x where "x \<in> set p1" "x \<in> set p2"
      by blast
    then obtain pref1 post1 pref2 post2 where pp: "p1 = pref1 @ x # post1" "p2 = pref2 @ x # post2"
      by (blast dest: split_list)
    hence "last p1 = last p2"
      using S(1)[OF pp]
      by simp
    thus False
      using that
      by simp
  qed
  show "last p1 \<noteq> last p2" if "set p1 \<inter> set p2 = {}"
    using that ne last_in_set
    by fastforce
qed

lemma longest_disj_pfx_rev:
  assumes "compute_alt_path_spec G M (Some (p1, p2))" "last p1 = last p2"
  shows "longest_disj_pfx p1 p2 =
           (case longest_disj_sfx (rev p1) (rev p2) of (c1, c2) \<Rightarrow> (Some (rev c1), Some (rev c2)))"
proof-
  note S = compute_alt_path_specD[OF assms(1)]
  have "rev p1 \<noteq> []" "rev p2 \<noteq> []" "hd (rev p1) = hd (rev p2)"
    using S(7,8) assms(2)
    by (auto simp: hd_rev)
  then obtain c b s1 s2 where r: "rev p1 = c @ b # s1" "rev p2 = c @ b # s2"
      "longest_disj_sfx (rev p1) (rev p2) = (b # s1, b # s2)" "s1 = [] \<or> s2 = [] \<or> hd s1 \<noteq> hd s2"
    using longest_disj_sfx_split
    by blast
  have p: "p1 = rev s1 @ b # rev c" "p2 = rev s2 @ b # rev c"
    using arg_cong[OF r(1), of rev] arg_cong[OF r(2), of rev]
    by simp_all
  have "rev s1 = [] \<or> rev s2 = [] \<or> last (rev s1) \<noteq> last (rev s2)"
    using r(4)
    by (auto simp: last_rev)
  hence "longest_disj_pfx p1 p2 = (Some (rev s1 @ [b]), Some (rev s2 @ [b]))"
    using longest_disj_pfx_common_sfx[OF S(1) p]
    by simp
  thus ?thesis
    using r(3)
    by simp
qed

locale Find_Aug_Path_subprocedures = Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and mate_empty :: 'mate +
  fixes compute_alt_path ::
    "'adjmap \<Rightarrow> 'v list \<Rightarrow> 'mate \<Rightarrow> ('v list \<times> 'v list) option"
  assumes compute_alt_path:
    "\<And>G vs M. \<lbrakk>graph_input G vs; matching_invar G M\<rbrakk>
       \<Longrightarrow> compute_alt_path_spec (ugraph_abs G) (matching_abs M) (compute_alt_path G vs M)"
    "\<And>G vs M. \<lbrakk>graph_input G vs; matching_invar G M;
                \<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p\<rbrakk>
       \<Longrightarrow> compute_alt_path G vs M \<noteq> None"
begin

definition \<^marker>\<open>provenance human\<close> "compute_match_blossom G vs M =
  (case compute_alt_path G vs M of
     Some (p1, p2) \<Rightarrow>
       (if last p1 \<noteq> last p2 then Some (Path (rev p1 @ p2))
        else (case longest_disj_sfx (rev p1) (rev p2) of
                (c1, c2) \<Rightarrow> Some (Blossom (rev (drop (length c1) p1)) (c1 @ rev c2))))
   | None \<Rightarrow> None)"

lemmas [code] = compute_match_blossom_def

lemma compute_match_blossom_sound_path:
  assumes "graph_input G vs" "matching_invar G M" "compute_match_blossom G vs M = Some (Path p)"
  shows "graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
proof-
  obtain p1 p2 where res: "compute_alt_path G vs M = Some (p1, p2)"
      "last p1 \<noteq> last p2" "p = rev p1 @ p2"
    using assms(3)
    by (auto simp: compute_match_blossom_def split: option.splits if_splits prod.splits)
  have spec: "compute_alt_path_spec (ugraph_abs G) (matching_abs M) (Some (p1, p2))"
    using compute_alt_path(1)[OF assms(1,2)] res(1)
    by simp
  note S = compute_alt_path_specD[OF spec]
  have disj: "set p1 \<inter> set p2 = {}"
    using common_suffix_disj_iff[OF spec] res(2)
    by simp
  have ne: "p1 \<noteq> []" "p2 \<noteq> []"
    using S(7,8)
    by auto
  have "path (ugraph_abs G) (rev p1 @ p2)"
    by (rule construct_path[OF S(11,12,13)])
  moreover have "distinct (rev p1 @ p2)"
    using S(9,10) disj
    by simp
  moreover have "matching_augmenting_path (matching_abs M) (rev p1 @ p2)"
    by (rule construct_aug_path'[OF disj ne S(3,2,4,5,7,8)])
  ultimately show ?thesis
    using res(3)
    by simp
qed

lemma compute_match_blossom_sound_blossom:
  assumes "graph_input G vs" "matching_invar G M" "compute_match_blossom G vs M = Some (Blossom stem C)"
  shows "blossom (ugraph_abs G) (matching_abs M) stem C"
proof-
  obtain p1 p2 c1 c2 where res: "compute_alt_path G vs M = Some (p1, p2)"
      "last p1 = last p2" "longest_disj_sfx (rev p1) (rev p2) = (c1, c2)"
      "stem = rev (drop (length c1) p1)" "C = c1 @ rev c2"
    using assms(3)
    by (auto simp: compute_match_blossom_def split: option.splits if_splits prod.splits)
  have spec: "compute_alt_path_spec (ugraph_abs G) (matching_abs M) (Some (p1, p2))"
    using compute_alt_path(1)[OF assms(1,2)] res(1)
    by simp
  note S = compute_alt_path_specD[OF spec]
  have pfxs: "(Some (rev c1), Some (rev c2)) = longest_disj_pfx p1 p2"
    using longest_disj_pfx_rev[OF spec res(2)] res(3)
    by simp
  obtain p where p: "p1 = rev c1 @ p" "p2 = rev c2 @ p"
    by (rule common_suffix[OF spec pfxs])
  have "path (ugraph_abs G) (rev (drop (length (rev c1)) p1) @ rev (rev c1) @ rev c2)"
    by (rule pfxs_path[OF pfxs S(11,12,13)])
  moreover have "match_blossom (matching_abs M) (rev (drop (length (rev c1)) p1)) (rev (rev c1) @ rev c2)"
    by (rule common_pfxs_form_match_blossom'[OF pfxs p S(3,2,4,6,7,8,9,10)
                                                matching_invar_props(2)[OF assms(2)]])
  ultimately show ?thesis
    using res(4,5)
    by simp
qed

lemma compute_match_blossom_complete:
  assumes "graph_input G vs" "matching_invar G M"
          "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
  shows "compute_match_blossom G vs M \<noteq> None"
  using compute_alt_path(2)[OF assms]
  by (auto simp: compute_match_blossom_def split: option.splits prod.splits)

lemmas compute_match_blossom = compute_match_blossom_sound_path compute_match_blossom_sound_blossom compute_match_blossom_complete

end

end
