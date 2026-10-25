theory Compute_Alt_Path_Invars
  imports Graph_Algorithms_Dev.Parent_Map Blossom_Prefixes
begin

provenance human

                                                        

subsection \<open>Main Search Procedure: Finding Alternating Paths\<close>

subsubsection \<open>Modelling the Search Procedure as a Recursive Function\<close> 

datatype label = Odd | Even

locale compute_alt_path = match G M

for G M::"'a set set"

begin

text \<open>At this stage we don't want t assume that the vertices have any ordering.\<close>

definition if1_cond where "if1_cond flabel ex = (\<exists>v1 v2. {v1, v2} \<in> G - ex \<and>
                                                         (\<exists>r. flabel v1 = Some (r, Even)) \<and>
                                                         flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M))"

definition if1 where (*I am using this because when the RHS is in the function the function package messes up the pairing.*)
  "if1 flabel ex v1 v2 v3 r = ({v1, v2} \<in> G - ex \<and>
             flabel v1 = Some (r, Even) \<and> flabel v2 = None \<and> {v2, v3} \<in> M)"

interpretation matching_graph: graph_abs M
  using graph_invar_subset[OF graph matching(2)]
  by \<^marker>\<open>provenance ai\<close> unfold_locales

definition if2_cond where "if2_cond flabel =
   (\<exists>v1 v2 r r'. {v1, v2} \<in> G \<and> flabel v1 = Some (r, Even) \<and> flabel v2 = Some (r', Even))"

definition if2 where 
  "if2 flabel v1 v2 r r' = ({v1, v2} \<in> G \<and> flabel v1 = Some (r, Even) \<and> flabel v2 = Some (r', Even))"

(*definition if1_1_cond where "if1_1_cond flabel v2 \<equiv> flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M)"*)

subsubsection \<open>Reasoning Infrastructure\<close>

lemma if1_cond_props:
  "if1_cond flabel ex \<Longrightarrow> (\<exists>v1 v2. {v1, v2} \<in> G - ex \<and> (\<exists>r. flabel v1 = Some (r, Even)) \<and> flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M))"
  unfolding if1_cond_def
  .

lemma if1_cond_props':
  "if1_cond flabel ex \<Longrightarrow> (\<exists>v1 v2 v3 r. if1 flabel ex v1 v2 v3 r)"
  unfolding if1_cond_def if1_def
  by simp

lemma if2_cond_props:
  "if2_cond flabel \<Longrightarrow> (\<exists>v1 v2 r r'. if2 flabel v1 v2 r r')"
  unfolding if2_cond_def if2_def
  .

lemma if1_props:
  assumes "if1 flabel ex v1 v2 v3 r"
  shows 
    "{v1, v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "flabel v2 = None" "{v2, v3} \<in> M"
  using assms
  unfolding if1_def 
  by auto

lemma if1_cond_props'':
  assumes "if1_cond flabel ex"
  obtains v1 v2 v3 r where "if1 flabel ex v1 v2 v3 r"
  using assms(1)
  unfolding if1_cond_def if1_def
  by auto


lemma if2_cond_props'':
  assumes "if2_cond flabel"
  obtains v1 v2 r r' where "if2 flabel v1 v2 r r'"
  using assms(1)
  unfolding if2_cond_def if2_def
  by auto

subsubsection \<open>Termination of the Search Procedure\<close>

subsubsection \<open>Algorithm is Partially Correct: Any Computed Alternating Paths Satisfy the Correctness Props\<close>

lemma wf_par':
  assumes wf: "parent_spec par" and
    par': "par' = par(v2 := Some v1, v3 := Some v2)" and
    neq: "v1 \<noteq> v2" "v2 \<noteq> v3" "v1 \<noteq> v3" and
    no_ances: "\<forall>v. par v \<noteq> Some v2" "\<forall>v. par v \<noteq> Some v3" and
    no_par: "par v2 = None" "par v3 = None"
  shows "parent_spec par'" (is ?g1) "parent_spec (par(v2 := Some v1))" (is ?g2)
proof-
  have "(v2, v1) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
  proof \<^marker>\<open>provenance ai\<close>
    assume "(v2, v1) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    then show False
      using \<^marker>\<open>provenance human\<close> neq(1) no_ances(1)
      by \<^marker>\<open>provenance human\<close> (cases rule: converse_rtranclE) auto
  qed
  then have wf_v2_v1: "wf (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using wf[unfolded parent_spec_def]
    by blast
  moreover have "{(x, y) |x y. Some x = (par(v2 \<mapsto> v1)) y} = (insert (v1, v2) {(x, y) |x y. Some x = par y})"
    using neq(1) no_par
    by auto
  ultimately show ?g2
    unfolding parent_spec_def
    by simp

  have "(v3, v2) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
  proof \<^marker>\<open>provenance ai\<close>
    assume "(v3, v2) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    then show False
      using \<^marker>\<open>provenance human\<close> neq(2) no_ances(2)
      by \<^marker>\<open>provenance human\<close> (cases rule: converse_rtranclE) auto
  qed
  moreover have "(v3, v2) \<notin>  {(x, y). (x, v1) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>* \<and> (v2, y) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*}"
  proof \<^marker>\<open>provenance ai\<close>
    assume "(v3, v2) \<in> {(x, y). (x, v1) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>* \<and> (v2, y) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*}"
    then have \<^marker>\<open>provenance human\<close> "(v3, v1) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*"
      by \<^marker>\<open>provenance ai\<close> simp
    then show False
      using \<^marker>\<open>provenance human\<close> neq(3) no_ances(2)
      by \<^marker>\<open>provenance human\<close> (cases rule: converse_rtranclE) auto
  qed
  ultimately have "(v3, v2) \<notin> (insert (v1, v2) {(x,y) | x y. (Some x = par y)})\<^sup>*"
    unfolding rtrancl_insert
    by simp
  then have "wf (insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)}))"
    using wf_v2_v1
    by \<^marker>\<open>provenance ai\<close> (simp add: wf_insert)
  moreover have "{(x,y) | x y. (Some x = par' y)} = insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using neq(1,2) no_par
    by(auto simp add: par')
  ultimately show ?g1
    unfolding parent_spec_def
    by simp
qed

(*Done: Invar 4*)

definition flabel_invar where "flabel_invar flabel = (\<forall>v1 v2. {v1, v2} \<in> M \<longrightarrow> ((flabel v1 = None) \<longleftrightarrow> (flabel v2 = None)))"

(*Done: Invar 10 *)

definition flabel_invar_2 where
  "flabel_invar_2 flabel =
     (\<forall>v1 v2. {v1, v2} \<in> M \<longrightarrow> ((\<exists>r. flabel v1 = Some (r, Even))
                     \<longleftrightarrow> (\<exists>r. flabel v2 = Some (r, Odd))))"

(*Done: Invar 5*)

definition flabel_par_invar where "flabel_par_invar par flabel = (\<forall>v. (flabel v = None) \<longrightarrow> (par v = None \<and> (\<forall>v'. par v' \<noteq> Some v)))"

lemma 
  assumes "(\<forall>v. par v = None)"
  shows "wf {(x,y). par y = Some x}"
  using assms
  by auto

lemma flabel_invar_2_props:
  "flabel_invar_2 flabel \<Longrightarrow> flabel v1 = Some (r, Even) \<Longrightarrow> flabel v2 = Some (s, Even) \<Longrightarrow> {v1, v2} \<notin> M"
  unfolding flabel_invar_2_def
  by force

lemma flabel_invar_pres:
  assumes invars: "flabel_invar flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "flabel_invar (flabel(v2 := Some (r, lab), v3 := Some (r2, lab2)))"
proof-
  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+
  have "flabel v3 = None"
    using invars \<open>{v2, v3} \<in> M\<close> \<open>flabel v2 = None\<close>
    unfolding flabel_invar_def
    by auto

  have aux: "(flabel a = None) = (flabel b = None)" if "{a, b} \<in> M" for a b
    using invars[unfolded flabel_invar_def] that
    by \<^marker>\<open>provenance ai\<close> blast
  have \<^marker>\<open>provenance ai\<close> aux2: "(a \<in> {v2, v3}) = (b \<in> {v2, v3})" if "{a, b} \<in> M" for a b
    using \<^marker>\<open>provenance human\<close> matching \<open>{v2,v3} \<in> M\<close> that
    by \<^marker>\<open>provenance human\<close> (auto intro: doubleton_in_matching simp: insert_commute)
  show ?thesis
    unfolding flabel_invar_def
  proof \<^marker>\<open>provenance ai\<close> (intro allI impI)
    fix a b
    assume ab: "{a, b} \<in> M"
    have "(flabel a = None) = (flabel b = None)" "(a \<in> {v2, v3}) = (b \<in> {v2, v3})"
      using aux[OF ab] aux2[OF ab]
      by simp_all
    then show "((flabel(v2 := Some (r, lab), v3 := Some (r2, lab2))) a = None) = ((flabel(v2 := Some (r, lab), v3 := Some (r2, lab2))) b = None)"
      by \<^marker>\<open>provenance human\<close> (auto simp: fun_upd_def)
  qed
qed

lemma flabel_invar_2_pres:
  assumes invars: "flabel_invar_2 flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "flabel_invar_2 (flabel(v2 := Some (r, Odd), v3 := Some (r, Even)))"
proof-
  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+

  have aux: "(\<exists>r. flabel a = Some (r, Even)) = (\<exists>r. flabel b = Some (r, Odd))" if "{a, b} \<in> M" for a b
    using invars[unfolded flabel_invar_2_def] that
    by \<^marker>\<open>provenance ai\<close> blast
  have \<^marker>\<open>provenance ai\<close> aux2: "(a = v2 \<and> b = v3) \<or> (a = v3 \<and> b = v2) \<or> (a \<notin> {v2, v3} \<and> b \<notin> {v2, v3})" if "{a, b} \<in> M" for a b
    using \<^marker>\<open>provenance human\<close> matching \<open>{v2,v3} \<in> M\<close> that
    by \<^marker>\<open>provenance human\<close> (auto intro: doubleton_in_matching simp: insert_commute)
  have "v2 \<noteq> v3"
    using \<open>{v2,v3} \<in> M\<close> matching(2) graph
    by (fastforce elim: dblton_graphE)
  show ?thesis
    unfolding flabel_invar_2_def
  proof \<^marker>\<open>provenance ai\<close> (intro allI impI)
    fix a b
    assume ab: "{a, b} \<in> M"
    show "((\<exists>r'. (flabel(v2 := Some (r, Odd), v3 := Some (r, Even))) a = Some (r', Even)) =
           (\<exists>r'. (flabel(v2 := Some (r, Odd), v3 := Some (r, Even))) b = Some (r', Odd)))"
      using \<^marker>\<open>provenance human\<close> aux[OF ab] aux2[OF ab] \<open>v2 \<noteq> v3\<close>
      by \<^marker>\<open>provenance human\<close> (auto simp: fun_upd_def)
  qed
qed


lemma flabel_par_invar_pres:
  assumes invars:"flabel_par_invar par flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "flabel_par_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) (flabel(v2 := Some (r, lab), v3 := Some (r, lab2)))" (is ?g1)
    "flabel_par_invar (par(v2 \<mapsto> v1)) (flabel(v2 := Some (r, lab)))" (is ?g2)
proof-

  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+

  show ?g1 ?g2
    using  invars
    unfolding flabel_par_invar_def
    by (auto simp add: \<open>flabel v1 = Some (r, Even)\<close>)
qed

lemma parent_spec_pres:
  assumes invars: "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "parent_spec (par(v2 \<mapsto> v1, v3 \<mapsto> v2))" (is ?g1) "parent_spec (par(v2 := Some v1))" (is ?g2)
proof-
  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+
  have "flabel v3 = None"
    using invars(2) \<open>{v2, v3} \<in> M\<close> \<open>flabel v2 = None\<close>
    unfolding flabel_invar_def
    by auto

  have "par v2 = None" (is ?p1) "par v3 = None" (is ?p2)
    "\<forall>v. par v \<noteq> Some v2" (is ?p3) "\<forall>v. par v \<noteq> Some v3" (is ?p4)
  proof-
    show ?p1 ?p3
      using \<open>flabel v2 = None\<close> invars(3)
      unfolding flabel_par_invar_def
      by simp+
    show ?p2 ?p4
      using \<open>flabel v3 = None\<close> invars(3)
      unfolding flabel_par_invar_def
      by simp+
  qed
  moreover have "v1 \<noteq> v2" 
    using graph \<open>{v1,v2} \<in> G -ex\<close>
    by (fastforce elim: dblton_graphE)
  moreover have "v2 \<noteq> v3"
    using graph \<open>{v2,v3} \<in> M\<close> matching(2)
    by (fastforce elim: dblton_graphE)
  moreover have "v1 \<noteq> v3"
  proof-
    show ?thesis
      using \<open>flabel v1 = Some (r, Even)\<close> \<open>flabel v3 = None\<close>
      by auto
  qed
  ultimately show ?g1 ?g2
    by(auto intro: wf_par'[OF invars(1), of _ v2 v1 v3])
qed \<^marker>\<open>provenance ai\<close>

(*Done: Invar 1 and 2*)

fun alt_labels_invar where
  "alt_labels_invar flabel r [] = True"
| "alt_labels_invar flabel r [v] = (flabel v = Some (r, Even))"
| "alt_labels_invar flabel r (v1 # v2 # vs) = ((if (flabel v1 = Some (r, Even) \<and> flabel v2 = Some (r, Odd)) then
                                                {v1,v2} \<in> M
                                              else if (flabel v1 = Some (r, Odd) \<and> flabel v2 = Some (r, Even)) then
                                                {v1, v2} \<notin> M
                                              else undefined)
                                             \<and> alt_labels_invar flabel r (v2 #vs))"


(*Proof of Invar 1 and 2 from paper*)

lemma alt_invars_then_alt_path:
  assumes 
    "parent_spec par"
    "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par v)"
    "alt_labels_invar flabel r (parent_spec.follow par v)"
  shows "alt_path (-M) (parent_spec.follow par v)"
  using assms
proof(induction "(parent_spec.follow par v)" arbitrary: v rule: induct_list012)
  case nil
  then show ?case
    by (simp add: alt_list_empty)
next
  case (single x)
  then have "x = v"
    using parent.follow_cons[OF parent.intro[OF assms(1)], where p = "[]" ]
    by simp
  then show ?case
    by (simp add: single(1)[symmetric] Nil alt_list_empty)
next
  case (sucsuc x y zs)
  then have "x = v"
    by (intro parent.follow_cons[OF parent.intro[OF assms(1)], where p = "y # zs"]) simp
  then have "parent_spec.follow par y = y # zs"
    using sucsuc(3)
    by (subst parent.follow_cons_2[OF parent.intro[OF assms(1)], of v y zs]) simp+
  show ?case
  proof(cases zs)
    case Nil
    then show ?thesis
      using sucsuc(5,6)
      by (simp add: sucsuc(3)[symmetric] Nil alt_list_empty alt_list_step)
  next
    case (Cons z' zs')
    then have "parent_spec.follow par z' = zs"
      using \<open>parent_spec.follow par y = y # zs\<close> parent.follow_cons_2[OF parent.intro[OF assms(1)]]
      by blast
    moreover have "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par z')"
      "alt_labels_invar flabel r (parent_spec.follow par z')"
      using sucsuc(5,6)
      by (simp add: alt_list_step sucsuc(3)[symmetric] \<open>parent_spec.follow par y = y # zs\<close> Cons \<open>parent_spec.follow par z' = zs\<close>)+
    ultimately have "alt_path (- M) (parent_spec.follow par z')"
      by (intro sucsuc(1) assms(1)) simp+
    moreover have "{x, y} \<in> M" "{y, z'} \<notin> M"
      using sucsuc(5,6) 
      by(simp add: sucsuc(3)[symmetric] alt_list_step Cons)+
    ultimately show ?thesis
      using \<open>parent_spec.follow par z' = zs\<close>
      by(simp add: sucsuc(3)[symmetric] alt_list_step Cons)
  qed
qed

lemma alt_labels_invar_cong:
  "(\<forall>v\<in> set vs. flabel v = flabel2 v) \<Longrightarrow> alt_labels_invar flabel r vs = alt_labels_invar flabel2 r vs"
proof(induction vs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a vs)
  then show ?case
    by(cases vs; auto)
qed

lemma v1_neq_v3:
  assumes "if1 flabel ex v1 v2 v3 r" "flabel_invar flabel" 
  shows "v1 \<noteq> v3"
proof-  
  have "flabel v3 = None"
    using assms(2) if1_props[OF assms(1)]
    unfolding flabel_invar_def
    by auto
  moreover have "flabel v1 \<noteq> None"
    using if1_props[OF assms(1)]
    by auto
  ultimately show ?thesis
    by blast
qed

end

context compute_alt_path
begin

lemma flabel_par_invar_props: 
  assumes "flabel_par_invar par flabel" "flabel v = None"
  shows "par v = None" "(\<forall>v'. par v' \<noteq> Some v)"
  using assms
  by(auto simp add: flabel_par_invar_def)

lemma ancestors_unaffected:
  assumes
    ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "flabel_par_invar par flabel"
    "parent_spec par"
    "flabel_invar flabel" and
    neq: "v2 \<noteq> v" "v3 \<noteq> v"
  shows "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) \<Longrightarrow> \<forall>v'\<in>set(parent_spec.follow par v). par v' = par' v'" (is "?par' \<Longrightarrow> ?g1")
    "flabel' = (flabel(v2 \<mapsto> a, v3 \<mapsto> b)) \<Longrightarrow> \<forall>v'\<in>set(parent_spec.follow par v). flabel v' = flabel' v'" (is "?flabel' \<Longrightarrow> ?g2")
proof-
  have "parent par"
    using invars(2)
    by (simp add: parent_def)
  moreover have "\<forall>v''. par v'' \<noteq> Some v2"
    by(intro flabel_par_invar_props[OF invars(1)] if1_props[OF ass])
  ultimately have "\<forall>v'\<in>set (parent_spec.follow par v). v' \<noteq> v2"
    by (intro v2_nin_ancestors neq)
  then have *: "\<forall>v'\<in>set (parent_spec.follow par v). par v' = (par(v2 \<mapsto> v1)) v'"
    by (intro ancestors_unaffected_1[where ?v1.0 = v1 and ?v2.0 = v2] neq \<open>parent par\<close>) blast+
  have "flabel v3 = None"
    using invars(3) if1_props(3,4)[OF ass]
    unfolding flabel_invar_def
    by \<^marker>\<open>provenance ai\<close> auto
  have "parent (par(v2 \<mapsto> v1))"
    unfolding parent_def
    by(intro parent_spec_pres(2)[OF invars(2,3,1) ass] \<open>parent par\<close>[unfolded parent_def])
  moreover  have "\<forall>v''. (par(v2 \<mapsto> v1)) v'' \<noteq> Some v3"
    using flabel_par_invar_props(2)[OF invars(1) \<open>flabel v3 = None\<close>] if1_props(2)[OF ass] \<open>flabel v3 = None\<close>
    by (auto simp: map_upd_Some_unfold)
  ultimately have "\<forall>v'\<in>set (parent_spec.follow (par(v2 \<mapsto> v1)) v). v' \<noteq> v3"
    by (intro v2_nin_ancestors neq)
  then have "\<forall>v'\<in>set (parent_spec.follow (par(v2 \<mapsto> v1)) v). (par(v2 \<mapsto> v1)) v' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v'"
    by (intro ancestors_unaffected_1[where ?par = "(par(v2 \<mapsto> v1))" and ?v1.0 = v2 and ?v2.0 = v3] neq \<open>parent (par(v2 \<mapsto> v1))\<close>) blast+
  moreover have "v3 \<notin> set (parent_spec.follow par v)"
  proof (intro parent.nin_ancestors[OF \<open>parent par\<close> _ neq(2)] ballI)
    fix \<^marker>\<open>provenance ai\<close> x
    assume \<^marker>\<open>provenance ai\<close> "x \<in> set (parent_spec.follow par v)"
    then \<^marker>\<open>provenance ai\<close> have "par x = (par(v2 \<mapsto> v1)) x"
      using \<^marker>\<open>provenance ai\<close> *
      by \<^marker>\<open>provenance ai\<close> blast
    then \<^marker>\<open>provenance ai\<close> show "par x \<noteq> Some v3"
      using \<open>\<forall>v''. (par(v2 \<mapsto> v1)) v'' \<noteq> Some v3\<close>
      by (auto dest: spec[of _ x])
  qed \<^marker>\<open>provenance ai\<close>
  ultimately show "?par' \<Longrightarrow> ?g1"
    by (simp add: "*")
  have *: "\<forall>v'\<in>set (parent_spec.follow par v). flabel v' = (flabel(v2 \<mapsto> a)) v'"
    by (intro ancestors_unaffected_1[where ?v1.0 = a and ?v2.0 = v2] neq \<open>parent par\<close> \<open>\<forall>v'\<in>set (parent_spec.follow par v). v' \<noteq> v2\<close>) blast+
  moreover have "\<forall>v'\<in>set (parent_spec.follow (par(v2 \<mapsto> v1)) v). (flabel(v2 \<mapsto> a)) v' = (flabel(v2 \<mapsto> a, v3 \<mapsto> b)) v'"
    by (intro ancestors_unaffected_1[where ?par = "(par(v2 \<mapsto> v1))" and ?v1.0 = b and ?v2.0 = v3] neq \<open>parent (par(v2 \<mapsto> v1))\<close>
        \<open>\<forall>v'\<in>set (parent_spec.follow (par(v2 \<mapsto> v1)) v). v' \<noteq> v3\<close>) blast+
  ultimately show "?flabel' \<Longrightarrow> ?g2"
    using \<open>v3 \<notin> set (parent_spec.follow par v)\<close>
    by (simp add: "*")
qed

lemma v1_neq_v2_neq_v3: assumes "if1 flabel ex v1 v2 v3 r" shows "v1 \<noteq> v2" "v2 \<noteq> v3"
  using if1_props[OF assms]
  using \<open>{v2, v3} \<in> M\<close> graph matching(2)
  by (fastforce elim: dblton_graphE)+

lemma alt_labels_invar_pres:
  assumes  ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent_spec.follow par v)"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par v)"
    "parent_spec par"
    "flabel_invar flabel" 
    "flabel_par_invar par flabel" and
    inG: "\<exists>lab. flabel' v = Some (r', lab)" and
    flabel': "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)))" and
    par': "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  shows "alt_labels_invar flabel' r' (parent_spec.follow par' v)"
  using assms
proof(induction flabel' r' "parent_spec.follow par' v" arbitrary: v rule: alt_labels_invar.induct)
  case (1 flabel' r')
  then show ?case
    by auto
next
  case (2 flabel' r' v')
  have **:"parent par" "parent par'"
    unfolding parent_def par'
    by(intro invars(3) parent_spec_pres[OF invars(3-5) 2(2)])+
  have "v1 \<noteq> v2"  "v2 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF 2(2)])+
  have "v1 \<noteq> v3"
    using v1_neq_v3[OF 2(2,6)]
    .
  have "v' = v"
    using 2(1)[symmetric]
    by (intro parent.follow_cons[OF **(2), where p = "[]"]) simp
  have "par' v = None"
    using parent.follow_None[OF **(2) 2(1)[symmetric]]
    by simp
  then have "par v = None"
    by (auto simp add: par' split: if_splits)
  moreover have "alt_labels_invar flabel r' (parent_spec.follow par v)"
  proof(cases "v = v1")
    case True
    then show ?thesis
      using 2(3,8,9) \<open>v1 \<noteq> v2\<close> \<open>v1 \<noteq> v3\<close>
      by auto
  next
    case F1: False
    show ?thesis
    proof(cases "v = v2")
      have "par' v2 = Some v1"
        using \<open>v2 \<noteq> v3\<close>
        by(simp add: 2(10))
      moreover case True
      ultimately have False        
        using \<open>par' v = None\<close>
        by simp
      then show ?thesis
        by simp
    next
      case F2: False
      then show ?thesis
      proof(cases "v = v3")
        have "par' v3 = Some v2"
          using \<open>v2 \<noteq> v3\<close>
          by(simp add: 2(10))
        moreover case True
        ultimately have False        
          using \<open>par' v = None\<close>
          by simp
        then show ?thesis
          by simp
      next
        case False
        then have "flabel v \<noteq> None"
          using F1 F2 2(8,9)
          by (auto split: if_splits)
        then show ?thesis
          using "2.prems"(8) "2.prems"(2) "2.prems"(7) F2 False
          by auto
      qed
    qed
  qed
  ultimately have "flabel v = Some (r', Even)"
    by (auto simp add: parent.follow_psimps[OF **(1)] 2(1)[symmetric] split: option.splits)
  moreover have "v \<noteq> v2"
    using if1_props[OF 2(2)] \<open>flabel v = Some (r', Even)\<close>
    by auto
  moreover have "v \<noteq> v3"
    using \<open>par' v = None\<close> 
    by(auto simp add: par')
  ultimately have "flabel' v \<noteq> None"
    unfolding 2(9)
    by (auto split: if_splits)
  then show ?case
    using \<open>par' v = None\<close>
    by (auto simp add: parent.follow_psimps[OF **(2)] 2(1)[symmetric] "2.prems"(8)
                       \<open>flabel v = Some (r', Even)\<close> \<open>v \<noteq> v2\<close> \<open>v \<noteq> v3\<close>)
next
  case (3 flabel' r' v1' v2' vs)
  have **:"parent par" "parent par'"
    unfolding parent_def par'
    using 3(3-10)
    by (intro invars(3) parent_spec_pres)+
  have "v1' = v"
    using 3(2)[symmetric] parent.follow_cons[OF **(2)]
    by simp
  have "{v2,v3} \<in> M"
    using if1_props(4)[OF 3(3)]
    .
  have "flabel v3 = None"
    using invars(4) if1_props(3,4)[OF ass]
    unfolding flabel_invar_def
    by \<^marker>\<open>provenance ai\<close> auto
  have "{v} \<notin> M" for v
    using matching(2) graph
    by (blast elim: dblton_graphE)
  have "par' v3 = Some v2"
    by (simp add: par')
  moreover have "par' v1' = Some v2'"
    using 3(2)[symmetric] parent.follow_cons_2(2)[OF **(2)] parent.follow_cons[OF **(2)]
    by blast
  ultimately have "v1' = v3 \<longrightarrow> v2' = v2"
    by auto
  moreover  have "v1' = v2 \<Longrightarrow> v2' \<noteq> v3"
    using \<open>par' v1' = Some v2'\<close> v1_neq_v3[OF ass invars(4)] v1_neq_v2_neq_v3[OF ass]
    by \<^marker>\<open>provenance ai\<close> (auto simp: par')
  ultimately have "v2' \<noteq> v3"
    using \<open>par' v1' = Some v2'\<close> flabel_par_invar_props(2)[OF invars(5) \<open>flabel v3 = None\<close>]
      v1_neq_v2_neq_v3[OF ass]
    by (auto simp: par' split: if_splits)
  moreover have "v3 \<noteq> v2"
    using \<open>\<And>v. {v} \<notin> M\<close> \<open>{v2, v3} \<in> M\<close>
    by auto
  moreover have "\<forall>v'. par v' \<noteq> Some v2"
    using flabel_par_invar_props(2)[OF invars(5) if1_props(3)[OF assms(1)]].
  ultimately consider (c1) "v1' = v3 \<and> v2' = v2" | (c2) "v1' = v2 \<and> v2' = v1" | (c3) "{v1', v2'} \<inter> {v2, v3} = {}"
    using \<open>par' v1' = Some v2'\<close> 
    by (cases "v1' = v2"; clarsimp) (fastforce simp: par')+
  then show ?case
  proof(cases )
    case c1
    show \<^marker>\<open>provenance ai\<close> ?thesis
    proof-
      have \<^marker>\<open>provenance human\<close> e: "v1' = v3" "v2' = v2"
        using \<^marker>\<open>provenance ai\<close> c1
        by \<^marker>\<open>provenance ai\<close> simp_all
      have \<^marker>\<open>provenance human\<close> fl: "flabel' v3 = Some (r, Even)" "flabel' v2 = Some (r, Odd)"
        using e \<open>v3 \<noteq> v2\<close> 3(10)
        by \<^marker>\<open>provenance ai\<close> simp_all
      have "r' = r"
        using \<^marker>\<open>provenance human\<close> 3(9) \<open>v1' = v\<close> e(1) fl(1)
        by auto
      have \<^marker>\<open>provenance human\<close> p1: "v2' # vs = parent_spec.follow par' v2"
        using parent.follow_cons_2(1)[OF **(2), of v v2' vs] 3(2)[symmetric] \<open>v1' = v\<close> e(2)
        by \<^marker>\<open>provenance ai\<close> simp
      have \<^marker>\<open>provenance human\<close> p2: "\<exists>lab. flabel' v2 = Some (r', lab)"
        using fl(2) \<open>r' = r\<close>
        by \<^marker>\<open>provenance ai\<close> auto
      have \<^marker>\<open>provenance human\<close> "alt_labels_invar flabel' r' (v2 # vs)"
        using 3(1)[of v2, OF p1 3(3-8) p2 3(10,11)] p1 e(2)
        by \<^marker>\<open>provenance ai\<close> simp
      then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> ?thesis
        using 3(2)[symmetric] e fl \<open>r' = r\<close> \<open>{v2, v3} \<in> M\<close>
        by (simp add: insert_commute)
    qed
  next
    have aa: "{v2, vx} \<in> M \<Longrightarrow> vx = v3" for vx
      using doubleton_in_matching[OF matching(1)] \<open>{v2, v3} \<in> M\<close>
      by blast
    case c2
    show \<^marker>\<open>provenance ai\<close> ?thesis
    proof-
      have \<^marker>\<open>provenance human\<close> e: "v1' = v2" "v2' = v1"
        using \<^marker>\<open>provenance ai\<close> c2
        by \<^marker>\<open>provenance ai\<close> simp_all
      have \<^marker>\<open>provenance human\<close> n13: "v1 \<noteq> v3"
        by (rule v1_neq_v3[OF ass invars(4)])
      have \<^marker>\<open>provenance human\<close> fl: "flabel' v2 = Some (r, Odd)" "flabel' v1 = Some (r, Even)"
        using e n13 v1_neq_v2_neq_v3[OF ass] if1_props(2)[OF ass] 3(10)
        by \<^marker>\<open>provenance ai\<close> simp_all
      have "r' = r"
        using \<^marker>\<open>provenance human\<close> 3(9) \<open>v1' = v\<close> e(1) fl(1)
        by auto
      have \<^marker>\<open>provenance human\<close> "{v2, v1} \<notin> M"
        using \<^marker>\<open>provenance ai\<close> aa[of v1] n13
        by \<^marker>\<open>provenance ai\<close> auto
      have \<^marker>\<open>provenance human\<close> p1: "v2' # vs = parent_spec.follow par' v1"
        using parent.follow_cons_2(1)[OF **(2), of v v2' vs] 3(2)[symmetric] \<open>v1' = v\<close> e(2)
        by \<^marker>\<open>provenance ai\<close> simp
      have \<^marker>\<open>provenance human\<close> p2: "\<exists>lab. flabel' v1 = Some (r', lab)"
        using fl(2) \<open>r' = r\<close>
        by \<^marker>\<open>provenance ai\<close> auto
      have \<^marker>\<open>provenance human\<close> "alt_labels_invar flabel' r' (v1 # vs)"
        using 3(1)[of v1, OF p1 3(3-8) p2 3(10,11)] p1 e(2)
        by \<^marker>\<open>provenance ai\<close> simp
      then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> ?thesis
        using 3(2)[symmetric] e fl \<open>r' = r\<close> \<open>{v2, v1} \<notin> M\<close>
        by \<^marker>\<open>provenance ai\<close> simp
    qed
  next
    case c3
    then have " parent_spec.follow par v1' = parent_spec.follow par' v1'"
      by (intro ancestors_unaffected(1)[OF 3(3,8,6,7) _ _ par'] follow_cong[OF \<open>parent par\<close> _ _ \<open>parent par'\<close>])
         (auto simp add: "**"(1) parent.follow_dom)
    then have follow_eq_follow': " parent_spec.follow par v = parent_spec.follow par' v"
      unfolding \<open>v1' = v\<close>
      .
    have "alt_labels_invar flabel r' (parent_spec.follow par v1') = alt_labels_invar flabel' r' (parent_spec.follow par v1')"
      by (intro alt_labels_invar_cong[OF] ancestors_unaffected(2)[OF 3(3,8,6,7) _ _ 3(10)])
         (use c3 in \<open>auto simp add: "**"(1) parent.follow_dom\<close>)
    then have "alt_labels_invar flabel r' (parent_spec.follow par v) = alt_labels_invar flabel' r' (parent_spec.follow par v)"
      unfolding \<open>v1' = v\<close>
      .
    moreover have "alt_labels_invar flabel r' (parent_spec.follow par v1')"
    proof-
      obtain lab where "flabel' v = Some (r', lab)"
        using 3
        by auto
      then have "flabel v = Some (r', lab)"
        using c3 \<open>v1' = v\<close>
        by (auto simp add: 3(10) split: if_splits)
      then show ?thesis
        by (intro 3(4)) (use \<open>v1' = v\<close> in simp)
    qed
    ultimately show ?thesis
      unfolding \<open>v1' = v\<close>
      by (simp add: follow_eq_follow')
  qed
qed

lemma alt_list_pres:
  assumes  ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par v)"
    "parent_spec par"
    "flabel_invar flabel" 
    "flabel_par_invar par flabel" and
    inG: "flabel' v = Some (r', Even)" and
    flabel': "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)))" and
    par': "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  shows "alt_list (\<lambda>v. flabel' v = Some (r', Even)) (\<lambda>v. flabel' v = Some (r', Odd)) (parent_spec.follow par' v)"
  using assms
proof(induction "(parent_spec.follow par' v)" arbitrary: v rule: induct_list012)
  case nil
  then show ?case
    by (simp add: alt_list_empty)
next
  case (single x)
  have "parent par'"
    unfolding parent_def par'
    using \<^marker>\<open>provenance ai\<close> single
    by (intro parent_spec_pres)
  then \<^marker>\<open>provenance ai\<close> have \<^marker>\<open>provenance ai\<close> "x = v"
    using \<^marker>\<open>provenance human\<close> single(1)[symmetric] parent.follow_cons[of par' v x "[]"]
    by simp
  then show ?case
    using single(1)[symmetric] single(7)
    by (simp add: alt_list_singleton)
next
  case (sucsuc x y zs)
  have **:"parent par" "parent par'"
    unfolding parent_def par'
    using sucsuc
    by (intro invars parent_spec_pres)+
  have "x = v"
    using sucsuc(3)[symmetric] parent.follow_cons[OF **(2)]
    by simp
  have "{v2,v3} \<in> M"
    using if1_props(4)[OF sucsuc(4)]
    .
  have "flabel v3 = None"
    using invars(3) if1_props(3,4)[OF ass]
    unfolding flabel_invar_def
    by \<^marker>\<open>provenance ai\<close> auto
  have "{v} \<notin> M" for v
    using matching(2) graph
    by (blast elim: dblton_graphE)
  have "par' v3 = Some v2"
    by (simp add: par')
  moreover have "par' x = Some y"
    using sucsuc(3)[symmetric] parent.follow_cons_2(2)[OF **(2)] parent.follow_cons[OF **(2)]
    by blast
  ultimately have "x = v3 \<longrightarrow> y = v2"
    by auto
  moreover  have "x = v2 \<Longrightarrow> y \<noteq> v3"
    using \<open>par' x = Some y\<close> v1_neq_v3[OF ass invars(3)] v1_neq_v2_neq_v3[OF ass]
    by \<^marker>\<open>provenance ai\<close> (auto simp: par')
  ultimately have "y \<noteq> v3"
    using \<open>par' x = Some y\<close> flabel_par_invar_props(2)[OF invars(4) \<open>flabel v3 = None\<close>]
      v1_neq_v2_neq_v3[OF ass]
    by (auto simp: par' split: if_splits)
  moreover have "v3 \<noteq> v2"
    using \<open>\<And>v. {v} \<notin> M\<close> \<open>{v2, v3} \<in> M\<close>
    by auto
  moreover have "\<forall>v'. par v' \<noteq> Some v2"
    using flabel_par_invar_props(2)[OF invars(4) if1_props(3)[OF assms(1)]] .
  ultimately consider (c1) "x = v3 \<and> y = v2" | (c2) "x = v2 \<and> y = v1" | (c3) "{x, y} \<inter> {v2, v3} = {}"
    using \<open>par' x = Some y\<close> 
    by (cases "x = v2"; clarsimp) (fastforce simp: par')+
  then show ?case
  proof cases
    case c1
    show \<^marker>\<open>provenance ai\<close> ?thesis
    proof-
      have \<^marker>\<open>provenance human\<close> e: "x = v3" "y = v2"
        using \<^marker>\<open>provenance ai\<close> c1
        by \<^marker>\<open>provenance ai\<close> simp_all
      have \<^marker>\<open>provenance human\<close> n13: "v1 \<noteq> v3"
        by (rule v1_neq_v3[OF ass invars(3)])
      have \<^marker>\<open>provenance human\<close> fl: "flabel' v3 = Some (r, Even)" "flabel' v2 = Some (r, Odd)" "flabel' v1 = Some (r, Even)"
        using e n13 v1_neq_v2_neq_v3[OF ass] if1_props(2)[OF ass] flabel'
        by \<^marker>\<open>provenance ai\<close> simp_all
      have \<^marker>\<open>provenance human\<close> fv: "flabel' v = Some (r, Even)"
        using fl(1) e(1) \<open>x = v\<close>
        by \<^marker>\<open>provenance ai\<close> simp
      have "r' = r"
        using \<^marker>\<open>provenance human\<close> sucsuc(9)[unfolded fv]
        by simp
      have \<^marker>\<open>provenance human\<close> h1: "zs = parent_spec.follow par' v1"
        using parent.follow_psimps[OF **(2), of y] parent.follow_cons_2(1)[OF **(2), of x y zs] sucsuc(3)[symmetric]
              \<open>x = v\<close> e(2) par' v1_neq_v2_neq_v3[OF ass]
        by \<^marker>\<open>provenance ai\<close> simp
      have \<^marker>\<open>provenance human\<close> h2: "flabel' v1 = Some (r', Even)"
        using fl(3) \<open>r' = r\<close>
        by \<^marker>\<open>provenance ai\<close> simp
      have \<^marker>\<open>provenance human\<close> "alt_list (\<lambda>v. flabel' v = Some (r', Even)) (\<lambda>v. flabel' v = Some (r', Odd)) zs"
        using sucsuc(1)[of v1, OF h1 sucsuc(4-8) h2 sucsuc(10,11)] h1
        by \<^marker>\<open>provenance ai\<close> simp
      then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> ?thesis
        using \<^marker>\<open>provenance ai\<close> sucsuc(3)[symmetric] e fl \<open>r' = r\<close>
        by (simp add: alt_list_step)
    qed
  next
    case c2
    then show ?thesis
      using "sucsuc.prems"(6) \<open>v3 \<noteq> v2\<close> \<open>x = v\<close> flabel'
      by auto
  next
    case c3
    case c3
    then have " parent_spec.follow par x = parent_spec.follow par' x"
      by (intro ancestors_unaffected(1)[OF sucsuc(4,8,6,7) _ _ par'] follow_cong[OF \<open>parent par\<close> _ _ \<open>parent par'\<close>])
         (auto simp add: "**"(1) parent.follow_dom)
    then have follow_eq_follow': " parent_spec.follow par v = parent_spec.follow par' v"
      unfolding \<open>x = v\<close>
      .
    have "\<forall>v'\<in>set (parent_spec.follow par x). flabel v' = flabel' v'"
      by (rule ancestors_unaffected(2)[OF sucsuc(4,8,6,7) _ _ flabel'])
         (use c3 in \<open>auto simp add: "**"(1) parent.follow_dom\<close>)
    then have "\<forall>v'\<in>set (parent_spec.follow par v). flabel v' = flabel' v'"
      unfolding \<open>x = v\<close> .
    then have "alt_list (\<lambda>v. flabel' v = Some (r', Even)) (\<lambda>v. flabel' v = Some (r', Odd)) (parent_spec.follow par v) =
           alt_list (\<lambda>v. flabel v = Some (r', Even)) (\<lambda>v. flabel v = Some (r', Odd)) (parent_spec.follow par v)"
      by (intro alt_list_cong_eq[OF]) simp+
    moreover have "alt_list (\<lambda>v. flabel v = Some (r', Even)) (\<lambda>v. flabel v = Some (r', Odd)) (parent_spec.follow par x)"
    proof-
      have "flabel' v = Some (r', Even)"
        using sucsuc
        by auto
      then have "flabel v = Some (r', Even)"
        using c3 \<open>x = v\<close>
        by (auto simp add: sucsuc(10) split: if_splits)
      then show ?thesis
        by (intro sucsuc(5)) (use \<open>x = v\<close> in simp)
    qed
    ultimately show ?thesis
      unfolding \<open>x = v\<close>
      by (simp add: follow_eq_follow')
  qed
qed

(*Done: Invar 6*)

definition "last_not_matched_invar par flabel =
   (\<forall>v. (flabel v \<noteq> None \<longrightarrow> (last (parent_spec.follow par v) \<notin> Vs M)))"

end

context parent
begin

lemma follow_cons_3: "\<exists>l. follow v = v # l"
  using follow_nempty[of v] follow_cons
  by (cases "follow v") auto

lemma follow_cons_3': obtains l where "follow v = v # l"
  using follow_nempty[of v] follow_cons
  by (cases "follow v") auto

lemma follow_cons_4: "parent v = Some v' \<Longrightarrow> follow v = v # (follow v')"
  using follow_psimps
  by auto

lemma follow_pinduct:
  "(\<And>v. (\<And>x2. parent v = Some x2 \<Longrightarrow> P x2) \<Longrightarrow> P v) \<Longrightarrow> P a"
  by (rule follow.pinduct[OF follow_dom]) blast

end

lemma last_follow_eq:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))"  and 
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v" "v' \<noteq> v"
  shows "last (parent_spec.follow (par (v \<mapsto> v'')) v') = last (parent_spec.follow par v')"
  using assms 
proof(induction v' rule: parent.follow_pinduct[OF parent.intro[OF invar(1)]])
  case (1 v')
  then have "parent par" "parent (par (v \<mapsto> v''))"
    unfolding parent_def
    by(intro 1)+
  then have "parent_spec.follow_dom (par (v \<mapsto> v'')) v'"
    by (simp add: parent.follow_dom)
  note follow_simps [simp] = parent_spec.follow.psimps[ OF parent.follow_dom[OF \<open>parent (par(v \<mapsto> v''))\<close>], of v']
    parent_spec.follow.psimps[OF  parent.follow_dom[OF \<open>parent par\<close>], of v']
  have *: "(par (v \<mapsto> v'')) v' = par v'"
    using 1
    by (auto split: if_splits)
  show ?case
  proof(cases "par v'")
    case None
    then show ?thesis
      by (simp only: follow_simps * split: if_splits option.splits) simp
  next
    case (Some a)
    then have "(par(v \<mapsto> v'')) v' = Some a"
      unfolding "*"
      .
    have "last (parent_spec.follow (par(v \<mapsto> v'')) a) = last (parent_spec.follow par a)"
      by (intro 1) (use Some 1(4) in \<open>auto simp add: \<open>parent par\<close> parent.follow_dom\<close>)
    moreover have "last (parent_spec.follow (par(v \<mapsto> v'')) v') = last (parent_spec.follow (par(v \<mapsto> v'')) a)"
      unfolding parent.follow_cons_4[OF \<open>parent (par(v \<mapsto> v''))\<close> \<open>(par(v \<mapsto> v'')) v' = Some a\<close>]
      using last_ConsR[OF parent.follow_nempty[OF \<open>parent (par(v \<mapsto> v''))\<close>]]
      .
    moreover have "last (parent_spec.follow par v') = last (parent_spec.follow par a)"
      unfolding parent.follow_cons_4[OF \<open>parent par\<close> Some]
      using last_ConsR[OF parent.follow_nempty[OF \<open>parent par\<close>]]
      .
    ultimately show ?thesis
      by (simp only: fun_upd_def)
  qed
qed

lemma follow_eq:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))" and
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v"
  shows "parent_spec.follow par v'' = parent_spec.follow (par(v \<mapsto> v'')) v''"
  by \<^marker>\<open>provenance ai\<close> (intro follow_cong parent.intro[OF invar(1)] parent.follow_dom[OF parent.intro[OF invar(1)]]
            no_children_not_in_follow[OF parent.intro[OF invar(1)] neq(1) _ refl] parent.intro[OF invar(2)])
     (use neq(2) in simp)

context compute_alt_path
begin

lemma compute_alt_path_follow_eq:
  assumes ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel" and
    neq: "v2 \<noteq> v" "v3 \<noteq> v"
  shows "parent_spec.follow par v = parent_spec.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v"
    (*Can use follow_eq to prove it?*)
  by (intro follow_cong parent.intro[OF invars(1)] parent.follow_dom[OF parent.intro[OF invars(1)]]
            ancestors_unaffected(1)[OF ass invars(3,1,2)] parent.intro[OF parent_spec_pres(1)[OF invars ass]])
     (use neq in auto)

end

lemma last_follow_eq_2:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))" and
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v"
  shows "last (parent_spec.follow (par (v \<mapsto> v'')) v) = last (parent_spec.follow par v'')"
proof(cases "par v''")
  note follow_simps [simp] = parent.follow_psimps[OF parent.intro[OF invar(1)]]
    parent.follow_psimps[OF parent.intro[OF invar(2)]]
  case None
  then show ?thesis
    using neq
    by auto
next
  note follow_simps [simp] = parent.follow_psimps[OF parent.intro[OF invar(1)], of v]
    parent.follow_psimps[OF parent.intro[OF invar(2)], of v]
  case (Some a)
  then show ?thesis
    using parent.follow_nempty[OF parent.intro[OF invar(2)], where v = v'']
    using follow_eq[OF invar neq]
    by simp
qed

context compute_alt_path
begin

lemma flabel_invar_props: "flabel_invar flabel \<Longrightarrow> {v1, v2} \<in> M \<Longrightarrow> (flabel v1 = None) \<Longrightarrow> (flabel v2 = None)"
  "flabel_invar flabel \<Longrightarrow> {v1, v2} \<in> M \<Longrightarrow> (flabel v1 \<noteq> None) \<Longrightarrow> (flabel v2 \<noteq> None)"
  unfolding flabel_invar_def
  by simp+

lemma compute_alt_path_last_eq:
  assumes ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
  shows  "last (parent_spec.follow (par(v2 \<mapsto> v1)) v2) = last (parent_spec.follow par v1)" (is ?g1)
    "\<And>v. v \<noteq> v2 \<Longrightarrow> last (parent_spec.follow (par(v2 \<mapsto> v1)) v) = last (parent_spec.follow par v)" (is "\<And>v. ?p v \<Longrightarrow> ?g2 v") 
    "last (parent_spec.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v3) = last (parent_spec.follow (par(v2 \<mapsto> v1)) v2)" (is ?g3)
    "\<And>v. v \<noteq> v3 \<Longrightarrow> last (parent_spec.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v) = last (parent_spec.follow (par(v2 \<mapsto> v1)) v)" (is "\<And>v. ?p2 v \<Longrightarrow> ?g4 v")
proof-
  have parent_spec: "parent_spec (par(v2 \<mapsto> v1))"
    using parent_spec_pres(2)[OF invars(1-3) ass]
    .
  moreover have "\<forall>v'. par v' \<noteq> Some v2"
    by(intro if1_props[OF ass] flabel_par_invar_props(2)[OF invars(3)])
  moreover have "v1 \<noteq> v2"
    by(intro v1_neq_v2_neq_v3[OF ass])
  ultimately show ?g1 "\<And>v. ?p v \<Longrightarrow> ?g2 v"
    by(intro last_follow_eq[OF invars(1) parent_spec] last_follow_eq_2[OF invars(1) parent_spec]; simp)+
  have "flabel v3 = None"
    using invars(2) if1_props(3,4)[OF ass]
    unfolding flabel_invar_def
    by \<^marker>\<open>provenance ai\<close> auto
  have "parent_spec (par(v2 \<mapsto> v1))" "parent_spec (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
    by (intro parent_spec_pres[OF invars(1-3) ass])+
  moreover have "v2 \<noteq> v3"
    by(intro v1_neq_v2_neq_v3[OF ass])
  moreover have  "\<forall>v'. (par(v2 \<mapsto> v1)) v' \<noteq> Some v3"
    using flabel_par_invar_props(2)[OF invars(3) \<open>flabel v3 = None\<close>] v1_neq_v3[OF ass invars(2)]
    by (auto simp: map_upd_Some_unfold)
  ultimately
  show ?g3 "\<And>v. ?p2 v \<Longrightarrow> ?g4 v"
    by(intro last_follow_eq[OF _ ] last_follow_eq_2[OF _ ]; simp)+
qed

lemma last_not_matched_invar_pres:
  assumes 
    ass: "if1 flabel ex v1 v2 v3 r" and
    invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "last_not_matched_invar par flabel"                
  shows "last_not_matched_invar (par(v2 \<mapsto> v1)) (flabel(v2 \<mapsto> (r, lab)))" (is ?g1)
    "last_not_matched_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r2, lab2)))" (is ?g2)
proof-
  have \<^marker>\<open>provenance ai\<close> gen: "\<And>v2 v1 v3 r lab (par :: 'a \<Rightarrow> 'a option) (flabel :: 'a \<Rightarrow> ('b \<times> label) option).
      last (parent_spec.follow (par(v2 \<mapsto> v1)) v2) = last (parent_spec.follow par v1) \<Longrightarrow>
      (\<And>v. v \<noteq> v2 \<Longrightarrow> last (parent_spec.follow (par(v2 \<mapsto> v1)) v) = last (parent_spec.follow par v)) \<Longrightarrow>
      last_not_matched_invar par flabel \<Longrightarrow> flabel_par_invar par flabel \<Longrightarrow> flabel v1 \<noteq> None \<Longrightarrow>
      last_not_matched_invar (par(v2 \<mapsto> v1)) (flabel(v2 \<mapsto> (r, lab)))"
  proof-
    fix \<^marker>\<open>provenance human\<close> v2 v1 v3 r lab and par :: "'a \<Rightarrow> 'a option" and flabel::"'a \<Rightarrow> ('b \<times> label) option"
    assume \<^marker>\<open>provenance human\<close> *: "last (parent_spec.follow (par(v2 \<mapsto> v1)) v2) = last (parent_spec.follow par v1)"
      "\<And>v. v \<noteq> v2 \<Longrightarrow> last (parent_spec.follow (par(v2 \<mapsto> v1)) v) = last (parent_spec.follow par v)"
    assume \<^marker>\<open>provenance human\<close> invar: "last_not_matched_invar par flabel" "flabel_par_invar par flabel"  and
      ass: "flabel v1 \<noteq> None"
    have \<^marker>\<open>provenance human\<close> "last (parent_spec.follow (par(v2 \<mapsto> v1)) v) \<notin> Vs M" if "(flabel(v2 \<mapsto> (r, lab))) v \<noteq> None" for v
    proof(cases "v = v2")
      case True
      have "last (parent_spec.follow par v1) \<notin> Vs M"
        using invar(1) ass
        by (auto simp: last_not_matched_invar_def)
      then have "last (parent_spec.follow (par(v2 \<mapsto> v1)) v1) \<notin> Vs M"
        using "*"(1,2)
        by (cases "v1 = v2") auto
      then have "last (parent_spec.follow (par(v2 \<mapsto> v1)) v2) \<notin> Vs M"
        using "*"(1) \<open>last (parent_spec.follow par v1) \<notin> Vs M\<close>
        by \<^marker>\<open>provenance ai\<close> simp
      then show ?thesis
        using True
        by simp
    next
      case False
      then show ?thesis
        using *(2)
        using invar that
        by (fastforce simp: last_not_matched_invar_def flabel_par_invar_def)
    qed
    then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "last_not_matched_invar (par(v2 \<mapsto> v1)) (flabel(v2 := Some (r, lab)))"
      unfolding last_not_matched_invar_def
      by(intro conjI allI impI)
        (*moreover have " v \<notin> Vs M" if "(par(v2 \<mapsto> v1)) v = None" for v
      using invar(1)
      unfolding last_not_matched_invar_def
      using that
      by (clarsimp split: if_splits)
    ultimately have "last_not_matched_invar (par(v2 \<mapsto> v1)) (flabel(v2 := Some (r, lab)))"
      unfolding last_not_matched_invar_def
      by(intro conjI allI impI)*)
  qed
  have "flabel v1 \<noteq> None"
    using if1_props(2)[OF ass]
    by auto
  then show g1: ?g1
    by(intro gen[OF compute_alt_path_last_eq(1,2)[OF ass invars(1-3)] invars(4,3)])
  have "(flabel(v2 \<mapsto> (r, lab))) v2 \<noteq> None"
    by auto
  moreover have "flabel_par_invar (par(v2 \<mapsto> v1)) (flabel(v2 \<mapsto> (r, lab)))"
    using flabel_par_invar_pres(2)[OF invars(3) ass] .
  ultimately show ?g2
    by (intro gen[OF compute_alt_path_last_eq(3,4)[OF ass invars(1-3)] g1]) auto
qed

lemma last_not_matched_invar_props: 
  assumes "last_not_matched_invar par flabel"
  shows  "(flabel v = Some a \<Longrightarrow> last (parent_spec.follow par v) \<notin> Vs M)"
  using assms
  unfolding last_not_matched_invar_def
  by simp+

(*Done: Invar 8*)

definition "matching_examined_invar flabel ex = (\<forall>v1 v2. {v1, v2} \<in> M \<longrightarrow> flabel v1 \<noteq> None \<longrightarrow> {v1, v2} \<in> ex)"

lemma matching_examined_invar_props: 
  "matching_examined_invar flabel ex \<Longrightarrow> {v1, v2} \<in> M \<Longrightarrow> flabel v1 = Some (r, lab) \<Longrightarrow> {v1, v2} \<in> ex"
  unfolding matching_examined_invar_def
  by simp

lemma matching_examined_invar_pres:
  assumes 
    invars: 
    "flabel_invar flabel"
    "matching_examined_invar flabel ex" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "matching_examined_invar (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) (insert {v2, v3} (insert {v1, v2} ex))" (is ?g1)
proof-
  have \<^marker>\<open>provenance ai\<close> "\<And>v1' v2'. {v1', v2'} \<in> M \<Longrightarrow> (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) v1' \<noteq> None \<Longrightarrow>
      {v1', v2'} \<in> insert {v2, v3} (insert {v1, v2} ex)"
  proof-
    fix \<^marker>\<open>provenance human\<close> v1' v2'
    have \<^marker>\<open>provenance human\<close> "flabel_invar (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab')))"
      using flabel_invar_pres[OF invars(1) ass]
      .
    assume \<^marker>\<open>provenance human\<close> ass2: "{v1', v2'} \<in> M" "(flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) v1' \<noteq> None"
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "(flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) v2' \<noteq> None"
      by (rule flabel_invar_props[OF flabel_invar_pres[OF invars(1) ass], of v1']) (use ass2 in auto)
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "{v1, v2} \<notin> M"
      using matching_examined_invar_props[OF invars(2)]
        if1_props[OF ass]
      by fastforce
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "v1' \<noteq> v2'"
      using matching(2) graph \<open>{v1', v2'} \<in> M\<close>
      by (auto elim: dblton_graphE)
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "v1 \<noteq> v2"
      using graph if1_props(1)[OF ass(1)]
      by (auto elim: dblton_graphE)
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "v1 \<noteq> v3"
      using v1_neq_v3[OF ass invars(1)].
    ultimately \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "{v1', v2'} \<in> insert {v2, v3} (insert {v1, v2} ex)"
      by (auto split: if_splits simp add: matching_examined_invar_props[OF invars(2)] insert_commute doubleton_eq_iff
                    dest: flabel_invar_props(1)[OF invars(1) _ if1_props(3)[OF ass]])
  qed
  then show ?thesis
    unfolding matching_examined_invar_def
    by simp
qed

lemma matching_examined_invar_imp:
  assumes ass: "if1 flabel ex v1 v2 v3 r" and
    invar: "matching_examined_invar flabel ex"
  shows "{v1, v2} \<notin> M"
  using if1_props[OF ass] matching_examined_invar_props[OF invar]
  by blast

end

lemma alt_list_length_odd:
  assumes invar: "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) vs" and 
    "flabel (hd vs) = Some (r, Even)"
    "flabel (last vs) = Some (r, Even)"
    "vs \<noteq> []"
  shows "odd (length vs)"
  using assms
proof(induction vs rule: induct_list012)
  case nil
  then show ?case
    by auto
next
  case (single x)
  then show ?case
    by auto
next
  case (sucsuc x y zs)
  then show ?case
  proof(cases zs)
    case Nil
    then show ?thesis
      using sucsuc
      by (auto simp add: alt_list_step)
  next
    case (Cons z zs')
    moreover have "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) zs" "flabel (hd zs) = Some (r, Even)"
      using sucsuc(3)
      by (auto simp add: alt_list_step Cons)
    moreover have "flabel (last zs) = Some (r, Even)"
    proof-
      have "last zs = last (x # y # zs)"
        using Cons
        by auto
      then show ?thesis
        using sucsuc(5)
        by simp
    qed
    ultimately have "odd (length zs)"
      by (intro sucsuc(1)) simp+
    then show ?thesis
      by simp
  qed
qed

context compute_alt_path
begin

(*Done: Invar 7*)

definition "last_even_invar par flabel = (\<forall>v r lab. flabel v = Some(r, lab) \<longrightarrow> flabel (last (parent_spec.follow par v)) = Some (r, Even))"

lemma last_even_invar_props:
  "last_even_invar par flabel \<Longrightarrow> flabel v = Some (r, lab) \<Longrightarrow> flabel (last (parent_spec.follow par v)) = Some (r, Even)"
  unfolding last_even_invar_def
  by auto

lemma last_even_invar_pres:
  assumes  invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "last_even_invar par flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "last_even_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r, lab')))"
proof-
  define par' where "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  define flabel' where "flabel' = (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r, lab')))"
  have "parent par'"
    unfolding par'_def
    using parent.intro[OF parent_spec_pres(1)[OF invars(1-3) ass]]
    .
  note follow_simps [simp] = parent_spec.follow.psimps[OF parent.follow_dom[OF \<open>parent par'\<close>]]
  have F: "\<And>v r lab. v2 \<noteq> v \<Longrightarrow> v3 \<noteq> v \<Longrightarrow> flabel' v = Some (r, lab) \<Longrightarrow>
      flabel' (last (parent_spec.follow par' v)) = Some (r, Even)"
  proof \<^marker>\<open>provenance ai\<close>-
    fix \<^marker>\<open>provenance human\<close> v r lab
    assume \<^marker>\<open>provenance human\<close> "v2 \<noteq> v" "v3 \<noteq> v"
      "flabel' v = Some (r, lab)" 
    then \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "flabel v = Some (r, lab)"
      by (auto simp: flabel'_def)
    then \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> i: "flabel (last (parent_spec.follow par v)) = Some (r, Even)"
      by (intro last_even_invar_props[OF invars(4), of _ r lab])
    have \<^marker>\<open>provenance human\<close> "flabel (last (parent_spec.follow par v)) = Some (r, Even)"
      using i
      by simp
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "\<forall>v'\<in>set (parent_spec.follow par v). v' \<noteq> v2"
      by(intro v2_nin_ancestors[OF parent.intro[OF invars(1)] flabel_par_invar_props(2)[OF invars(3)]] if1_props[OF ass] \<open>v2 \<noteq> v\<close>)
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "\<forall>v'\<in>set (parent_spec.follow par v). v' \<noteq> v3"
      by(intro v2_nin_ancestors[OF parent.intro[OF invars(1)] flabel_par_invar_props(2)[OF invars(3)]] flabel_invar_props(1)[OF invars(2) if1_props(4,3)[OF ass]] \<open>v3 \<noteq> v\<close> )
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "(last (parent_spec.follow par v)) \<in> set (parent_spec.follow par v)"
      using parent.follow_nempty[OF parent.intro[OF invars(1)]]
      by simp
    ultimately \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "flabel' (last (parent_spec.follow par v)) = Some (r, Even)"
      unfolding flabel'_def
      by simp
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "parent_spec.follow par v =  parent_spec.follow par' v"
      unfolding par'_def
      using compute_alt_path_follow_eq[OF ass invars(1,2,3) \<open>v2 \<noteq> v\<close> \<open>v3 \<noteq> v\<close>]
      .
    ultimately \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "flabel' (last (parent_spec.follow par' v)) = Some (r, Even)"
      by simp
  qed
  moreover have *: "(last (parent_spec.follow par' v2)) = (last (parent_spec.follow par' v1))"
  proof-
    have "par' v2 = Some v1"
      unfolding par'_def
      using v1_neq_v2_neq_v3(2)[OF ass]
      by simp
    then show ?thesis
      using parent.follow_nempty[OF \<open>parent par'\<close>]
      by (simp split: if_splits)
  qed
  moreover have "(last (parent_spec.follow par' v3)) = (last (parent_spec.follow par' v1))"
  proof-
    have "par' v3 = Some v2"
      unfolding par'_def
      using if1_props[OF ass]
      by simp
    then show ?thesis
      using \<open>parent par'\<close> parent.follow_nempty
      by (subst *[symmetric]) fastforce
  qed
  moreover have "v1 \<noteq> v2" "v1 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF ass] v1_neq_v3[OF ass invars(2)])+
  ultimately have "flabel' (last (parent_spec.follow par' v)) = Some (r, Even)" if "flabel' v = Some (r, lab)" for v r lab
  proof \<^marker>\<open>provenance ai\<close> (cases "v = v2")
    case True
    have \<^marker>\<open>provenance human\<close> "flabel' v1 = Some (r, Even)"
      using that True v1_neq_v2_neq_v3(2)[OF ass] v1_neq_v2_neq_v3(1)[OF ass] v1_neq_v3[OF ass invars(2)] if1_props(2)[OF ass]
      by (auto simp: flabel'_def)
    then show ?thesis
      using F[of v1] * True that v1_neq_v2_neq_v3(1)[OF ass] v1_neq_v3[OF ass invars(2)]
      by \<^marker>\<open>provenance human\<close> (simp del: follow_simps)
  next
    case False
    show ?thesis
    proof \<^marker>\<open>provenance human\<close>(cases "v = v3")
      case \<^marker>\<open>provenance ai\<close> True
      have "flabel' v1 = Some (r, Even)"
        using that True v1_neq_v2_neq_v3(2)[OF ass] v1_neq_v2_neq_v3(1)[OF ass] v1_neq_v3[OF ass invars(2)] if1_props(2)[OF ass]
        by (auto simp: flabel'_def)
      then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?thesis
        using F[of v1] \<open>last (parent_spec.follow par' v3) = last (parent_spec.follow par' v1)\<close> True that
          v1_neq_v2_neq_v3(1)[OF ass] v1_neq_v3[OF ass invars(2)]
        by \<^marker>\<open>provenance human\<close> (simp del: follow_simps)
    next \<^marker>\<open>provenance ai\<close>
      case \<^marker>\<open>provenance ai\<close> False
      then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?thesis
        using \<^marker>\<open>provenance human\<close> F[of v] \<open>\<not> v = v2\<close> that
        by simp
    qed \<^marker>\<open>provenance ai\<close>
  qed
  then show ?thesis
    unfolding flabel'_def par'_def last_even_invar_def
    by simp
qed

lemma last_even_invar_imp:
  assumes invars: 
    "parent_spec par"
    "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par v)"
    "last_even_invar par flabel" and
    "flabel v = Some (r, Even)"
  shows "odd (length (parent_spec.follow par v))"
proof-
  have "flabel (last (parent_spec.follow par v)) = Some (r, Even)"
    using assms
    unfolding last_even_invar_def
    by simp
  moreover have "parent_spec.follow par v \<noteq> []"
    by (rule parent.follow_nempty[OF parent.intro[OF invars(1)]])
  moreover have "flabel (hd (parent_spec.follow par v)) = Some (r, Even)"
    using invars(2) \<open>parent_spec.follow par v \<noteq> []\<close>
    by (cases "parent_spec.follow par v") (auto simp: alt_list_step)
  ultimately show ?thesis
    by (intro alt_list_length_odd[OF invars(2)])
qed

(*Done: Invar 9*)

definition "distinct_invar par = (\<forall>v. distinct (parent_spec.follow par v))"

lemma distinct_invar_props: "distinct_invar par \<Longrightarrow> distinct (parent_spec.follow par v)"
  unfolding distinct_invar_def
  by simp

lemma distinct_invar_pres:
  assumes invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par v)"
    "distinct_invar par"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "distinct_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
proof-

  define par' where "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  have invar': "parent_spec par'"
    unfolding par'_def
    by (rule parent_spec_pres(1)[OF invars(1-3) ass])
  note follow_simps [simp] = parent_spec.follow.psimps[OF  parent.follow_dom[OF parent.intro[OF invar']], of v2]
    parent_spec.follow.psimps[OF  parent.follow_dom[OF parent.intro[OF invar']], of v3]

  have "v2 \<noteq> v3"
    using v1_neq_v2_neq_v3(2)[OF ass].
  then have pars: "par' v2 = Some v1" "par' v3 = Some v2"
    unfolding par'_def
    by simp+
  then have rw: "(parent_spec.follow par' v3) = v3 # v2 # (parent_spec.follow par' v1)"
    by simp

  have "flabel v1 = Some (r, Even)"
    using if1_props(2)[OF ass(1)].
  then have *: "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par v1)"
    using invars(4)
    by blast
  have "flabel v = Some (r, Even) \<or> flabel v = Some (r, Odd)" if "v \<in> set (parent_spec.follow par v1)" for v
    by(intro alt_list_or[OF *] that)
  then have ances_some: "flabel v \<noteq> None" if "v \<in> set (parent_spec.follow par v1)" for v
    using that
    by fastforce
  moreover have "flabel v2 = None"
    using if1_props(3)[OF ass]
    by simp
  moreover have "flabel v3 = None"
    by (intro flabel_invar_props[OF invars(2) if1_props(4)[OF ass]] \<open>flabel v2 = None\<close>)
  ultimately have "v3 \<notin> set (parent_spec.follow par v1)" "v2 \<notin> set (parent_spec.follow par v1)"
    by fastforce+


  have rw_v: "(parent_spec.follow par v) = (parent_spec.follow par' v)" if "v3 \<noteq> v" "v2 \<noteq> v" for v
    unfolding par'_def
    by(intro compute_alt_path_follow_eq[OF ass invars(1-3)] if1_props(3)[OF ass(1)] that)
  then have rw_v1: "(parent_spec.follow par v1) = (parent_spec.follow par' v1)"
    using \<open>flabel v1 = Some (r, Even)\<close> \<open>flabel v2 = None\<close> \<open>flabel v3 = None\<close>
    by force
  have "\<And>v. distinct (parent_spec.follow par' v)"
  proof \<^marker>\<open>provenance ai\<close>-
    fix \<^marker>\<open>provenance human\<close> v
    consider \<^marker>\<open>provenance human\<close> (c1) "v = v2" | (c2) "v = v3" | (c3) "v \<notin> {v2, v3}"
      by auto
    then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "distinct (parent_spec.follow par' v)"
    proof(cases)
      case c1
      moreover have "distinct (parent_spec.follow par' v1)"
        using distinct_invar_props[OF invars(5), of v1] rw_v1
        by simp
      ultimately show ?thesis
        using c1 \<open>v2 \<notin> set (parent_spec.follow par v1)\<close>
        by(simp add: pars rw_v1)
    next
      case c2
      moreover have "flabel v3 = None"
        by(intro flabel_invar_props[OF invars(2) if1_props(4)[OF ass]] if1_props(3)[OF ass])
      ultimately have "flabel v = None"
        by simp
      then have "v \<notin> set (parent_spec.follow par v1)"
        using ances_some
        by fastforce
      moreover have "distinct (parent_spec.follow par' v1)"
        using distinct_invar_props[OF invars(5), of v1] rw_v1
        by simp
      ultimately show ?thesis
        using c2 \<open>v2 \<notin> set (parent_spec.follow par v1)\<close> \<open>v3 \<notin> set (parent_spec.follow par v1)\<close>
          \<open>v2 \<noteq> v3\<close>
        by(simp add: pars rw_v1)
    next
      case c3
      then have *: "(parent_spec.follow par v) = (parent_spec.follow par' v)"
        using rw_v
        by auto
      show ?thesis
        using distinct_invar_props[OF invars(5), of v]
        unfolding *[symmetric] .
    qed
  qed
  then show ?thesis
    unfolding distinct_invar_def par'_def
    by(intro allI)
qed

(*Done: Invar 9*)

definition "path_invar par = (\<forall>v \<in> Vs G. path G (parent_spec.follow par v))"

lemma path_invar_props: "path_invar par \<Longrightarrow> v \<in> Vs G \<Longrightarrow> path G (parent_spec.follow par v)"
  unfolding path_invar_def
  by simp

lemma path_invar_pres:
  assumes invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "path_invar par"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "path_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
proof-
  define par' where "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  have invar': "parent_spec par'"
    unfolding par'_def
    by (rule parent_spec_pres(1)[OF invars(1-3) ass])
  note follow_simps [simp] = parent_spec.follow.psimps[OF parent.follow_dom[OF parent.intro[OF invar']]]

  have "v2 \<noteq> v3"
    using v1_neq_v2_neq_v3(2)[OF ass].
  then have pars: "par' v2 = Some v1" "par' v3 = Some v2"
    unfolding par'_def
    by simp+
  then have rw: "(parent_spec.follow par' v3) = v3 # v2 # (parent_spec.follow par' v1)"
    by simp

  have "{v3, v2} \<in> G"
    using if1_props(4)[OF ass] matching(2)
    by (auto simp: insert_commute)
  have "{v2, v1} \<in> G"
    using if1_props(1)[OF ass]
    by (auto simp: insert_commute)
  then have "v1 \<in> Vs G"
    unfolding Vs_def
    by auto

  have rw_v: "(parent_spec.follow par v) = (parent_spec.follow par' v)" if "v3 \<noteq> v" "v2 \<noteq> v" for v
    unfolding par'_def
    by(intro compute_alt_path_follow_eq[OF ass invars(1-3)] if1_props(3)[OF ass(1)] if1_props(1)[OF ass] that)
  then have rw_v1: "(parent_spec.follow par v1) = (parent_spec.follow par' v1)"
    using ass invars(2) v1_neq_v2_neq_v3(1) v1_neq_v3
    by fastforce
  have "\<And>v. v \<in> Vs G \<Longrightarrow> path G (parent_spec.follow par' v)"
  proof \<^marker>\<open>provenance ai\<close>-
    fix \<^marker>\<open>provenance human\<close> v
    assume \<^marker>\<open>provenance human\<close> "v \<in> Vs G"
    consider \<^marker>\<open>provenance human\<close> (c1) "v = v2" | (c2) "v = v3" | (c3) "v \<notin> {v2, v3}"
      by auto
    then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "path G (parent_spec.follow par' v)"
    proof(cases)
      case c1
      moreover have "path G (parent_spec.follow par' v1)"
        using path_invar_props[OF invars(4), of v1] rw_v1 \<open>v1 \<in> Vs G\<close>
        by simp
      ultimately show ?thesis
        using c1 \<open>{v2, v1} \<in> G\<close>
        by (simp add: pars rw_v1; (split option.splits)+; simp+)
    next
      case c2
      moreover have "path G (parent_spec.follow par' v1)"
        using path_invar_props[OF invars(4), of v1] rw_v1 \<open>v1 \<in> Vs G\<close>
        by simp
      ultimately show ?thesis
        using c2 \<open>{v2, v1} \<in> G\<close> \<open>{v3, v2} \<in> G\<close>
        by (simp add: pars rw_v1; (split option.splits)+; simp+)
    next
      case c3
      then have *: "(parent_spec.follow par v) = (parent_spec.follow par' v)"
        using rw_v
        by auto
      show ?thesis
        using path_invar_props[OF invars(4), of v] \<open>v \<in> Vs G\<close>
        unfolding *[symmetric] .
    qed
  qed
  then show ?thesis
    unfolding path_invar_def par'_def
    by(intro ballI)
qed

subsubsection \<open>Algorithm is Totally Correct: it does not miss Alternating Paths\<close>

(*Done: Invar 11*)

definition "examined_have_odd_verts_invar ex flabel = (\<forall>e\<in>ex. \<exists>v\<in>e.\<exists>r. flabel v = Some (r, Odd))"

lemma examined_have_odd_verts_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "examined_have_odd_verts_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
proof-
  have "flabel v2 = None"
    using if1_props(3)[OF ass].
  moreover have "flabel v3 = None"
    by(rule if1_props[OF ass] flabel_invar_props(1)[OF invars(1)])+
  ultimately show ?thesis
    using invars(2) v1_neq_v2_neq_v3(2)[OF ass]
    by \<^marker>\<open>provenance ai\<close> (clarsimp simp: examined_have_odd_verts_invar_def) (drule bspec, assumption, erule bexE, intro bexI, auto)
qed

lemma examined_have_odd_verts_invar_props:
  "examined_have_odd_verts_invar ex flabel \<Longrightarrow> \<forall>v\<in>e. flabel v = None \<Longrightarrow> e \<notin> ex"
  unfolding examined_have_odd_verts_invar_def
  by auto

(*Done: Invar 12*)

definition "unexamined_matched_unlabelled_invar ex flabel = (\<forall>e\<in>M - ex. \<forall>v\<in>e. flabel v = None)"

lemma unexamined_matched_unlabelled_invar_props:
  "unexamined_matched_unlabelled_invar ex flabel \<Longrightarrow> e \<in> M \<Longrightarrow> e \<notin> ex \<Longrightarrow> v \<in> e \<Longrightarrow> flabel v = None"
  unfolding unexamined_matched_unlabelled_invar_def
  by auto

lemma unexamined_matched_unlabelled_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "unexamined_matched_unlabelled_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
proof-
  have "flabel v2 = None"
    by(rule if1_props[OF ass])
  moreover have "flabel v3 = None"
    by(rule if1_props[OF ass] flabel_invar_props(1)[OF invars(1)])+
  ultimately show ?thesis
    using unexamined_matched_unlabelled_invar_props[OF invars(2)]
      if1_props[OF ass]
      matching_unique_match[OF matching(1)]
    by (simp add: unexamined_matched_unlabelled_invar_def) blast
qed

(*Done: Invar 13*)

definition "finite_odds_invar flabel = finite {v. \<exists>r. flabel v = Some (r, Odd)}"

lemma finite_odds_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "finite_odds_invar flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "finite_odds_invar(flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
proof-
  define flabel' where "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
  have "flabel v2 = None"
    by(rule if1_props[OF ass])
  moreover have "flabel v3 = None"
    by(intro calculation flabel_invar_props(1)[OF invars(1) if1_props(4)[OF ass]])
  moreover have "v2 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF ass])
  ultimately have "{v. \<exists>r. flabel' v = Some (r, Odd)} = insert v2 {v. \<exists>r. flabel v = Some (r, Odd)}"
    unfolding flabel'_def
    by auto
  then show ?thesis
    using invars(2)
    unfolding finite_odds_invar_def flabel'_def
    by simp
qed

(*Done: Invar 14*)

definition "odd_labelled_verts_num_invar ex flabel = 
              (card {v. \<exists>r. flabel v = Some (r, Odd)} = card (M \<inter> ex))"

lemma odd_labelled_verts_num_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "finite_odds_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "odd_labelled_verts_num_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
proof-
  define flabel' where "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
  have "v2 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF ass])
  moreover have "flabel v2 = None"
    by(rule if1_props[OF ass])
  moreover have "flabel v3 = None"
    by(rule if1_props[OF ass] flabel_invar_props(1)[OF invars(1)])+
  ultimately have "{v. \<exists>r. flabel' v = Some (r, Odd)} = insert v2 {v. \<exists>r. flabel v = Some (r, Odd)}" "v2 \<notin> {v. \<exists>r. flabel v = Some (r, Odd)}"
    unfolding flabel'_def
    by auto
  moreover have "finite {v. \<exists>r. flabel v = Some (r, Odd)}"
    using invars(3)
    unfolding finite_odds_invar_def
    by simp
  ultimately have i: "card {v. \<exists>r. flabel' v = Some (r, Odd)} = card {v. \<exists>r. flabel v = Some (r, Odd)} + 1"
    by simp
  define ex' where "ex' = (insert {v2, v3} (insert {v1, v2} ex))"
  have "flabel v3 = None"
    by (simp add: \<open>flabel v3 = None\<close>)
  then have "{v2, v3} \<notin> ex"
    by (intro examined_have_odd_verts_invar_props[where flabel = flabel] invars)
       (use \<open>flabel v2 = None\<close> in simp)
  moreover have "{v1, v2} \<notin> M"
    using \<open>flabel v2 = None\<close> ass compute_alt_path.if1_props(2) compute_alt_path_axioms flabel_invar_props(2) invars(1)
    by fastforce
  moreover have "{v2, v3} \<in> M"
    by(rule if1_props[OF ass])
  moreover have "finite M"
    using infinite_super matching(2) finite_E
    by auto
  ultimately have ii: "card (M \<inter> ex') = card (M \<inter> ex) + 1"
    unfolding ex'_def
    by simp
  show ?thesis
    using i ii invars(2)
    by (auto simp: odd_labelled_verts_num_invar_def ex'_def flabel'_def)  
qed

(*Done: Invar 15*)

definition
  "ulabelled_verts_matched_invar ex flabel = (\<forall>v \<in> (Vs G). flabel v = None \<longrightarrow> (\<exists>e\<in>(M - ex). v \<in> e))"

lemma ulabelled_verts_matched_invar_pres:
  assumes invars: 
    "ulabelled_verts_matched_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "ulabelled_verts_matched_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
  using invars
  using if1_props(2)[OF ass]
  by (fastforce simp add: ulabelled_verts_matched_invar_def Vs_def)

(*Done: Invar 16*)

definition 
  "odd_then_matched_examined_invar ex flabel =
     (\<forall>v \<in> (Vs G). \<exists>r. flabel v = Some(r, Odd) \<longrightarrow> (\<exists>e\<in>(M \<inter> ex). v \<in> e))"

lemma odd_then_matched_examined_invar_pres:
  assumes invars: 
    "flabel_invar flabel"
    "odd_then_matched_examined_invar ex flabel"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "odd_then_matched_examined_invar (insert {v2, v3} (insert {v1, v2} ex)) (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r', Even)))"
  using assms
  unfolding odd_then_matched_examined_invar_def Vs_def
  by (fastforce simp add: if1_props)+

end

definition odd_set_cover where
  "odd_set_cover OSC G = (finite OSC \<and> (\<forall>s\<in>OSC. odd (card s) \<and> finite s) \<and>
                         (\<forall>e\<in>G.\<exists>s\<in>OSC. (if card s = 1 then s \<inter> e \<noteq> empty else e \<subseteq> s)))"

definition capacity1 where
  "capacity1 s = (if card s = 1 then 1 else (card s) div 2)"

lemma cap11[simp]: "capacity1 {x} = 1"
  unfolding capacity1_def
  by simp

definition capacity2 where
  "capacity2 OSC = (\<Sum>s\<in>OSC. capacity1 s)"

lemma cap21[simp]: "capacity2 {{x}} = 1"
  unfolding capacity2_def
  by simp

definition es where
  "es s = {e. card e = 2 \<and> e \<subseteq> s}"

lemma es_minus: "es (s - e) = (es s) - {e'. e' \<inter> e \<noteq> empty}"
  unfolding es_def
  by auto

lemma es_minus_matched: "matching M \<Longrightarrow> e \<in> M \<Longrightarrow> (M \<inter> (es s - {e})) = (M \<inter> es (s - e))"
  by (auto simp add: es_minus matching_def) (simp add: es_def)

lemma es_sing: "es {v} = {}"
  unfolding es_def
  by (auto simp: subset_iff card_Suc_eq numeral_2_eq_2)

lemma odd_set_coverI: 
  assumes "finite OSC" "(\<And>s. s\<in>OSC \<Longrightarrow> odd (card s) \<and> finite s)"
          "(\<And>e. e\<in>G \<Longrightarrow> \<exists>s\<in>OSC. (if card s = 1 then s \<inter> e \<noteq> empty else e \<subseteq> s))"
  shows "odd_set_cover OSC G"
  using assms 
  by (auto simp: odd_set_cover_def)

lemma capacity_bounds_common_edges:
  assumes 
    "finite G"
    "finite s"
    "matching M"
    "M \<subseteq> G"
    "odd (card s)"
    "dblton_graph G"
  shows "card (M \<inter> es s) \<le> capacity1 s"
proof-
  have "finite M"
    using assms(1,4)
    using infinite_super
    by auto
  then show ?thesis
    using assms
  proof(induction M arbitrary: s)
    case empty
    then show ?case
      by simp
  next
    case (insert e M')
    obtain v1 v2 where e: "e = {v1, v2}" "v1 \<noteq> v2"
      using insert.prems(4) insert.prems(6)
      by (auto elim: dblton_graphE)
    define es' where "es' = es s - {e}"
    define s' where "s' = s - e"
    have "card s = 1 \<or> card s = 3 \<or> 5 \<le> card s"
      using \<^marker>\<open>provenance ai\<close> insert(8)
      by \<^marker>\<open>provenance ai\<close> presburger
    consider (one) "card s = 1" | (three) "card s = 3" | (ge_five)"card s \<ge> 5"
      using \<^marker>\<open>provenance ai\<close> \<open>card s = 1 \<or> card s = 3 \<or> 5 \<le> card s\<close>
      by \<^marker>\<open>provenance ai\<close> blast
    then show ?case
    proof cases
      case one
      then obtain v where "s = {v}"
        by (erule card_1_singletonE)
      then have "card (insert e M' \<inter> es s) \<le> 1"
        by(simp add: es_sing)
      then show ?thesis
        using one
        by(simp add: capacity1_def)
    next
      define M where "M = insert e M'"
      then have "matching M"
        using insert(6)
        by simp
      case three
      then obtain u1 u2 u3 where u1u2u3: "s = {u1, u2, u3}" "u1 \<noteq> u2" "u1 \<noteq> u3"  "u2 \<noteq> u3"
        by (auto simp: card_Suc_eq numeral_3_eq_3 numeral_2_eq_2)
      then have "es s = {{u1,u2}, {u2,u3}, {u1,u3}}" "{u1,u2} \<noteq> {u2,u3}" "{u1,u2} \<noteq> {u1,u3}" "{u2,u3} \<noteq> {u1,u3}"
        unfolding es_def
        by (auto simp: card_Suc_eq numeral_2_eq_2 subset_iff)
      then have "\<exists>e1 e2. e1 \<noteq> e2 \<and> e1 \<in> M \<and> e2 \<in> M \<and> e1 \<inter> e2 \<noteq> empty" if "2 \<le> card (M \<inter> es s)"
      proof \<^marker>\<open>provenance ai\<close>-
        have \<^marker>\<open>provenance human\<close> "Suc 1 \<le> card (M \<inter> es s)"
          using \<^marker>\<open>provenance ai\<close> that
          by \<^marker>\<open>provenance ai\<close> simp
        then have "\<exists>a B. M \<inter> es s = insert a B \<and> a \<notin> B \<and> 1 \<le> card B \<and> finite B"
          by \<^marker>\<open>provenance human\<close> (rule iffD1[OF card_le_Suc_iff])
        then obtain a B where aB: "M \<inter> es s = insert a B" "a \<notin> B" "1 \<le> card B"
          by \<^marker>\<open>provenance human\<close> (elim exE conjE) (intro that)
        then have "B \<noteq> {}"
          by auto
        then obtain b where "b \<in> B"
          by auto
        then have \<^marker>\<open>provenance human\<close> e12: "a \<in> M \<inter> es s" "b \<in> M \<inter> es s" "a \<noteq> b"
          using \<^marker>\<open>provenance ai\<close> aB
          by \<^marker>\<open>provenance ai\<close> auto
        then have "a \<in> M" "b \<in> M" "a \<inter> b \<noteq> empty"
          using \<open>es s = {{u1, u2}, {u2, u3}, {u1, u3}}\<close> u1u2u3(2-4)
          by auto
        then show ?thesis
          using e12(3)
          by blast
      qed
      then have "card (M \<inter> es s) \<le> 1"
        using \<open>matching M\<close>
        by(fastforce simp add: matching_def)
      then show ?thesis
        using three
        by(simp add: capacity1_def M_def)
    next
      case ge_five
      show ?thesis
      proof(cases "e\<subseteq>s")
        have "(insert e M' \<inter> es s) \<subseteq> insert e (M' \<inter> es s')"
          using insert(2) matching_unique_match[OF insert.prems(3)]
          by(auto simp add: es_minus es_def s'_def subset_iff)
        then have "card (insert e M' \<inter> es s) \<le> card (insert e (M' \<inter> es s'))"
          by (intro card_mono) (use insert(5) in \<open>auto simp add: s'_def es_def\<close>)
        also have "... \<le> card (M' \<inter> es s') + 1"
          by (simp add: insert.hyps(1) insert.hyps(2))
        finally have "card (insert e M' \<inter> es s) \<le> card (M' \<inter> es s') + 1".
        moreover case True
        then have "card (s - {v1, v2}) = card s - 2"
          by (simp add: e insert.prems(2))
        then have "capacity1 s' + 1 \<le> capacity1 s"
          unfolding capacity1_def s'_def e
          using ge_five
          by auto
        moreover have "odd (card s')"
          using insert(8) \<open>card (s - {v1, v2}) = card s - 2\<close> ge_five
          by(simp add: s'_def e(1))
        then have "card (M' \<inter> es s') \<le> capacity1 s'"
          using insert
          by(auto simp: s'_def matching_def)
        ultimately show ?thesis
          by linarith
      next
        case False
        then have "(M' \<inter> es s) = (insert e M' \<inter> es s)"
          using insert(2) matching_unique_match[OF insert.prems(3)]
          by(auto simp add: es_minus es_def s'_def subset_iff)
        moreover have "card (M' \<inter> es s) \<le> capacity1 s"
          by ((rule insert)+) (use insert in \<open>auto simp: s'_def matching_def\<close>)
        ultimately show ?thesis
          by simp
      qed
    qed 
  qed
qed

lemma OSC_empty: "odd_set_cover {} G \<Longrightarrow> G = {}"
  unfolding odd_set_cover_def
  by auto

lemma OSC_insert:
  assumes "card s \<ge> 3" "odd_set_cover (insert s OSC) G" "dblton_graph G"
  shows "odd_set_cover OSC (G - es s)"
proof-
  have "\<And>e. e \<in> G - es s \<Longrightarrow> \<exists>s\<in>OSC. if card s = 1 then s \<inter> e \<noteq> {} else e \<subseteq> s"
  proof \<^marker>\<open>provenance ai\<close>-
    fix \<^marker>\<open>provenance human\<close> e
    assume \<^marker>\<open>provenance human\<close> "e\<in>G - es s"
    then \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "e \<in> G"
      by simp
    then \<^marker>\<open>provenance human\<close> obtain \<^marker>\<open>provenance human\<close> s' where s': "s'\<in>(insert s OSC)"  "if card s' = 1 then s' \<inter> e \<noteq> {} else e \<subseteq> s'"
      using assms(2)
      by (auto simp add: odd_set_cover_def)
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "card e = 2"
      using assms(3) \<open>e \<in> G\<close>
      by (fastforce elim: dblton_graphE)
    ultimately \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "\<exists>s\<in>OSC. if card s = 1 then s \<inter> e \<noteq> {} else e \<subseteq> s"
      using assms(1) s' \<open>e \<in> G - es s\<close>
      by (fastforce simp add: es_def)
  qed
  then show ?thesis
    using assms(2)
    unfolding odd_set_cover_def
    by auto
qed

lemma odd_set_cover_bounds_matching_size:
  assumes 
    "finite G"
    "matching M"
    "M \<subseteq> G"
    "odd_set_cover OSC G"
    "dblton_graph G"
  shows "card M \<le> capacity2 OSC"
proof-
  have "finite OSC"
    using assms(4) odd_set_cover_def
    by blast
  then show ?thesis
    using assms
  proof(induction OSC arbitrary: M G)
    case empty
    then have "M = {}"
      using OSC_empty
      by auto
    then show ?case
      by (simp add: capacity2_def)
  next
    case (insert s OSC)
    then show ?case
    proof(cases "card s = 1")
      case True
      then obtain v where v: "s = {v}"
        by(elim card_1_singletonE)
      define ev where "ev = {e. v \<in> e}"
      have "finite (M \<inter> ev)"
        using insert.prems(1,3) infinite_super
        by \<^marker>\<open>provenance ai\<close> blast
      have "odd_set_cover OSC (G - ev)"
        using insert(1,7)
        unfolding odd_set_cover_def ev_def
        by (fastforce simp: card_Suc_eq v)
      moreover have "matching (M - ev)" "(M - ev) \<subseteq> (G - ev)"
        using insert(5,6)
        by (auto simp add: matching_def)
      ultimately have "card (M - ev) \<le> capacity2 OSC"
        by (intro insert(3)[where G = "G - ev"]) (use insert in \<open>auto simp add: dblton_graph_def\<close>)
      moreover have "\<exists>e1 e2. e1 \<noteq> e2 \<and> e1 \<in> M \<and> e2 \<in> M \<and> e1 \<inter> e2 \<noteq> empty" if "2 \<le> card (M \<inter> ev)"
      proof \<^marker>\<open>provenance ai\<close>-
        have \<^marker>\<open>provenance human\<close> "Suc 1 \<le> card (M \<inter> ev)"
          using that
          by \<^marker>\<open>provenance ai\<close> simp
        then have "\<exists>a B. M \<inter> ev = insert a B \<and> a \<notin> B \<and> 1 \<le> card B \<and> finite B"
          by \<^marker>\<open>provenance human\<close> (rule iffD1[OF card_le_Suc_iff])
        then obtain a B where aB: "M \<inter> ev = insert a B" "a \<notin> B" "1 \<le> card B"
          by \<^marker>\<open>provenance human\<close> (elim exE conjE) (intro that)
        then have "B \<noteq> {}"
          by auto
        then obtain b where "b \<in> B"
          by auto
        then have "a \<in> M \<inter> ev" "b \<in> M \<inter> ev" "a \<noteq> b"
          using aB
          by auto
        then show ?thesis
          unfolding ev_def
          by auto
      qed
      then have "card (M \<inter> ev) \<le> 1"
        using \<open>matching M\<close>
        by(fastforce simp add: matching_def)      
      then have "card M \<le> card (M - ev) + 1"
        using \<^marker>\<open>provenance ai\<close> card_Diff_subset_Int[of M ev] \<open>finite (M \<inter> ev)\<close>
        by \<^marker>\<open>provenance ai\<close> arith
      moreover have "capacity2 (insert s OSC) = capacity2 OSC + 1"
        using insert(1,2)
        by (simp add: True capacity1_def capacity2_def)
      ultimately show ?thesis
        by linarith
    next
      case False
      moreover have "odd (card s)"
        using insert(7)
        unfolding odd_set_cover_def
        by auto
      ultimately have "card s \<ge> 3"
        by presburger
      then have "odd_set_cover OSC (G - es s)"
        by (intro OSC_insert insert)
      moreover have "matching (M - es s)" "M - es s \<subseteq> G -  es s"
        using insert
        by (auto simp add: Diff_mono matching_def)
      ultimately have "card (M - es s) \<le> capacity2 OSC"
        by (intro insert(3)[where G = "G - es s"]) (use insert in \<open>auto simp: dblton_graph_def\<close>)
      moreover have "card (M \<inter> es s) \<le> capacity1 s"
        by (intro capacity_bounds_common_edges[OF insert(4)] insert)
           (use \<open>odd (card s)\<close> odd_card_imp_not_empty in \<open>force+\<close>)
      moreover have "finite (M \<inter> es s)"
        using insert.prems(1,3) infinite_super
        by blast
      then have "card (M - es s) = card M - card (M \<inter> es s)"
        using card_Diff_subset_Int
        by auto
      ultimately have "card M \<le> capacity2 OSC + capacity1 s"
        by simp
      then show ?thesis
        by (simp add: capacity2_def insert(1,2))
    qed
  qed
qed

lemma OSC_union: "odd_set_cover OSC1 G1 \<Longrightarrow> odd_set_cover OSC2 G2 \<Longrightarrow> odd_set_cover (OSC1 \<union> OSC2) (G1 \<union> G2)"
  unfolding odd_set_cover_def
  by \<^marker>\<open>provenance ai\<close> (auto simp: Un_iff; (drule bspec, assumption, erule bexE, rule bexI, auto split: if_splits))

lemma OSC_inter: "odd_set_cover OSC G1 \<Longrightarrow> odd_set_cover OSC (G1 \<inter> G2)"
  unfolding odd_set_cover_def
  by auto

lemma card_sing_image: "card {{x} | x . P x} = card {x . P x}"
proof-
  have "card ((\<lambda>x. {x}) ` {x . P x}) =  card {x . P x}"
    by (intro card_image) simp
  then show ?thesis
    by (simp add: setcompr_eq_image)
qed

lemma card_UNION_const:
  assumes "finite S"
    "(\<And>s. s \<in> S \<Longrightarrow> card s = k)"
    "\<And>s s'. s \<noteq> s' \<Longrightarrow> s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> s \<inter> s' = {}"
  shows "card (\<Union> S) = k * card S"
  using assms
proof(induction S)
  case empty
  then show ?case
    by simp
next
  case (insert s S')
  then show ?case
  proof \<^marker>\<open>provenance ai\<close> (cases "k = 0")
    case True
    have \<^marker>\<open>provenance human\<close> "card s = 0" "card (\<Union> S') = 0"
      using \<^marker>\<open>provenance ai\<close> insert True
      by \<^marker>\<open>provenance ai\<close> auto
    then show ?thesis
      using True
      by \<^marker>\<open>provenance human\<close> (cases "finite s") (auto simp: card_eq_0_iff)
  next
    case False
    have \<^marker>\<open>provenance human\<close> fin: "finite s" "finite (\<Union> S')"
      using \<^marker>\<open>provenance ai\<close> insert False
      by (auto intro: card_ge_0_finite)
    have \<^marker>\<open>provenance human\<close> "s \<inter> s' = {}" if "s' \<in> S'" for s'
      using insert.prems(2)[of s s'] insert.hyps(2) that
      by \<^marker>\<open>provenance ai\<close> auto
    then have \<^marker>\<open>provenance human\<close> "s \<inter> \<Union> S' = {}"
      by \<^marker>\<open>provenance ai\<close> auto
    then show ?thesis
      using fin insert
      by \<^marker>\<open>provenance human\<close> (simp add: card_Un_disjoint)
  qed

qed

lemma capacity1_gt1: "0 < k \<Longrightarrow> card s = Suc (2 * k) \<Longrightarrow> capacity1 s = k"
  unfolding capacity1_def
  by auto

lemma capacity2_sings:
  assumes "finite {{v} | v . P v}" shows "capacity2 {{v} | v . P v} = card {{v} | v . P v}"
proof-
  have "sum capacity1 {{v} |v. P v} = (\<Sum>s\<in>{{v} |v. P v}. 1)"
    using assms
    by(fastforce simp:capacity2_def intro: sum.mono_neutral_cong_right)
  then show ?thesis
    unfolding capacity2_def
    by simp
qed


lemma capacity2_Un_disjoint: "S \<inter> U = {} \<Longrightarrow> finite S \<Longrightarrow> finite U \<Longrightarrow> capacity2 (S \<union> U) = capacity2 S + capacity2 U"
  by (simp add: capacity2_def sum.union_disjoint)

context compute_alt_path
begin

lemma finiteM: "finite M"
  using finite_E matching(2) finite_subset
  by blast

lemma compute_alt_path_from_tree_2':
  assumes invars: 
    "flabel_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    "finite_odds_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "ulabelled_verts_matched_invar ex flabel"
    "odd_then_matched_examined_invar ex flabel" and
    noL1: "\<not> if1_cond flabel ex" and
    if2_nholds: "\<not> if2_cond flabel" and
    init:       
    "finite ex" "ex \<subseteq> G"
  shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
proof-
  have "\<exists>OSC. odd_set_cover OSC G \<and> capacity2 OSC = card M"
  proof \<^marker>\<open>provenance ai\<close>-
      define \<^marker>\<open>provenance human\<close> lab_osc where "lab_osc = {{v} | v . \<exists>r. flabel v = Some (r, Odd)}"
      have \<^marker>\<open>provenance human\<close> *: "\<And>es. (\<And>e. e \<in> es \<Longrightarrow> \<exists>v \<in> e. \<exists>r. flabel v = Some (r, Odd)) \<Longrightarrow>
                    odd_set_cover lab_osc (es \<inter> G)"
      proof \<^marker>\<open>provenance ai\<close>-
        fix \<^marker>\<open>provenance human\<close> es
        assume \<^marker>\<open>provenance human\<close> "\<And>e. e \<in> es \<Longrightarrow> \<exists>v \<in> e. \<exists>r. flabel v = Some (r, Odd)"
        then \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "\<exists>s\<in>lab_osc. e \<inter> s \<noteq> {}" if "e \<in> es" for e 
        proof \<^marker>\<open>provenance ai\<close>-
          obtain \<^marker>\<open>provenance human\<close> v where "v \<in> e" "\<exists>r. flabel v = Some (r, Odd)"
            using \<^marker>\<open>provenance ai\<close> \<open>\<And>e. e \<in> es \<Longrightarrow> \<exists>v \<in> e. \<exists>r. flabel v = Some (r, Odd)\<close>[of e] \<open>e \<in> es\<close>
            by \<^marker>\<open>provenance ai\<close> blast
          then show ?thesis
            unfolding \<^marker>\<open>provenance human\<close> lab_osc_def
            by \<^marker>\<open>provenance human\<close> auto
        qed
        moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "finite lab_osc"
          unfolding lab_osc_def
          using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
          by force
        moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "odd (card s) \<and> finite s" if "s\<in>lab_osc" for s
          using that
          unfolding lab_osc_def
          by auto
        moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "card s = 1" if "s \<in> lab_osc" for s
          using that
          unfolding lab_osc_def
          by auto
        ultimately \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "odd_set_cover lab_osc es"
          unfolding odd_set_cover_def
          by (simp add: inf_commute)
        then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "odd_set_cover lab_osc (es \<inter> G)"
          by(rule OSC_inter)
      qed
      have \<^marker>\<open>provenance human\<close> "odd_set_cover lab_osc (ex \<inter> G)"
        by \<^marker>\<open>provenance ai\<close> (intro *) (use \<open>examined_have_odd_verts_invar ex flabel\<close> examined_have_odd_verts_invar_def in blast)
      have \<^marker>\<open>provenance human\<close> "finite lab_osc"
        unfolding lab_osc_def
        using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
        by force
      have \<^marker>\<open>provenance human\<close> lab: "flabel x = None \<or> (\<exists>r. flabel x = Some (r, Odd)) \<or> (\<exists>r. flabel x = Some (r, Even))" for x
      proof \<^marker>\<open>provenance ai\<close>(cases "flabel x")
        case None
        then show ?thesis
          by simp
      next
        case (Some p)
        then obtain \<^marker>\<open>provenance human\<close> r l where "p = (r, l)"
          by \<^marker>\<open>provenance ai\<close> (cases p)
        then show ?thesis
          using Some
          by (cases l) auto
      qed
      have \<^marker>\<open>provenance human\<close> all_verts_labelled: "\<exists>v. v \<in> e \<and> (flabel v = None \<or> (\<exists>r. flabel v = Some (r, Odd)))"
        if "e \<in> G" for e
      proof-
        obtain v1 v2 where "e = {v1, v2}" "v1 \<noteq> v2"
          using \<open>e \<in> G\<close> graph_invar_dblton[OF graph]
          by (auto elim: dblton_graphE)
        then have "flabel v1 = None \<or> (\<exists>r. flabel v1 = Some (r, Odd)) \<or>
                   flabel v2 = None \<or> (\<exists>r. flabel v2 = Some (r, Odd))"
          using if2_nholds lab[of v1] lab[of v2] \<open>e = {v1, v2}\<close> that
          unfolding if2_cond_def
          by \<^marker>\<open>provenance ai\<close> auto
        moreover have "v1 \<in> e" "v2 \<in> e"
          using \<open>e = {v1, v2}\<close>
          by auto
        ultimately show ?thesis
          by auto
      qed
      have \<^marker>\<open>provenance human\<close> lab_osc_covers: "\<exists>s\<in>lab_osc. s \<inter> e \<noteq> {} \<and>  card s = 1"
        if "v \<in> e" "\<exists>r. flabel v = Some (r, Odd)" for e v
      proof-
        have "{v} \<in> lab_osc"
          using that
          unfolding lab_osc_def
          by auto
        moreover have "card {v} = 1"
          by simp
        ultimately show ?thesis
          using that
          by auto
      qed
      consider \<^marker>\<open>provenance human\<close> (all_match_ex) "card (M - ex) = 0" | (one_match_unex) "card (M - ex) = 1" | (mult_match_unex) "2 \<le> card (M - ex)"
        by linarith
      then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> ?thesis
      proof cases
        case all_match_ex
        then have "flabel v \<noteq> None" if "v \<in> e" "e \<in> G" for v e
          using \<open>ulabelled_verts_matched_invar ex flabel\<close> that finiteM 
          by (force simp: ulabelled_verts_matched_invar_def)
        then have "\<exists>v \<in> e. \<exists>r. flabel v = Some (r, Odd)" if "e \<in> G" for e
          using all_verts_labelled that
          by blast
        then have "odd_set_cover lab_osc (G \<inter> G)"
          by (intro *) simp
        then have "odd_set_cover lab_osc G"
          by simp
        moreover have "M \<inter> ex = M"
          using all_match_ex finite_subset[OF matching(2) finite_E]
          by fastforce
        then have "card (M \<inter> ex) = card M"
          by simp
        then have "card M = card lab_osc"
          using \<open>odd_labelled_verts_num_invar ex flabel\<close> 
          unfolding odd_labelled_verts_num_invar_def lab_osc_def card_sing_image
          by simp
        moreover have "... = capacity2 lab_osc"
          using \<open>finite lab_osc\<close>
          unfolding lab_osc_def
          by (intro capacity2_sings[symmetric]) auto
        ultimately show ?thesis
          by auto
      next
        case one_match_unex
        then obtain e where "(M - ex) = {e}" 
          by(auto simp: card_Suc_eq)
        then obtain v1 v2 where "e = {v1, v2}" "v1 \<noteq> v2"
          using matching(2) graph
          by (auto elim!: dblton_graphE)
        then have "flabel v1 = None" "flabel v2 = None"
          using \<open>unexamined_matched_unlabelled_invar ex flabel\<close> \<open>M - ex = {e}\<close>
          by(auto simp: unexamined_matched_unlabelled_invar_def)
        define unlab_osc where "unlab_osc = {{v1}}"
        define osc where "osc = lab_osc \<union> unlab_osc"
        have "\<exists>s\<in>osc. s \<inter> e' \<noteq> {} \<and> card s = 1" if "e' \<in> G - ex" for e'
        proof(cases "e' \<in> M")
          case True
          then have "e = e'"
            using \<open>M - ex = {e}\<close> that
            by auto
          then show ?thesis
            by(auto simp add: unlab_osc_def \<open>e = {v1, v2}\<close> osc_def)
        next
          case False
          obtain va where "va \<in> e'" "flabel va = None \<or> (\<exists>r. flabel va = Some (r, Odd))"
            using all_verts_labelled \<open>e' \<in> G - ex\<close>
            by force      
          then consider "(\<exists>r. flabel va = Some (r, Odd))" | "flabel va = None"
            by auto
          then show ?thesis
          proof cases
            case 1
            then have "{va} \<in> osc"
              unfolding osc_def lab_osc_def
              by auto
            then show ?thesis
              using \<open>va \<in> e'\<close>
              by auto
          next
            case 2
            then have "va = v1 \<or> va = v2"
              using invars(6) \<open>M - ex = {e}\<close> \<open>e = {v1, v2}\<close> \<open>va \<in> e'\<close> that edges_are_Vs
              unfolding ulabelled_verts_matched_invar_def
              by \<^marker>\<open>provenance ai\<close> auto
            then consider (v1) "va = v1" | (v2) "va = v2"
              by auto
            then show ?thesis
            proof cases
              case v1
              then show ?thesis
                using \<open>va \<in> e'\<close>
                by (auto simp: osc_def unlab_osc_def)
            next
              case v2
              obtain vb where "e' = {va, vb}" "va \<noteq> vb"
                using \<open>va \<in> e'\<close> \<open>e' \<in> G - ex\<close> graph
                by auto
              consider (none) "flabel vb = None" | (odd) "\<exists>r. flabel vb = Some (r, Odd)" | (even) "\<exists>r. flabel vb = Some (r, Even)"
                by (cases "flabel vb"; auto intro: label.exhaust)
              then show ?thesis
              proof cases
                case none
                then show ?thesis
                proof \<^marker>\<open>provenance ai\<close>-
                  have "vb \<in> Vs G"
                    using \<^marker>\<open>provenance human\<close> \<open>e' = {va, vb}\<close> \<open>e' \<in> G - ex\<close> edges_are_Vs
                    by auto
                  then have \<^marker>\<open>provenance human\<close> "vb = v1 \<or> vb = v2"
                    using invars(6) none \<open>M - ex = {e}\<close> \<open>e = {v1, v2}\<close>
                    unfolding ulabelled_verts_matched_invar_def
                    by \<^marker>\<open>provenance ai\<close> auto
                  then have "e' = e"
                    using \<^marker>\<open>provenance human\<close> \<open>e' = {va, vb}\<close> \<open>va \<noteq> vb\<close> v2 \<open>e = {v1, v2}\<close>
                    by auto
                  then show ?thesis
                    using \<^marker>\<open>provenance human\<close> \<open>M - ex = {e}\<close> False
                    by auto
                qed
              next
                case odd
                then have "\<exists>s\<in>lab_osc. s \<inter> e' \<noteq> {} \<and> card s = 1"
                  using \<open>e' = {va, vb}\<close> lab_osc_covers
                  by auto
                then show ?thesis
                  unfolding osc_def
                  by blast
              next
                case even
                moreover have "{v2, v1} \<in> M"
                  using \<open>M - ex = {e}\<close> \<open>e = {v1, v2}\<close>
                  by auto
                moreover have "{vb, va} \<in> G - ex"
                  using \<open>e' \<in> G - ex\<close> \<open>e' = {va, vb}\<close>
                  by (simp add: insert_commute)
                ultimately have "if1_cond flabel ex"
                  unfolding if1_cond_def
                  using v2 \<open>flabel v2 = None\<close>
                  by auto
                then show ?thesis
                  using noL1
                  by simp
              qed 
            qed
          qed
        qed
        moreover have "finite osc"
          unfolding osc_def lab_osc_def unlab_osc_def
          using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
          by force
        moreover have "odd (card s) \<and> finite s" if "s\<in>osc" for s
          using that
          unfolding lab_osc_def osc_def unlab_osc_def
          by auto
        moreover have "card s = 1" if "s \<in> osc" for s
          using that
          unfolding osc_def lab_osc_def unlab_osc_def
          by auto
        ultimately have "odd_set_cover osc (G - ex)"
          unfolding odd_set_cover_def
          by simp
        hence "odd_set_cover (osc \<union> lab_osc) ((G - ex) \<union> (ex \<inter> G))"
          by (intro OSC_union) (use \<open>odd_set_cover lab_osc (ex \<inter> G)\<close> in \<open>simp+\<close>)
        hence i: "odd_set_cover osc G"
          unfolding osc_def
          by (simp add: Un_Diff_Int Un_commute inf_commute)
        have "lab_osc \<inter> unlab_osc = {}"
          using \<open>flabel v1 = None\<close>
          unfolding lab_osc_def unlab_osc_def
          by auto
        moreover have "finite unlab_osc"
          by (simp add: unlab_osc_def)
        ultimately have "card osc = card lab_osc + card unlab_osc"
          unfolding osc_def
          by (intro card_Un_disjoint) (use \<open>finite lab_osc\<close> in auto)
        also have "... = card (M - ex) + card (M \<inter> ex)"
          unfolding unlab_osc_def
          using \<open>card (M - ex) = 1\<close> \<open>odd_labelled_verts_num_invar ex flabel\<close> 
          unfolding odd_labelled_verts_num_invar_def lab_osc_def card_sing_image
          by simp
        also have "... = card ((M - ex) \<union> (M \<inter> ex))"
          by (intro card_Un_disjoint[symmetric]) (use finiteM in auto)
        finally have "card osc = card ((M - ex) \<union> (M \<inter> ex))".
        moreover have "M = ((M - ex) \<union> (M \<inter> ex))"
          by auto
        ultimately have "card M = card osc"
          by simp
        moreover have *: "osc = {{v} | v. v = v1 \<or> (\<exists>r. flabel v = Some (r, Odd))}"
          unfolding osc_def lab_osc_def unlab_osc_def
          by auto
        moreover have "finite ..."
          using * \<open>finite osc\<close>
          by simp
        then have "capacity2 ... = card ..."
          by (intro capacity2_sings) (use \<open>finite lab_osc\<close> in \<open>auto simp: lab_osc_def\<close>)
        ultimately have "capacity2 osc = card M"
          by simp
        then show ?thesis
          using i
          by blast
      next
        case mult_match_unex
        then obtain e M' where M': "e \<in> M - ex" "M - ex = insert e M'" "e \<notin> M'"
          by(auto simp: card_le_Suc_iff numeral_2_eq_2)
        then obtain v1 v2 where v1v2: "e = {v1, v2}" "v1 \<noteq> v2"
          using matching(2) graph
          by (force elim: dblton_graphE)
        have M'M: "M' \<subseteq> M"
          using \<^marker>\<open>provenance ai\<close> M'(2)
          by \<^marker>\<open>provenance ai\<close> auto
        have \<^marker>\<open>provenance ai\<close> finM': "finite M'"
          using \<^marker>\<open>provenance human\<close> finite_Diff[OF finiteM, of ex] M'(2)
          by simp
        have "v1 \<notin> \<Union> M'" (*as, e is disjoint will edges in M', as M is a matching*)
          using M'M M'(1,3) v1v2(1) matching_unique_match[OF matching(1)]
          by \<^marker>\<open>provenance ai\<close> blast
        have "e = {v2, v1}"
          using \<open>e = {v1, v2}\<close>
          by auto
        then have "v2 \<notin> \<Union> M'"
          using M'M M'(1,3) matching_unique_match[OF matching(1)]
          by \<^marker>\<open>provenance ai\<close> blast
        define unlab_osc1 where "unlab_osc1  = {{v1}}"
        define unlab_osc2 where "unlab_osc2  = {{v2} \<union> \<Union>M'}"
        define osc where "osc = lab_osc \<union> unlab_osc1 \<union> unlab_osc2"
        have card_unlab_osc2: "card ({v2} \<union> \<Union> M') = Suc (2 * card M')"
        proof-
          have "finite M'"
            by \<^marker>\<open>provenance ai\<close> (rule finM')
          moreover have "card e = 2" if "e \<in> M'" for e
            using graph matching(2) M'M that
            by (auto simp: dblton_graph_def card_2_iff)
          moreover have "e \<inter> e' = {}" if "e \<in> M'" "e' \<in> M'" "e \<noteq> e'" for e e'
            using matching(1) that M'M matching_unique_match[OF matching(1)]
            by \<^marker>\<open>provenance ai\<close> blast
          ultimately have "card (\<Union>M') = (2 * card M')"
            by (intro card_UNION_const)
          have "{v2} \<inter> \<Union>M' = {}"
            using \<open>v2 \<notin> \<Union>M'\<close>
            by auto
          moreover have "finite (\<Union>M')"
            using finM' M'M matching(2) graph_invar_dblton[OF graph]
            by (intro finite_Union) (auto simp: dblton_graph_def)
          ultimately have "card ({v2} \<union> \<Union> M') = card {v2} + card (\<Union>M')"
            unfolding unlab_osc2_def
            by (intro card_Un_disjoint) auto
          then show ?thesis
            using \<open>card (\<Union>M') = (2 * card M')\<close>
            by simp
        qed

        have "finite unlab_osc1"
          unfolding unlab_osc1_def
          by auto
        moreover have "finite unlab_osc2"
          unfolding unlab_osc2_def
          by auto
        moreover have "unlab_osc1 \<inter> unlab_osc2 = {}"
          using \<open>v1 \<noteq> v2\<close> \<open>v1 \<notin> \<Union>M'\<close>
          by (auto simp: unlab_osc1_def unlab_osc2_def)
        ultimately have "capacity2 (unlab_osc1 \<union> unlab_osc2) = capacity2 unlab_osc1 + capacity2 unlab_osc2"
          by (intro capacity2_Un_disjoint)
        moreover have "capacity2 unlab_osc1 = 1"
          by (auto simp: unlab_osc1_def)
        moreover have "capacity2 unlab_osc2 = card M'"
        proof-
          have "finite M'"
            by \<^marker>\<open>provenance ai\<close> (rule finM')
          then have "0 < card M'"
            using mult_match_unex M' card_unlab_osc2
            by simp
          hence "capacity1 ({v2} \<union> \<Union> M') = card M'"
            using card_unlab_osc2
            by (intro capacity1_gt1)
          then show ?thesis
            unfolding unlab_osc2_def
            by (auto simp add: capacity2_def)
        qed
        ultimately have "capacity2 (unlab_osc1 \<union> unlab_osc2) = Suc (card M')"
          by simp
        moreover have "card (M - ex) = Suc (card M')"
          using \<^marker>\<open>provenance ai\<close> M'(2,3) finM'
          by (simp add: card_insert_disjoint)
        ultimately have "capacity2 (unlab_osc1 \<union> unlab_osc2) = card (M -ex)"
          by auto
        moreover have "capacity2 (lab_osc \<union> (unlab_osc1 \<union> unlab_osc2)) = capacity2 lab_osc + capacity2 (unlab_osc1 \<union> unlab_osc2)"
        proof-
          have "flabel v = None" if "v \<in> \<Union>M'" for v
            using that invars(3) M'(2)
            unfolding unexamined_matched_unlabelled_invar_def
            by auto
          moreover have "flabel v2 = None"
            using invars(3) M'(1) unexamined_matched_unlabelled_invar_props v1v2(1)
            by fastforce
          ultimately have "lab_osc \<inter> unlab_osc2 = {}"
            unfolding lab_osc_def unlab_osc2_def
            by auto
          moreover have "flabel v1 = None"
            using invars(3) M'(1) unexamined_matched_unlabelled_invar_props v1v2(1)
            by fastforce
          then have "lab_osc \<inter> unlab_osc1 = {}"
            using \<open>flabel v1 = None\<close>
            unfolding lab_osc_def unlab_osc1_def
            by auto
          ultimately have "lab_osc \<inter> (unlab_osc1 \<union> unlab_osc2) = {}"
            by auto
          moreover have "finite (unlab_osc1 \<union> unlab_osc2)"
            using \<open>finite unlab_osc1\<close> \<open>finite unlab_osc2\<close>
            by simp
          moreover have "finite lab_osc"
            unfolding lab_osc_def
            using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
            by force
          ultimately show ?thesis
            by (intro capacity2_Un_disjoint)
        qed
        moreover have "capacity2 lab_osc = card lab_osc"
          using \<open>finite lab_osc\<close>
          unfolding lab_osc_def
          by (intro capacity2_sings) auto
        then have "card lab_osc = card (M \<inter> ex)"
          using \<open>odd_labelled_verts_num_invar ex flabel\<close> 
          unfolding odd_labelled_verts_num_invar_def lab_osc_def card_sing_image
          by simp
        moreover have "card ((M - ex) \<union> (M \<inter> ex)) = card (M - ex) + card (M \<inter> ex)"
          by (intro card_Un_disjoint) (use finiteM in auto)
        ultimately have "capacity2 osc = card M"
          by (simp add: Un_Diff_Int \<open>capacity2 lab_osc = card lab_osc\<close> Un_assoc osc_def)
        moreover have "odd_set_cover osc G"
        proof-
          have "\<exists>s\<in>osc. (s \<inter> e' \<noteq> {} \<and> card s = 1) \<or> e' \<subseteq> s" if "e' \<in> G - ex" for e'
          proof-
            have "e' = e \<or> e' \<in> M' \<or> e' \<notin> M"
              using M' v1v2 that
              by auto
            then consider (e) "e' = e" | (M') "e' \<in> M'" | (unmatched) "e' \<notin> M"
              by blast
            then show ?thesis
            proof cases
              case e
              then show ?thesis
                by (simp add: osc_def unlab_osc1_def v1v2(1))
            next
              case M'
              then have "\<exists>s\<in>unlab_osc2. e' \<subseteq> s"
                unfolding unlab_osc2_def
                by auto
              then show ?thesis
                unfolding osc_def
                by auto
            next
              case unmatched
              have "e' \<in> G"
                using that
                by simp
              then obtain va vb where "e' = {va, vb}" "va \<noteq> vb"
                using graph
                by (blast elim: dblton_graphE)
              have "(\<forall>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even)) \<or>
                  ((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Odd))) \<or>
                  ((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even)) \<and> (\<exists>v\<in>{va,vb}. flabel v = None)) \<or>
                  (\<forall>v\<in>{va,vb}. flabel v = None)"
                by (cases "flabel va"; cases "flabel vb") (use label.exhaust label.distinct in auto)
              then consider
                (evens) "(\<forall>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even))" |
                (odd) "((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Odd)))" |
                (even_unlab) "((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even)) \<and> (\<exists>v\<in>{va,vb}. flabel v = None))"|
                (nones) "(\<forall>v\<in>{va,vb}. flabel v = None)"
                by presburger
              then show ?thesis
              proof cases
                case evens
                then have "if2_cond flabel"
                  unfolding if2_cond_def
                  using \<open>e' = {va, vb}\<close> \<open>e' \<in> G\<close>
                  by blast
                hence False
                  using \<open>\<not> if2_cond flabel\<close>
                  by simp
                then show ?thesis
                  by simp
              next
                case odd
                then have "\<exists>s\<in>lab_osc. s \<inter> e' \<noteq> {} \<and> card s = 1"
                  using \<open>e' = {va, vb}\<close> lab_osc_covers
                  by auto
                then show ?thesis
                  unfolding osc_def
                  by blast
              next
                case even_unlab
                then obtain e where "e \<in> M" "(flabel va = None \<and> va \<in> e) \<or> (flabel vb = None \<and> vb \<in> e)"
                  using \<open>ulabelled_verts_matched_invar ex flabel\<close>
                    \<open>e' \<in> G - ex\<close> \<open>e' = {va, vb}\<close>
                  unfolding ulabelled_verts_matched_invar_def Vs_def
                  by fastforce
                then obtain v where "(flabel va = None \<and> e = {v, va}) \<or> (flabel vb = None \<and> e = {v, vb})"
                  using graph matching(2)
                  by (auto elim: dblton_graphE)
                then have "flabel v = None"
                  using \<open>e \<in> M\<close> \<open>flabel_invar flabel\<close>
                  unfolding flabel_invar_def
                  by auto
                then have "if1_cond flabel ex"
                proof \<^marker>\<open>provenance ai\<close>-
                  have \<^marker>\<open>provenance human\<close> e'G: "{va, vb} \<in> G - ex" "{vb, va} \<in> G - ex"
                    using \<open>e' = {va, vb}\<close> that
                    by (simp_all add: insert_commute)
                  consider (A) "flabel va = None \<and> e = {v, va}" | (B) "flabel vb = None \<and> e = {v, vb}"
                    using \<open>flabel va = None \<and> e = {v, va} \<or> flabel vb = None \<and> e = {v, vb}\<close>
                    by blast
                  then show ?thesis
                  proof cases
                    case A
                    then obtain \<^marker>\<open>provenance human\<close> r where "flabel vb = Some (r, Even)"
                      using \<^marker>\<open>provenance ai\<close> even_unlab
                      by \<^marker>\<open>provenance ai\<close> auto
                    then show ?thesis
                      unfolding \<^marker>\<open>provenance human\<close> if1_cond_def
                      by (intro exI[of _ vb] exI[of _ va]) (use A e'G \<open>e \<in> M\<close> in \<open>auto simp: insert_commute\<close>)
                  next
                    case B
                    then obtain \<^marker>\<open>provenance human\<close> r where "flabel va = Some (r, Even)"
                      using \<^marker>\<open>provenance ai\<close> even_unlab
                      by \<^marker>\<open>provenance ai\<close> auto
                    then show ?thesis
                      unfolding \<^marker>\<open>provenance human\<close> if1_cond_def
                      by (intro exI[of _ va] exI[of _ vb]) (use B e'G \<open>e \<in> M\<close> in \<open>auto simp: insert_commute\<close>)
                  qed
                qed
                hence False
                  using \<open>\<not> if1_cond flabel ex\<close>
                  by simp
                then show ?thesis
                  by simp
              next
                case nones
                then show ?thesis
                proof(cases "va = v1 \<or> vb = v1")
                  case True
                  then have "\<exists>s\<in>unlab_osc1. s \<inter> e' \<noteq> {} \<and> card s = 1"
                    using \<open>e' = {va, vb}\<close>
                    unfolding unlab_osc1_def
                    by auto
                  then show ?thesis
                    unfolding osc_def
                    by auto
                next
                  case False
                  then have "va \<noteq> v1" "vb \<noteq> v1"
                    by simp+
                  have "\<Union>(M - ex) = {v1, v2} \<union> \<Union> M'"
                    using unlab_osc2_def \<open>M - ex = insert e M'\<close> \<open>e = {v1, v2}\<close>
                    by auto
                  also have  "... - {v1} = {v2} \<union> \<Union> M'"
                    using \<open>v1 \<noteq> v2\<close> \<open>v1 \<notin> \<Union> M'\<close>
                    by auto
                  finally have "\<Union>(M - ex) - {v1} = {v2} \<union> \<Union> M'".
                  moreover have "va \<in> \<Union>(M - ex)" "vb \<in> \<Union>(M - ex)"
                    proof \<^marker>\<open>provenance ai\<close>-
                      have \<^marker>\<open>provenance human\<close> "va \<in> Vs G" "vb \<in> Vs G"
                        using \<open>e' = {va, vb}\<close> \<open>e' \<in> G\<close> edges_are_Vs edges_are_Vs_2
                        by \<^marker>\<open>provenance ai\<close> auto
                      then show "va \<in> \<Union>(M - ex)" "vb \<in> \<Union>(M - ex)"
                        using \<^marker>\<open>provenance human\<close> nones invars(6)
                        unfolding \<^marker>\<open>provenance human\<close> ulabelled_verts_matched_invar_def
                        by auto
                    qed
                  then have "{va, vb} \<subseteq> \<Union>(M - ex) - {v1}"
                    using \<open>va \<noteq> v1\<close> \<open>vb \<noteq> v1\<close>
                    by auto
                  ultimately have "\<exists>s\<in>unlab_osc2. e' \<subseteq> s"
                    using \<open>e' = {va, vb}\<close>
                    by (simp add: unlab_osc2_def)
                  then show ?thesis
                    unfolding osc_def
                    by auto
                qed
              qed
            qed
          qed
          moreover have "finite osc"
            by (simp add: \<open>finite lab_osc\<close> osc_def unlab_osc1_def unlab_osc2_def)
          moreover have "odd (card s) \<and> finite s" if "s \<in> osc" for s
            using that card_unlab_osc2
            unfolding lab_osc_def osc_def unlab_osc1_def unlab_osc2_def
            by (cases "finite (\<Union>M')") auto
          ultimately have i: "odd_set_cover osc (G - ex)"
          proof \<^marker>\<open>provenance ai\<close>-
            have \<^marker>\<open>provenance human\<close> e_ne: "e \<noteq> {}" if "e \<in> G" for e
              using that graph_invar_dblton[OF graph]
              by (auto elim: dblton_graphE)
            have \<^marker>\<open>provenance human\<close> "\<exists>s\<in>osc. if card s = 1 then s \<inter> e \<noteq> {} else e \<subseteq> s" if "e \<in> G - ex" for e
              using \<^marker>\<open>provenance ai\<close> \<open>\<And>e'. e' \<in> G - ex \<Longrightarrow> \<exists>s\<in>osc. s \<inter> e' \<noteq> {} \<and> card s = 1 \<or> e' \<subseteq> s\<close>[of e] that e_ne[of e]
              by \<^marker>\<open>provenance ai\<close> auto
            then show ?thesis
              using \<open>finite osc\<close> \<open>\<And>s. s \<in> osc \<Longrightarrow> odd (card s) \<and> finite s\<close>
              by \<^marker>\<open>provenance human\<close> (intro odd_set_coverI) auto
          qed
          hence "odd_set_cover (osc \<union> lab_osc) ((G - ex) \<union> (ex \<inter> G))"
            by (intro OSC_union) (use \<open>odd_set_cover lab_osc (ex \<inter> G)\<close> in \<open>simp+\<close>)
          then show ?thesis
            unfolding osc_def
            by (simp add: Un_Diff_Int inf_commute Un_ac)
        qed
        ultimately show ?thesis
          by blast
      qed
  qed \<^marker>\<open>provenance human\<close>
  then have bound: "card M' \<le> card M" if "matching M'" "M' \<subseteq> G" for M'
    by \<^marker>\<open>provenance ai\<close> (elim exE conjE)
       (drule odd_set_cover_bounds_matching_size[OF finite_E that(1) that(2) _ graph_invar_dblton[OF graph]], simp)
  show \<^marker>\<open>provenance ai\<close> ?thesis
  proof (rule notI)
    assume "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
    then obtain p where p: "matching_augmenting_path M p" "path G p" "distinct p"
      by auto
    have \<^marker>\<open>provenance human\<close> "card (M \<oplus> set (edges_of_path p)) \<le> card M"
      by (rule bound[OF Berge_2(1,3)[OF p(1) matching(2) p(2,3) finiteM matching(1)]])
    then show False
      using \<^marker>\<open>provenance human\<close> Berge_2(2)[OF p(1) matching(2) p(2,3) finiteM matching(1)]
      by simp
  qed \<^marker>\<open>provenance human\<close>
qed \<^marker>\<open>provenance ai\<close>

subsubsection \<open>Bringing it All Together: Final Correctness Theorems\<close>

lemma invar_init:
  fixes flabel::"('a \<Rightarrow> ('a \<times> label) option)" and
    ex::"'a set set" and 
    par::"'a \<Rightarrow> 'a option" 
  assumes initialisation:
    "\<And>v. flabel v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
  shows
    "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent_spec.follow par v)"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par v)"
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "last_not_matched_invar par flabel"
    "matching_examined_invar flabel ex"
    "last_even_invar par flabel"
    "distinct_invar par"
    "path_invar par"
    "flabel_invar_2 flabel"
    "examined_have_odd_verts_invar ex flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    "finite_odds_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "ulabelled_verts_matched_invar ex flabel"
    "odd_then_matched_examined_invar ex flabel"
proof-
  show "flabel_invar flabel"
    using assms  
    unfolding flabel_invar_def
    by (auto simp: edges_are_Vs)
  show "examined_have_odd_verts_invar ex flabel"
    using assms  
    unfolding examined_have_odd_verts_invar_def
    by auto
  show "unexamined_matched_unlabelled_invar ex flabel"
    using assms  
    unfolding unexamined_matched_unlabelled_invar_def
    by (auto simp: Vs_def)
  show "finite_odds_invar flabel"
    using assms  
    unfolding finite_odds_invar_def Vs_def
    by (auto intro: finite_subset[of _ "{}"])
  show "odd_labelled_verts_num_invar ex flabel"
    using assms  
    unfolding odd_labelled_verts_num_invar_def
    using card_eq_0_iff
    by fastforce
  show "ulabelled_verts_matched_invar ex flabel"
    using assms  
    unfolding ulabelled_verts_matched_invar_def Vs_def
    by auto
  show "odd_then_matched_examined_invar ex flabel" 
    using assms  
    unfolding odd_then_matched_examined_invar_def
    by auto
  show "parent_spec par"
    using assms  
    unfolding parent_spec_def
    by auto
  then have "parent par"
    by (simp add: parent_def)
  then have par[simp]: "(parent_spec.follow par v) = [v]" if "par v = None" for v
    using parent.follow_psimps[OF \<open>parent par\<close>] that
    by auto
  then show "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent_spec.follow par v)"
    using assms  
    by (auto split: if_splits)
  show "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent_spec.follow par v)"
    using assms  
    by (auto simp: alt_list_step alt_list_empty)
  show "flabel_par_invar par flabel"
    using assms  
    unfolding flabel_par_invar_def
    by auto
  show "last_not_matched_invar par flabel"
    using assms  
    unfolding last_not_matched_invar_def Vs_def
    by auto
  show "matching_examined_invar flabel ex"
    using assms  
    unfolding matching_examined_invar_def Vs_def
    by auto
  show "last_even_invar par flabel"
    using assms  
    unfolding last_even_invar_def
    by auto
  show "distinct_invar par"
    using assms  
    unfolding distinct_invar_def
    by auto
  show "path_invar par"
    using assms  
    unfolding path_invar_def
    by (auto simp: Vs_def)
  show "flabel_invar_2 flabel"
    using assms  
    unfolding flabel_invar_2_def
    by (simp add: edges_are_Vs)
qed

abbreviation "ex_init \<equiv> {}"
abbreviation "par_init \<equiv> Map.empty"
abbreviation "flabel_init \<equiv> (\<lambda>v. if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)"

end \<^marker>\<open>provenance ai\<close>

subsection \<^marker>\<open>provenance ai\<close> \<open>The abstract search, one state at a time\<close>

context \<^marker>\<open>provenance ai\<close> compute_alt_path
begin

(* PLAN CHANGE: type annotation; without it the label type of flabel is generalised to a second
   type variable and the lemmas cannot be applied to the abstract search of type 'a. *)
definition \<^marker>\<open>provenance ai\<close> search_invars ::
  "'a set set \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> ('a \<times> label) option) \<Rightarrow> bool" where
  "search_invars ex par flabel \<longleftrightarrow>
     (\<forall>v r lab. flabel v = Some (r, lab) \<longrightarrow> alt_labels_invar flabel r (parent_spec.follow par v)) \<and>
     (\<forall>v r. flabel v = Some (r, Even) \<longrightarrow>
        alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd))
                 (parent_spec.follow par v)) \<and>
     parent_spec par \<and> flabel_invar flabel \<and> flabel_par_invar par flabel \<and>
     last_not_matched_invar par flabel \<and> matching_examined_invar flabel ex \<and>
     last_even_invar par flabel \<and> distinct_invar par \<and> path_invar par \<and>
     flabel_invar_2 flabel \<and>
     examined_have_odd_verts_invar ex flabel \<and> unexamined_matched_unlabelled_invar ex flabel \<and>
     finite_odds_invar flabel \<and> odd_labelled_verts_num_invar ex flabel \<and>
     ulabelled_verts_matched_invar ex flabel \<and> odd_then_matched_examined_invar ex flabel \<and>
     finite ex \<and> ex \<subseteq> G"

lemma search_invarsD:
  assumes "search_invars ex par flabel"
  shows "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent_spec.follow par v)"
        "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow>
           alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd))
                    (parent_spec.follow par v)"
        "parent_spec par" "flabel_invar flabel" "flabel_par_invar par flabel"
        "last_not_matched_invar par flabel" "matching_examined_invar flabel ex"
        "last_even_invar par flabel" "distinct_invar par" "path_invar par" "flabel_invar_2 flabel"
        "examined_have_odd_verts_invar ex flabel" "unexamined_matched_unlabelled_invar ex flabel"
        "finite_odds_invar flabel" "odd_labelled_verts_num_invar ex flabel"
        "ulabelled_verts_matched_invar ex flabel" "odd_then_matched_examined_invar ex flabel"
        "finite ex" "ex \<subseteq> G"
  using assms
  by (auto simp: search_invars_def)

lemma \<^marker>\<open>provenance ai\<close> search_invars_init:
  "search_invars {} (\<lambda>v. None) (\<lambda>v. if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)"
  using invar_init[where flabel = "\<lambda>v. if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None"
                     and ex = "{}" and par = "\<lambda>v. None"]
  by (simp add: search_invars_def)

text \<^marker>\<open>provenance ai\<close> \<open>A growth step preserves the invariants. The individual steps are those of the induction
  steps of the soundness and the completeness proofs of the abstract search.\<close>

lemma search_invars_if1:
  assumes invars: "search_invars ex par flabel" and ass: "if1 flabel ex v1 v2 v3 r"
  shows "search_invars (insert {v2, v3} (insert {v1, v2} ex)) (par(v2 \<mapsto> v1, v3 \<mapsto> v2))
           (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)))"
proof \<^marker>\<open>provenance ai\<close>-
  note I = search_invarsD[OF invars]
  let \<^marker>\<open>provenance human\<close> ?par' = "par(v2 \<mapsto> v1, v3 \<mapsto> v2)"
  let \<^marker>\<open>provenance human\<close> ?flabel' = "flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even))"
  let \<^marker>\<open>provenance human\<close> ?ex' = "insert {v2, v3} (insert {v1, v2} ex)"
  have \<^marker>\<open>provenance human\<close> "parent_spec ?par'"
    using parent_spec_pres(1)[OF I(3,4,5) ass] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "flabel_invar ?flabel'"
    using flabel_invar_pres[OF I(4) ass, of Odd _ Even] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "flabel_par_invar ?par' ?flabel'"
    using flabel_par_invar_pres(1)[OF I(5) ass] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "alt_labels_invar ?flabel' r' (parent_spec.follow ?par' v)"
    if "?flabel' v = Some (r', lab)" for v r' lab
    by (intro alt_labels_invar_pres[OF ass I(1,2,3,4,5)]) (use that in auto)
  moreover have \<^marker>\<open>provenance human\<close> "alt_list (\<lambda>v. ?flabel' v = Some (r', Even)) (\<lambda>v. ?flabel' v = Some (r', Odd))
                   (parent_spec.follow ?par' v)"
    if "?flabel' v = Some (r', Even)" for v r'
    using alt_list_pres[OF ass I(2,3,4,5)] that
    by auto
  moreover have \<^marker>\<open>provenance human\<close> "last_not_matched_invar ?par' ?flabel'"
    by (intro last_not_matched_invar_pres(2)[OF ass I(3,4,5,6)])
  moreover have \<^marker>\<open>provenance human\<close> "matching_examined_invar ?flabel' ?ex'"
    using matching_examined_invar_pres[OF I(4,7) ass] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "last_even_invar ?par' ?flabel'"
    using last_even_invar_pres[OF I(3,4,5,8) ass] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "distinct_invar ?par'"
    using distinct_invar_pres[OF I(3,4,5,2,9) ass] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "path_invar ?par'"
    using path_invar_pres[OF I(3,4,5,10) ass] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "flabel_invar_2 ?flabel'"
    by (intro flabel_invar_2_pres[OF _ ass] I(11))
  moreover have \<^marker>\<open>provenance human\<close> "examined_have_odd_verts_invar ?ex' ?flabel'"
    using examined_have_odd_verts_invar_pres(1)[OF I(4,12) ass] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "unexamined_matched_unlabelled_invar ?ex' ?flabel'"
    using unexamined_matched_unlabelled_invar_pres(1)[OF I(4,13) ass] . \<^marker>\<open>provenance ai\<close>
  moreover have \<^marker>\<open>provenance human\<close> "finite_odds_invar ?flabel'"
    by (intro finite_odds_invar_pres[where ex = ex and ?v1.0 = v1] I ass)
  moreover have \<^marker>\<open>provenance human\<close> "odd_labelled_verts_num_invar ?ex' ?flabel'"
    by (intro odd_labelled_verts_num_invar_pres[where ex = ex and ?v1.0 = v1] I ass)
  moreover have \<^marker>\<open>provenance human\<close> "ulabelled_verts_matched_invar ?ex' ?flabel'"
    by (intro ulabelled_verts_matched_invar_pres[where ex = ex and ?v1.0 = v1] I ass)
  moreover have \<^marker>\<open>provenance human\<close> "odd_then_matched_examined_invar ?ex' ?flabel'"
    by (intro odd_then_matched_examined_invar_pres[where ex = ex and ?v1.0 = v1] I ass)
  moreover have \<^marker>\<open>provenance human\<close> "finite ?ex'"
    using \<^marker>\<open>provenance ai\<close> I(18)
    by \<^marker>\<open>provenance ai\<close> simp
  moreover have \<^marker>\<open>provenance human\<close> "?ex' \<subseteq> G"
    using I(19) if1_props(1,4)[OF ass] matching(2)
    by \<^marker>\<open>provenance ai\<close> auto
  ultimately show ?thesis
    by \<^marker>\<open>provenance human\<close> (simp add: search_invars_def)
qed

text \<^marker>\<open>provenance ai\<close> \<open>An edge between two even vertices yields two paths with the properties required by
  @{const compute_alt_path_spec}. The argument is the returning case of the soundness proof of
  the abstract search.\<close>

lemma search_invars_if2_sound:
  assumes invars: "search_invars ex par flabel" and if2: "if2 flabel v1 v2 r s"
  shows "compute_alt_path_spec G M (Some (parent_spec.follow par v1, parent_spec.follow par v2))"
proof \<^marker>\<open>provenance ai\<close>-
  note I = search_invarsD[OF invars]
  define \<^marker>\<open>provenance human\<close> p1 where "p1 = parent_spec.follow par v1"
  define p2 where "p2 = parent_spec.follow par v2"
  have \<^marker>\<open>provenance human\<close> s: "flabel v1 = Some (r, Even)" "flabel v2 = Some (s, Even)" "{v1, v2} \<in> G"
    using \<^marker>\<open>provenance ai\<close> if2
    by \<^marker>\<open>provenance ai\<close> (auto simp: if2_def)
  have prt: "parent par"
    using I(3)
    by \<^marker>\<open>provenance human\<close> (simp add: parent_def)
  have \<^marker>\<open>provenance human\<close> hds: "hd p1 = v1" "hd p2 = v2"
    by (simp_all add: p1_def p2_def parent.follow_hd[OF prt])
  have \<^marker>\<open>provenance human\<close> from_tree:
    "\<And>pref1 x post1 pref2 post2. \<lbrakk>p1 = pref1 @ x # post1; p2 = pref2 @ x # post2\<rbrakk> \<Longrightarrow> post1 = post2"
    using parent.from_tree[OF prt]
    by (fastforce simp: p1_def p2_def)
  have \<^marker>\<open>provenance human\<close> lasts: "last p1 \<notin> Vs M" "last p2 \<notin> Vs M"
    using \<^marker>\<open>provenance ai\<close> I(6) s(1,2)
    by (auto simp: last_not_matched_invar_def p1_def p2_def)
  have \<^marker>\<open>provenance human\<close> nM: "{v1, v2} \<notin> M"
    by (rule flabel_invar_2_props[OF I(11) s(1,2)])
  have \<^marker>\<open>provenance human\<close> alt1: "alt_path M (hd p1 # p2)"
  proof \<^marker>\<open>provenance ai\<close>-
    have "alt_path (-M) p2"
      unfolding p2_def
      by \<^marker>\<open>provenance human\<close> (rule alt_invars_then_alt_path[OF I(3) I(2)[OF s(2)] I(1)[OF s(2)]])
    moreover have \<^marker>\<open>provenance human\<close> "{hd p1, hd p2} \<notin> M"
      using \<^marker>\<open>provenance ai\<close> nM
      by \<^marker>\<open>provenance ai\<close> (simp add: hds)
    ultimately show ?thesis
      by \<^marker>\<open>provenance human\<close> (rule nin_M_alt_path[rotated])
  qed
  have \<^marker>\<open>provenance human\<close> alt2: "alt_path M (hd p2 # p1)"
  proof \<^marker>\<open>provenance ai\<close>-
    have "alt_path (-M) p1"
      unfolding p1_def
      by \<^marker>\<open>provenance human\<close> (rule alt_invars_then_alt_path[OF I(3) I(2)[OF s(1)] I(1)[OF s(1)]])
    moreover have \<^marker>\<open>provenance human\<close> "{hd p2, hd p1} \<notin> M"
      using \<^marker>\<open>provenance ai\<close> nM
      by (simp add: hds insert_commute)
    ultimately show ?thesis
      by \<^marker>\<open>provenance human\<close> (rule nin_M_alt_path[rotated])
  qed
  have \<^marker>\<open>provenance human\<close> "v1 \<noteq> v2"
    using \<^marker>\<open>provenance ai\<close> graph s(3)
    by (auto elim: dblton_graphE simp: doubleton_eq_iff)
  hence hds_neq: "hd p1 \<noteq> hd p2"
    by (simp add: hds)
  have odds: "odd (length p1)" "odd (length p2)"
    using last_even_invar_imp[OF I(3) I(2)[OF s(1)] I(8) s(1)]
          last_even_invar_imp[OF I(3) I(2)[OF s(2)] I(8) s(2)]
    by \<^marker>\<open>provenance human\<close> (simp_all add: p1_def p2_def)
  have \<^marker>\<open>provenance human\<close> dists: "distinct p1" "distinct p2"
    by (simp_all add: p1_def p2_def distinct_invar_props[OF I(9)])
  have \<^marker>\<open>provenance human\<close> "v1 \<in> Vs G" "v2 \<in> Vs G"
    using \<^marker>\<open>provenance ai\<close> s(3)
    by (auto simp: Vs_def)
  hence paths: "path G p1" "path G p2"
    by \<^marker>\<open>provenance human\<close> (simp_all add: p1_def p2_def path_invar_props[OF I(10)])
  have \<^marker>\<open>provenance human\<close> edge: "{hd p1, hd p2} \<in> G"
    using \<^marker>\<open>provenance ai\<close> s(3)
    by \<^marker>\<open>provenance ai\<close> (simp add: hds)
  have \<^marker>\<open>provenance human\<close> "compute_alt_path_spec G M (Some (p1, p2))"
    unfolding compute_alt_path_spec_def
    using \<^marker>\<open>provenance ai\<close> from_tree alt1 alt2 lasts hds_neq odds dists paths edge
    by auto
  thus ?thesis
    by \<^marker>\<open>provenance human\<close> (simp add: p1_def p2_def)
qed \<^marker>\<open>provenance human\<close>

text \<^marker>\<open>provenance ai\<close> \<open>If no growth step applies and no edge joins two even vertices, there is no augmenting
  path (@{thm [source] compute_alt_path_from_tree_2'}).\<close>

lemma \<^marker>\<open>provenance ai\<close> search_invars_complete:
  assumes invars: "search_invars ex par flabel"
      and no_if1: "\<not> if1_cond flabel ex" and no_if2: "\<not> if2_cond flabel"
  shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
proof-
  note I = search_invarsD[OF invars]
  show ?thesis
    by (rule compute_alt_path_from_tree_2'[OF I(4,12,13,14,15,16,17) no_if1 no_if2 I(18,19)])
qed

end

end

