theory Blossom_Algo_Search              
  imports Blossom_Algo_Forest_Struct Blossom_Algo_Compute_Aug_Path 
begin                                                        

subsection \<open>Main Search Procedure: Finding Alternating Paths\<close>

subsubsection \<open>Modelling the Search Procedure as a Recursive Function\<close> 

datatype label = Odd | Even

locale compute_alt_path = match G M + choose sel 

for G M::"'a set set" and sel::"'a set \<Rightarrow> 'a"

begin

text \<open>At this stage we don't want t assume that the vertices have any ordering.\<close>

definition if1_cond where "if1_cond flabel ex = (\<exists>v1 v2. {v1, v2} \<in> G - ex \<and>
                                                         (\<exists>r. flabel v1 = Some (r, Even)) \<and>
                                                         flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M))"

definition if1 where (*I am using this because when the RHS is in the function the function package messes up the pairing.*)
  "if1 flabel ex v1 v2 v3 r = ({v1, v2} \<in> G - ex \<and>
             flabel v1 = Some (r, Even) \<and> flabel v2 = None \<and> {v2, v3} \<in> M)"

interpretation matching_graph: graph_abs M
  apply(unfold_locales)
  using graph_invar_subset[OF graph matching(2)] .

find_theorems name: neighbourhood

definition 
  "sel_if1 flabel ex = 
     (let es = D \<inter> {(v1,v2)| v1 v2. {v1,v2} \<in> (G - ex) \<and> (\<exists>r. flabel v1 = Some (r, Even)) \<and> flabel v2 = None \<and> v2 \<in> Vs M};
         (v1,v2) = sel_pair es;
         v3 = sel (Undirected_Set_Graphs.neighbourhood M v2);
         r = fst (the (flabel v1)) 
     in (v1,v2,v3,r))"

definition if2_cond where "if2_cond flabel =
   (\<exists>v1 v2 r r'. {v1, v2} \<in> G \<and> flabel v1 = Some (r, Even) \<and> flabel v2 = Some (r', Even))"

definition if2 where 
  "if2 flabel v1 v2 r r' = ({v1, v2} \<in> G \<and> flabel v1 = Some (r, Even) \<and> flabel v2 = Some (r', Even))"

definition 
  "sel_if2 flabel = 
     (let es = D \<inter> {(v1,v2)| v1 v2. {v1, v2} \<in> G \<and> (\<exists>r1. flabel v1 = Some (r1, Even)) \<and> 
                                   (\<exists>r2. flabel v2 = Some (r2, Even))};
         (v1,v2) = sel_pair es;
         r1 = fst (the (flabel v1)); 
         r2 = fst (the (flabel v2)) 
     in (v1,v2,r1,r2))"

(*definition if1_1_cond where "if1_1_cond flabel v2 \<equiv> flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M)"*)

function (domintros) compute_alt_path:: "'a set set \<Rightarrow>
                                         ('a \<Rightarrow> 'a option) \<Rightarrow>
                                         ('a \<Rightarrow> ('a \<times> label) option) \<Rightarrow>
                                         (('a list \<times> 'a list) option)" where
  "compute_alt_path ex par flabel = 
    (if if1_cond flabel ex then
       let
         (v1,v2,v3,r) = sel_if1 flabel ex;
         ex' = insert {v1, v2} ex;
         ex'' = insert {v2, v3} ex';
         par' = par(v2 := Some v1, v3 := Some v2);
         flabel' = flabel(v2 := Some (r, Odd), v3 := Some (r, Even));
         return = compute_alt_path ex'' par' flabel'
       in
         return
     else if if2_cond flabel then
        let
          (v1,v2,r,r') = sel_if2 flabel; 
          return = Some (parent.follow par v1, parent.follow par v2)
        in
          return
     else
       let
          return = None
       in
         return)"
  by pat_completeness auto

subsubsection \<open>Reasoning Infrastructure\<close>

lemma if1_cond_props:
  "if1_cond flabel ex \<Longrightarrow> (\<exists>v1 v2. {v1, v2} \<in> G - ex \<and> (\<exists>r. flabel v1 = Some (r, Even)) \<and> flabel v2 = None \<and> (\<exists>v3. {v2, v3} \<in> M))"
  unfolding if1_cond_def
  .

lemma if1_cond_props':
  "if1_cond flabel ex \<Longrightarrow> (\<exists>v1 v2 v3 r. if1 flabel ex v1 v2 v3 r)"
  unfolding if1_cond_def if1_def by simp

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
  by (smt surj_pair)


lemma if1_cond_props''':
  assumes "if1_cond flabel ex" "(v1, v2, v3, r) = sel_if1 flabel ex"
  shows "if1 flabel ex v1 v2 v3 r"
proof-

  have "case (sel_if1 flabel ex) of (v1,v2,v3,r) \<Rightarrow> if1 flabel ex v1 v2 v3 r"
  proof-
    let ?es = "D \<inter> {(v1,v2)| v1 v2. {v1,v2} \<in> (G - ex) \<and> (\<exists>r. flabel v1 = Some (r, Even)) \<and> flabel v2 = None \<and> v2 \<in> Vs M}"
    have "?es\<noteq>{}"
      using assms 
      apply (clarsimp elim!: if1_cond_props'' simp: sel_if1_def edge_iff_edge_1 if1_def insert_commute split: prod.split)
      using insert_commute
      by blast
    moreover have "finite ?es"
      using Vs_eq_dVs finite_Vs finite_vertices_iff
      by fastforce
    ultimately have "sel_pair ?es \<in> ?es"
      by force
    moreover obtain v1 v2 where "sel_pair ?es = (v1,v2)"
      by (cases "sel_pair ?es") auto
    ultimately have "(Undirected_Set_Graphs.neighbourhood M v2) \<noteq> {}"
      using assms \<open>?es \<noteq> {}\<close> matching_graph.vs_member'
      by (auto elim!: if1_cond_props''
               simp: sel_if1_def edge_iff_edge_1 if1_def Undirected_Set_Graphs.neighbourhood_def 
               split: prod.split)
    moreover have "finite (Undirected_Set_Graphs.neighbourhood M v2)"
      by (meson matching_graph.graph neighbourhood_subset_Vs rev_finite_subset)
    ultimately have "sel (Undirected_Set_Graphs.neighbourhood M v2) \<in> (Undirected_Set_Graphs.neighbourhood M v2)"
      by (auto simp add: sel)
    hence "{v2, sel (Undirected_Set_Graphs.neighbourhood M v2)} \<in> M"
      by auto

    moreover have "\<exists>r. flabel v1 = Some (r, Even)"
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close>
      by auto

    ultimately show ?thesis
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close> \<open>if1_cond flabel ex\<close>
      by(auto simp: sel_if1_def if1_def)
  qed
  thus ?thesis
    using assms(2)
    by auto
qed

lemma if1_cond_props'''':
  assumes "if1_cond flabel ex"
  shows "\<exists>v1 v2 v3 r. (v1, v2, v3, r) = sel_if1 flabel ex \<and> if1 flabel ex v1 v2 v3 r"
proof-
  let ?q = "sel_if1 flabel ex"
  have "(fst ?q, fst (snd ?q), fst (snd (snd ?q)), snd (snd (snd ?q))) = ?q"
    by simp
  then show ?thesis
    using if1_cond_props'''[OF assms]
    by metis
qed

lemma if2_cond_props'':
  assumes "if2_cond flabel"
  obtains v1 v2 r r' where "if2 flabel v1 v2 r r'"
  using assms(1)
  unfolding if2_cond_def if2_def
  by (smt surj_pair)

lemma if2_cond_props''':
  assumes "if2_cond flabel" "(v1, v2, r1, r2) = sel_if2 flabel"
  shows "if2 flabel v1 v2 r1 r2"
proof-

  have "case (sel_if2 flabel) of (v1,v2,r1,r2) \<Rightarrow> if2 flabel v1 v2 r1 r2"
  proof-
    let ?es = "D \<inter> {(v1,v2)| v1 v2. {v1, v2} \<in> G \<and> (\<exists>r1. flabel v1 = Some (r1, Even)) \<and> 
                                   (\<exists>r2. flabel v2 = Some (r2, Even))}"
    have "?es\<noteq>{}"
      using assms 
      by (auto elim!: if2_cond_props'' simp: sel_if2_def edge_iff_edge_1 if2_def insert_commute split: prod.split)
    moreover have "finite ?es"
      using Vs_eq_dVs finite_Vs finite_vertices_iff
      by fastforce
    ultimately have "sel_pair ?es \<in> ?es"
      by force
    moreover obtain v1 v2 where "sel_pair ?es = (v1,v2)"
      by (cases "sel_pair ?es") auto
  

    moreover have "\<exists>r1. flabel v1 = Some (r1, Even)" "\<exists>r2. flabel v2 = Some (r2, Even)"
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close>
      by auto
    ultimately show ?thesis
      using \<open>sel_pair ?es \<in> ?es\<close> \<open>sel_pair ?es = (v1, v2)\<close> \<open>if2_cond flabel\<close>
      by(auto simp: sel_if2_def if2_def)
  qed

  thus ?thesis
    using assms(2)
    by force
qed

lemma if2_cond_props'''':
  assumes "if2_cond flabel"
  shows "\<exists>v1 v2 r r'. (v1, v2, r, r') = sel_if2 flabel \<and> if2 flabel v1 v2 r r'"
proof-
  let ?q = "sel_if2 flabel"
  have "(fst ?q, fst (snd ?q), fst (snd (snd ?q)), snd (snd (snd ?q))) = ?q"
    by simp
  then show ?thesis
    using if2_cond_props'''[OF assms]
    by metis
qed


lemma compute_alt_path_if1:
  assumes "compute_alt_path_dom (ex,par,flabel)" 
    "if1_cond flabel ex"
    "(v1, v2, v3, r) = sel_if1 flabel ex"
    "ex' = insert {v2, v3} (insert {v1, v2} ex)"
    "par' = par(v2 := Some v1, v3 := Some v2)"
    "flabel' = flabel(v2 := Some (r, Odd), v3 := Some (r, Even))"
  shows "local.compute_alt_path ex par flabel = compute_alt_path ex' par' flabel'"
  using assms
  by (auto simp add:  compute_alt_path.psimps[OF assms(1)] Let_def split: if_splits prod.splits)


lemma compute_alt_path_pinduct_2':
  assumes "compute_alt_path_dom (ex, par, flabel)"
    "(\<And>ex par flabel.
    compute_alt_path_dom (ex, par, flabel) \<Longrightarrow>
    (\<And>v1 v2 v3 r ex' par' flabel'.
        if1_cond flabel ex \<Longrightarrow>
        (v1,v2,v3,r) = sel_if1 flabel ex \<Longrightarrow>
        ex' = insert {v2,v3} (insert {v1, v2} ex) \<Longrightarrow>
        par' = par(v2 \<mapsto> v1, v3 \<mapsto> v2) \<Longrightarrow>
        flabel' = flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)) \<Longrightarrow> P ex' par' flabel') \<Longrightarrow>
    P ex par flabel)"
  shows "P ex par flabel"
  apply(rule compute_alt_path.pinduct[OF assms(1)])
  using assms(2)
  by metis

lemma compute_alt_path_pinduct_2:
  "compute_alt_path_dom (ex, par, flabel) \<Longrightarrow> 
(\<And>ex par flabel.
    compute_alt_path_dom (ex, par, flabel) \<Longrightarrow>
    (\<And>v1 v2 v3 r ex' par' flabel'.
        if1_cond flabel ex \<Longrightarrow>
        (v1,v2,v3,r) = sel_if1 flabel ex \<Longrightarrow>
        ex' = insert {v2, v3} (insert {v1, v2} ex) \<Longrightarrow>
        par' = par(v2 \<mapsto> v1, v3 \<mapsto> v2) \<Longrightarrow>
        flabel' = flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)) \<Longrightarrow> P ex' par' flabel') \<Longrightarrow>
    P ex par flabel) \<Longrightarrow> P ex par flabel"
  apply (rule compute_alt_path_pinduct_2')
  by metis+

subsubsection \<open>Termination of the Search Procedure\<close>

definition "compute_alt_path_meas ex = card (G - ex)"

lemma compute_alt_path_dom:
  assumes "finite ex" "ex \<subseteq> G"
  shows "compute_alt_path_dom (ex, par, flabel)"
  using assms
proof(induction "compute_alt_path_meas ex" arbitrary: ex par flabel rule: nat_less_induct)
  case 1
  then have IH: "compute_alt_path_dom (ex', par', flabel')"
    if "compute_alt_path_meas ex' < compute_alt_path_meas ex" "finite ex'" "ex' \<subseteq> G"
    for ex' par' flabel'
    using that
    by simp

  show ?case
  proof (cases "if1_cond flabel ex")
    case True
    {
      fix v1 v2 v3 r
      assume "(v1, v2, v3, r) = sel_if1 flabel ex"
      then have "if1 flabel ex v1 v2 v3 r"
        by(rule if1_cond_props'''[OF True])
      then have  v1v2: "{v1, v2} \<in> G - ex" "{v2, v3} \<in> M"
        by(rule if1_props)+
      then have "{v1, v2} \<in> G" "{v1, v2} \<notin> ex"
        by simp+
      define ex' where "ex' = insert {v1, v2} ex"

      have "compute_alt_path_meas ex' < compute_alt_path_meas ex"
      proof-
        have "card ex < card ex'"
          unfolding ex'_def
          using 1(2) \<open>{v1, v2} \<notin> ex\<close>
          by auto
        moreover have "compute_alt_path_meas ex' = card G - card ex'"
          unfolding compute_alt_path_meas_def ex'_def
          using graph 1(2,3) \<open>{v1,v2} \<in> G\<close>
          by (simp add: card_Diff_subset)
        moreover have "compute_alt_path_meas ex = card G - card ex"
          unfolding compute_alt_path_meas_def
          using graph 1(2,3)
          by (simp add: card_Diff_subset)
        ultimately show ?thesis
          apply simp
          apply(intro diff_less_mono2)
          subgoal .
          subgoal apply(rule psubset_card_mono)
            subgoal using finite_E .
            subgoal apply(rule psubsetI)
              subgoal using 1(3) .
              subgoal using \<open>{v1, v2} \<in> G\<close> \<open>{v1, v2} \<notin> ex\<close>
                by auto
              done
            done
          done
      qed       
      moreover have "finite ex'"
        unfolding ex'_def
        using 1(2)
        by auto
      ultimately have "compute_alt_path_meas (insert e ex') < compute_alt_path_meas ex" for e
        apply(simp add: compute_alt_path_meas_def ex'_def)
        by (metis Diff_insert card_Diff1_le dual_order.strict_trans1 linorder_not_le)
      moreover have "finite (insert e ex')" for e
        by (simp add: \<open>finite ex'\<close>)
      moreover have "{v2, v3} \<in> G"
        using matching(2) \<open>{v2, v3} \<in> M\<close>
        by auto
      then have "(insert {v2, v3} ex') \<subseteq> G"
        unfolding ex'_def
        using \<open>{v1,v2} \<in> G\<close> 1(3)
        by auto
      ultimately have compute_alt_path_dom_ex': "compute_alt_path_dom (insert {v2, v3} ex', par', flabel')" for par' flabel'
        apply(intro IH)
        .
    }
    then show ?thesis
      using compute_alt_path.domintros
      by metis
  next
    case False
    then show ?thesis
      apply(subst compute_alt_path.domintros)
      by blast+
  qed
qed


lemma assumes 
  "compute_alt_path_dom(ex, par, flabel)"
  "Some (p1, p2) = compute_alt_path ex par flabel"
shows "\<exists>v1 par. p1 = parent.follow par v1"
  using assms
  apply(induction rule: compute_alt_path.pinduct)
  by(auto simp add: compute_alt_path.psimps Let_def split: if_splits option.splits prod.splits)

lemma assumes 
  "compute_alt_path_dom(ex, par, flabel)"
  "Some (p1, p2) = compute_alt_path ex par flabel"
shows "\<exists>v2 par. p2 = parent.follow par v2"
  using assms
  apply(induction rule: compute_alt_path.pinduct)
  by(auto simp add: compute_alt_path.psimps Let_def split: if_splits option.splits prod.splits)

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
    using neq(1) no_ances(1)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  then have wf_v2_v1: "wf (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using wf[unfolded parent_spec_def] by blast
  moreover have "{(x, y) |x y. Some x = (par(v2 \<mapsto> v1)) y} = (insert (v1, v2) {(x, y) |x y. Some x = par y})"
    using neq(1) no_par
    by auto
  ultimately show ?g2
    unfolding parent_spec_def
    by simp

  have "(v3, v2) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    using neq(2) no_ances(2)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  moreover have "(v3, v2) \<notin>  {(x, y). (x, v1) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>* \<and> (v2, y) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*}"
    using neq(3) no_ances(2)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  ultimately have "(v3, v2) \<notin> (insert (v1, v2) {(x,y) | x y. (Some x = par y)})\<^sup>*"
    unfolding rtrancl_insert
    by simp
  then have "wf (insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)}))"
    apply(subst wf_insert)
    using wf_v2_v1
    by simp
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
  using assms wf_empty
  by simp

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

  have "v = v2" if "{v, v3} \<in> M" for v
    using matching that \<open>{v2,v3} \<in> M\<close>
    unfolding matching_def2
    apply (clarsimp simp add: doubleton_eq_iff Vs_def)
    by (smt doubleton_eq_iff insertI1)
  moreover have "v = v3" if "{v, v2} \<in> M" for v
    using matching that \<open>{v2,v3} \<in> M\<close>
    unfolding matching_def2
    apply (clarsimp simp add: doubleton_eq_iff Vs_def)
    by (smt doubleton_eq_iff insertI1)
  ultimately show ?thesis
    using invars
    unfolding flabel_invar_def
    apply safe
    subgoal by (smt \<open>\<And>va. {va, v2} \<in> M \<Longrightarrow> va = v3\<close> \<open>\<And>va. {va, v3} \<in> M \<Longrightarrow> va = v2\<close> fun_upd_idem_iff fun_upd_other fun_upd_upd option.distinct(1))
    subgoal by (metis \<open>\<And>v2a v1a. \<lbrakk>\<And>v. {v, v3} \<in> M \<Longrightarrow> v = v2; \<And>v. {v, v2} \<in> M \<Longrightarrow> v = v3; \<forall>v1 v2. {v1, v2} \<in> M \<longrightarrow> (flabel v1 = None) = (flabel v2 = None); {v1a, v2a} \<in> M; (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r2, lab2))) v1a = None\<rbrakk> \<Longrightarrow> (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r2, lab2))) v2a = None\<close> \<open>\<And>va. {va, v2} \<in> M \<Longrightarrow> va = v3\<close> \<open>\<And>va. {va, v3} \<in> M \<Longrightarrow> va = v2\<close> doubleton_eq_iff)
    done
qed

lemma flabel_invar_2_pres:
  assumes invars: "flabel_invar_2 flabel" and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "flabel_invar_2 (flabel(v2 := Some (r, Odd), v3 := Some (r, Even)))"
proof-
  have "{v1,v2} \<in> G - ex" "flabel v1 = Some (r, Even)" "{v2, v3} \<in> M" "flabel v2 = None"
    by (intro if1_props[OF ass])+

  have "v = v2" if "{v, v3} \<in> M" for v
    using matching that \<open>{v2,v3} \<in> M\<close>
    unfolding matching_def2
    apply (clarsimp simp add: doubleton_eq_iff Vs_def)
    by (smt doubleton_eq_iff insertI1)
  moreover have "v = v3" if "{v, v2} \<in> M" for v
    using matching that \<open>{v2,v3} \<in> M\<close>
    unfolding matching_def2
    apply (clarsimp simp add: doubleton_eq_iff Vs_def)
    by (smt doubleton_eq_iff insertI1)
  ultimately show ?thesis
    using invars
    unfolding flabel_invar_2_def
    apply safe
    subgoal 
      by (smt dblton_graph_def Pair_inject doubleton_eq_iff graph in_mono map_upd_Some_unfold 
              matching(2))
    subgoal 
      by (smt Pair_inject insert_commute map_upd_Some_unfold)
    done
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
qed

lemma compute_alt_path_dom_if1:
  assumes "if1 flabel ex v1 v2 v3 r"
    "finite ex" "ex \<subseteq> G"
    "ex' = insert {v2, v3} (insert {v1, v2} ex)"
  shows "compute_alt_path_dom (ex', par', flabel')"
  unfolding assms(4)
  apply(rule compute_alt_path_dom)
  using if1_props[OF assms(1)] assms(2,3) matching(2)
  by auto

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
    "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "alt_labels_invar flabel r (parent.follow par v)"
  shows "alt_path (-M) (parent.follow par v)"
  using assms
proof(induction "(parent.follow par v)" arbitrary: v rule: induct_list012)
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
    apply(intro parent.follow_cons[OF parent.intro[OF assms(1)], where p = "y # zs"])
    by simp
  then have "parent.follow par y = y # zs"
    apply(subst parent.follow_cons_2[OF parent.intro[OF assms(1)], of v y zs])
    using sucsuc(3)
    by simp+
  show ?case
  proof(cases zs)
    case Nil
    then show ?thesis
      using sucsuc(5,6)
      by (simp add: sucsuc(3)[symmetric] Nil alt_list_empty alt_list_step)
  next
    case (Cons z' zs')
    then have "parent.follow par z' = zs"
      using \<open>parent.follow par y = y # zs\<close> parent.follow_cons_2[OF parent.intro[OF assms(1)]]
      by blast
    moreover have "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par z')"
      "alt_labels_invar flabel r (parent.follow par z')"
      using sucsuc(5,6)
      by (simp add: alt_list_step sucsuc(3)[symmetric] \<open>parent.follow par y = y # zs\<close> Cons \<open>parent.follow par z' = zs\<close>)+
    ultimately have "alt_path (- M) (parent.follow par z')"
      apply(intro sucsuc(1) assms(1))
      by simp+
    moreover have "{x, y} \<in> M" "{y, z'} \<notin> M"
      using sucsuc(5,6) 
      by(simp add: sucsuc(3)[symmetric] alt_list_step Cons)+
    ultimately show ?thesis
      using \<open>parent.follow par z' = zs\<close>
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
    by metis
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
  shows "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) \<Longrightarrow> \<forall>v'\<in>set(parent.follow par v). par v' = par' v'" (is "?par' \<Longrightarrow> ?g1")
    "flabel' = (flabel(v2 \<mapsto> a, v3 \<mapsto> b)) \<Longrightarrow> \<forall>v'\<in>set(parent.follow par v). flabel v' = flabel' v'" (is "?flabel' \<Longrightarrow> ?g2")
proof-
  have "parent par"
    using invars(2)
    by (simp add: parent_def)
  moreover have "\<forall>v''. par v'' \<noteq> Some v2"
    by(intro flabel_par_invar_props[OF invars(1)] if1_props[OF ass])
  ultimately have "\<forall>v'\<in>set (parent.follow par v). v' \<noteq> v2"
    apply(intro v2_nin_ancestors neq) .
  then have *: "\<forall>v'\<in>set (parent.follow par v). par v' = (par(v2 \<mapsto> v1)) v'"
    apply(intro ancestors_unaffected_1[where ?v1.0 = v1 and ?v2.0 = v2] neq \<open>parent par\<close>)
    by blast+
  have "parent (par(v2 \<mapsto> v1))"
    unfolding parent_def
    by(intro parent_spec_pres(2)[OF invars(2,3,1) ass] \<open>parent par\<close>[unfolded parent_def])
  moreover  have "\<forall>v''. (par(v2 \<mapsto> v1)) v'' \<noteq> Some v3"
    using flabel_par_invar_props[OF invars(1)] if1_props[OF ass]
    by (metis flabel_invar_def invars(3) map_upd_Some_unfold option.distinct(1))
  ultimately have "\<forall>v'\<in>set (parent.follow (par(v2 \<mapsto> v1)) v). v' \<noteq> v3"
    apply(intro v2_nin_ancestors neq) .
  then have "\<forall>v'\<in>set (parent.follow (par(v2 \<mapsto> v1)) v). (par(v2 \<mapsto> v1)) v' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v'"
    apply(intro ancestors_unaffected_1[where ?par = "(par(v2 \<mapsto> v1))" and ?v1.0 = v2 and ?v2.0 = v3] neq \<open>parent (par(v2 \<mapsto> v1))\<close>)
    by blast+
  moreover have "v3 \<notin> set (parent.follow par v)"
    using parent.nin_ancestors
    by (metis "*" \<open>\<forall>v''. (par(v2 \<mapsto> v1)) v'' \<noteq> Some v3\<close> \<open>parent par\<close> neq(2))
  ultimately show "?par' \<Longrightarrow> ?g1"
    by (simp add: "*")
  have *: "\<forall>v'\<in>set (parent.follow par v). flabel v' = (flabel(v2 \<mapsto> a)) v'"
    apply(intro ancestors_unaffected_1[where ?v1.0 = a and ?v2.0 = v2] neq \<open>parent par\<close> \<open>\<forall>v'\<in>set (parent.follow par v). v' \<noteq> v2\<close>)
    by blast+
  moreover have "\<forall>v'\<in>set (parent.follow (par(v2 \<mapsto> v1)) v). (flabel(v2 \<mapsto> a)) v' = (flabel(v2 \<mapsto> a, v3 \<mapsto> b)) v'"
    apply(intro ancestors_unaffected_1[where ?par = "(par(v2 \<mapsto> v1))" and ?v1.0 = b and ?v2.0 = v3] neq \<open>parent (par(v2 \<mapsto> v1))\<close>
        \<open>\<forall>v'\<in>set (parent.follow (par(v2 \<mapsto> v1)) v). v' \<noteq> v3\<close>)
    by blast+
  ultimately show "?flabel' \<Longrightarrow> ?g2"
    using \<open>v3 \<notin> set (parent.follow par v)\<close>
    by (simp add: "*")
qed

lemma v1_neq_v2_neq_v3: assumes "if1 flabel ex v1 v2 v3 r" shows "v1 \<noteq> v2" "v2 \<noteq> v3"
  using if1_props[OF assms]
  using \<open>{v2, v3} \<in> M\<close> graph matching(2)
  by (fastforce elim: dblton_graphE)+

lemma alt_labels_invar_pres:
  assumes  ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent.follow par v)"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "parent_spec par"
    "flabel_invar flabel" 
    "flabel_par_invar par flabel" and
    inG: "\<exists>lab. flabel' v = Some (r', lab)" and
    flabel': "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)))" and
    par': "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  shows "alt_labels_invar flabel' r' (parent.follow par' v)"
  using assms
proof(induction flabel' r' "parent.follow par' v" arbitrary: v rule: alt_labels_invar.induct)
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
    apply(intro parent.follow_cons[OF **(2), where p = "[]"])
    by simp
  have "par' v = None"
    using parent.follow_None[OF **(2) 2(1)[symmetric]]
    by simp
  then have "par v = None"
    by (auto simp add: par' split: if_splits)
  moreover have "alt_labels_invar flabel r' (parent.follow par v)"
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
          using "2.prems"(8) "2.prems"(2) "2.prems"(7) F2 False by auto
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
  have "{v} \<notin> M" for v
    using matching(2) graph
    by (blast elim: dblton_graphE)
  have "par' v3 = Some v2"
    by (simp add: par')
  moreover have "par' v1' = Some v2'"
    using 3(2)[symmetric] parent.follow_cons_2(2)[OF **(2)] parent.follow_cons[OF **(2)]
    by metis
  ultimately have "v1' = v3 \<longrightarrow> v2' = v2"
    by auto
  moreover  have "v1' = v2 \<Longrightarrow> v2' \<noteq> v3"
    by (metis (no_types, lifting) "**"(2) "3.hyps"(2) \<open>v1' = v\<close> assms(1) invars(4) map_upd_Some_unfold not_Cons_self2 par' parent.follow_cons_2(1) parent.follow_cons_2(2) v1_neq_v3)
  ultimately have "v2' \<noteq> v3"
    by (metis \<open>par' v1' = Some v2'\<close> \<open>{v2, v3} \<in> M\<close> ass flabel_invar_def flabel_par_invar_props(2) fun_upd_apply if1_props(3) invars(4) invars(5) par')
  moreover have "v3 \<noteq> v2"
    using \<open>\<And>v. {v} \<notin> M\<close> \<open>{v2, v3} \<in> M\<close> by auto
  moreover have "\<forall>v'. par v' \<noteq> Some v2"
    using flabel_par_invar_props(2)[OF invars(5) if1_props(3)[OF assms(1)]].
  ultimately consider (c1) "v1' = v3 \<and> v2' = v2" | (c2) "v1' = v2 \<and> v2' = v1" | (c3) "{v1', v2'} \<inter> {v2, v3} = {}"
    using \<open>par' v1' = Some v2'\<close> 
    apply (cases "v1' = v2"; clarsimp)
    by (fastforce simp: par')+
  then show ?case
  proof(cases )
    case c1
    then show ?thesis
      apply(simp add: par' \<open> flabel' = flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even))\<close>)
      by (smt "**"(2) "3.hyps"(1) "3.hyps"(2) "3.prems"(7) "3.prems"(8) Pair_inject \<open>v1' = v\<close>
              \<open>{v2, v3} \<in> M\<close> alt_labels_invar.simps(3) ass insert_commute invars(1) invars(2)
              invars(3) invars(4) invars(5) map_upd_Some_unfold par' parent.follow_cons_2(1))
  next
    have aa: "{v2, vx} \<in> M \<Longrightarrow> vx = v3" for vx
      using doubleton_in_matching[OF matching(1)] \<open>{v2, v3} \<in> M\<close>
      by blast
    case c2
    then show ?thesis
      by (smt "**"(2) "3.hyps"(1) "3.hyps"(2) "3.prems"(7) "3.prems"(8) Pair_inject
              \<open>v1' = v\<close> \<open>v2' \<noteq> v3\<close> \<open>v3 \<noteq> v2\<close> aa alt_labels_invar.simps(3) ass
              compute_alt_path.if1_props(2) compute_alt_path_axioms invars(1) invars(2) invars(3)
              invars(4) invars(5) label.distinct(1) map_upd_Some_unfold par' parent.follow_cons_2(1))
  next
    case c3
    then have " parent.follow par v1' = parent.follow par' v1'"
      apply(intro  ancestors_unaffected(1)[OF 3(3,8,6,7) _ _ par'] follow_cong[OF \<open>parent par\<close> _ _ \<open>parent par'\<close>])
      by (auto simp add: "**"(1) parent.follow_dom)
    then have follow_eq_follow': " parent.follow par v = parent.follow par' v"
      unfolding \<open>v1' = v\<close>
      .
    have "alt_labels_invar flabel r' (parent.follow par v1') = alt_labels_invar flabel' r' (parent.follow par v1')"
      apply(intro alt_labels_invar_cong[OF] ancestors_unaffected(2)[OF 3(3,8,6,7) _ _ 3(10)])
      using c3
      by (auto simp add: "**"(1) parent.follow_dom)
    then have "alt_labels_invar flabel r' (parent.follow par v) = alt_labels_invar flabel' r' (parent.follow par v)"
      unfolding \<open>v1' = v\<close>
      .
    moreover have "alt_labels_invar flabel r' (parent.follow par v1')"
    proof-
      obtain lab where "flabel' v = Some (r', lab)"
        using 3
        by auto
      then have "flabel v = Some (r', lab)"
        using c3 \<open>v1' = v\<close>
        by (auto simp add: 3(10) split: if_splits)
      then show ?thesis
        apply(intro 3(4))
        using \<open>v1' = v\<close>
        by simp
    qed
    ultimately show ?thesis
      unfolding \<open>v1' = v\<close>
      by (simp add: follow_eq_follow')
  qed
qed

lemma alt_list_pres:
  assumes  ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "parent_spec par"
    "flabel_invar flabel" 
    "flabel_par_invar par flabel" and
    inG: "flabel' v = Some (r', Even)" and
    flabel': "flabel' = (flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even)))" and
    par': "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  shows "alt_list (\<lambda>v. flabel' v = Some (r', Even)) (\<lambda>v. flabel' v = Some (r', Odd)) (parent.follow par' v)"
  using assms
proof(induction "(parent.follow par' v)" arbitrary: v rule: induct_list012)
  case nil
  then show ?case
    by (simp add: alt_list_empty)
next
  case (single x)
  then show ?case
    by (metis (mono_tags, lifting) alt_list.simps compute_alt_path.parent_spec_pres(1) compute_alt_path_axioms par' parent.follow_cons parent.intro)
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
  have "{v} \<notin> M" for v
    using matching(2) graph
    by (blast elim: dblton_graphE)
  have "par' v3 = Some v2"
    by (simp add: par')
  moreover have "par' x = Some y"
    using sucsuc(3)[symmetric] parent.follow_cons_2(2)[OF **(2)] parent.follow_cons[OF **(2)]
    by metis
  ultimately have "x = v3 \<longrightarrow> y = v2"
    by auto
  moreover  have "x = v2 \<Longrightarrow> y \<noteq> v3"
    by (metis (no_types, lifting) "**"(2) "sucsuc.hyps"(3) \<open>x = v\<close> assms(1) assms(2) invars(3) map_upd_Some_unfold not_Cons_self2 par' parent.follow_cons_2(1) parent.follow_cons_2(2) v1_neq_v3)
  ultimately have "y \<noteq> v3"
    by (metis \<open>par' x = Some y\<close> \<open>{v2, v3} \<in> M\<close> ass flabel_invar_def flabel_par_invar_props(2) fun_upd_other if1_props(3) invars(3) invars(4) par')
  moreover have "v3 \<noteq> v2"
    using \<open>\<And>v. {v} \<notin> M\<close> \<open>{v2, v3} \<in> M\<close> by auto
  moreover have "\<forall>v'. par v' \<noteq> Some v2"
    using flabel_par_invar_props(2)[OF invars(4) if1_props(3)[OF assms(1)]] .
  ultimately consider (c1) "x = v3 \<and> y = v2" | (c2) "x = v2 \<and> y = v1" | (c3) "{x, y} \<inter> {v2, v3} = {}"
    using \<open>par' x = Some y\<close> 
    apply (cases "x = v2"; clarsimp)
    by (fastforce simp: par')+
  then show ?case
  proof cases
    case c1
    then show ?thesis
      apply(cases zs)
      subgoal by (metis "**"(2) "sucsuc.hyps"(3) \<open>x = v\<close> fun_upd_def option.simps(3) par' parent.follow_None parent.follow_cons_2(1))
      subgoal by (smt (z3) "**"(2) Pair_inject \<open>x = v\<close> alt_list_step ass compute_alt_path.if1_props(2) compute_alt_path_axioms flabel' map_upd_Some_unfold not_Cons_self2 par' parent.follow_cons_2(1) parent.follow_cons_2(2) sucsuc.hyps(1) sucsuc.hyps(3) sucsuc.prems(2) sucsuc.prems(3) sucsuc.prems(4) sucsuc.prems(5) sucsuc.prems(6))
      done
  next
    case c2
    then show ?thesis
      using "sucsuc.prems"(6) \<open>v3 \<noteq> v2\<close> \<open>x = v\<close> flabel' by auto
  next
    case c3
    case c3
    then have " parent.follow par x = parent.follow par' x"
      apply(intro  ancestors_unaffected(1)[OF sucsuc(4,8,6,7) _ _ par'] follow_cong[OF \<open>parent par\<close> _ _ \<open>parent par'\<close>])
      by (auto simp add: "**"(1) parent.follow_dom)
    then have follow_eq_follow': " parent.follow par v = parent.follow par' v"
      unfolding \<open>x = v\<close>
      .
    have "\<forall>v'\<in>set (parent.follow par x). flabel v' = flabel' v'"
      apply(rule ancestors_unaffected(2)[OF sucsuc(4,8,6,7) _ _ flabel'])
      using c3 
      by (auto simp add: "**"(1) parent.follow_dom)
    then have "\<forall>v'\<in>set (parent.follow par v). flabel v' = flabel' v'"
      unfolding \<open>x = v\<close> .
    then have "alt_list (\<lambda>v. flabel' v = Some (r', Even)) (\<lambda>v. flabel' v = Some (r', Odd)) (parent.follow par v) =
           alt_list (\<lambda>v. flabel v = Some (r', Even)) (\<lambda>v. flabel v = Some (r', Odd)) (parent.follow par v)"
      apply(intro alt_list_cong_eq[OF] )
      by simp+
    moreover have "alt_list (\<lambda>v. flabel v = Some (r', Even)) (\<lambda>v. flabel v = Some (r', Odd)) (parent.follow par x)"
    proof-
      have "flabel' v = Some (r', Even)"
        using sucsuc
        by auto
      then have "flabel v = Some (r', Even)"
        using c3 \<open>x = v\<close>
        by (auto simp add: sucsuc(10) split: if_splits)
      then show ?thesis
        apply(intro sucsuc(5))
        using \<open>x = v\<close>
        by simp
    qed
    ultimately show ?thesis
      unfolding \<open>x = v\<close>
      by (simp add: follow_eq_follow')
  qed
qed

(*Done: Invar 6*)

definition "last_not_matched_invar par flabel =
   (\<forall>v. (flabel v \<noteq> None \<longrightarrow> (last (parent.follow par v) \<notin> Vs M)))"

end

context parent
begin

lemma follow_cons_3: "\<exists>l. follow v = v # l"
  by (metis follow_cons follow_nempty list.exhaust)

lemma follow_cons_3': obtains l where "follow v = v # l"
  by (metis follow_cons follow_nempty list.exhaust)

lemma follow_cons_4: "parent v = Some v' \<Longrightarrow> follow v = v # (follow v')"
  using follow_psimps
  by auto

lemma follow_pinduct:
  "(\<And>v. (\<And>x2. parent v = Some x2 \<Longrightarrow> P x2) \<Longrightarrow> P v) \<Longrightarrow> P a"
  by (metis follow.pinduct[OF follow_dom])

end

lemma last_follow_eq:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))"  and 
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v" "v' \<noteq> v"
  shows "last (parent.follow (par (v \<mapsto> v'')) v') = last (parent.follow par v')"
  using assms 
proof(induction v' rule: parent.follow_pinduct[OF parent.intro[OF invar(1)]])
  case (1 v')
  then have "parent par" "parent (par (v \<mapsto> v''))"
    unfolding parent_def
    by(intro 1)+
  then have "parent.follow_dom (par (v \<mapsto> v'')) v'"
    by (simp add: parent.follow_dom)
  note follow_simps [simp] = parent.follow.psimps[OF \<open>parent (par(v \<mapsto> v''))\<close> parent.follow_dom[OF \<open>parent (par(v \<mapsto> v''))\<close>], of v']
    parent.follow.psimps[OF \<open>parent par\<close> parent.follow_dom[OF \<open>parent par\<close>], of v']
  have *: "(par (v \<mapsto> v'')) v' = par v'"
    using 1
    by (auto split: if_splits)
  show ?case
  proof(cases "par v'")
    case None
    then show ?thesis
      apply (simp only: follow_simps * split: if_splits option.splits)
      by simp
  next
    case (Some a)
    then have "(par(v \<mapsto> v'')) v' = Some a"
      unfolding "*"
      .
    have "last (parent.follow (par(v \<mapsto> v'')) a) = last (parent.follow par a)"
      apply(intro 1)
      using Some 1(4)
      by (auto simp add: \<open>parent par\<close> parent.follow_dom)
    moreover have "last (parent.follow (par(v \<mapsto> v'')) v') = last (parent.follow (par(v \<mapsto> v'')) a)"
      unfolding parent.follow_cons_4[OF \<open>parent (par(v \<mapsto> v''))\<close> \<open>(par(v \<mapsto> v'')) v' = Some a\<close>]
      using last_ConsR[OF parent.follow_nempty[OF \<open>parent (par(v \<mapsto> v''))\<close>]]
      .
    moreover have "last (parent.follow par v') = last (parent.follow par a)"
      unfolding parent.follow_cons_4[OF \<open>parent par\<close> Some]
      using last_ConsR[OF parent.follow_nempty[OF \<open>parent par\<close>]]
      .
    ultimately show ?thesis
      by metis
  qed
qed

lemma follow_eq:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))" and
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v"
  shows "parent.follow par v'' = parent.follow (par(v \<mapsto> v'')) v''"
  apply(rule follow_cong )
  subgoal using parent.intro[OF invar(1)].
  subgoal using parent.follow_dom[OF parent.intro[OF invar(1)]]. 
  subgoal apply(rule no_children_not_in_follow[where ?v2.0 = v and ?v1.0 = v''])
    subgoal using parent.intro[OF invar(1)] .
    subgoal using neq by auto
    subgoal using neq(2) by simp
    subgoal by blast
    done
  subgoal using parent.intro[OF invar(2)] .
  done

context compute_alt_path
begin

lemma compute_alt_path_follow_eq:
  assumes ass: "if1 flabel ex v1 v2 v3 r" and
    invars: "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel" and
    neq: "v2 \<noteq> v" "v3 \<noteq> v"
  shows "parent.follow par v = parent.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v"
    (*Can use follow_eq to prove it?*)
  apply(intro follow_cong)
  subgoal using parent.intro[OF invars(1)] .
  subgoal using parent.follow_dom[OF parent.intro[OF invars(1)]] .
  subgoal apply(intro ancestors_unaffected(1)[OF ass invars(3,1,2)])
    using neq by auto
  subgoal using parent.intro[OF parent_spec_pres(1)[OF invars ass]] .
  done

end

lemma last_follow_eq_2:
  assumes invar: "parent_spec par" "parent_spec (par (v \<mapsto> v''))" and
    neq: "\<forall>v'. par v' \<noteq> Some v" "v'' \<noteq> v"
  shows "last (parent.follow (par (v \<mapsto> v'')) v) = last (parent.follow par v'')"
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
  shows  "last (parent.follow (par(v2 \<mapsto> v1)) v2) = last (parent.follow par v1)" (is ?g1)
    "\<And>v. v \<noteq> v2 \<Longrightarrow> last (parent.follow (par(v2 \<mapsto> v1)) v) = last (parent.follow par v)" (is "\<And>v. ?p v \<Longrightarrow> ?g2 v") 
    "last (parent.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v3) = last (parent.follow (par(v2 \<mapsto> v1)) v2)" (is ?g3)
    "\<And>v. v \<noteq> v3 \<Longrightarrow> last (parent.follow (par(v2 \<mapsto> v1, v3 \<mapsto> v2)) v) = last (parent.follow (par(v2 \<mapsto> v1)) v)" (is "\<And>v. ?p2 v \<Longrightarrow> ?g4 v")
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
  have "parent_spec (par(v2 \<mapsto> v1))" "parent_spec (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
    by (intro parent_spec_pres[OF invars(1-3) ass])+
  moreover have "v2 \<noteq> v3"
    by(intro v1_neq_v2_neq_v3[OF ass])
  moreover have  "\<forall>v'. (par(v2 \<mapsto> v1)) v' \<noteq> Some v3"
    using \<open>v2 \<noteq> v3\<close>
    by (metis ass compute_alt_path.if1_props(3) compute_alt_path.if1_props(4) compute_alt_path_axioms flabel_invar_def flabel_par_invar_props(2) fun_upd_apply invars(2) invars(3) option.inject v1_neq_v3)
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
  {
    fix v2 v1 v3 r lab and par :: "'a \<Rightarrow> 'a option" and flabel::"'a \<Rightarrow> ('b \<times> label) option"
    assume *: "last (parent.follow (par(v2 \<mapsto> v1)) v2) = last (parent.follow par v1)"
      "last (parent.follow (par(v2 \<mapsto> v1)) v) = last (parent.follow par v)" if  "v \<noteq> v2" for v
    assume invar: "last_not_matched_invar par flabel" "flabel_par_invar par flabel"  and
      ass: "flabel v1 \<noteq> None"
    have "last (parent.follow (par(v2 \<mapsto> v1)) v) \<notin> Vs M" if "(flabel(v2 \<mapsto> (r, lab))) v \<noteq> None" for v
    proof(cases "v = v2")
      case True
      have "last (parent.follow par v1) \<notin> Vs M"
        using invar(1) ass
        by (auto simp: last_not_matched_invar_def)
      then have "last (parent.follow (par(v2 \<mapsto> v1)) v1) \<notin> Vs M"
        by (metis "*"(1) "*"(2))
      then have "last (parent.follow (par(v2 \<mapsto> v1)) v2) \<notin> Vs M"
        by (metis "*"(1) "*"(2))
      then show ?thesis
        using True by simp
    next
      case False
      then show ?thesis
        using *(2)
        using invar that
        by (fastforce simp: last_not_matched_invar_def flabel_par_invar_def)
    qed
    then have "last_not_matched_invar (par(v2 \<mapsto> v1)) (flabel(v2 := Some (r, lab)))"
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
  } note gen = this
  have "flabel v1 \<noteq> None" using if1_props(2)[OF ass]
    by auto
  then show g1: ?g1
    by(intro gen[OF compute_alt_path_last_eq(1,2)[OF ass invars(1-3)] invars(4,3)])
  have "(flabel(v2 \<mapsto> (r, lab))) v2 \<noteq> None"
    by auto
  moreover have "flabel_par_invar (par(v2 \<mapsto> v1)) (flabel(v2 \<mapsto> (r, lab)))"
    using flabel_par_invar_pres(2)[OF invars(3) ass] .
  ultimately show ?g2
    apply(intro gen[OF compute_alt_path_last_eq(3,4)[OF ass invars(1-3)] g1]) 
    by auto
qed

lemma last_not_matched_invar_props: 
  assumes "last_not_matched_invar par flabel"
  shows  "(flabel v = Some a \<Longrightarrow> last (parent.follow par v) \<notin> Vs M)"
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
  {
    fix v1' v2'
    have "flabel_invar (flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab')))"
      using flabel_invar_pres[OF invars(1) ass]
      .
    assume ass2: "{v1', v2'} \<in> M" "(flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) v1' \<noteq> None"
    moreover have "(flabel(v2 \<mapsto> (r, lab), v3 \<mapsto> (r', lab'))) v2' \<noteq> None"
      apply(rule flabel_invar_props[OF flabel_invar_pres[OF invars(1) ass], of v1'])
      using ass2
      by auto
    moreover have "{v1, v2} \<notin> M"
      using matching_examined_invar_props[OF invars(2)]
        if1_props[OF ass]
      by fastforce
    moreover have "v1' \<noteq> v2'"
      using matching(2) graph \<open>{v1', v2'} \<in> M\<close>
      apply clarsimp
      by (blast elim: dblton_graphE)
    moreover have "v1 \<noteq> v2"
      using graph if1_props(1)[OF ass(1)]
      apply clarsimp
      by  (blast elim: dblton_graphE)
    moreover have "v1 \<noteq> v3"
      using v1_neq_v3[OF ass invars(1)].
    ultimately have "{v1', v2'} \<in> insert {v2, v3} (insert {v1, v2} ex)"
      apply (clarsimp split: if_splits simp add: matching_examined_invar_props[OF invars(2)] insert_commute doubleton_eq_iff)
      subgoal using matching_examined_invar_props[OF invars(2)] insert_commute by metis
      done
  }
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
      apply(intro sucsuc(1))
      by simp+
    then show ?thesis
      by simp
  qed
qed

context compute_alt_path
begin

(*Done: Invar 7*)

definition "last_even_invar par flabel = (\<forall>v r lab. flabel v = Some(r, lab) \<longrightarrow> flabel (last (parent.follow par v)) = Some (r, Even))"

lemma last_even_invar_props:
  "last_even_invar par flabel \<Longrightarrow> flabel v = Some (r, lab) \<Longrightarrow> flabel (last (parent.follow par v)) = Some (r, Even)"
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
  note follow_simps [simp] = parent.follow.psimps[OF \<open>parent par'\<close> parent.follow_dom[OF \<open>parent par'\<close>]]
  {
    fix v r lab
    assume "v2 \<noteq> v" "v3 \<noteq> v"
      "flabel' v = Some (r, lab)" 
    then have "flabel v = Some (r, lab)"
      by (auto simp: flabel'_def)
    then have i: "flabel (last (parent.follow par v)) = Some (r, Even)"
      apply (intro last_even_invar_props[OF invars(4), of _ r lab])
      .
    have "flabel (last (parent.follow par v)) = Some (r, Even)"
      using i
      by simp
    moreover have "\<forall>v'\<in>set (parent.follow par v). v' \<noteq> v2"
      by(intro v2_nin_ancestors[OF parent.intro[OF invars(1)] flabel_par_invar_props(2)[OF invars(3)]] if1_props[OF ass] \<open>v2 \<noteq> v\<close>)
    moreover have "\<forall>v'\<in>set (parent.follow par v). v' \<noteq> v3"
      by(intro v2_nin_ancestors[OF parent.intro[OF invars(1)] flabel_par_invar_props(2)[OF invars(3)]] flabel_invar_props(1)[OF invars(2) if1_props(4,3)[OF ass]] \<open>v3 \<noteq> v\<close> )
    moreover have "(last (parent.follow par v)) \<in> set (parent.follow par v)"
      using parent.follow_nempty[OF parent.intro[OF invars(1)]]
      by simp
    ultimately have "flabel' (last (parent.follow par v)) = Some (r, Even)"
      unfolding flabel'_def
      by simp
    moreover have "parent.follow par v =  parent.follow par' v"
      unfolding par'_def
      using compute_alt_path_follow_eq[OF ass invars(1,2,3) \<open>v2 \<noteq> v\<close> \<open>v3 \<noteq> v\<close>]
      .
    ultimately have "flabel' (last (parent.follow par' v)) = Some (r, Even)"
      by simp
  }
  moreover have *: "(last (parent.follow par' v2)) = (last (parent.follow par' v1))"
  proof-
    have "par' v2 = Some v1"
      unfolding par'_def
      using v1_neq_v2_neq_v3(2)[OF ass]
      by simp
    then show ?thesis
      using parent.follow_nempty[OF \<open>parent par'\<close>]
      by (simp split: if_splits)
  qed
  moreover have "(last (parent.follow par' v3)) = (last (parent.follow par' v1))"
  proof-
    have "par' v3 = Some v2"
      unfolding par'_def
      using if1_props[OF ass]
      by simp
    then show ?thesis
      apply (subst *[symmetric])
      using \<open>parent par'\<close> parent.follow_nempty by fastforce
  qed
  moreover have "v1 \<noteq> v2" "v1 \<noteq> v3"
    by(rule v1_neq_v2_neq_v3[OF ass] v1_neq_v3[OF ass invars(2)])+
  ultimately have "flabel' (last (parent.follow par' v)) = Some (r, Even)" if "flabel' v = Some (r, lab)" for v r lab
    using that
    by (smt ass flabel'_def if1_props(2) map_upd_Some_unfold prod.inject)
  then show ?thesis
    unfolding flabel'_def par'_def last_even_invar_def
    by simp
qed

lemma last_even_invar_imp:
  assumes invars: 
    "parent_spec par"
    "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "last_even_invar par flabel" and
    "flabel v = Some (r, Even)"
  shows "odd (length (parent.follow par v))"
proof-
  have "flabel (last (parent.follow par v)) = Some (r, Even)"
    using assms
    unfolding last_even_invar_def
    by simp
  moreover have "parent.follow par v \<noteq> []"
    by (metis (mono_tags, lifting) invars(1)  parent.follow_nempty parent.intro)
  moreover have "flabel (hd (parent.follow par v)) = Some (r, Even)"
    by (metis (mono_tags, lifting) alt_list.simps invars(2) list.sel(1) calculation(2))
  ultimately show ?thesis
    by (intro alt_list_length_odd[OF invars(2)])
qed

(*Done: Invar 9*)

definition "distinct_invar par = (\<forall>v. distinct (parent.follow par v))"

lemma distinct_invar_props: "distinct_invar par \<Longrightarrow> distinct (parent.follow par v)"
  unfolding distinct_invar_def
  by simp

lemma distinct_invar_pres:
  assumes invars: 
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "distinct_invar par"
    and
    ass: "if1 flabel ex v1 v2 v3 r"
  shows "distinct_invar (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
proof-

  define par' where "par' = (par(v2 \<mapsto> v1, v3 \<mapsto> v2))"
  have invar': "parent_spec par'"
    unfolding par'_def
    by (meson assms(6) assms(5) parent_spec_pres(1) invars(1) invars(2) invars(3))
  note follow_simps [simp] = parent.follow.psimps[OF parent.intro[OF invar'] parent.follow_dom[OF parent.intro[OF invar']], of v2]
    parent.follow.psimps[OF parent.intro[OF invar'] parent.follow_dom[OF parent.intro[OF invar']], of v3]

  have "v2 \<noteq> v3"
    using v1_neq_v2_neq_v3(2)[OF ass].
  then have pars: "par' v2 = Some v1" "par' v3 = Some v2"
    unfolding par'_def
    by simp+
  then have rw: "(parent.follow par' v3) = v3 # v2 # (parent.follow par' v1)"
    by simp

  have "flabel v1 = Some (r, Even)"
    using if1_props(2)[OF ass(1)].
  then have *: "alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v1)"
    using invars(4)
    by blast
  have "flabel v = Some (r, Even) \<or> flabel v = Some (r, Odd)" if "v \<in> set (parent.follow par v1)" for v
    by(intro alt_list_or[OF *] that)
  then have ances_some: "flabel v \<noteq> None" if "v \<in> set (parent.follow par v1)" for v
    using that
    by fastforce
  moreover have "flabel v2 = None"
    using if1_props(3)[OF ass]
    by simp
  moreover have "flabel v3 = None"
    by (intro flabel_invar_props[OF invars(2) if1_props(4)[OF ass]] \<open>flabel v2 = None\<close>)
  ultimately have "v3 \<notin> set (parent.follow par v1)" "v2 \<notin> set (parent.follow par v1)"
    by fastforce+


  have rw_v: "(parent.follow par v) = (parent.follow par' v)" if "v3 \<noteq> v" "v2 \<noteq> v" for v
    unfolding par'_def
    by(intro compute_alt_path_follow_eq[OF ass invars(1-3)] if1_props(3)[OF ass(1)] that)
  then have rw_v1: "(parent.follow par v1) = (parent.follow par' v1)"
    using \<open>flabel v1 = Some (r, Even)\<close> \<open>flabel v2 = None\<close> \<open>flabel v3 = None\<close> by force
  {
    fix v
    consider (c1) "v = v2" | (c2) "v = v3" | (c3) "v \<notin> {v2, v3}"
      by auto
    then have "distinct (parent.follow par' v)"
    proof(cases)
      case c1
      moreover have "distinct (parent.follow par' v1)"
        using distinct_invar_props[OF invars(5), of v1] rw_v1
        by simp
      ultimately show ?thesis
        using c1 \<open>v2 \<notin> set (parent.follow par v1)\<close>
        by(simp add: pars rw_v1)
    next
      case c2
      moreover have "flabel v3 = None"
        by(intro flabel_invar_props[OF invars(2) if1_props(4)[OF ass]] if1_props(3)[OF ass])
      ultimately have "flabel v = None"
        by simp
      then have "v \<notin> set (parent.follow par v1)"
        using ances_some
        by fastforce
      moreover have "distinct (parent.follow par' v1)"
        using distinct_invar_props[OF invars(5), of v1] rw_v1
        by simp
      ultimately show ?thesis
        using c2 \<open>v2 \<notin> set (parent.follow par v1)\<close> \<open>v3 \<notin> set (parent.follow par v1)\<close>
          \<open>v2 \<noteq> v3\<close>
        by(simp add: pars rw_v1)
    next
      case c3
      then have *: "(parent.follow par v) = (parent.follow par' v)"
        using rw_v
        by auto
      show ?thesis
        using distinct_invar_props[OF invars(5), of v]
        unfolding *[symmetric] .
    qed
  }
  then show ?thesis
    unfolding distinct_invar_def par'_def
    by(intro allI)
qed

(*Done: Invar 9*)

definition "path_invar par = (\<forall>v \<in> Vs G. path G (parent.follow par v))"

lemma path_invar_props: "path_invar par \<Longrightarrow> v \<in> Vs G \<Longrightarrow> path G (parent.follow par v)"
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
    by (meson ass parent_spec_pres(1) invars(1) invars(2) invars(3))
  note follow_simps [simp] = parent.follow.psimps[OF parent.intro[OF invar'] parent.follow_dom[OF parent.intro[OF invar']]]

  have "v2 \<noteq> v3"
    using v1_neq_v2_neq_v3(2)[OF ass].
  then have pars: "par' v2 = Some v1" "par' v3 = Some v2"
    unfolding par'_def
    by simp+
  then have rw: "(parent.follow par' v3) = v3 # v2 # (parent.follow par' v1)"
    by simp

  have "{v3, v2} \<in> G"
    by (metis ass compute_alt_path.if1_def matching(2) compute_alt_path_axioms in_mono insert_commute)
  have "{v2, v1} \<in> G"
    by (metis Diff_iff ass if1_def insert_commute)
  then have "v1 \<in> Vs G"
    unfolding Vs_def
    by auto

  have rw_v: "(parent.follow par v) = (parent.follow par' v)" if "v3 \<noteq> v" "v2 \<noteq> v" for v
    unfolding par'_def
    by(intro compute_alt_path_follow_eq[OF ass invars(1-3)] if1_props(3)[OF ass(1)] if1_props(1)[OF ass] that)
  then have rw_v1: "(parent.follow par v1) = (parent.follow par' v1)"
    using ass invars(2) v1_neq_v2_neq_v3(1) v1_neq_v3 by fastforce
  {
    fix v
    assume "v \<in> Vs G"
    consider (c1) "v = v2" | (c2) "v = v3" | (c3) "v \<notin> {v2, v3}"
      by auto
    then have "path G (parent.follow par' v)"
    proof(cases)
      case c1
      moreover have "path G (parent.follow par' v1)"
        using path_invar_props[OF invars(4), of v1] rw_v1 \<open>v1 \<in> Vs G\<close>
        by simp
      ultimately show ?thesis
        using c1 \<open>{v2, v1} \<in> G\<close>
        apply(simp add: pars rw_v1)
        apply(split option.splits)+
        by simp+
    next
      case c2
      moreover have "path G (parent.follow par' v1)"
        using path_invar_props[OF invars(4), of v1] rw_v1 \<open>v1 \<in> Vs G\<close>
        by simp
      ultimately show ?thesis
        using c2 \<open>{v2, v1} \<in> G\<close> \<open>{v3, v2} \<in> G\<close>
        apply(simp add: pars rw_v1)
        apply(split option.splits)+
        by simp+
    next
      case c3
      then have *: "(parent.follow par v) = (parent.follow par' v)"
        using rw_v
        by auto
      show ?thesis
        using path_invar_props[OF invars(4), of v] \<open>v \<in> Vs G\<close>
        unfolding *[symmetric] .
    qed
  }
  then show ?thesis
    unfolding path_invar_def par'_def
    by(intro ballI)
qed

lemma compute_alt_path_from_tree_1:
  assumes invars: 
    "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent.follow par v)"
    (*Done *)
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
    "parent_spec par"
    "flabel_invar flabel"
    "flabel_par_invar par flabel"
    "last_not_matched_invar par flabel"
    "matching_examined_invar flabel ex"
    "last_even_invar par flabel"
    "distinct_invar par"
    "path_invar par"
    "flabel_invar_2 flabel" and
    ret:    
    "compute_alt_path ex par flabel = Some (p1, p2)" and
    init:       
    "finite ex" "ex \<subseteq> G"
  shows "last p1 \<notin> Vs M \<and>
       last p2 \<notin> Vs M \<and>
       hd p1 \<noteq> hd p2 \<and>
       odd (length p1) \<and>
       odd (length p2) \<and>
       distinct p1 \<and>
       distinct p2 \<and>
       path G p1 \<and>
       path G p2 \<and>
       {hd p1, hd p2} \<in> G \<and>
       (\<forall>x pref1 post1 pref2 post2. p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow> post1 = post2) \<and>
       alt_path M (hd p1 # p2) \<and> 
       alt_path M (hd p2 # p1)" 
  using assms
proof(induction ex par flabel arbitrary: p1 p2 rule: compute_alt_path_pinduct_2)
  case 1
  then show ?case
    by(intro compute_alt_path_dom init)
next
  case (2 ex par flabel)
  show ?case
  proof(cases "if1_cond flabel ex")
    case True
    obtain v1 v2 v3 r where sel: "(v1,v2,v3,r) = sel_if1 flabel ex" "if1 flabel ex v1 v2 v3 r"
      using if1_cond_props''''[OF True] by metis
    let ?par' = "par(v2 \<mapsto> v1, v3 \<mapsto> v2)"
    let ?flabel' = "flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even))"
    let ?ex' = "insert {v2, v3} (insert {v1, v2} ex)"
    have "compute_alt_path ex par flabel = compute_alt_path ?ex' ?par' ?flabel'"
      by(auto intro: compute_alt_path_if1[OF 2(1) True sel(1)])
    then have "compute_alt_path ?ex' ?par' ?flabel' = Some (p1, p2)"
      using 2
      by simp
    moreover have "parent_spec ?par'"
      using parent_spec_pres(1)[OF 2(5-7) sel(2)].
    moreover have "flabel_invar (?flabel')"
      using flabel_invar_pres[OF 2(6) sel(2), of Odd _ Even].
    moreover have "flabel_par_invar (?par') (?flabel')"
      using flabel_par_invar_pres(1)[OF 2(7) sel(2)].
    moreover have "compute_alt_path_dom (?ex', ?par', ?flabel')"
      apply(intro compute_alt_path_dom_if1[OF sel(2)])
      using 2(16,15)
      by auto
    moreover have "finite (insert {v1, v2} ex)"
      using 2(15)
      by auto
    moreover have "?ex' \<subseteq> G"
      by (meson "2.prems"(14) DiffD1 compute_alt_path.if1_props(1) compute_alt_path_axioms if1_props(4) insert_subsetI matching(2) sel(2) subsetD)
    moreover have "alt_labels_invar ?flabel' r' (parent.follow ?par' v)" if "?flabel' v = Some (r', lab)" for v r' lab
      apply(intro alt_labels_invar_pres[OF sel(2) 2(3,4,5,6,7)])
      using that
      by auto
    moreover have "alt_list (\<lambda>v. ?flabel' v = Some (r', Even)) (\<lambda>v. ?flabel' v = Some (r', Odd)) (parent.follow ?par' v)" if "?flabel' v = Some (r', Even)" for v r'
      using alt_list_pres[OF sel(2) 2(4,5,6,7)] 2(5,6,7) that
      by auto
    moreover have "finite ?ex'"
      using 2(15)
      by auto
    moreover have "last_not_matched_invar ?par' ?flabel'"
      by(intro last_not_matched_invar_pres(2)[OF sel(2) 2(5,6,7,8)])
    moreover have "matching_examined_invar ?flabel' ?ex'"
      using matching_examined_invar_pres[OF 2(6,9) sel(2)]
      .
    moreover have "last_even_invar ?par' ?flabel'"
      using last_even_invar_pres[OF 2(5,6,7,10) sel(2)]
      .
    moreover have "distinct_invar ?par' "
      using distinct_invar_pres[OF 2(5,6,7,4,11) sel(2)]
      .
    moreover have "path_invar ?par'"
      using path_invar_pres[OF 2(5,6,7,12) sel(2)]
      .
    moreover have "flabel_invar_2 ?flabel'"
      by(intro flabel_invar_2_pres[OF _ sel(2)] 2)
    ultimately show ?thesis
      using sel
      apply(intro 2(2)[OF True, of v1 v2 v3 r])
      by (simp; blast)+
  next
    case False
    then have if2_holds: "if2_cond flabel"
      using 2(14)
      by(auto simp add: compute_alt_path.psimps[OF 2(1)] split: if_splits prod.splits)
    then obtain v1 v2 r s where v1v2r: "(v1,v2,r,s) = sel_if2 flabel" "if2 flabel v1 v2 r s"
      using if2_cond_props''''
      by force
    then have s: "flabel v2 = Some (s, Even)" "p1 = parent.follow par v1" "p2 = parent.follow par v2"
                 "flabel v1 = Some (r, Even)" "{v1, v2} \<in> G"
      unfolding if2_def
      using False 2(14) v1v2r(1)
      by (auto simp add: compute_alt_path.psimps[OF 2(1)] Let_def split: if_splits prod.splits)
    moreover have "v1 = hd p1" "v2 = hd p2"
      by (metis "2.prems"(3,4) calculation(3,2) list.sel(1) parent.follow_cons_3 parent.intro)+
    moreover have "\<forall>x pref1 post1 pref2 post2. p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow> post1 = post2"
      using "2.prems"(3) parent.from_tree parent.intro s(2) s(3) by fastforce
    moreover have "(\<forall>v. flabel v \<noteq> None \<longrightarrow> last (parent.follow par v) \<notin> Vs M)"
      using 2(8)
      unfolding last_not_matched_invar_def .
    then have "last (parent.follow par v1) \<notin> Vs M" "last (parent.follow par v2) \<notin> Vs M"
      using s by auto
    moreover have "{v1, v2} \<notin> M"
      by(intro flabel_invar_2_props[OF 2(13), where ?r = r and ?s = s] s)
    then have "alt_path M (v1 # parent.follow par v2)"
      apply(intro nin_M_alt_path)
      subgoal apply(subst \<open>p2 = parent.follow par v2\<close>[symmetric])
        by(simp add: \<open>v1 = hd p1\<close> \<open>v2 = hd p2\<close>)
      subgoal using alt_invars_then_alt_path[where ?r = s, OF 2(5,4) 2(3)[OF \<open>flabel v2 = Some (s, Even)\<close>] ]
        subgoal using \<open>flabel v2 = Some (s, Even)\<close> .
        done
      done
    moreover have "alt_path M (v2 # parent.follow par v1)"
      apply(intro nin_M_alt_path)
      subgoal using \<open>{v1, v2} \<notin> M\<close>
        apply(subst \<open>p1 = parent.follow par v1\<close>[symmetric])
        by(simp add: \<open>v1 = hd p1\<close> \<open>v2 = hd p2\<close> insert_commute)
      subgoal using alt_invars_then_alt_path[where ?r = r, OF 2(5,4) 2(3)[OF \<open>flabel v1 = Some (r, Even)\<close>] ]
        subgoal using \<open>flabel v1 = Some (r, Even)\<close> .
        done
      done
    moreover have "v1 \<noteq> v2"
      using graph s(5)
      by (auto elim: dblton_graphE)
    moreover have "odd (length (parent.follow par v1))"
      using last_even_invar_imp[OF 2(5,4,10) \<open>flabel v1 = Some (r, Even)\<close> ] \<open>flabel v1 = Some (r, Even)\<close>
      by simp
    moreover have "odd (length (parent.follow par v2))"
      using last_even_invar_imp[OF 2(5,4,10) ] \<open>flabel v2 = Some (s, Even)\<close> 
      by blast
    moreover have "distinct (parent.follow par v1)" "distinct (parent.follow par v2)"
      by(intro distinct_invar_props[OF 2(11)])+
    moreover have "v1 \<in> Vs G"
      using s(5) by(auto simp: Vs_def)
    then have "path G (parent.follow par v1)"
      by(intro path_invar_props[OF 2(12)])
    moreover have "v2 \<in> Vs G"
      using s(5) by(auto simp: Vs_def)
    then have "path G (parent.follow par v2)"
      by(intro path_invar_props[OF 2(12)])
    ultimately show ?thesis
      using 2(5)
      by metis
  qed
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
    apply (clarsimp simp: examined_have_odd_verts_invar_def)
    using option.distinct(1)
    by metis
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
    apply (simp add: unexamined_matched_unlabelled_invar_def)
    by blast
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
    apply(intro examined_have_odd_verts_invar_props[where flabel = flabel] invars)
    using \<open>flabel v2 = None\<close>
    by simp
  moreover have "{v1, v2} \<notin> M"
    using \<open>flabel v2 = None\<close> ass compute_alt_path.if1_props(2) compute_alt_path_axioms flabel_invar_props(2) invars(1) by fastforce
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
  apply(auto simp add: es_minus matching_def)
  by (simp add: es_def)

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
    using infinite_super by auto
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
    consider (one) "card s = 1" | (three) "card s = 3" | (ge_five)"card s \<ge> 5"
      using insert(8)
      by (metis (no_types, lifting) One_nat_def Suc_leI antisym_conv card_gt_0_iff eval_nat_numeral(3) even_numeral insert.prems(2) not_less_eq_eq numeral_3_eq_3 numeral_4_eq_4 odd_card_imp_not_empty)
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
        using that u1u2u3(2-4)
        apply(simp add: card_le_Suc_iff numeral_2_eq_2 Int_def ex_in_conv)
        by (smt insert_compr mem_Collect_eq)
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
          apply(intro card_mono)
          using insert(5)
          by (auto simp add: s'_def es_def)
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
          apply(rule insert)+
          using insert
          by(auto simp: s'_def matching_def)
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
  {
    fix e
    assume "e\<in>G - es s"
    then have "e \<in> G"
      by simp
    then obtain s' where s': "s'\<in>(insert s OSC)"  "if card s' = 1 then s' \<inter> e \<noteq> {} else e \<subseteq> s'"
      using assms(2)
      by (auto simp add: odd_set_cover_def)
    moreover have "card e = 2"
      using assms(3) \<open>e \<in> G\<close>
      by (fastforce elim: dblton_graphE)
    ultimately have "\<exists>s\<in>OSC. if card s = 1 then s \<inter> e \<noteq> {} else e \<subseteq> s"
      using assms(1) s' \<open>e \<in> G - es s\<close>
      by (fastforce simp add: es_def)
  }
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
    using assms(4) odd_set_cover_def by blast
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
      have "odd_set_cover OSC (G - ev)"
        using insert(1,7)
        unfolding odd_set_cover_def ev_def
        by (fastforce simp: card_Suc_eq v)
      moreover have "matching (M - ev)" "(M - ev) \<subseteq> (G - ev)"
        using insert(5,6)
        by (auto simp add: matching_def)
      ultimately have "card (M - ev) \<le> capacity2 OSC"
        apply(intro insert(3)[where G = "G - ev"])
        using insert
        by (auto simp add: dblton_graph_def)
      moreover have "\<exists>e1 e2. e1 \<noteq> e2 \<and> e1 \<in> M \<and> e2 \<in> M \<and> e1 \<inter> e2 \<noteq> empty" if "2 \<le> card (M \<inter> ev)"
        using that 
        apply(simp add: card_le_Suc_iff numeral_2_eq_2 Int_def ex_in_conv ev_def)
        by (metis (mono_tags, lifting) insert_iff mem_Collect_eq)
      then have "card (M \<inter> ev) \<le> 1"
        using \<open>matching M\<close>
        by(fastforce simp add: matching_def)      
      then have "card M \<le> card (M - ev) + 1"
        by (metis card_Diff_subset_Int diff_le_mono2 finite_Int insert.prems(1) insert.prems(3) le_diff_conv rev_finite_subset)
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
        apply(intro OSC_insert insert) .
      moreover have "matching (M - es s)" "M - es s \<subseteq> G -  es s"
        using insert
        by (auto simp add: Diff_mono matching_def)
      ultimately have "card (M - es s) \<le> capacity2 OSC"
        apply(intro insert(3)[where G = "G - es s"])
        using insert
        by (auto simp: dblton_graph_def)
      moreover have "card (M \<inter> es s) \<le> capacity1 s"
        apply(intro capacity_bounds_common_edges[OF insert(4)] insert)
        using \<open>odd (card s)\<close> odd_card_imp_not_empty
        by (force elim: )+
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
  by (auto; metis Un_iff)

lemma OSC_inter: "odd_set_cover OSC G1 \<Longrightarrow> odd_set_cover OSC (G1 \<inter> G2)"
  unfolding odd_set_cover_def
  by auto

lemma card_sing_image: "card {{x} | x . P x} = card {x . P x}"
proof-
  have "card ((\<lambda>x. {x}) ` {x . P x}) =  card {x . P x}"
    apply(intro card_image)
    by simp
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
  then show ?case by simp
next
  case (insert s S')
  then show ?case
    apply simp
    by (metis add_diff_cancel_left' card_Un_disjoint card_eq_0_iff diff_zero finite_Un finite_Union
              insert.prems(2) insert_partition mult.commute mult_0_right)
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
    ret:
    "compute_alt_path ex par flabel = None" and
    init:       
    "finite ex" "ex \<subseteq> G"
  shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
proof-
  have "\<exists>OSC. odd_set_cover OSC G \<and> capacity2 OSC = card M"
    using assms
  proof(induction ex par flabel rule: compute_alt_path_pinduct_2)
    case 1
    then show ?case
      by(intro compute_alt_path_dom init)
  next
    case (2 ex par flabel)
    show ?case
    proof(cases "if1_cond flabel ex")
      case True
      obtain v1 v2 v3 r where sel: "(v1, v2, v3, r) = sel_if1 flabel ex" "if1 flabel ex v1 v2 v3 r"
        using if1_cond_props''''[OF True] by metis
      let ?par' = "par(v2 \<mapsto> v1, v3 \<mapsto> v2)"
      let ?flabel' = "flabel(v2 \<mapsto> (r, Odd), v3 \<mapsto> (r, Even))"
      let ?ex' = "insert {v2, v3} (insert {v1, v2} ex)"
      have "compute_alt_path ex par flabel = compute_alt_path ?ex' ?par' ?flabel'"
        by(auto intro: compute_alt_path_if1[OF 2(1) True sel(1)])
      then have "compute_alt_path ?ex' ?par' ?flabel' = None"
        using 2
        by simp
      moreover have "flabel_invar ?flabel'"
        using flabel_invar_pres[OF 2(3) sel(2), of Odd _ Even].
      moreover have "examined_have_odd_verts_invar ?ex' ?flabel'"
        using examined_have_odd_verts_invar_pres(1)[OF 2(3,4) sel(2)].
      moreover have "?ex' \<subseteq> G"
        by (meson "2.prems"(10) DiffD1 compute_alt_path.if1_props(1) compute_alt_path_axioms if1_props(4) insert_subsetI matching(2) sel(2) subsetD)
      moreover have "finite ?ex'"
        using 2
        by auto
      moreover have "unexamined_matched_unlabelled_invar ?ex' ?flabel'"
        using unexamined_matched_unlabelled_invar_pres(1)[OF 2(3,5) sel(2)].
      moreover have "finite_odds_invar ?flabel'"
        by(intro finite_odds_invar_pres[where ex = ex and ?v1.0 = v1] 2 sel)
      moreover have "odd_labelled_verts_num_invar ?ex' ?flabel'"
        by(intro odd_labelled_verts_num_invar_pres[where ex = ex and ?v1.0 = v1] 2 sel)
      moreover have "ulabelled_verts_matched_invar ?ex' ?flabel'"
        by(intro ulabelled_verts_matched_invar_pres[where ex = ex and ?v1.0 = v1] 2 sel)
      moreover have "odd_then_matched_examined_invar ?ex' ?flabel'"
        by(intro odd_then_matched_examined_invar_pres[where ex = ex and ?v1.0 = v1] 2 sel)
      ultimately show ?thesis
        using sel
        apply(intro 2(2)[OF True, of v1 v2 v3 r])
        by (simp; blast)+
    next
      case noL1: False
      then have if2_nholds: "\<not>if2_cond flabel"
        using 2
        by(auto simp add: compute_alt_path.psimps[OF 2(1)] split: prod.splits)
      define lab_osc where "lab_osc = {{v} | v . \<exists>r. flabel v = Some (r, Odd)}"
      {
        fix es
        assume "\<And>e. e \<in> es \<Longrightarrow> \<exists>v \<in> e. \<exists>r. flabel v = Some (r, Odd)"
        then have "\<exists>s\<in>lab_osc. e \<inter> s \<noteq> {}" if "e \<in> es" for e 
          using \<open>examined_have_odd_verts_invar ex flabel\<close> that
          unfolding examined_have_odd_verts_invar_def lab_osc_def
          apply auto
          by (metis disjoint_insert(2))
        moreover have "finite lab_osc"
          unfolding lab_osc_def
          using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
          by force
        moreover have "odd (card s) \<and> finite s" if "s\<in>lab_osc" for s
          using that
          unfolding lab_osc_def
          by auto
        moreover have "card s = 1" if "s \<in> lab_osc" for s
          using that
          unfolding lab_osc_def
          by auto
        ultimately have "odd_set_cover lab_osc es"
          unfolding odd_set_cover_def
          by (simp add: inf_commute)
        then have "odd_set_cover lab_osc (es \<inter> G)"
          by(rule OSC_inter)
      } note * = this
      have "odd_set_cover lab_osc (ex \<inter> G)"
        apply(intro *)
        using \<open>examined_have_odd_verts_invar ex flabel\<close>
        using examined_have_odd_verts_invar_def
        by blast
      have "finite lab_osc"
        unfolding lab_osc_def
        using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
        by force
      have all_verts_labelled: "\<exists>v. v \<in> e \<and> (flabel v = None \<or> (\<exists>r. flabel v = Some (r, Odd)))"
        if "e \<in> G" for e
      proof-
        obtain v1 v2 where "e = {v1, v2}" "v1 \<noteq> v2"
          using \<open>e \<in> G\<close> graph_invar_dblton[OF graph]
          apply -
          by(erule dblton_graphE)
        then have "flabel v1 = None \<or> (\<exists>r. flabel v1 = Some (r, Odd)) \<or>
                   flabel v2 = None \<or> (\<exists>r. flabel v2 = Some (r, Odd))"
          using if2_nholds
          unfolding if2_cond_def
          by (smt label.exhaust option.exhaust surj_pair that)
        moreover have "v1 \<in> e" "v2 \<in> e"
          using \<open>e = {v1, v2}\<close>
          by auto
        ultimately show ?thesis
          by auto
      qed
      have lab_osc_covers: "\<exists>s\<in>lab_osc. s \<inter> e \<noteq> {} \<and>  card s = 1"
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
      consider (all_match_ex) "card (M - ex) = 0" | (one_match_unex) "card (M - ex) = 1" | (mult_match_unex) "2 \<le> card (M - ex)"
        by linarith
      then show ?thesis
      proof cases
        case all_match_ex
        then have "flabel v \<noteq> None" if "v \<in> e" "e \<in> G" for v e
          using \<open>ulabelled_verts_matched_invar ex flabel\<close> that finiteM 
          by (force simp: ulabelled_verts_matched_invar_def)
        then have "\<exists>v \<in> e. \<exists>r. flabel v = Some (r, Odd)" if "e \<in> G" for e
          using all_verts_labelled that
          by blast
        then have "odd_set_cover lab_osc (G \<inter> G)"
          apply(intro *)
          by simp
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
          apply(intro capacity2_sings[symmetric])
          by auto
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
              by (metis "2.prems"(6) DiffD1 \<open>M - ex = {e}\<close> \<open>e = {v1, v2}\<close> \<open>va \<in> e'\<close>
                        ulabelled_verts_matched_invar_def insertE singletonD that vs_member_intro)
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
                  using "2.prems"(6)
                  by (smt  DiffD1 Diff_insert_absorb False \<open>M - ex = {e}\<close> \<open>e = {v1, v2}\<close>
                          \<open>e' = {va, vb}\<close> \<open>va \<noteq> vb\<close> edges_are_Vs insert_absorb insert_commute v2
                          singletonD singleton_insert_inj_eq' that ulabelled_verts_matched_invar_def)
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
                  by metis
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
          apply(intro OSC_union)
          using \<open>odd_set_cover lab_osc (ex \<inter> G)\<close>
          by simp+
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
          apply(intro card_Un_disjoint)
          using \<open>finite lab_osc\<close>
          by auto
        also have "... = card (M - ex) + card (M \<inter> ex)"
          unfolding unlab_osc_def
          using \<open>card (M - ex) = 1\<close> \<open>odd_labelled_verts_num_invar ex flabel\<close> 
          unfolding odd_labelled_verts_num_invar_def lab_osc_def card_sing_image
          by simp
        also have "... = card ((M - ex) \<union> (M \<inter> ex))"
          apply(intro card_Un_disjoint[symmetric])
          using finiteM
          by auto
        finally have "card osc = card ((M - ex) \<union> (M \<inter> ex))".
        moreover have "M = ((M - ex) \<union> (M \<inter> ex))"
          by auto
        ultimately have "card M = card osc"
          by simp
        moreover have *: "osc = {{v} | v. v = v1 \<or> (\<exists>r. flabel v = Some (r, Odd))}"
          unfolding osc_def lab_osc_def unlab_osc_def
          by auto
        moreover have "finite ..."
          using * \<open>finite osc\<close> by simp
        then have "capacity2 ... = card ..."
          apply(intro capacity2_sings)
          using \<open>finite lab_osc\<close>
          by (auto simp: lab_osc_def)
        ultimately have "capacity2 osc = card M"
          by simp
        then show ?thesis
          using i
          by metis
      next
        case mult_match_unex
        then obtain e M' where M': "e \<in> M - ex" "M - ex = insert e M'" "e \<notin> M'"
          by(auto simp: card_le_Suc_iff numeral_2_eq_2)
        then obtain v1 v2 where v1v2: "e = {v1, v2}" "v1 \<noteq> v2"
          using matching(2) graph
          by (force elim: dblton_graphE)
        have "v1 \<notin> \<Union> M'" (*as, e is disjoint will edges in M', as M is a matching*)
          by (metis DiffD1 Diff_insert_absorb M'(2) M'(3) Union_iff matching(1) insertI1 matching_unique_match v1v2(1))
        have "e = {v2, v1}"
          using \<open>e = {v1, v2}\<close> by auto
        then have "v2 \<notin> \<Union> M'"
          by (metis DiffD1 Diff_insert_absorb M'(2) M'(3) Union_iff matching(1) insertI1 matching_unique_match)
        define unlab_osc1 where "unlab_osc1  = {{v1}}"
        define unlab_osc2 where "unlab_osc2  = {{v2} \<union> \<Union>M'}"
        define osc where "osc = lab_osc \<union> unlab_osc1 \<union> unlab_osc2"
        have card_unlab_osc2: "card ({v2} \<union> \<Union> M') = Suc (2 * card M')"
        proof-
          have "finite M'"
            by (metis M'(2) finiteM finite_Diff finite_insert)
          moreover have "card e = 2" if "e \<in> M'" for e
            using graph matching(2)
            by (metis dblton_graph_def Diff_subset M'(2) card_2_iff insert_subset subset_iff that)
          moreover have "e \<inter> e' = {}" if "e \<in> M'" "e' \<in> M'" "e \<noteq> e'" for e e'
            using matching(1) that
            unfolding matching_def2
            by (metis Diff_subset Int_emptyI M'(2) in_mono matching(1) matching_unique_match subset_insertI)
          ultimately have "card (\<Union>M') = (2 * card M')"
            apply(intro card_UNION_const).
          have "{v2} \<inter> \<Union>M' = {}"
            using \<open>v2 \<notin> \<Union>M'\<close> by auto
          moreover have "finite (\<Union>M')"
            using matching(2) graph(1) M'(2)
            by (metis dblton_graph_def Un_Diff_Int Union_Un_distrib Union_insert
                      finite.simps finite_Un finite_Union finite_insert finite_E
                      inf.orderE inf_commute)
          ultimately have "card ({v2} \<union> \<Union> M') = card {v2} + card (\<Union>M')"
            unfolding unlab_osc2_def
            apply(intro card_Un_disjoint)
            by auto
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
          apply(intro capacity2_Un_disjoint) .
        moreover have "capacity2 unlab_osc1 = 1"
          by (auto simp: unlab_osc1_def)
        moreover have "capacity2 unlab_osc2 = card M'"
        proof-
          have "finite M'"
            by (metis M'(2) finiteM finite_Diff finite_insert)
          then have "0 < card M'"
            using mult_match_unex M' card_unlab_osc2
            by simp
          hence "capacity1 ({v2} \<union> \<Union> M') = card M'"
            using card_unlab_osc2
            apply(intro capacity1_gt1) .
          then show ?thesis
            unfolding unlab_osc2_def
            by (auto simp add: capacity2_def)
        qed
        ultimately have "capacity2 (unlab_osc1 \<union> unlab_osc2) = Suc (card M')"
          by simp
        moreover have "card (M - ex) = Suc (card M')"
          using M' finiteM
          by (metis card_insert_disjoint finite_Diff finite_insert)
        ultimately have "capacity2 (unlab_osc1 \<union> unlab_osc2) = card (M -ex)"
          by auto
        moreover have "capacity2 (lab_osc \<union> (unlab_osc1 \<union> unlab_osc2)) = capacity2 lab_osc + capacity2 (unlab_osc1 \<union> unlab_osc2)"
        proof-
          have "flabel v = None" if "v \<in> \<Union>M'" for v
            using that
            apply auto
            by (metis "2.prems"(3) M'(2) subset_eq  subset_insertI unexamined_matched_unlabelled_invar_def)
          moreover have "flabel v2 = None"
            using "2.prems"(3) M'(1) unexamined_matched_unlabelled_invar_props v1v2(1) by fastforce
          ultimately have "lab_osc \<inter> unlab_osc2 = {}"
            unfolding lab_osc_def unlab_osc2_def
            by auto
          moreover have "flabel v1 = None"
            using "2.prems"(3) M'(1) unexamined_matched_unlabelled_invar_props v1v2(1) by fastforce
          then have "lab_osc \<inter> unlab_osc1 = {}"
            using \<open>flabel v1 = None\<close>
            unfolding lab_osc_def unlab_osc1_def
            by auto
          ultimately have "lab_osc \<inter> (unlab_osc1 \<union> unlab_osc2) = {}" by auto
          moreover have "finite (unlab_osc1 \<union> unlab_osc2)"
            using \<open>finite unlab_osc1\<close> \<open>finite unlab_osc2\<close>
            by simp
          moreover have "finite lab_osc"
            unfolding lab_osc_def
            using \<open>finite_odds_invar flabel\<close> finite_odds_invar_def
            by force
          ultimately show ?thesis
            apply(intro capacity2_Un_disjoint) .
        qed
        moreover have "capacity2 lab_osc = card lab_osc"
          using \<open>finite lab_osc\<close>
          unfolding lab_osc_def
          apply(intro capacity2_sings)
          by auto
        then have "card lab_osc = card (M \<inter> ex)"
          using \<open>odd_labelled_verts_num_invar ex flabel\<close> 
          unfolding odd_labelled_verts_num_invar_def lab_osc_def card_sing_image
          by simp
        moreover have "card ((M - ex) \<union> (M \<inter> ex)) = card (M - ex) + card (M \<inter> ex)"
          apply(intro card_Un_disjoint)
          using finiteM
          by auto
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
              by metis
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
                using that by simp
              then obtain va vb where "e' = {va, vb}" "va \<noteq> vb"
                using graph
                by (blast elim: dblton_graphE)
              have "(\<forall>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even)) \<or>
                  ((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Odd))) \<or>
                  ((\<exists>v\<in>{va,vb}.\<exists>r. flabel v = Some (r, Even)) \<and> (\<exists>v\<in>{va,vb}. flabel v = None)) \<or>
                  (\<forall>v\<in>{va,vb}. flabel v = None)"
                apply (cases "flabel va"; cases "flabel vb")
                using label.exhaust label.distinct
                by auto
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
                  unfolding if1_cond_def
                  by (smt \<open>e \<in> M\<close> \<open>e' = {va, vb}\<close> \<open>flabel va = None \<and> e = {v, va} \<or> flabel vb = None \<and> e = {v, vb}\<close> empty_iff even_unlab insertE insert_commute option.distinct(1) that)
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
                    using nones
                    by (metis "2.prems"(6) Union_iff \<open>e' = {va, vb}\<close> \<open>e' \<in> G\<close> edges_are_Vs insertI1 
                              ulabelled_verts_matched_invar_def insert_commute)+
                  then have "{va, vb} \<subseteq> \<Union>(M - ex) - {v1}"
                    using \<open>va \<noteq> v1\<close> \<open>vb \<noteq> v1\<close>
                    by auto
                  ultimately have "\<exists>s\<in>unlab_osc2. e' \<subseteq> s"
                    using \<open>e' = {va, vb}\<close> by (simp add: unlab_osc2_def)
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
            apply auto
            by (metis card.infinite finite_insert nat.simps(3))
          ultimately have i: "odd_set_cover osc (G - ex)"
            using graph
            apply(intro odd_set_coverI)
            apply simp_all
            by (metis inf.absorb_iff2 insert_not_empty dblton_graphE)
          hence "odd_set_cover (osc \<union> lab_osc) ((G - ex) \<union> (ex \<inter> G))"
            apply(intro OSC_union)
            using \<open>odd_set_cover lab_osc (ex \<inter> G)\<close>
            by simp+
          then show ?thesis
            unfolding osc_def
            by (metis Un_Diff_Int inf_commute le_sup_iff sup.absorb1 sup_ge1)
        qed
        ultimately show ?thesis
          by metis
      qed
    qed
  qed
  then have "card M' \<le> card M" if "matching M'" "M' \<subseteq> G" for M'
    using odd_set_cover_bounds_matching_size graph finite_E that
    by metis
  then show ?thesis
    by (meson Berge_2(1) Berge_2(2) Berge_2(3) finiteM leD matching(1) matching(2))
qed

lemma compute_alt_path_from_tree_2:
  assumes invars: 
    "flabel_invar flabel"
    "examined_have_odd_verts_invar ex flabel"
    "unexamined_matched_unlabelled_invar ex flabel"
    "finite_odds_invar flabel"
    "odd_labelled_verts_num_invar ex flabel"
    "ulabelled_verts_matched_invar ex flabel"
    "odd_then_matched_examined_invar ex flabel" and
    aug_path:
    "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
    and
    init:       
    "finite ex" "ex \<subseteq> G"
  shows "\<exists>match_blossom_comp. compute_alt_path ex par flabel = Some match_blossom_comp"
  using compute_alt_path_from_tree_2'[OF invars _ init, where par = par] option.distinct aug_path
  by blast

subsubsection \<open>Bringing it All Together: Final Correctness Theorems\<close>

lemma invar_init:
  fixes flabel::"('a \<Rightarrow> ('a \<times> label) option)" and
    ex::"'a set set" and 
    par::"'a \<Rightarrow> 'a option" 
  assumes initialisation:
    "\<And>v. flabel v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
  shows
    "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent.follow par v)"
    "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
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
    apply simp
    using not_finite_existsD
    by blast
  show "odd_labelled_verts_num_invar ex flabel"
    using assms  
    unfolding odd_labelled_verts_num_invar_def
    using card_eq_0_iff by fastforce
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
  then have par[simp]: "(parent.follow par v) = [v]" if "par v = None" for v
    using parent.follow_psimps[OF \<open>parent par\<close>] that
    by auto
  then show "\<And>v r lab. flabel v = Some (r, lab) \<Longrightarrow> alt_labels_invar flabel r (parent.follow par v)"
    using assms  
    apply auto
    by (metis Pair_inject option.inject option.simps(3))
  show "\<And>v r. flabel v = Some (r, Even) \<Longrightarrow> alt_list (\<lambda>v. flabel v = Some (r, Even)) (\<lambda>v. flabel v = Some (r, Odd)) (parent.follow par v)"
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

lemma compute_alt_path_from_tree_sound:
  fixes flabel::"'a \<Rightarrow> ('a \<times> label) option" and
    ex::"'a set set" and
    par::"'a \<Rightarrow> 'a option"
  assumes  initialisation:
    "\<And>v. flabel v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
    and
    ret:
    "compute_alt_path ex par flabel = Some (p1, p2)"
  shows "last p1 \<notin> Vs M \<and>
       last p2 \<notin> Vs M \<and>
       hd p1 \<noteq> hd p2 \<and>
       odd (length p1) \<and>
       odd (length p2) \<and>
       distinct p1 \<and>
       distinct p2 \<and>
       path G p1 \<and>
       path G p2 \<and>
       {hd p1, hd p2} \<in> G \<and>
       (\<forall>x pref1 post1 pref2 post2. p1 = pref1 @ x # post1 \<and> p2 = pref2 @ x # post2 \<longrightarrow> post1 = post2) \<and>
       alt_path M (hd p1 # p2) \<and> 
       alt_path M (hd p2 # p1)"
  apply(intro compute_alt_path_from_tree_1[OF invar_init(1-11)[OF initialisation] ret])
  using initialisation
  by auto

lemma compute_alt_path_from_tree_sound':
  fixes flabel::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> ('a \<times> label) option" and
    ex::"'a set set" and
    par::"'a \<Rightarrow> 'a option"
  assumes  initialisation:
    "\<And>v G M. flabel G M v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
  shows "compute_alt_path_spec G M (compute_alt_path ex par (flabel G M))"
  using compute_alt_path_from_tree_sound[where par = par, OF initialisation]
  unfolding compute_alt_path_spec_def
  apply(intro conjI)
  by metis+

lemma compute_alt_path_from_tree_complete:
  fixes flabel::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> ('a \<times> label) option" and
    ex::"'a set set" and
    par::"'a \<Rightarrow> 'a option"
  assumes  initialisation:
    "\<And>G M v. flabel G M v = (if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)" "ex = empty"
    "\<And>v. par v = None"
    and
    aug_path:
    "\<exists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p"
  shows "\<exists>match_blossom_comp. compute_alt_path ex par (flabel G M) = Some match_blossom_comp"
  apply(intro compute_alt_path_from_tree_2 invar_init[OF initialisation] aug_path)
  using initialisation
  by auto

end 

locale compute_alt_path_use =
  g: graph_abs E +
  choose sel +
  create_vert create_vert 
  for sel create_vert:: "'a set \<Rightarrow> 'a" and E::"'a set set "
begin

abbreviation "flabel \<equiv> (\<lambda>G M v. if v \<in> Vs G \<and> v \<notin> Vs M then Some (v, Even) else None)"
abbreviation "ex \<equiv> empty"
abbreviation "par \<equiv> (\<lambda>v. None)"

interpretation compute_match_blossom'_use E sel create_vert "(\<lambda>G M. compute_alt_path.compute_alt_path G M sel ex par (flabel G M))"
proof(unfold_locales,goal_cases)
  case (2 G M)
  then interpret compute_alt_path  G M
    apply unfold_locales
    by auto
  show ?case
    apply(rule compute_alt_path_from_tree_complete)
    using 2
    by auto
next
  case (1 G M)
  then interpret compute_alt_path G M
    apply unfold_locales
    by auto
   show ?case
     apply(rule compute_alt_path_from_tree_sound')
     by auto
qed

lemmas find_max_matching_works = find_max_matching_works 
end

end