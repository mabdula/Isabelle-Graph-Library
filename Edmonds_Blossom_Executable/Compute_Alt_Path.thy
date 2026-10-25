theory Compute_Alt_Path
  imports Graph_Matching_Specs Compute_Alt_Path_Invars
begin

provenance ai

section \<open>The alternating forest search of Edmonds' blossom algorithm\<close>

text \<open>The search grows an alternating forest rooted at the free vertices. Every vertex of the
  forest carries a label: the root of its tree and its parity (even or odd). The search keeps a
  queue of even vertices whose neighbours remain to be scanned, and the list of edges, from the
  even vertex currently being scanned, that remain to be examined. An edge to an unlabelled
  vertex grows the forest by that vertex and its mate; an edge between two even vertices ends the
  search with the two paths from its endpoints to their roots. If every even vertex has been
  scanned, no augmenting path exists.

  The correctness proof uses the invariants of the abstract search, which are proved in the
  theory \<open>Compute_Alt_Path_Invars\<close>: every growth step of the search is one of the steps
  @{const compute_alt_path.if1} and @{const compute_alt_path.if2} that preserve them.\<close>

subsection \<open>Edges of a forest given by parent pointers\<close>

definition "forest_edges par = {{a, b} | a b. par a = Some b}"

lemma forest_edges_empty[simp]: "forest_edges (\<lambda>v. None) = {}"
  by (simp add: forest_edges_def)

lemma forest_edgesI: "par a = Some b \<Longrightarrow> {a, b} \<in> forest_edges par"
  unfolding forest_edges_def
  by blast

lemma forest_edges_update:
  assumes "par w = None" "par x = None" "w \<noteq> x"
  shows "forest_edges (par(w \<mapsto> v, x \<mapsto> w)) = insert {w, x} (insert {v, w} (forest_edges par))"
proof(intro equalityI subsetI)
  fix e
  assume "e \<in> forest_edges (par(w \<mapsto> v, x \<mapsto> w))"
  then obtain a b where e: "e = {a, b}" "(par(w \<mapsto> v, x \<mapsto> w)) a = Some b"
    by (auto simp: forest_edges_def)
  show "e \<in> insert {w, x} (insert {v, w} (forest_edges par))"
  proof(cases "a = x")
    case True
    then show ?thesis
      using e
      by (auto simp: insert_commute)
  next
    case False
    show ?thesis
    proof(cases "a = w")
      case True
      then show ?thesis
        using e \<open>a \<noteq> x\<close>
        by (auto simp: insert_commute)
    next
      case False
      then show ?thesis
        using e \<open>a \<noteq> x\<close>
        by (auto simp: forest_edges_def)
    qed
  qed
next
  fix e
  assume "e \<in> insert {w, x} (insert {v, w} (forest_edges par))"
  then consider "e = {w, x}" | "e = {v, w}" | "e \<in> forest_edges par"
    by blast
  then show "e \<in> forest_edges (par(w \<mapsto> v, x \<mapsto> w))"
  proof cases
    case 1
    then show ?thesis
      using forest_edgesI[of "par(w \<mapsto> v, x \<mapsto> w)" x w]
      by (simp add: insert_commute)
  next
    case 2
    then show ?thesis
      using assms(3) forest_edgesI[of "par(w \<mapsto> v, x \<mapsto> w)" w v]
      by (simp add: insert_commute)
  next
    case 3
    then obtain a b where ab: "e = {a, b}" "par a = Some b"
      by (auto simp: forest_edges_def)
    moreover have "a \<noteq> w" "a \<noteq> x"
      using ab(2) assms(1,2)
      by auto
    ultimately show ?thesis
      by (auto simp: forest_edges_def)
  qed
qed

subsection \<open>The program state\<close>

record ('v, 'parents, 'labels) Compute_Alt_Path_state =
  queue :: "'v list"
  unscanned :: "('v \<times> 'v) list"
  forest_parents :: 'parents
  forest_labels :: 'labels

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

subsection \<open>The loop\<close>

locale Compute_Alt_Path =
  Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty +
  Parent: Map parent_empty parent_update parent_delete parent_lookup parent_invar +
  Label: Map label_empty label_update label_delete label_lookup label_invar
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option"
  and mate_empty :: 'mate
  and parent_empty :: 'parents
  and parent_update :: "'v \<Rightarrow> 'v \<Rightarrow> 'parents \<Rightarrow> 'parents"
  and parent_delete :: "'v \<Rightarrow> 'parents \<Rightarrow> 'parents"
  and parent_lookup :: "'parents \<Rightarrow> 'v \<Rightarrow> 'v option"
  and parent_invar :: "'parents \<Rightarrow> bool"
  and label_empty :: 'labels
  and label_update :: "'v \<Rightarrow> 'v \<times> label \<Rightarrow> 'labels \<Rightarrow> 'labels"
  and label_delete :: "'v \<Rightarrow> 'labels \<Rightarrow> 'labels"
  and label_lookup :: "'labels \<Rightarrow> 'v \<Rightarrow> ('v \<times> label) option"
  and label_invar :: "'labels \<Rightarrow> bool" +
  fixes G :: 'adjmap and vs :: "'v list" and M :: 'mate
begin

definition "Compute_Alt_Path_axiom \<longleftrightarrow> graph_input G vs \<and> matching_invar G M"

abbreviation "abs_parents state \<equiv> parent_lookup (forest_parents state)"
abbreviation "abs_labels state \<equiv> label_lookup (forest_labels state)"
abbreviation "abs_examined state \<equiv> forest_edges (abs_parents state)"

function \<^marker>\<open>provenance ai_human\<close> (domintros) Compute_Alt_Path ::
  "('v, 'parents, 'labels) Compute_Alt_Path_state \<Rightarrow>
   ('v, 'parents, 'labels) Compute_Alt_Path_state" where
  "Compute_Alt_Path state =
     (case unscanned state of
        (v, w) # rest \<Rightarrow>
          (case label_lookup (forest_labels state) w of
             None \<Rightarrow>
               (case mate_lookup M w of
                  Some x \<Rightarrow>
                    (let r = fst (the (label_lookup (forest_labels state) v)) in
                     Compute_Alt_Path
                       (state \<lparr>queue := x # queue state, unscanned := rest,
                               forest_parents :=
                                 parent_update x w (parent_update w v (forest_parents state)),
                               forest_labels :=
                                 label_update x (r, Even)
                                   (label_update w (r, Odd) (forest_labels state))\<rparr>))
                | None \<Rightarrow> Compute_Alt_Path (state \<lparr>unscanned := rest\<rparr>))
           | Some (r, Even) \<Rightarrow> state
           | Some (r, Odd) \<Rightarrow> Compute_Alt_Path (state \<lparr>unscanned := rest\<rparr>))
      | [] \<Rightarrow>
          (case queue state of
             v # q \<Rightarrow>
               Compute_Alt_Path
                 (state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>)
           | [] \<Rightarrow> state))"
  by pat_completeness auto

partial_function \<^marker>\<open>provenance ai_human\<close> (tailrec) Compute_Alt_Path_impl ::
  "('v, 'parents, 'labels) Compute_Alt_Path_state \<Rightarrow>
   ('v, 'parents, 'labels) Compute_Alt_Path_state" where
  "Compute_Alt_Path_impl state =
     (case unscanned state of
        (v, w) # rest \<Rightarrow>
          (case label_lookup (forest_labels state) w of
             None \<Rightarrow>
               (case mate_lookup M w of
                  Some x \<Rightarrow>
                    (let r = fst (the (label_lookup (forest_labels state) v)) in
                     Compute_Alt_Path_impl
                       (state \<lparr>queue := x # queue state, unscanned := rest,
                               forest_parents :=
                                 parent_update x w (parent_update w v (forest_parents state)),
                               forest_labels :=
                                 label_update x (r, Even)
                                   (label_update w (r, Odd) (forest_labels state))\<rparr>))
                | None \<Rightarrow> Compute_Alt_Path_impl (state \<lparr>unscanned := rest\<rparr>))
           | Some (r, Even) \<Rightarrow> state
           | Some (r, Odd) \<Rightarrow> Compute_Alt_Path_impl (state \<lparr>unscanned := rest\<rparr>))
      | [] \<Rightarrow>
          (case queue state of
             v # q \<Rightarrow>
               Compute_Alt_Path_impl
                 (state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>)
           | [] \<Rightarrow> state))"

lemma Compute_Alt_Path_impl_same:
  assumes "Compute_Alt_Path_dom state"
  shows "Compute_Alt_Path_impl state = Compute_Alt_Path state"
  apply(induction rule: Compute_Alt_Path.pinduct[OF assms])
  apply(subst Compute_Alt_Path_impl.simps)
  by (auto simp: Compute_Alt_Path.psimps Let_def
          split: list.splits prod.splits option.splits label.splits)

definition \<^marker>\<open>provenance ai_human\<close> "free_vertices = filter (\<lambda>v. neighbour_list G v \<noteq> [] \<and> mate_lookup M v = None) vs"

definition \<^marker>\<open>provenance ai_human\<close> "initial_labels =
  foldr (\<lambda>v l. label_update v (v, Even) l) free_vertices label_empty"

definition \<^marker>\<open>provenance ai_human\<close> "initial_state =
  \<lparr>queue = free_vertices, unscanned = [], forest_parents = parent_empty,
   forest_labels = initial_labels\<rparr>"

text \<open>The answer is read off the final state: if the search stopped at an edge between two even
  vertices, the two paths from its endpoints to their roots.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "alternating_paths state =
  (case unscanned state of
     (v, w) # _ \<Rightarrow> Some (follow_impl (parent_lookup (forest_parents state)) v,
                         follow_impl (parent_lookup (forest_parents state)) w)
   | [] \<Rightarrow> None)"

definition \<^marker>\<open>provenance ai_human\<close> "Compute_Alt_Path_run = alternating_paths (Compute_Alt_Path initial_state)"

definition \<^marker>\<open>provenance ai_human\<close> "Compute_Alt_Path_run_impl =
  alternating_paths (Compute_Alt_Path_impl initial_state)"

lemmas [code] = Compute_Alt_Path_impl.simps free_vertices_def initial_labels_def
  initial_state_def alternating_paths_def Compute_Alt_Path_run_impl_def

definition "Compute_Alt_Path_call_1_conds state =
  (\<exists>v w rest x. unscanned state = (v, w) # rest \<and> label_lookup (forest_labels state) w = None \<and>
              mate_lookup M w = Some x)"

definition "Compute_Alt_Path_upd1 state =
  (case unscanned state of
     (v, w) # rest \<Rightarrow>
       (let x = the (mate_lookup M w); r = fst (the (label_lookup (forest_labels state) v)) in
        state \<lparr>queue := x # queue state, unscanned := rest,
               forest_parents := parent_update x w (parent_update w v (forest_parents state)),
               forest_labels :=
                 label_update x (r, Even) (label_update w (r, Odd) (forest_labels state))\<rparr>)
   | [] \<Rightarrow> state)"

definition "Compute_Alt_Path_call_2_conds state =
  (\<exists>v w rest. unscanned state = (v, w) # rest \<and>
            (\<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even)) \<and>
            (label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None))"

definition "Compute_Alt_Path_upd2 state = state \<lparr>unscanned := tl (unscanned state)\<rparr>"

definition "Compute_Alt_Path_call_3_conds state =
  (\<exists>v q. unscanned state = [] \<and> queue state = v # q)"

definition "Compute_Alt_Path_upd3 state =
  (case queue state of
     v # q \<Rightarrow> state \<lparr>queue := q, unscanned := map (Pair v) (neighbour_list G v)\<rparr>
   | [] \<Rightarrow> state)"

definition "Compute_Alt_Path_ret_1_conds state =
  (\<exists>v w rest r. unscanned state = (v, w) # rest \<and> label_lookup (forest_labels state) w = Some (r, Even))"

abbreviation "Compute_Alt_Path_ret1 state \<equiv> state"

definition "Compute_Alt_Path_ret_2_conds state =
  (unscanned state = [] \<and> queue state = [])"

abbreviation "Compute_Alt_Path_ret2 state \<equiv> state"

definition "invar_1 state \<longleftrightarrow>
  parent_invar (forest_parents state) \<and> label_invar (forest_labels state)"

definition "invar_forest state \<longleftrightarrow>
  compute_alt_path.search_invars (ugraph_abs G) (matching_abs M)
    (abs_examined state) (abs_parents state) (abs_labels state)"

definition "invar_unscanned state \<longleftrightarrow>
  (\<forall>v w. (v, w) \<in> set (unscanned state) \<longrightarrow>
     {v, w} \<in> ugraph_abs G \<and> (\<exists>r. label_lookup (forest_labels state) v = Some (r, Even)))"

definition "invar_queue state \<longleftrightarrow>
  (\<forall>v \<in> set (queue state). \<exists>r. label_lookup (forest_labels state) v = Some (r, Even))"

definition "invar_scanned state \<longleftrightarrow>
  (\<forall>v r. label_lookup (forest_labels state) v = Some (r, Even) \<longrightarrow>
     v \<in> set (queue state) \<or>
     (\<forall>w. {v, w} \<in> ugraph_abs G \<longrightarrow>
        (v, w) \<in> set (unscanned state) \<or>
        (\<exists>r'. label_lookup (forest_labels state) w = Some (r', Odd))))"

definition "call_1_measure state =
  card {v \<in> Vs (ugraph_abs G). label_lookup (forest_labels state) v = None}"

definition "call_2_measure state = length (unscanned state)"

definition "call_3_measure state = length (queue state)"

definition "Compute_Alt_Path_term_rel' =
  call_1_measure <*mlex*> call_3_measure <*mlex*> call_2_measure <*mlex*> {}"

lemma Compute_Alt_Path_call_1_conds[call_cond_elims]:
  "Compute_Alt_Path_call_1_conds state \<Longrightarrow>
   (\<lbrakk>\<exists>v w rest x. unscanned state = (v, w) # rest \<and> label_lookup (forest_labels state) w = None \<and>
                mate_lookup M w = Some x\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Compute_Alt_Path_call_1_conds_def)

lemma Compute_Alt_Path_call_1_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = (v, w) # rest; label_lookup (forest_labels state) w = None;
    mate_lookup M w = Some x\<rbrakk> \<Longrightarrow> Compute_Alt_Path_call_1_conds state"
  by (auto simp: Compute_Alt_Path_call_1_conds_def)

lemma Compute_Alt_Path_call_2_conds[call_cond_elims]:
  "Compute_Alt_Path_call_2_conds state \<Longrightarrow>
   (\<lbrakk>\<exists>v w rest. unscanned state = (v, w) # rest \<and>
              (\<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even)) \<and>
              (label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None)\<rbrakk> \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: Compute_Alt_Path_call_2_conds_def)

lemma Compute_Alt_Path_call_2_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = (v, w) # rest; \<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even);
    label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None\<rbrakk>
   \<Longrightarrow> Compute_Alt_Path_call_2_conds state"
  by (auto simp: Compute_Alt_Path_call_2_conds_def)

lemma Compute_Alt_Path_call_3_conds[call_cond_elims]:
  "Compute_Alt_Path_call_3_conds state \<Longrightarrow>
   (\<lbrakk>unscanned state = []; \<exists>v q. queue state = v # q\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Compute_Alt_Path_call_3_conds_def)

lemma Compute_Alt_Path_call_3_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = []; queue state = v # q\<rbrakk> \<Longrightarrow> Compute_Alt_Path_call_3_conds state"
  by (auto simp: Compute_Alt_Path_call_3_conds_def)

lemma Compute_Alt_Path_ret_1_conds[call_cond_elims]:
  "Compute_Alt_Path_ret_1_conds state \<Longrightarrow>
   (\<lbrakk>\<exists>v w rest r. unscanned state = (v, w) # rest \<and>
                label_lookup (forest_labels state) w = Some (r, Even)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Compute_Alt_Path_ret_1_conds_def)

lemma Compute_Alt_Path_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = (v, w) # rest; label_lookup (forest_labels state) w = Some (r, Even)\<rbrakk>
   \<Longrightarrow> Compute_Alt_Path_ret_1_conds state"
  by (auto simp: Compute_Alt_Path_ret_1_conds_def)

lemma Compute_Alt_Path_ret_2_conds[call_cond_elims]:
  "Compute_Alt_Path_ret_2_conds state \<Longrightarrow>
   (\<lbrakk>unscanned state = []; queue state = []\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Compute_Alt_Path_ret_2_conds_def)

lemma Compute_Alt_Path_ret_2_condsI[call_cond_intros]:
  "\<lbrakk>unscanned state = []; queue state = []\<rbrakk> \<Longrightarrow> Compute_Alt_Path_ret_2_conds state"
  by (auto simp: Compute_Alt_Path_ret_2_conds_def)

lemma Compute_Alt_Path_cases:
  assumes "Compute_Alt_Path_call_1_conds state \<Longrightarrow> P"
          "Compute_Alt_Path_call_2_conds state \<Longrightarrow> P"
          "Compute_Alt_Path_call_3_conds state \<Longrightarrow> P"
          "Compute_Alt_Path_ret_1_conds state \<Longrightarrow> P"
          "Compute_Alt_Path_ret_2_conds state \<Longrightarrow> P"
  shows "P"
proof(cases "unscanned state")
  case Nil
  then show ?thesis
    using assms(3,5)
    by (cases "queue state")
       (auto simp: Compute_Alt_Path_call_3_conds_def
                   Compute_Alt_Path_ret_2_conds_def)
next
  case (Cons e rest)
  obtain v w where e: "e = (v, w)"
    by (cases e)
  show ?thesis
  proof(cases "label_lookup (forest_labels state) w")
    case None
    then show ?thesis
      using assms(1,2) Cons e
      by (cases "mate_lookup M w")
         (auto simp: Compute_Alt_Path_call_1_conds_def
                     Compute_Alt_Path_call_2_conds_def)
  next
    case (Some rl)
    obtain r l where rl: "rl = (r, l)"
      by (cases rl)
    show ?thesis
      using assms(2,4) Cons e Some rl
      by (cases l)
         (auto simp: Compute_Alt_Path_call_2_conds_def
                     Compute_Alt_Path_ret_1_conds_def)
  qed
qed

lemma Compute_Alt_Path_simps:
  assumes "Compute_Alt_Path_dom state"
  shows "Compute_Alt_Path_call_1_conds state \<Longrightarrow>
           Compute_Alt_Path state =
             Compute_Alt_Path (Compute_Alt_Path_upd1 state)"
        "Compute_Alt_Path_call_2_conds state \<Longrightarrow>
           Compute_Alt_Path state =
             Compute_Alt_Path (Compute_Alt_Path_upd2 state)"
        "Compute_Alt_Path_call_3_conds state \<Longrightarrow>
           Compute_Alt_Path state =
             Compute_Alt_Path (Compute_Alt_Path_upd3 state)"
        "Compute_Alt_Path_ret_1_conds state \<Longrightarrow>
           Compute_Alt_Path state = Compute_Alt_Path_ret1 state"
        "Compute_Alt_Path_ret_2_conds state \<Longrightarrow>
           Compute_Alt_Path state = Compute_Alt_Path_ret2 state"
  by (auto simp: Compute_Alt_Path.psimps[OF assms] Let_def
                 Compute_Alt_Path_call_1_conds_def Compute_Alt_Path_upd1_def
                 Compute_Alt_Path_call_2_conds_def Compute_Alt_Path_upd2_def
                 Compute_Alt_Path_call_3_conds_def Compute_Alt_Path_upd3_def
                 Compute_Alt_Path_ret_1_conds_def Compute_Alt_Path_ret_2_conds_def
          split: option.splits label.splits)

lemma Compute_Alt_Path_induct:
  assumes "Compute_Alt_Path_dom state"
  assumes "\<And>state. \<lbrakk>Compute_Alt_Path_dom state;
                     Compute_Alt_Path_call_1_conds state \<Longrightarrow>
                       P (Compute_Alt_Path_upd1 state);
                     Compute_Alt_Path_call_2_conds state \<Longrightarrow>
                       P (Compute_Alt_Path_upd2 state);
                     Compute_Alt_Path_call_3_conds state \<Longrightarrow>
                       P (Compute_Alt_Path_upd3 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
proof(induction rule: Compute_Alt_Path.pinduct[OF assms(1)])
  case (1 state)
  show ?case
  proof(rule assms(2)[OF 1(1)])
    assume "Compute_Alt_Path_call_1_conds state"
    then obtain v w rest x where c: "unscanned state = (v, w) # rest"
        "label_lookup (forest_labels state) w = None" "mate_lookup M w = Some x"
      by (auto elim!: call_cond_elims)
    have "P (state \<lparr>queue := x # queue state, unscanned := rest,
               forest_parents := parent_update x w (parent_update w v (forest_parents state)),
               forest_labels := label_update x (fst (the (label_lookup (forest_labels state) v)), Even)
                                  (label_update w (fst (the (label_lookup (forest_labels state) v)), Odd)
                                     (forest_labels state))\<rparr>)"
      by (rule 1(4)[OF c(1) refl c(2) c(3) refl])
    thus "P (Compute_Alt_Path_upd1 state)"
      by (simp add: Compute_Alt_Path_upd1_def c Let_def)
  next
    assume "Compute_Alt_Path_call_2_conds state"
    then obtain v w rest where c: "unscanned state = (v, w) # rest"
        "\<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even)"
        "label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None"
      by (auto elim!: call_cond_elims)
    show "P (Compute_Alt_Path_upd2 state)"
    proof(cases "label_lookup (forest_labels state) w")
      case None
      hence mate: "mate_lookup M w = None"
        using c(3)
        by simp
      have "P (state \<lparr>unscanned := rest\<rparr>)"
        by (rule 1(3)[OF c(1) refl _ mate]) (fact None)
      thus ?thesis
        by (simp add: Compute_Alt_Path_upd2_def c)
    next
      case (Some rl)
      then obtain r l where rl: "rl = (r, l)"
        by (cases rl)
      hence "l = Odd"
        using c(2) Some
        by (cases l) auto
      hence "P (state \<lparr>unscanned := rest\<rparr>)"
        by (rule 1(5)[OF c(1) refl Some rl[symmetric]])
      thus ?thesis
        by (simp add: Compute_Alt_Path_upd2_def c)
    qed
  next
    assume "Compute_Alt_Path_call_3_conds state"
    then obtain v q where c: "unscanned state = []" "queue state = v # q"
      by (auto elim!: call_cond_elims)
    thus "P (Compute_Alt_Path_upd3 state)"
      using 1(2)[OF c]
      by (simp add: Compute_Alt_Path_upd3_def c)
  qed
qed

lemma Compute_Alt_Path_domintros:
  assumes "Compute_Alt_Path_call_1_conds state \<Longrightarrow>
             Compute_Alt_Path_dom (Compute_Alt_Path_upd1 state)"
          "Compute_Alt_Path_call_2_conds state \<Longrightarrow>
             Compute_Alt_Path_dom (Compute_Alt_Path_upd2 state)"
          "Compute_Alt_Path_call_3_conds state \<Longrightarrow>
             Compute_Alt_Path_dom (Compute_Alt_Path_upd3 state)"
  shows "Compute_Alt_Path_dom state"
proof(rule Compute_Alt_Path.domintros, goal_cases)
  case (1 v q)
  hence "Compute_Alt_Path_call_3_conds state"
    by (intro call_cond_intros)
  thus ?case
    using assms(3) 1
    by (simp add: Compute_Alt_Path_upd3_def)
next
  case (2 v w rest)
  hence "Compute_Alt_Path_call_2_conds state"
    by (intro call_cond_intros) auto
  thus ?case
    using assms(2) 2
    by (simp add: Compute_Alt_Path_upd2_def)
next
  case (3 v w rest x)
  hence "Compute_Alt_Path_call_1_conds state"
    by (intro call_cond_intros)
  thus ?case
    using assms(1) 3
    by (simp add: Compute_Alt_Path_upd1_def Let_def)
next
  case (4 v w rest r)
  hence "Compute_Alt_Path_call_2_conds state"
    by (intro call_cond_intros) auto
  thus ?case
    using assms(2) 4
    by (simp add: Compute_Alt_Path_upd2_def)
qed

subsection \<open>Data-structure facts\<close>

lemma upd1_abs:
  assumes "invar_1 state" "unscanned state = (v, w) # rest" "mate_lookup M w = Some x"
          "label_lookup (forest_labels state) v = Some (r, Even)"
  shows "abs_parents (Compute_Alt_Path_upd1 state) = (abs_parents state)(w \<mapsto> v, x \<mapsto> w)"
        "abs_labels (Compute_Alt_Path_upd1 state) =
           (abs_labels state)(w \<mapsto> (r, Odd), x \<mapsto> (r, Even))"
        "queue (Compute_Alt_Path_upd1 state) = x # queue state"
        "unscanned (Compute_Alt_Path_upd1 state) = rest"
        "invar_1 (Compute_Alt_Path_upd1 state)"
  using assms
  by (auto simp: invar_1_def Compute_Alt_Path_upd1_def Parent.map_update Label.map_update
                 Parent.invar_update Label.invar_update)

lemma upd2_abs[simp]:
  "abs_parents (Compute_Alt_Path_upd2 state) = abs_parents state"
  "abs_labels (Compute_Alt_Path_upd2 state) = abs_labels state"
  "queue (Compute_Alt_Path_upd2 state) = queue state"
  "unscanned (Compute_Alt_Path_upd2 state) = tl (unscanned state)"
  by (simp_all add: Compute_Alt_Path_upd2_def)

lemma upd3_abs:
  assumes "queue state = v # q"
  shows "abs_parents (Compute_Alt_Path_upd3 state) = abs_parents state"
        "abs_labels (Compute_Alt_Path_upd3 state) = abs_labels state"
        "queue (Compute_Alt_Path_upd3 state) = q"
        "unscanned (Compute_Alt_Path_upd3 state) = map (Pair v) (neighbour_list G v)"
  using assms
  by (simp_all add: Compute_Alt_Path_upd3_def)

lemma label_foldr:
  "label_invar (foldr (\<lambda>v l. label_update v (v, Even) l) xs label_empty) \<and>
   label_lookup (foldr (\<lambda>v l. label_update v (v, Even) l) xs label_empty) =
     (\<lambda>v. if v \<in> set xs then Some (v, Even) else None)"
  by (induction xs)
     (auto simp: Label.map_empty Label.invar_empty Label.map_update Label.invar_update fun_eq_iff)

lemma follow_impl_eq:
  assumes "parent_spec par"
  shows "follow_impl par = parent_spec.follow par"
proof-
  interpret par_here: parent par
    using assms
    by (simp add: parent_def)
  show ?thesis
    using par_here.follow_impl_is_follow[folded follow_impl_def] .
qed

subsection \<open>Proofs\<close>

context
  assumes Compute_Alt_Path_axiom: Compute_Alt_Path_axiom
begin

lemma graph_input_G[simp]: "graph_input G vs"
  and matching_invar_M[simp]: "matching_invar G M"
  using Compute_Alt_Path_axiom
  by (simp_all add: Compute_Alt_Path_axiom_def)

interpretation abs_search: compute_alt_path "ugraph_abs G" "matching_abs M"
  apply unfold_locales
  using ugraph_abs_graph_invar[OF graph_input_G] matching_invar_props[OF matching_invar_M]
  by (auto intro: someI_ex)

lemma finite_Vs_G[simp]: "finite (Vs (ugraph_abs G))"
  using ugraph_abs_graph_invar[OF graph_input_G]
  by simp

lemma Vs_G_subset_vs: "Vs (ugraph_abs G) \<subseteq> set vs"
  by (rule Vs_ugraph_abs_subset_vs[OF graph_input_G])

lemma mate_lookup_iff: "mate_lookup M u = Some v \<longleftrightarrow> {u, v} \<in> matching_abs M"
  using matching_invar_M
  by (simp add: matching_invar_def matching_abs_iff)

lemma Vs_matching_iff: "u \<in> Vs (matching_abs M) \<longleftrightarrow> mate_lookup M u \<noteq> None"
  using matching_invar_M
  by (simp add: matching_invar_def Vs_matching_abs_iff)

lemma set_free_vertices:
  "set free_vertices = {v. v \<in> Vs (ugraph_abs G) \<and> v \<notin> Vs (matching_abs M)}"
  using Vs_G_subset_vs
  by (auto simp: free_vertices_def neighbour_list_nonempty_iff[OF graph_input_G] Vs_matching_iff)

lemma initial_labels:
  "label_invar initial_labels"
  "label_lookup initial_labels =
     (\<lambda>v. if v \<in> Vs (ugraph_abs G) \<and> v \<notin> Vs (matching_abs M) then Some (v, Even) else None)"
  using label_foldr[of free_vertices]
  by (auto simp: initial_labels_def set_free_vertices fun_eq_iff)

subsubsection \<open>Facts about the branches\<close>

lemma call_1_facts:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_forest state"
          "invar_unscanned state"
  obtains v w rest x r where
    "unscanned state = (v, w) # rest" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
proof-
  obtain v w rest x where vw: "unscanned state = (v, w) # rest"
      "label_lookup (forest_labels state) w = None" "mate_lookup M w = Some x"
    using assms(1)
    by (auto elim!: call_cond_elims)
  obtain r where r: "label_lookup (forest_labels state) v = Some (r, Even)" "{v, w} \<in> ugraph_abs G"
    using assms(3) vw(1)
    by (auto simp: invar_unscanned_def)
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(2)
    by (simp add: invar_forest_def)
  have wx: "{w, x} \<in> matching_abs M"
    using vw(3)
    by (simp add: mate_lookup_iff)
  have par_w: "abs_parents state w = None" "\<forall>v'. abs_parents state v' \<noteq> Some w"
    using abs_search.search_invarsD(5)[OF I] vw(2)
    by (auto simp: abs_search.flabel_par_invar_def)
  hence "{v, w} \<notin> abs_examined state"
    by (auto simp: forest_edges_def doubleton_eq_iff)
  hence if1: "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    using r vw(2) wx
    by (simp add: abs_search.if1_def)
  have "label_lookup (forest_labels state) x = None"
  proof(rule ccontr)
    assume "label_lookup (forest_labels state) x \<noteq> None"
    hence "label_lookup (forest_labels state) w \<noteq> None"
      using abs_search.flabel_invar_props[OF abs_search.search_invarsD(4)[OF I] _ ]
            wx
      by (simp add: insert_commute)
    thus False
      using vw(2)
      by simp
  qed
  moreover have "w \<noteq> x"
    using abs_search.v1_neq_v2_neq_v3(2)[OF if1] .
  ultimately show ?thesis
    using that vw r if1
    by blast
qed

lemma call_2_odd:
  assumes "Compute_Alt_Path_call_2_conds state" "invar_forest state"
          "invar_unscanned state"
  obtains v w rest r where "unscanned state = (v, w) # rest"
    "label_lookup (forest_labels state) w = Some (r, Odd)"
proof-
  obtain v w rest where vw: "unscanned state = (v, w) # rest"
      "\<forall>r. label_lookup (forest_labels state) w \<noteq> Some (r, Even)"
      "label_lookup (forest_labels state) w = None \<longrightarrow> mate_lookup M w = None"
    using assms(1)
    by (auto elim!: call_cond_elims)
  have "{v, w} \<in> ugraph_abs G"
    using assms(3) vw(1)
    by (auto simp: invar_unscanned_def)
  hence w_in: "w \<in> Vs (ugraph_abs G)"
    by (auto simp: Vs_def)
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(2)
    by (simp add: invar_forest_def)
  have "label_lookup (forest_labels state) w \<noteq> None"
  proof
    assume none: "label_lookup (forest_labels state) w = None"
    hence "\<exists>e \<in> matching_abs M - abs_examined state. w \<in> e"
      using abs_search.search_invarsD(16)[OF I] w_in
      by (auto simp: abs_search.ulabelled_verts_matched_invar_def)
    hence "w \<in> Vs (matching_abs M)"
      by (auto simp: Vs_def)
    thus False
      using vw(3) none
      by (simp add: Vs_matching_iff)
  qed
  then obtain r l where "label_lookup (forest_labels state) w = Some (r, l)"
    by auto
  moreover hence "l = Odd"
    using vw(2)
    by (cases l) auto
  ultimately show ?thesis
    using that vw(1)
    by blast
qed

subsubsection \<open>The representation invariant\<close>

lemma invar_1_props[invar_props_elims]:
  "invar_1 state \<Longrightarrow>
   (\<lbrakk>parent_invar (forest_parents state); label_invar (forest_labels state)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>parent_invar (forest_parents state); label_invar (forest_labels state)\<rbrakk> \<Longrightarrow> invar_1 state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_1[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state"
  shows "invar_1 (Compute_Alt_Path_upd1 state)"
proof-
  obtain v w rest x r where f:
    "unscanned state = (v, w) # rest" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  show ?thesis
    by (rule upd1_abs(5)[OF assms(2) f(1,3,4)])
qed

lemma invar_1_holds_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_2_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Compute_Alt_Path_upd2 state)"
  by (auto simp: invar_1_def Compute_Alt_Path_upd2_def)

lemma invar_1_holds_3[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_3_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Compute_Alt_Path_upd3 state)"
  by (auto simp: invar_1_def Compute_Alt_Path_upd3_def split: list.splits)

lemma invar_1_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_1_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Compute_Alt_Path_ret1 state)"
  by auto

lemma invar_1_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_2_conds state; invar_1 state\<rbrakk>
   \<Longrightarrow> invar_1 (Compute_Alt_Path_ret2 state)"
  by auto

subsubsection \<open>The invariants of the abstract search\<close>

lemma invar_forest_props[invar_props_elims]:
  "invar_forest state \<Longrightarrow>
   (abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_forest_def)

lemma invar_forest_intro[invar_props_intros]:
  "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)
   \<Longrightarrow> invar_forest state"
  by (auto simp: invar_forest_def)

lemma invar_forest_holds_1[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state"
  shows "invar_forest (Compute_Alt_Path_upd1 state)"
proof-
  obtain v w rest x r where f:
    "unscanned state = (v, w) # rest" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(3)
    by (simp add: invar_forest_def)
  have none: "abs_parents state w = None" "abs_parents state x = None"
    using abs_search.search_invarsD(5)[OF I] f(2,6)
    by (auto simp: abs_search.flabel_par_invar_def)
  show ?thesis
    using abs_search.search_invars_if1[OF I f(8)] forest_edges_update[OF none f(7)]
    by (simp add: invar_forest_def upd1_abs[OF assms(2) f(1,3,4)])
qed

lemma invar_forest_holds_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_2_conds state; invar_forest state\<rbrakk>
   \<Longrightarrow> invar_forest (Compute_Alt_Path_upd2 state)"
  by (simp add: invar_forest_def)

lemma invar_forest_holds_3[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_3_conds state; invar_forest state\<rbrakk>
   \<Longrightarrow> invar_forest (Compute_Alt_Path_upd3 state)"
  by (auto elim!: call_cond_elims simp: invar_forest_def upd3_abs)

lemma invar_forest_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_1_conds state; invar_forest state\<rbrakk>
   \<Longrightarrow> invar_forest (Compute_Alt_Path_ret1 state)"
  by auto

lemma invar_forest_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_2_conds state; invar_forest state\<rbrakk>
   \<Longrightarrow> invar_forest (Compute_Alt_Path_ret2 state)"
  by auto

subsubsection \<open>The edges that remain to be examined\<close>

lemma invar_unscanned_props[invar_props_elims]:
  "invar_unscanned state \<Longrightarrow>
   ((\<forall>v w. (v, w) \<in> set (unscanned state) \<longrightarrow>
       {v, w} \<in> ugraph_abs G \<and> (\<exists>r. label_lookup (forest_labels state) v = Some (r, Even)))
    \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: invar_unscanned_def)

lemma invar_unscanned_intro[invar_props_intros]:
  "(\<forall>v w. (v, w) \<in> set (unscanned state) \<longrightarrow>
      {v, w} \<in> ugraph_abs G \<and> (\<exists>r. label_lookup (forest_labels state) v = Some (r, Even)))
   \<Longrightarrow> invar_unscanned state"
  by (auto simp: invar_unscanned_def)

lemma invar_unscanned_holds_1[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state"
  shows "invar_unscanned (Compute_Alt_Path_upd1 state)"
proof-
  obtain v w rest x r where f:
    "unscanned state = (v, w) # rest" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  note upd = upd1_abs[OF assms(2) f(1,3,4)]
  show ?thesis
  proof(rule invar_unscanned_intro, intro allI impI)
    fix a b
    assume "(a, b) \<in> set (unscanned (Compute_Alt_Path_upd1 state))"
    hence "(a, b) \<in> set (unscanned state)"
      by (simp add: upd f(1))
    then obtain r' where r': "{a, b} \<in> ugraph_abs G"
        "label_lookup (forest_labels state) a = Some (r', Even)"
      using assms(4)
      by (auto simp: invar_unscanned_def)
    hence "a \<noteq> w" "a \<noteq> x"
      using f(2,6)
      by auto
    thus "{a, b} \<in> ugraph_abs G \<and>
          (\<exists>r. label_lookup (forest_labels (Compute_Alt_Path_upd1 state)) a = Some (r, Even))"
      using r'
      by (auto simp: upd)
  qed
qed

lemma invar_unscanned_holds_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_2_conds state; invar_unscanned state\<rbrakk>
   \<Longrightarrow> invar_unscanned (Compute_Alt_Path_upd2 state)"
  by (auto elim!: call_cond_elims simp: invar_unscanned_def Compute_Alt_Path_upd2_def)

lemma invar_unscanned_holds_3[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_3_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_unscanned (Compute_Alt_Path_upd3 state)"
proof(elim call_cond_elims exE)
  fix v q
  assume c: "unscanned state = []" "queue state = v # q"
  assume "invar_queue state"
  hence "\<exists>r. label_lookup (forest_labels state) v = Some (r, Even)"
    using c(2)
    by (auto simp: invar_queue_def)
  thus "invar_unscanned (Compute_Alt_Path_upd3 state)"
    by (auto simp: invar_unscanned_def Compute_Alt_Path_upd3_def c(2)
                   neighbour_list_ugraph_abs[OF graph_input_G])
qed

lemma invar_unscanned_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_1_conds state; invar_unscanned state\<rbrakk>
   \<Longrightarrow> invar_unscanned (Compute_Alt_Path_ret1 state)"
  by auto

lemma invar_unscanned_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_2_conds state; invar_unscanned state\<rbrakk>
   \<Longrightarrow> invar_unscanned (Compute_Alt_Path_ret2 state)"
  by auto

subsubsection \<open>The queue holds even vertices\<close>

lemma invar_queue_props[invar_props_elims]:
  "invar_queue state \<Longrightarrow>
   ((\<forall>v \<in> set (queue state). \<exists>r. label_lookup (forest_labels state) v = Some (r, Even)) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_queue_def)

lemma invar_queue_intro[invar_props_intros]:
  "(\<forall>v \<in> set (queue state). \<exists>r. label_lookup (forest_labels state) v = Some (r, Even))
   \<Longrightarrow> invar_queue state"
  by (auto simp: invar_queue_def)

lemma invar_queue_holds_1[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_queue (Compute_Alt_Path_upd1 state)"
proof-
  obtain v w rest x r where f:
    "unscanned state = (v, w) # rest" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  show ?thesis
    using assms(5) f(2)
    by (fastforce simp: invar_queue_def upd1_abs[OF assms(2) f(1,3,4)])
qed

lemma invar_queue_holds_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_2_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_queue (Compute_Alt_Path_upd2 state)"
  by (simp add: invar_queue_def Compute_Alt_Path_upd2_def)

lemma invar_queue_holds_3[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_3_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_queue (Compute_Alt_Path_upd3 state)"
proof(elim call_cond_elims exE)
  fix v q
  assume c: "unscanned state = []" "queue state = v # q"
  assume "invar_queue state"
  thus "invar_queue (Compute_Alt_Path_upd3 state)"
    using c(2)
    by (auto simp: invar_queue_def Compute_Alt_Path_upd3_def)
qed

lemma invar_queue_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_1_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_queue (Compute_Alt_Path_ret1 state)"
  by auto

lemma invar_queue_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_2_conds state; invar_queue state\<rbrakk>
   \<Longrightarrow> invar_queue (Compute_Alt_Path_ret2 state)"
  by auto

subsubsection \<open>Scanned even vertices have only odd neighbours\<close>

lemma invar_scanned_props[invar_props_elims]:
  "invar_scanned state \<Longrightarrow>
   ((\<forall>v r. label_lookup (forest_labels state) v = Some (r, Even) \<longrightarrow>
       v \<in> set (queue state) \<or>
       (\<forall>w. {v, w} \<in> ugraph_abs G \<longrightarrow>
          (v, w) \<in> set (unscanned state) \<or>
          (\<exists>r'. label_lookup (forest_labels state) w = Some (r', Odd)))) \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (auto simp: invar_scanned_def)

lemma invar_scanned_intro[invar_props_intros]:
  "(\<forall>v r. label_lookup (forest_labels state) v = Some (r, Even) \<longrightarrow>
      v \<in> set (queue state) \<or>
      (\<forall>w. {v, w} \<in> ugraph_abs G \<longrightarrow>
         (v, w) \<in> set (unscanned state) \<or>
         (\<exists>r'. label_lookup (forest_labels state) w = Some (r', Odd))))
   \<Longrightarrow> invar_scanned state"
  by (auto simp: invar_scanned_def)

lemma invar_scanned_holds_1[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_scanned state"
  shows "invar_scanned (Compute_Alt_Path_upd1 state)"
proof-
  obtain v w rest x r where f:
    "unscanned state = (v, w) # rest" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r, Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r"
    by (rule call_1_facts[OF assms(1,3,4)])
  note upd = upd1_abs[OF assms(2) f(1,3,4)]
  show ?thesis
    unfolding invar_scanned_def
  proof(intro allI impI)
    fix y r'
    assume y: "label_lookup (forest_labels (Compute_Alt_Path_upd1 state)) y = Some (r', Even)"
    show "y \<in> set (queue (Compute_Alt_Path_upd1 state)) \<or>
          (\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow>
             (y, z) \<in> set (unscanned (Compute_Alt_Path_upd1 state)) \<or>
             (\<exists>r''. label_lookup (forest_labels (Compute_Alt_Path_upd1 state)) z =
                     Some (r'', Odd)))"
    proof(cases "y = x")
      case True
      then show ?thesis
        by (simp add: upd)
    next
      case False
      hence "label_lookup (forest_labels state) y = Some (r', Even)"
        using y f(7)
        by (auto simp: upd split: if_splits)
      hence "y \<in> set (queue state) \<or>
             (\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow> (y, z) \<in> set (unscanned state) \<or>
                (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd)))"
        using assms(5)
        by (auto simp: invar_scanned_def)
      thus ?thesis
      proof
        assume "y \<in> set (queue state)"
        thus ?thesis
          by (simp add: upd)
      next
        assume all: "\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow> (y, z) \<in> set (unscanned state) \<or>
                         (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd))"
        have "(y, z) \<in> set rest \<or>
              (\<exists>r''. label_lookup (forest_labels (Compute_Alt_Path_upd1 state)) z =
                      Some (r'', Odd))"
          if "{y, z} \<in> ugraph_abs G" for z
        proof-
          consider "(y, z) = (v, w)" | "(y, z) \<in> set rest"
            | "\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd)"
            using mp[OF spec[OF all, of z] \<open>{y, z} \<in> ugraph_abs G\<close>] f(1)
            by auto
          thus ?thesis
          proof cases
            case 1
            then show ?thesis
              using f(7)
              by (auto simp: upd)
          next
            case 2
            then show ?thesis
              by simp
          next
            case 3
            then obtain r'' where z: "label_lookup (forest_labels state) z = Some (r'', Odd)"
              by blast
            hence "z \<noteq> w" "z \<noteq> x"
              using f(2,6)
              by auto
            thus ?thesis
              using z
              by (auto simp: upd)
          qed
        qed
        thus ?thesis
          by (simp add: upd)
      qed
    qed
  qed
qed

lemma invar_scanned_holds_2[invar_holds_intros]:
  assumes "Compute_Alt_Path_call_2_conds state" "invar_forest state"
          "invar_unscanned state" "invar_scanned state"
  shows "invar_scanned (Compute_Alt_Path_upd2 state)"
proof-
  obtain v w rest r where f: "unscanned state = (v, w) # rest"
      "label_lookup (forest_labels state) w = Some (r, Odd)"
    by (rule call_2_odd[OF assms(1-3)])
  show ?thesis
    unfolding invar_scanned_def
  proof(intro allI impI)
    fix y r'
    assume y: "label_lookup (forest_labels (Compute_Alt_Path_upd2 state)) y = Some (r', Even)"
    hence y': "label_lookup (forest_labels state) y = Some (r', Even)"
      by (simp add: Compute_Alt_Path_upd2_def)
    have h: "y \<in> set (queue state) \<or>
             (\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow> (y, z) \<in> set (unscanned state) \<or>
                (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd)))"
      using mp[OF spec[OF spec[OF assms(4)[unfolded invar_scanned_def], of y], of r'] y'] .
    from h show "y \<in> set (queue (Compute_Alt_Path_upd2 state)) \<or>
          (\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow>
             (y, z) \<in> set (unscanned (Compute_Alt_Path_upd2 state)) \<or>
             (\<exists>r''. label_lookup (forest_labels (Compute_Alt_Path_upd2 state)) z =
                     Some (r'', Odd)))"
    proof
      assume "y \<in> set (queue state)"
      thus ?thesis
        by (simp add: Compute_Alt_Path_upd2_def)
    next
      assume all: "\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow> (y, z) \<in> set (unscanned state) \<or>
                      (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd))"
      have "(y, z) \<in> set rest \<or> (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd))"
        if "{y, z} \<in> ugraph_abs G" for z
      proof-
        have "(y, z) \<in> set (unscanned state) \<or>
              (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd))"
          using mp[OF spec[OF all, of z] that] .
        thus ?thesis
          using f
          by auto
      qed
      thus ?thesis
        by (simp add: Compute_Alt_Path_upd2_def f(1))
    qed
  qed
qed

lemma invar_scanned_holds_3[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_call_3_conds state; invar_scanned state\<rbrakk>
   \<Longrightarrow> invar_scanned (Compute_Alt_Path_upd3 state)"
proof(elim call_cond_elims exE)
  fix v q
  assume c: "unscanned state = []" "queue state = v # q"
  assume inv: "invar_scanned state"
  show "invar_scanned (Compute_Alt_Path_upd3 state)"
    unfolding invar_scanned_def
  proof(intro allI impI)
    fix y r'
    assume y: "label_lookup (forest_labels (Compute_Alt_Path_upd3 state)) y = Some (r', Even)"
    hence y': "label_lookup (forest_labels state) y = Some (r', Even)"
      by (simp add: Compute_Alt_Path_upd3_def c(2))
    have h: "y \<in> set (queue state) \<or>
             (\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow> (y, z) \<in> set (unscanned state) \<or>
                (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd)))"
      using mp[OF spec[OF spec[OF inv[unfolded invar_scanned_def], of y], of r'] y'] .
    show "y \<in> set (queue (Compute_Alt_Path_upd3 state)) \<or>
          (\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow>
             (y, z) \<in> set (unscanned (Compute_Alt_Path_upd3 state)) \<or>
             (\<exists>r''. label_lookup (forest_labels (Compute_Alt_Path_upd3 state)) z =
                     Some (r'', Odd)))"
    proof(cases "y = v")
      case True
      have "(y, z) \<in> set (unscanned (Compute_Alt_Path_upd3 state))"
        if "{y, z} \<in> ugraph_abs G" for z
        using True that neighbour_list_ugraph_abs[OF graph_input_G, of z v]
        by (simp add: Compute_Alt_Path_upd3_def c(2) insert_commute)
      thus ?thesis
        by blast
    next
      case False
      from h show ?thesis
      proof
        assume "y \<in> set (queue state)"
        hence "y \<in> set (queue (Compute_Alt_Path_upd3 state))"
          using c(2) False
          by (simp add: Compute_Alt_Path_upd3_def)
        thus ?thesis
          by blast
      next
        assume all: "\<forall>z. {y, z} \<in> ugraph_abs G \<longrightarrow> (y, z) \<in> set (unscanned state) \<or>
                        (\<exists>r''. label_lookup (forest_labels state) z = Some (r'', Odd))"
        have "\<exists>r''. label_lookup (forest_labels (Compute_Alt_Path_upd3 state)) z =
                     Some (r'', Odd)"
          if "{y, z} \<in> ugraph_abs G" for z
          using mp[OF spec[OF all, of z] that] c(1)
          by (simp add: Compute_Alt_Path_upd3_def c(2))
        thus ?thesis
          by blast
      qed
    qed
  qed
qed

lemma invar_scanned_holds_ret_1[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_1_conds state; invar_scanned state\<rbrakk>
   \<Longrightarrow> invar_scanned (Compute_Alt_Path_ret1 state)"
  by auto

lemma invar_scanned_holds_ret_2[invar_holds_intros]:
  "\<lbrakk>Compute_Alt_Path_ret_2_conds state; invar_scanned state\<rbrakk>
   \<Longrightarrow> invar_scanned (Compute_Alt_Path_ret2 state)"
  by auto

subsubsection \<open>The invariants hold for the whole loop\<close>

lemma invar_1_holds[invar_holds_intros]:
  assumes "Compute_Alt_Path_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_1 (Compute_Alt_Path state)"
  using assms(2-)
proof(induction rule: Compute_Alt_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Compute_Alt_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Compute_Alt_Path_simps[OF IH(1)])
qed

lemma invar_forest_holds[invar_holds_intros]:
  assumes "Compute_Alt_Path_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_forest (Compute_Alt_Path state)"
  using assms(2-)
proof(induction rule: Compute_Alt_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Compute_Alt_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Compute_Alt_Path_simps[OF IH(1)])
qed

lemma invar_unscanned_holds[invar_holds_intros]:
  assumes "Compute_Alt_Path_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_unscanned (Compute_Alt_Path state)"
  using assms(2-)
proof(induction rule: Compute_Alt_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Compute_Alt_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Compute_Alt_Path_simps[OF IH(1)])
qed

lemma invar_queue_holds[invar_holds_intros]:
  assumes "Compute_Alt_Path_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state"
  shows "invar_queue (Compute_Alt_Path state)"
  using assms(2-)
proof(induction rule: Compute_Alt_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Compute_Alt_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Compute_Alt_Path_simps[OF IH(1)])
qed

lemma invar_scanned_holds[invar_holds_intros]:
  assumes "Compute_Alt_Path_dom state" "invar_1 state" "invar_forest state"
          "invar_unscanned state" "invar_queue state" "invar_scanned state"
  shows "invar_scanned (Compute_Alt_Path state)"
  using assms(2-)
proof(induction rule: Compute_Alt_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Compute_Alt_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Compute_Alt_Path_simps[OF IH(1)])
qed

subsubsection \<open>Termination\<close>

named_theorems termination_intros

declare termination_intros

lemma in_prod_relI[intro!,termination_intros]:
  "\<lbrakk>f1 a = f1 a'; (a, a') \<in> f2 <*mlex*> r\<rbrakk> \<Longrightarrow> (a,a') \<in> (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)+

definition "less_rel = {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)

lemma call_1_terminates[termination_intros]:
  assumes "Compute_Alt_Path_call_1_conds state" "invar_1 state" "invar_forest state"
          "invar_unscanned state"
  shows "(Compute_Alt_Path_upd1 state, state) \<in> call_1_measure <*mlex*> r"
proof-
  obtain v w rest x r' where f:
    "unscanned state = (v, w) # rest" "label_lookup (forest_labels state) w = None"
    "mate_lookup M w = Some x" "label_lookup (forest_labels state) v = Some (r', Even)"
    "{v, w} \<in> ugraph_abs G" "label_lookup (forest_labels state) x = None" "w \<noteq> x"
    "abs_search.if1 (abs_labels state) (abs_examined state) v w x r'"
    by (rule call_1_facts[OF assms(1,3,4)])
  let ?U = "\<lambda>s. {v \<in> Vs (ugraph_abs G). label_lookup (forest_labels s) v = None}"
  have "w \<in> Vs (ugraph_abs G)"
    using f(5)
    by (auto simp: Vs_def)
  hence "w \<in> ?U state"
    using f(2)
    by simp
  moreover have "?U (Compute_Alt_Path_upd1 state) \<subseteq> ?U state - {w}"
    by (auto simp: upd1_abs[OF assms(2) f(1,3,4)] split: if_splits)
  ultimately have "?U (Compute_Alt_Path_upd1 state) \<subset> ?U state"
    by blast
  moreover have "finite (?U state)"
    by simp
  ultimately have "call_1_measure (Compute_Alt_Path_upd1 state) < call_1_measure state"
    by (simp add: call_1_measure_def psubset_card_mono)
  thus ?thesis
    by (rule mlex_less)
qed

lemma call_2_measure_1[termination_intros]:
  "call_1_measure state = call_1_measure (Compute_Alt_Path_upd2 state)"
  by (simp add: call_1_measure_def Compute_Alt_Path_upd2_def)

lemma call_2_measure_3[termination_intros]:
  "call_3_measure state = call_3_measure (Compute_Alt_Path_upd2 state)"
  by (simp add: call_3_measure_def Compute_Alt_Path_upd2_def)

lemma call_2_terminates[termination_intros]:
  "Compute_Alt_Path_call_2_conds state \<Longrightarrow>
     (Compute_Alt_Path_upd2 state, state) \<in> call_2_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less
           simp: call_2_measure_def Compute_Alt_Path_upd2_def)

lemma call_3_measure_1[termination_intros]:
  "Compute_Alt_Path_call_3_conds state \<Longrightarrow>
     call_1_measure state = call_1_measure (Compute_Alt_Path_upd3 state)"
  by (auto elim!: call_cond_elims simp: call_1_measure_def Compute_Alt_Path_upd3_def)

lemma call_3_terminates[termination_intros]:
  "Compute_Alt_Path_call_3_conds state \<Longrightarrow>
     (Compute_Alt_Path_upd3 state, state) \<in> call_3_measure <*mlex*> r"
  by (auto elim!: call_cond_elims intro!: mlex_less
           simp: call_3_measure_def Compute_Alt_Path_upd3_def)

lemma wf_term_rel: "wf Compute_Alt_Path_term_rel'"
  by (auto simp: wf_mlex Compute_Alt_Path_term_rel'_def)

lemma in_Compute_Alt_Path_term_rel'[termination_intros]:
  "\<lbrakk>Compute_Alt_Path_call_1_conds state; invar_1 state; invar_forest state;
    invar_unscanned state\<rbrakk> \<Longrightarrow>
     (Compute_Alt_Path_upd1 state, state) \<in> Compute_Alt_Path_term_rel'"
  "Compute_Alt_Path_call_2_conds state \<Longrightarrow>
     (Compute_Alt_Path_upd2 state, state) \<in> Compute_Alt_Path_term_rel'"
  "Compute_Alt_Path_call_3_conds state \<Longrightarrow>
     (Compute_Alt_Path_upd3 state, state) \<in> Compute_Alt_Path_term_rel'"
  unfolding Compute_Alt_Path_term_rel'_def
  by (((rule call_1_terminates; assumption) |
       (rule in_prod_relI[of call_1_measure,
                           OF call_2_measure_1[symmetric]
                              in_prod_relI[of call_3_measure,
                                           OF call_2_measure_3[symmetric] call_2_terminates]];
        assumption) |
       (rule in_prod_relI[of call_1_measure,
                           OF call_3_measure_1[symmetric] call_3_terminates];
        assumption+))+)

lemma Compute_Alt_Path_terminates[termination_intros]:
  assumes "invar_1 state" "invar_forest state" "invar_unscanned state" "invar_queue state"
  shows "Compute_Alt_Path_dom state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
  proof(rule Compute_Alt_Path_domintros)
    assume c: "Compute_Alt_Path_call_1_conds x"
    show "Compute_Alt_Path_dom (Compute_Alt_Path_upd1 x)"
      by (rule less.IH[OF in_Compute_Alt_Path_term_rel'(1)[OF c less.prems(1-3)]
                          invar_1_holds_1[OF c less.prems(1-3)]
                          invar_forest_holds_1[OF c less.prems(1-3)]
                          invar_unscanned_holds_1[OF c less.prems(1-3)]
                          invar_queue_holds_1[OF c less.prems(1-4)]])
  next
    assume c: "Compute_Alt_Path_call_2_conds x"
    show "Compute_Alt_Path_dom (Compute_Alt_Path_upd2 x)"
      by (rule less.IH[OF in_Compute_Alt_Path_term_rel'(2)[OF c]
                          invar_1_holds_2[OF c less.prems(1)]
                          invar_forest_holds_2[OF c less.prems(2)]
                          invar_unscanned_holds_2[OF c less.prems(3)]
                          invar_queue_holds_2[OF c less.prems(4)]])
  next
    assume c: "Compute_Alt_Path_call_3_conds x"
    show "Compute_Alt_Path_dom (Compute_Alt_Path_upd3 x)"
      by (rule less.IH[OF in_Compute_Alt_Path_term_rel'(3)[OF c]
                          invar_1_holds_3[OF c less.prems(1)]
                          invar_forest_holds_3[OF c less.prems(2)]
                          invar_unscanned_holds_3[OF c less.prems(4)]
                          invar_queue_holds_3[OF c less.prems(4)]])
  qed
qed

subsubsection \<open>Correctness\<close>

lemma Compute_Alt_Path_correct_ret_1:
  assumes "invar_forest state" "invar_unscanned state" "Compute_Alt_Path_ret_1_conds state"
  shows "compute_alt_path_spec (ugraph_abs G) (matching_abs M) (alternating_paths state)"
proof-
  obtain v w rest r' where f: "unscanned state = (v, w) # rest"
      "label_lookup (forest_labels state) w = Some (r', Even)"
    using assms(3)
    by (auto elim!: call_cond_elims)
  obtain r where r: "label_lookup (forest_labels state) v = Some (r, Even)" "{v, w} \<in> ugraph_abs G"
    using assms(2) f(1)
    by (auto simp: invar_unscanned_def)
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(1)
    by (simp add: invar_forest_def)
  have "abs_search.if2 (abs_labels state) v w r r'"
    using f(2) r
    by (simp add: abs_search.if2_def)
  hence spec: "compute_alt_path_spec (ugraph_abs G) (matching_abs M)
                 (Some (parent_spec.follow (abs_parents state) v,
                        parent_spec.follow (abs_parents state) w))"
    by (rule abs_search.search_invars_if2_sound[OF I])
  have "follow_impl (abs_parents state) = parent_spec.follow (abs_parents state)"
    by (rule follow_impl_eq[OF abs_search.search_invarsD(3)[OF I]])
  thus ?thesis
    using spec f(1)
    by (simp add: alternating_paths_def)
qed

lemma Compute_Alt_Path_correct_ret_2:
  assumes "invar_forest state" "invar_scanned state" "Compute_Alt_Path_ret_2_conds state"
  shows "alternating_paths state = None"
        "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
proof-
  have nil: "unscanned state = []" "queue state = []"
    using assms(3)
    by (auto elim!: call_cond_elims)
  thus "alternating_paths state = None"
    by (simp add: alternating_paths_def)
  have I: "abs_search.search_invars (abs_examined state) (abs_parents state) (abs_labels state)"
    using assms(1)
    by (simp add: invar_forest_def)
  have odd: "\<exists>r'. abs_labels state w = Some (r', Odd)"
    if "abs_labels state v = Some (r, Even)" "{v, w} \<in> ugraph_abs G" for v w r
  proof-
    have "v \<in> set (queue state) \<or>
          (\<forall>w. {v, w} \<in> ugraph_abs G \<longrightarrow> (v, w) \<in> set (unscanned state) \<or>
             (\<exists>r'. label_lookup (forest_labels state) w = Some (r', Odd)))"
      using mp[OF spec[OF spec[OF assms(2)[unfolded invar_scanned_def], of v], of r] that(1)] .
    thus ?thesis
      using that(2) nil
      by auto
  qed
  have "\<not> abs_search.if1_cond (abs_labels state) (abs_examined state)"
  proof
    assume "abs_search.if1_cond (abs_labels state) (abs_examined state)"
    then obtain v1 v2 r where e: "{v1, v2} \<in> ugraph_abs G - abs_examined state"
        "abs_labels state v1 = Some (r, Even)" "abs_labels state v2 = None"
      by (auto simp: abs_search.if1_cond_def)
    thus False
      using odd[OF e(2) DiffD1[OF e(1)]]
      by simp
  qed
  moreover have "\<not> abs_search.if2_cond (abs_labels state)"
  proof
    assume "abs_search.if2_cond (abs_labels state)"
    then obtain v1 v2 r r' where e: "{v1, v2} \<in> ugraph_abs G"
        "abs_labels state v1 = Some (r, Even)" "abs_labels state v2 = Some (r', Even)"
      by (auto simp: abs_search.if2_cond_def)
    thus False
      using odd[OF e(2) e(1)]
      by simp
  qed
  ultimately have "\<nexists>p. matching_augmenting_path (matching_abs M) p \<and> path (ugraph_abs G) p \<and>
                       distinct p"
    by (rule abs_search.search_invars_complete[OF I])
  thus "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    by blast
qed

lemma ret_holds[ret_holds_intros]:
  assumes "Compute_Alt_Path_dom state"
  shows "Compute_Alt_Path_ret_1_conds (Compute_Alt_Path state) \<or>
         Compute_Alt_Path_ret_2_conds (Compute_Alt_Path state)"
proof(induction rule: Compute_Alt_Path_induct[OF assms])
  case IH: (1 state)
  show ?case
  proof(rule Compute_Alt_Path_cases[where state = state])
    assume c: "Compute_Alt_Path_call_1_conds state"
    show ?thesis
      using IH(2)[OF c]
      by (simp add: Compute_Alt_Path_simps(1)[OF IH(1) c])
  next
    assume c: "Compute_Alt_Path_call_2_conds state"
    show ?thesis
      using IH(3)[OF c]
      by (simp add: Compute_Alt_Path_simps(2)[OF IH(1) c])
  next
    assume c: "Compute_Alt_Path_call_3_conds state"
    show ?thesis
      using IH(4)[OF c]
      by (simp add: Compute_Alt_Path_simps(3)[OF IH(1) c])
  next
    assume c: "Compute_Alt_Path_ret_1_conds state"
    show ?thesis
      using c
      by (simp add: Compute_Alt_Path_simps(4)[OF IH(1) c])
  next
    assume c: "Compute_Alt_Path_ret_2_conds state"
    show ?thesis
      using c
      by (simp add: Compute_Alt_Path_simps(5)[OF IH(1) c])
  qed
qed

subsubsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 initial_state" "invar_forest initial_state" "invar_unscanned initial_state"
  "invar_queue initial_state" "invar_scanned initial_state"
  "Compute_Alt_Path_dom initial_state"
proof-
  show inv1: "invar_1 initial_state"
    using initial_labels(1)
    by (auto intro!: invar_props_intros simp: initial_state_def Parent.invar_empty)
  show invf: "invar_forest initial_state"
    using abs_search.search_invars_init
    by (simp add: invar_forest_def initial_state_def initial_labels(2) Parent.map_empty)
  show invu: "invar_unscanned initial_state"
    by (simp add: invar_unscanned_def initial_state_def)
  show invq: "invar_queue initial_state"
    by (auto simp: invar_queue_def initial_state_def initial_labels(2) set_free_vertices)
  show "invar_scanned initial_state"
    by (auto simp: invar_scanned_def initial_state_def initial_labels(2) set_free_vertices
            split: if_splits)
  show "Compute_Alt_Path_dom initial_state"
    by (rule Compute_Alt_Path_terminates[OF inv1 invf invu invq])
qed

lemma Compute_Alt_Path_impl_to_Compute_Alt_Path:
  "Compute_Alt_Path_impl initial_state = Compute_Alt_Path initial_state"
  by (auto intro!: Compute_Alt_Path_impl_same initial_state_props)

subsubsection \<open>Final correctness\<close>

lemma final_state_invars:
  "invar_forest (Compute_Alt_Path initial_state)"
  "invar_unscanned (Compute_Alt_Path initial_state)"
  "invar_scanned (Compute_Alt_Path initial_state)"
proof-
  show "invar_forest (Compute_Alt_Path initial_state)"
    by (rule invar_forest_holds[OF initial_state_props(6,1-4)])
  show "invar_unscanned (Compute_Alt_Path initial_state)"
    by (rule invar_unscanned_holds[OF initial_state_props(6,1-4)])
  show "invar_scanned (Compute_Alt_Path initial_state)"
    by (rule invar_scanned_holds[OF initial_state_props(6,1-5)])
qed

lemma Compute_Alt_Path_correct_1:
  "compute_alt_path_spec (ugraph_abs G) (matching_abs M)
     (alternating_paths (Compute_Alt_Path initial_state))"
proof-
  have "Compute_Alt_Path_ret_1_conds (Compute_Alt_Path initial_state) \<or>
        Compute_Alt_Path_ret_2_conds (Compute_Alt_Path initial_state)"
    by (rule ret_holds[OF initial_state_props(6)])
  thus ?thesis
  proof
    assume "Compute_Alt_Path_ret_1_conds (Compute_Alt_Path initial_state)"
    thus ?thesis
      by (rule Compute_Alt_Path_correct_ret_1[OF final_state_invars(1,2)])
  next
    assume r: "Compute_Alt_Path_ret_2_conds (Compute_Alt_Path initial_state)"
    have "alternating_paths (Compute_Alt_Path initial_state) = None"
      by (rule Compute_Alt_Path_correct_ret_2(1)[OF final_state_invars(1,3) r])
    thus ?thesis
      by (simp add: compute_alt_path_spec_def)
  qed
qed

lemma Compute_Alt_Path_correct_2:
  assumes "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
  shows "alternating_paths (Compute_Alt_Path initial_state) \<noteq> None"
proof-
  have "Compute_Alt_Path_ret_1_conds (Compute_Alt_Path initial_state) \<or>
        Compute_Alt_Path_ret_2_conds (Compute_Alt_Path initial_state)"
    by (rule ret_holds[OF initial_state_props(6)])
  thus ?thesis
  proof
    assume "Compute_Alt_Path_ret_1_conds (Compute_Alt_Path initial_state)"
    thus ?thesis
      by (auto elim!: call_cond_elims simp: alternating_paths_def)
  next
    assume r: "Compute_Alt_Path_ret_2_conds (Compute_Alt_Path initial_state)"
    show ?thesis
      using Compute_Alt_Path_correct_ret_2(2)[OF final_state_invars(1,3) r] assms
      by blast
  qed
qed

lemma Compute_Alt_Path_run_impl_correct:
  "compute_alt_path_spec (ugraph_abs G) (matching_abs M) Compute_Alt_Path_run_impl"
  "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p \<Longrightarrow>
     Compute_Alt_Path_run_impl \<noteq> None"
  using Compute_Alt_Path_correct_1 Compute_Alt_Path_correct_2
  by (simp_all add: Compute_Alt_Path_run_impl_def
                    Compute_Alt_Path_impl_to_Compute_Alt_Path)

end

end

end

