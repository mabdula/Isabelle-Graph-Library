theory DFS_Skeleton
  imports Directed_Set_Graphs.Pair_Graph_Specs Data_Structures.Set2_Addons
begin

text ‹A generic DFS skeleton: the search spine (stack/seen) is fixed; per-algorithm semantics
are supplied as the callbacks found/on_found/on_empty/on_backtrack, which may only write the
extensible-record slot 'more.›

record ('ver, 'vset) DFS_skel_state = stack:: "'ver list" seen:: "'vset"

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

locale DFS_skel =
  Graph: Pair_Graph_Specs where lookup = lookup +
 set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
for lookup :: "'adjmap ⇒ 'v ⇒ 'vset option" +
fixes G::"'adjmap" and s::"'v"
  and found       :: "('v,'vset,'more) DFS_skel_state_scheme ⇒ bool"
  and on_found    :: "('v,'vset,'more) DFS_skel_state_scheme ⇒ ('v,'vset,'more) DFS_skel_state_scheme"
  and on_empty    :: "('v,'vset,'more) DFS_skel_state_scheme ⇒ ('v,'vset,'more) DFS_skel_state_scheme"
  and on_backtrack:: "'v ⇒ ('v,'vset,'more) DFS_skel_state_scheme ⇒ ('v,'vset,'more) DFS_skel_state_scheme"
begin

abbreviation "neighbourhood' ≡ Graph.neighbourhood G"
notation "neighbourhood'" ("𝒩⇩G _" 100)

function (domintros) DFS_skel::"('v,'vset,'more) DFS_skel_state_scheme ⇒ ('v,'vset,'more) DFS_skel_state_scheme" where
  "DFS_skel dfs_state =
     (case (stack dfs_state) of (v # stack_tl) ⇒
       (if found dfs_state then on_found dfs_state
        else (if ((𝒩⇩G v) -⇩G (seen dfs_state)) ≠ ∅⇩N then
                let u = (sel ((𝒩⇩G v) -⇩G (seen dfs_state)));
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skel (dfs_state ⦇stack := stack', seen := seen'⦈)
              else
                DFS_skel (on_backtrack v (dfs_state ⦇stack := stack_tl⦈))))
     | _ ⇒ on_empty dfs_state)"
  by pat_completeness auto

partial_function (tailrec) DFS_skel_impl::"('v,'vset,'more) DFS_skel_state_scheme ⇒ ('v,'vset,'more) DFS_skel_state_scheme" where
  "DFS_skel_impl dfs_state =
     (case (stack dfs_state) of (v # stack_tl) ⇒
       (if found dfs_state then on_found dfs_state
        else (if ((𝒩⇩G v) -⇩G (seen dfs_state)) ≠ ∅⇩N then
                let u = (sel ((𝒩⇩G v) -⇩G (seen dfs_state)));
                    stack' = u # (stack dfs_state);
                    seen' = insert u (seen dfs_state)
                in DFS_skel_impl (dfs_state ⦇stack := stack', seen := seen'⦈)
              else
                DFS_skel_impl (on_backtrack v (dfs_state ⦇stack := stack_tl⦈))))
     | _ ⇒ on_empty dfs_state)"

lemmas [code] = DFS_skel_impl.simps

lemma DFS_skel_impl_same:
  assumes "DFS_skel_dom state"
  shows   "DFS_skel_impl state = DFS_skel state"
  by(induction rule: DFS_skel.pinduct[OF assms])
    (subst DFS_skel.psimps, simp, subst DFS_skel_impl.simps,
     auto split: list.split if_split simp add: Let_def)

definition "DFS_skel_call_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) ⇒
       (if found dfs_state then False
        else (if ((𝒩⇩G v) -⇩G (seen dfs_state)) ≠ ∅⇩N then True else False))
     | _ ⇒ False)"

lemma DFS_skel_call_1_conds[call_cond_elims]:
  "DFS_skel_call_1_conds dfs_state ⟹
   ⟦⟦∃v stack_tl. stack dfs_state = v # stack_tl;
    ¬ found dfs_state;
    (𝒩⇩G (hd (stack dfs_state))) -⇩G (seen dfs_state) ≠ ∅⇩N⟧ ⟹ P⟧ ⟹ P"
  by(auto simp: DFS_skel_call_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_skel_upd1 dfs_state = (
    let
      N = (𝒩⇩G (hd (stack dfs_state)));
      u = (sel ((N -⇩G (seen dfs_state))));
      stack' = u # (stack dfs_state);
      seen' = insert u (seen dfs_state)
    in
      dfs_state ⦇stack := stack', seen := seen'⦈)"

definition "DFS_skel_call_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) ⇒
       (if found dfs_state then False
        else (if ((𝒩⇩G v) -⇩G (seen dfs_state)) ≠ ∅⇩N then False else True))
     | _ ⇒ False)"

lemma DFS_skel_call_2_conds[call_cond_elims]:
  "DFS_skel_call_2_conds dfs_state ⟹
   ⟦⟦∃v stack_tl. stack dfs_state = v # stack_tl;
    ¬ found dfs_state;
    (𝒩⇩G (hd (stack dfs_state))) -⇩G (seen dfs_state) = ∅⇩N⟧ ⟹ P⟧ ⟹ P"
  by(auto simp: DFS_skel_call_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_skel_upd2 dfs_state =
  on_backtrack (hd (stack dfs_state)) (dfs_state ⦇stack := tl (stack dfs_state)⦈)"

definition "DFS_skel_ret_1_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) ⇒ False | _ ⇒ True)"

lemma DFS_skel_ret_1_conds[call_cond_elims]:
  "DFS_skel_ret_1_conds dfs_state ⟹ ⟦⟦stack dfs_state = []⟧ ⟹ P⟧ ⟹ P"
  by(auto simp: DFS_skel_ret_1_conds_def split: list.splits if_splits)

lemma DFS_skel_ret_1_condsI[call_cond_intros]:
  "⟦stack dfs_state = []⟧ ⟹ DFS_skel_ret_1_conds dfs_state"
  by(auto simp: DFS_skel_ret_1_conds_def split: list.splits if_splits)

definition "DFS_skel_ret1 dfs_state = on_empty dfs_state"

definition "DFS_skel_ret_2_conds dfs_state =
    (case (stack dfs_state) of (v # stack_tl) ⇒ (if found dfs_state then True else False) | _ ⇒ False)"

lemma DFS_skel_ret_2_conds[call_cond_elims]:
  "DFS_skel_ret_2_conds dfs_state ⟹
   ⟦⟦∃v stack_tl. stack dfs_state = v # stack_tl; found dfs_state⟧ ⟹ P⟧ ⟹ P"
  by(auto simp: DFS_skel_ret_2_conds_def split: list.splits if_splits)

lemma DFS_skel_ret_2_condsI[call_cond_intros]:
  "⟦∃v stack_tl. stack dfs_state = v # stack_tl; found dfs_state⟧ ⟹ DFS_skel_ret_2_conds dfs_state"
  by(auto simp: DFS_skel_ret_2_conds_def split: list.splits if_splits)

definition "DFS_skel_ret2 dfs_state = on_found dfs_state"

lemma DFS_skel_cases:
  assumes "DFS_skel_call_1_conds dfs_state ⟹ P"
      "DFS_skel_call_2_conds dfs_state ⟹ P"
      "DFS_skel_ret_1_conds dfs_state ⟹ P"
      "DFS_skel_ret_2_conds dfs_state ⟹ P"
  shows "P"
proof-
  have "DFS_skel_call_1_conds dfs_state ∨ DFS_skel_call_2_conds dfs_state ∨
        DFS_skel_ret_1_conds dfs_state ∨ DFS_skel_ret_2_conds dfs_state"
    by (auto simp add: DFS_skel_call_1_conds_def DFS_skel_call_2_conds_def
                        DFS_skel_ret_1_conds_def DFS_skel_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms by auto
qed

lemma DFS_skel_simps:
  assumes "DFS_skel_dom dfs_state"
  shows "DFS_skel_call_1_conds dfs_state ⟹ DFS_skel dfs_state = DFS_skel (DFS_skel_upd1 dfs_state)"
      "DFS_skel_call_2_conds dfs_state ⟹ DFS_skel dfs_state = DFS_skel (DFS_skel_upd2 dfs_state)"
      "DFS_skel_ret_1_conds dfs_state ⟹ DFS_skel dfs_state = DFS_skel_ret1 dfs_state"
      "DFS_skel_ret_2_conds dfs_state ⟹ DFS_skel dfs_state = DFS_skel_ret2 dfs_state"
  by (auto simp add: DFS_skel.psimps[OF assms] Let_def
                       DFS_skel_call_1_conds_def DFS_skel_upd1_def DFS_skel_call_2_conds_def DFS_skel_upd2_def
                       DFS_skel_ret_1_conds_def DFS_skel_ret1_def
                       DFS_skel_ret_2_conds_def DFS_skel_ret2_def
            split: list.splits option.splits if_splits)

lemma DFS_skel_induct:
  assumes "DFS_skel_dom dfs_state"
  assumes "⋀dfs_state. ⟦DFS_skel_dom dfs_state;
                        DFS_skel_call_1_conds dfs_state ⟹ P (DFS_skel_upd1 dfs_state);
                        DFS_skel_call_2_conds dfs_state ⟹ P (DFS_skel_upd2 dfs_state)⟧ ⟹ P dfs_state"
  shows "P dfs_state"
  apply(rule DFS_skel.pinduct[OF assms(1)])
  apply(rule assms(2)[simplified DFS_skel_call_1_conds_def DFS_skel_upd1_def DFS_skel_call_2_conds_def DFS_skel_upd2_def])
  by (auto simp: Let_def split: list.splits option.splits if_splits)

lemma DFS_skel_domintros:
  assumes "DFS_skel_call_1_conds dfs_state ⟹ DFS_skel_dom (DFS_skel_upd1 dfs_state)"
  assumes "DFS_skel_call_2_conds dfs_state ⟹ DFS_skel_dom (DFS_skel_upd2 dfs_state)"
  shows "DFS_skel_dom dfs_state"
proof(rule DFS_skel.domintros, goal_cases)
  case (1 x21 x22)
  then show ?case
    using assms(1)[simplified DFS_skel_call_1_conds_def DFS_skel_upd1_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
next
  case (2 x21 x22)
  then show ?case
    using assms(2)[simplified DFS_skel_call_2_conds_def DFS_skel_upd2_def]
    by (force simp: Let_def split: list.splits option.splits if_splits)
qed

definition "DFS_skel_axioms = (Graph.graph_inv G ∧ Graph.finite_graph G ∧ Graph.finite_vsets G)"

definition "invar_1 dfs_state = vset_inv (seen dfs_state)"

definition "invar_seen_stack dfs_state ⟷
    distinct (stack dfs_state)
    ∧ set (stack dfs_state) ⊆ t_set (seen dfs_state)
    ∧ t_set (seen dfs_state) ⊆ dVs (Graph.digraph_abs G)"

definition "call_1_measure dfs_state = card (dVs (Graph.digraph_abs G) - t_set (seen dfs_state))"

definition "call_2_measure dfs_state = card (set (stack dfs_state))"

definition "DFS_skel_term_rel' = (call_1_measure) <*mlex*> (call_2_measure) <*mlex*> {}"

end

text ‹The reasoning layer: the callbacks must not disturb the search spine (stack/seen), and the
graph is well-formed. Under these the structural invariants and termination hold generically.›

locale DFS_skel_thms = DFS_skel +
  assumes DFS_skel_axioms: DFS_skel_axioms
    and on_found_stack[simp]:     "stack (on_found st) = stack st"
    and on_found_seen[simp]:      "seen (on_found st) = seen st"
    and on_empty_stack[simp]:     "stack (on_empty st) = stack st"
    and on_empty_seen[simp]:      "seen (on_empty st) = seen st"
    and on_backtrack_stack[simp]: "stack (on_backtrack v st) = stack st"
    and on_backtrack_seen[simp]:  "seen (on_backtrack v st) = seen st"
begin

context
includes set_ops.automation2 and Graph.adjmap.automation and Graph.vset.set.automation
begin

lemma graph_inv[simp,intro]:
          "Graph.graph_inv G"
          "Graph.finite_graph G"
          "Graph.finite_vsets G"
  using DFS_skel_axioms
  by (auto simp: DFS_skel_axioms_def)

lemma finite_neighbourhoods[simp]:
          "lookup G v = Some N ⟹ finite (t_set N)"
  using graph_inv(3)
  by fastforce

lemmas simps[simp] = Graph.neighbourhood_abs[OF graph_inv(1)] Graph.are_connected_abs[OF graph_inv(1)]

lemma invar_1_props[invar_props_elims]:
  "invar_1 dfs_state ⟹ (⟦vset_inv (seen dfs_state)⟧ ⟹ P) ⟹ P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]: "⟦vset_inv (seen dfs_state)⟧ ⟹ invar_1 dfs_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_1[invar_holds_intros]:
  "⟦DFS_skel_call_1_conds dfs_state; invar_1 dfs_state⟧ ⟹ invar_1 (DFS_skel_upd1 dfs_state)"
  by (auto simp: Let_def DFS_skel_upd1_def elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_1_holds_2[invar_holds_intros]:
  "⟦DFS_skel_call_2_conds dfs_state; invar_1 dfs_state⟧ ⟹ invar_1 (DFS_skel_upd2 dfs_state)"
  by (auto simp: DFS_skel_upd2_def elim!: invar_props_elims intro: invar_props_intros)

lemma invar_1_holds_4[invar_holds_intros]:
  "⟦DFS_skel_ret_1_conds dfs_state; invar_1 dfs_state⟧ ⟹ invar_1 (DFS_skel_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: DFS_skel_ret1_def)

lemma invar_1_holds_5[invar_holds_intros]:
  "⟦DFS_skel_ret_2_conds dfs_state; invar_1 dfs_state⟧ ⟹ invar_1 (DFS_skel_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro: invar_props_intros simp: DFS_skel_ret2_def)

lemma invar_1_holds[invar_holds_intros]:
   assumes "DFS_skel_dom dfs_state" "invar_1 dfs_state"
   shows "invar_1 (DFS_skel dfs_state)"
  using assms(2)
proof(induction rule: DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-4) invar_holds_intros simp: DFS_skel_simps[OF IH(1)])
qed

lemma invar_seen_stack_props[invar_props_elims]:
   "invar_seen_stack dfs_state ⟹
     (⟦distinct (stack dfs_state); set (stack dfs_state) ⊆ t_set (seen dfs_state);
       t_set (seen dfs_state) ⊆ dVs (Graph.digraph_abs G)⟧ ⟹ P) ⟹ P "
  by (auto simp: invar_seen_stack_def)

lemma invar_seen_stack_intro[invar_props_intros]:
  "⟦distinct (stack dfs_state); set (stack dfs_state) ⊆ t_set (seen dfs_state);
    t_set (seen dfs_state) ⊆ dVs (Graph.digraph_abs G)⟧ ⟹ invar_seen_stack dfs_state"
  by (auto simp: invar_seen_stack_def)

lemma invar_seen_stack_holds_1[invar_holds_intros]:
  "⟦DFS_skel_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state⟧ ⟹
     invar_seen_stack (DFS_skel_upd1 dfs_state)"
  by (force simp: Let_def DFS_skel_upd1_def elim!: call_cond_elims
            elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_holds_2[invar_holds_intros]:
  "⟦DFS_skel_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state⟧ ⟹
     invar_seen_stack (DFS_skel_upd2 dfs_state)"
  by (auto elim!: call_cond_elims simp: DFS_skel_upd2_def
           elim!: invar_props_elims intro!: invar_props_intros)

lemma invar_seen_stack_holds_4[invar_holds_intros]:
   "⟦DFS_skel_ret_1_conds dfs_state; invar_seen_stack dfs_state⟧ ⟹
       invar_seen_stack (DFS_skel_ret1 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: DFS_skel_ret1_def)

lemma invar_seen_stack_holds_5[invar_holds_intros]:
   "⟦DFS_skel_ret_2_conds dfs_state; invar_seen_stack dfs_state⟧ ⟹
       invar_seen_stack (DFS_skel_ret2 dfs_state)"
  by (auto elim!: invar_props_elims intro!: invar_props_intros simp: DFS_skel_ret2_def)

lemma invar_seen_stack_holds[invar_holds_intros]:
   assumes "DFS_skel_dom dfs_state" "invar_1 dfs_state" "invar_seen_stack dfs_state"
   shows "invar_seen_stack (DFS_skel dfs_state)"
   using assms(2-)
proof(induction rule: DFS_skel_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_skel_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_skel_simps[OF IH(1)])
qed

named_theorems termination_intros

lemma in_prod_relI[intro!,termination_intros]:
  "⟦f1 a = f1 a'; (a, a') ∈ f2 <*mlex*> r⟧ ⟹ (a,a') ∈ (f1 <*mlex*> f2 <*mlex*> r)"
   by (simp add: mlex_iff)+

definition "less_rel = {(x::nat, y::nat). x < y}"

lemma wf_less_rel[intro!]: "wf less_rel"
  by(auto simp: less_rel_def wf_less)

lemma call_1_measure_nonsym[simp]: "(call_1_measure dfs_state, call_1_measure dfs_state) ∉ less_rel"
  by (auto simp: less_rel_def)

lemma call_1_terminates[termination_intros]:
  "⟦DFS_skel_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state⟧ ⟹
     (DFS_skel_upd1 dfs_state, dfs_state) ∈ call_1_measure <*mlex*> r"
  by(fastforce elim!: invar_props_elims call_cond_elims
          simp add: DFS_skel_upd1_def call_1_measure_def Let_def
          intro!: mlex_less psubset_card_mono
          dest!: Graph.vset.choose')

lemma call_2_measure_nonsym[simp]: "(call_2_measure dfs_state, call_2_measure dfs_state) ∉ less_rel"
  by (auto simp: less_rel_def)

lemma call_2_measure_1[termination_intros]:
  "⟦DFS_skel_call_2_conds dfs_state; invar_1 dfs_state⟧ ⟹
    call_1_measure dfs_state = call_1_measure (DFS_skel_upd2 dfs_state)"
  by(auto simp add: DFS_skel_upd2_def call_1_measure_def Let_def)

lemma call_2_terminates[termination_intros]:
  "⟦DFS_skel_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state⟧ ⟹
     (DFS_skel_upd2 dfs_state, dfs_state) ∈ call_2_measure <*mlex*> r"
  by(auto elim!: invar_props_elims call_cond_elims
          simp add: DFS_skel_upd2_def call_2_measure_def
          intro!: mlex_less)

lemma wf_term_rel: "wf DFS_skel_term_rel'"
  by(auto simp: wf_mlex DFS_skel_term_rel'_def)

lemma in_DFS_skel_term_rel'[termination_intros]:
  "⟦DFS_skel_call_1_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state⟧ ⟹
            (DFS_skel_upd1 dfs_state, dfs_state) ∈ DFS_skel_term_rel'"
  "⟦DFS_skel_call_2_conds dfs_state; invar_1 dfs_state; invar_seen_stack dfs_state⟧ ⟹
            (DFS_skel_upd2 dfs_state, dfs_state) ∈ DFS_skel_term_rel'"
  by (simp add: DFS_skel_term_rel'_def termination_intros)+

lemma DFS_skel_terminates[termination_intros]:
  assumes "invar_1 dfs_state" "invar_seen_stack dfs_state"
  shows "DFS_skel_dom dfs_state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
    by (rule DFS_skel_domintros) (auto intro!: invar_holds_intros less in_DFS_skel_term_rel')
qed

end

end
end

