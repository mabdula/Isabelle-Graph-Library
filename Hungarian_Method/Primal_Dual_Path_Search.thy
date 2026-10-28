(*
  Author: Thomas Ammer
*)

theory Primal_Dual_Path_Search
  imports
    Basic_Matching.Berge
    Data_Structures.More_Arith
    Data_Structures.More_Logic
    Basic_Matching.Alternating_Forest_Spec
    Data_Structures.Fixed_Univ_Map_Specs
    Data_Structures.Fixed_Univ_Set_Specs
    Data_Structures.Fixed_Univ_Key_Value_Queue_Specs
    Path_Search_Result
    Data_Structures.Iterable_Set_Specs
begin

provenance human

section ‹Path Search for Hungarian Method›

subsection ‹Defining the Function and Setup for Reasoning›

record ('forest, 'ben, 'heap, 'miss, 'v, 'g) hungarian_search_state = 
  forest::'forest
  best_even_neighbour::'ben
  heap::'heap
  missed::'miss
  acc::real
  augpath::"('v list) option"
  neighb_coll::'g

text ‹All maps are total maps on a fixed universe @{term K} of vertices. A vertex without best even
      neighbour or without buddy is mapped to the sentinel @{term nil}, which is not in @{term K}.
      Missed values and potentials default to ‹0›. The partial maps @{term ben_lookup} and
      @{term buddy} are views used in the proofs only.›

locale primal_dual_path_search_spec = 
 ben_map: fixed_univ_map K ben_invar ben_upd ben_get +
 missed_map: fixed_univ_map K missed_invar missed_upd missed_get +
 potential_map: fixed_univ_map K potential_invar potential_upd potential_get +
 vset: fixed_univ_set K vset_invar vset_to_set vset_empty vset_insert vset_delete vset_isin
for K::"'v set" and ben_invar and ben_upd::"'ben ⇒ 'v ⇒ 'v ⇒ 'ben" and ben_get
    and missed_invar and missed_upd::"'miss ⇒ 'v ⇒ real ⇒ 'miss" and missed_get
    and potential_invar and potential_upd::"'potential ⇒ 'v ⇒ real ⇒ 'potential"
    and potential_get
    and vset_invar and vset_to_set::"'vset ⇒ 'v set" and vset_empty vset_insert vset_delete
    vset_isin +
  fixes G::"'v set set"
    and edge_costs::"'v ⇒ 'v ⇒ real"
    and edge_costs_code::"'v ⇒ 'v ⇒ real"
    and left::'vset
    and right::'vset
    and in_G::"'v ⇒ 'v ⇒ bool"

    and rnb_invar::"'g ⇒ bool"
    and rnb_abstract::"'g ⇒ 'v ⇒ 'v set"
    and rnb_current::"'g ⇒ 'v ⇒ 'v"
    and rnb_has::"'g ⇒ 'v ⇒ bool"
    and rnb_iterated::"'g ⇒ 'v ⇒ 'v set"
    and rnb_remaining::"'g ⇒ 'v ⇒ 'v set"
    and rnb_move::"'g ⇒ 'v ⇒ 'g"
    and rnb_reset::"'g ⇒ 'v ⇒ 'g"
    and rnb_init::'g

    and buddy_get::"'v ⇒ 'v"

    and extend_forest_even_unclassified::
        "'forest ⇒ 'v ⇒ 'v ⇒ 'v ⇒ 'forest"
    and evens::"'forest ⇒ 'vset"
    and odds::"'forest ⇒ 'vset"
    and get_path::"'forest ⇒ 'v ⇒ 'v list"
    and abstract_forest::"'forest ⇒ 'v set set"
    and empty_forest::"'vset ⇒ 'forest"
    and forest_invar::"'v set set ⇒ 'forest ⇒ bool"
    and roots::"'forest ⇒ 'vset"

    and initial_pot::"'potential"

    and heap_empty::'heap
    and heap_extract_min::"'heap ⇒ ('heap × 'v option)"
    and heap_decrease_key::"'heap ⇒ 'v ⇒ real ⇒ 'heap"
    and heap_insert::"'heap ⇒ 'v ⇒ real ⇒ 'heap"
    and heap_invar::"'heap ⇒ bool"
    and heap_abstract::"'heap ⇒ ('v × real) set"
 
    and vset_iterate_ben::"('g × 'ben × 'heap ⇒ 'v ⇒ 'g × 'ben × 'heap)
        ⇒ 'g × 'ben × 'heap ⇒ 'vset ⇒ 'g × 'ben × 'heap"
    and vset_iterate_pot::"('potential ⇒ 'v ⇒ 'potential)
      ⇒ 'potential ⇒ 'vset ⇒ 'potential"
    and vset_filter::"('v ⇒ bool) ⇒ 'vset ⇒ 'vset"

    and vset_is_empty::"'vset ⇒ bool"
    and ben_empty::'ben and missed_empty::'miss and nil::'v
begin

definition "ben_lookup ben v = (if ben_get ben v = nil then None else Some (ben_get ben v))"
definition "buddy v = (if buddy_get v = nil then None else Some (buddy_get v))"

notation edge_costs ("𝗐")

abbreviation "aevens state ≡ vset_to_set (evens (forest state))"
abbreviation "aodds state ≡ vset_to_set (odds (forest state))"
abbreviation "missed_at state v ≡ missed_get (missed state) v"
abbreviation "π v ≡ potential_get initial_pot v"
abbreviation "ℱ state ≡ abstract_forest (forest state)"
abbreviation "L  ≡ vset_to_set left"
abbreviation "R  ≡ vset_to_set right"

definition "ℳ = {{u, v} | u v. Some v = buddy u}"
definition "w⇩π u v = edge_costs u v - π u - π v"

text ‹The reduced costs as computed by the algorithm, using the costs @{term edge_costs_code}.
      These are only ever evaluated for a left vertex and one of its right neighbours.›

definition "w⇩π_code u v = edge_costs_code u v - π u - π v"

abbreviation "rneighbs l ≡ rnb_abstract rnb_init l"

definition working_potential ("π⇧*") where
"π⇧* state v =
        (if vset_isin (evens (forest state)) v then 
           π v + acc state - missed_at state v
         else if vset_isin (odds (forest state)) v then 
           π v - acc state + missed_at state v
         else π v)"

text ‹Relaxing a single edge ‹{l, r}› from the new even vertex ‹l›.›

definition "relax_neighbour off l = 
       (λ (ben, queue) r. 
                (let l' = ben_get ben r in
                 if l' = nil then
                     (ben_upd ben r l, heap_insert queue r (w⇩π_code l r + off l))
                 else if w⇩π_code l r + off l < w⇩π_code l' r + off l'
                 then (ben_upd ben r l, heap_decrease_key queue r (w⇩π_code l r + off l))
                 else (ben, queue)))"

text ‹The same in terms of the partial view, for the proofs.›

lemma relax_neighbour_view: "relax_neighbour off l = 
       (λ (ben, queue) r. 
                (case ben_lookup ben r of None ⇒
                     (ben_upd ben r l, heap_insert queue r (w⇩π_code l r + off l)) |
                 Some l' ⇒
                 if w⇩π_code l r + off l < w⇩π_code l' r + off l'
                 then (ben_upd ben r l, heap_decrease_key queue r (w⇩π_code l r + off l))
                 else (ben, queue)))"
  unfolding relax_neighbour_def ben_lookup_def Let_def by (intro ext) (auto split: prod.splits)

text ‹Scanning the remaining right neighbours of ‹l› by advancing the cursor at ‹l›
      in the collection of neighbourhoods.›

partial_function (tailrec) scan_neighbours::
  "('v ⇒ real) ⇒ 'v ⇒ 'g ⇒ 'ben × 'heap ⇒ 'g × 'ben × 'heap" where
"scan_neighbours off l C ben_queue = 
   (if rnb_has C l 
    then scan_neighbours off l (rnb_move C l) 
             (relax_neighbour off l ben_queue (rnb_current C l))
    else (C, ben_queue))"

definition "update_best_even_neighbour off C ben queue l =
   scan_neighbours off l (rnb_reset C l) (ben, queue)"

definition "update_best_even_neighbours off C ben queue new_evens =
  vset_iterate_ben 
    (λ cbq l. update_best_even_neighbour off (fst cbq) (fst (snd cbq)) (snd (snd cbq)) l) 
  (C, ben, queue) new_evens"

definition "unmatched_lefts = 
  vset_filter (λ v. buddy_get v = nil) left"
definition "forest_roots = unmatched_lefts"
definition "init_best_even_neighbour = 
   update_best_even_neighbours (λ x. 0) rnb_init ben_empty heap_empty unmatched_lefts"

definition "initial_state = 
 ⦇forest= empty_forest forest_roots, 
  best_even_neighbour= fst (snd init_best_even_neighbour),
  heap = snd (snd init_best_even_neighbour),
  missed = missed_empty,
  acc = 0,
  augpath = None,
  neighb_coll = fst init_best_even_neighbour⦈"

function (domintros) search_path_loop::
  "('forest, 'ben, 'heap, 'miss, 'v, 'g) hungarian_search_state ⇒
   ('forest, 'ben, 'heap, 'miss, 'v, 'g) hungarian_search_state" where
"search_path_loop state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_ε = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of
          None ⇒ state ⦇augpath:=None⦈ |
          Some r ⇒
            (let l = ben_get ben r;
                 acc' = w⇩π_code l r + missed_ε l
             in
             (case buddy r of 
                 None ⇒
                    state ⦇ acc := acc',
                            augpath:= Some (r # get_path F l) ⦈|
                 Some l' ⇒
                     (let missed' = missed_upd (missed_upd (missed state) r acc') l' acc' 
                                                ;
                          (C', ben', queue') = update_best_even_neighbour 
                                           (missed_get missed')
                                           (neighb_coll state) ben queue l';
                          F'= extend_forest_even_unclassified F l r l' 
                      in  
                    search_path_loop (state ⦇ forest:= F', 
                            best_even_neighbour:=ben', neighb_coll:=C',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' ⦈)
             )))))"
  by pat_completeness auto

definition "search_path_loop_fail_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of None ⇒ True|
                        Some r ⇒ False))"

lemma search_path_loop_fail_condE:
  "search_path_loop_fail_cond state ⟹
  (⋀ queue heap_min. 
    ⟦ (queue, heap_min) = heap_extract_min (heap state); heap_min = None⟧ ⟹ P)
  ⟹ P"
  apply(cases "heap_extract_min (heap state)")
  apply(all ‹cases "snd (heap_extract_min (heap state))"›)
  by(auto simp add: search_path_loop_fail_cond_def)

definition "search_path_loop_succ_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of
          None ⇒ False|
          Some r ⇒ (case buddy r of 
                        None ⇒ True|
                        Some l' ⇒ False )))"

lemma search_path_loop_succ_condE:
  "search_path_loop_succ_cond state ⟹
  (⋀ queue heap_min r. 
      ⟦(queue, heap_min) = heap_extract_min (heap state); heap_min = Some r; buddy r = None⟧ ⟹ P)
  ⟹ P"
  apply(cases "heap_extract_min (heap state)")
  apply(all ‹cases "snd (heap_extract_min (heap state))"›)
  apply(all ‹cases "buddy (the (snd (heap_extract_min (heap state))))"›)
  by(auto simp add: search_path_loop_succ_cond_def)

definition "search_path_loop_cont_cond state = 
  (let (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of None ⇒ False|
                        Some r ⇒ (case buddy r of None ⇒ False|
                                                   Some l' ⇒ True)))"

lemma search_path_loop_cont_condE:
  "search_path_loop_cont_cond state ⟹
  (⋀ queue heap_min r l'. 
    ⟦heap_extract_min (heap state) = (queue, heap_min); heap_min = Some r; buddy r = Some l'⟧ ⟹ P)
  ⟹ P"
  apply(cases "heap_extract_min (heap state)")
  apply(all ‹cases "snd (heap_extract_min (heap state))"›)
  apply(all ‹cases "buddy (the (snd (heap_extract_min (heap state))))"›)
  by(auto simp add: search_path_loop_cont_cond_def)

lemma search_path_loop_cases:
  assumes "search_path_loop_fail_cond state ⟹ P"
          "search_path_loop_succ_cond state ⟹ P"
          "search_path_loop_cont_cond state ⟹ P"
    shows P
  using assms
  apply(cases "heap_extract_min (heap state)")
  apply(all ‹cases "snd (heap_extract_min (heap state))"›)
  apply(all ‹cases "buddy (the (snd (heap_extract_min (heap state))))"›)
  by(auto simp add: search_path_loop_fail_cond_def
                    search_path_loop_succ_cond_def search_path_loop_cont_cond_def)

definition "search_path_loop_fail_upd state = state ⦇augpath:=None⦈"

definition "search_path_loop_succ_upd state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_ε = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state);
       r = the heap_min;
       l = ben_get ben r;
       acc' = w⇩π_code l r + missed_ε l
    in state ⦇ acc := acc', augpath:= Some (r # get_path F l) ⦈)"

definition "search_path_loop_cont_upd state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_ε = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state);
       r = the heap_min;
       l = ben_get ben r;
        acc' = w⇩π_code l r + missed_ε l;
       l' =  the (buddy r);
       missed' = missed_upd (missed_upd (missed state) r acc') l' acc';
       (C', ben', queue') = update_best_even_neighbour 
                 (missed_get missed') (neighb_coll state) ben queue l';
       F'= extend_forest_even_unclassified F l r l' 
    in state ⦇ forest:= F', best_even_neighbour:=ben', neighb_coll:=C',
              heap:=queue', missed:=missed', acc:= acc' ⦈)"
 
lemma search_path_loop_simps:
  "search_path_loop_fail_cond state ⟹ search_path_loop state = search_path_loop_fail_upd state"
  "search_path_loop_succ_cond state ⟹ search_path_loop state = search_path_loop_succ_upd state"
  "⟦search_path_loop_dom state; search_path_loop_cont_cond state⟧ ⟹
   search_path_loop state = search_path_loop (search_path_loop_cont_upd state)"
proof(goal_cases)
  case 1
  show ?case 
    apply(subst search_path_loop.psimps)
    apply(all ‹cases "heap_extract_min (heap state)"›)
    apply(all ‹cases "snd (heap_extract_min (heap state))"›)
    using 1
    by(auto intro: search_path_loop.domintros
             simp add: search_path_loop_fail_cond_def search_path_loop_fail_upd_def)
next
  case 2
  show ?case
    apply(subst search_path_loop.psimps)
    apply(all ‹cases "heap_extract_min (heap state)"›)
    apply(all ‹cases "snd (heap_extract_min (heap state))"›)
    apply(all ‹cases "buddy (the (snd (heap_extract_min (heap state))))"›)
    using 2
    by(auto intro: search_path_loop.domintros
             simp add: search_path_loop_succ_cond_def search_path_loop_succ_upd_def)
next
  case 3
  show ?case 
    apply(subst search_path_loop.psimps[OF 3(1)])
    apply(all ‹cases "heap_extract_min (heap state)"›)
    apply(all ‹cases "snd (heap_extract_min (heap state))"›)
    apply(all ‹cases "buddy (the (snd (heap_extract_min (heap state))))"›)
    using 3
    by(auto simp add: search_path_loop_cont_cond_def search_path_loop_cont_upd_def Let_def
               split: option.split prod.split)
qed

lemma search_path_loop_induct:
  assumes "search_path_loop_dom state"
          "⋀ state. ⟦search_path_loop_dom state;
                      search_path_loop_cont_cond state ⟹ P (search_path_loop_cont_upd state)⟧
                     ⟹ P state"
   shows "P state"
proof(induction rule: search_path_loop.pinduct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
  proof(cases state rule: search_path_loop_cases, goal_cases)
    case 1
    then show ?case
     by(auto elim!:  search_path_loop_fail_condE
            intro!: assms(2)[OF IH(1)]
          simp add: search_path_loop_cont_cond_def)
  next
    case 2
    then show ?case 
     by(auto elim!:  search_path_loop_succ_condE
            intro!: assms(2)[OF IH(1)] 
          simp add: search_path_loop_cont_cond_def)
  next
    case 3
    show ?case 
      apply(rule assms(2)[OF IH(1)])
      using 3 assms(2)
      by(auto intro!: IH(2)
               elim!: search_path_loop_cont_condE
            simp add: search_path_loop_cont_upd_def Let_def 
               split: option.split prod.split)
  qed
qed

lemma search_path_loop_domintros:
  "search_path_loop_fail_cond state ⟹ search_path_loop_dom state"
  "search_path_loop_succ_cond state ⟹ search_path_loop_dom state"
  "⟦search_path_loop_cont_cond state; search_path_loop_dom (search_path_loop_cont_upd state)⟧ 
   ⟹ search_path_loop_dom state"
proof(goal_cases)
  case 1
  show ?case 
    apply(rule search_path_loop.domintros)
    apply(all ‹cases "heap_extract_min (heap state)"›)
    apply(all ‹cases "snd (heap_extract_min (heap state))"›)
    using 1
    by(auto intro: search_path_loop.domintros
             simp add: search_path_loop_fail_cond_def search_path_loop_fail_upd_def)
next
  case 2
  show ?case
    apply(rule search_path_loop.domintros)
    apply(all ‹cases "heap_extract_min (heap state)"›)
    apply(all ‹cases "snd (heap_extract_min (heap state))"›)
    apply(all ‹cases "buddy (the (snd (heap_extract_min (heap state))))"›)
    using 2
    by(auto intro: search_path_loop.domintros
             simp add: search_path_loop_succ_cond_def search_path_loop_succ_upd_def)
next
  case 3
  show ?case 
    apply(rule search_path_loop.domintros)
    apply(all ‹cases "heap_extract_min (heap state)"›)
    apply(all ‹cases "snd (heap_extract_min (heap state))"›)
    apply(all ‹cases "buddy (the (snd (heap_extract_min (heap state))))"›)
    using 3
    by(auto simp add: search_path_loop_cont_cond_def search_path_loop_cont_upd_def
                      Let_def prod.split
               split: option.split prod.split)
qed

partial_function (tailrec) search_path_loop_impl::
  "('forest, 'ben, 'heap, 'miss, 'v, 'g) hungarian_search_state ⇒
   ('forest, 'ben, 'heap, 'miss, 'v, 'g) hungarian_search_state" where
"search_path_loop_impl state = 
  (let F = forest state;
       ben = best_even_neighbour state;
       missed_ε = missed_at state;
       (queue, heap_min) = heap_extract_min (heap state)
   in (case heap_min of
          None ⇒ state ⦇augpath:=None⦈ |
          Some r ⇒
            (let l = ben_get ben r;
                 acc' = w⇩π_code l r + missed_ε l
             in
             (let l' = buddy_get r in
              if l' = nil then
                    state ⦇ acc := acc',
                            augpath:= Some (r # get_path F l) ⦈
              else
                     (let missed' = missed_upd (missed_upd (missed state) r acc') l' acc';
                          (C', ben', queue') = update_best_even_neighbour 
                                           (missed_get missed')
                                           (neighb_coll state) ben queue l';
                          F'= extend_forest_even_unclassified F l r l' 
                      in  
            search_path_loop_impl (state ⦇ forest:= F', 
                            best_even_neighbour:=ben', neighb_coll:=C',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' ⦈)
             )))))"

definition "new_potential state = 
(vset_iterate_pot (λ p v. potential_upd p v (π v - acc state + missed_at state v))
   (vset_iterate_pot (λ p v. potential_upd p v (π v + acc state - missed_at state v)) 
      initial_pot (evens (forest state)))
  (odds (forest state)))"

definition "search_path = 
(if vset_is_empty unmatched_lefts then (Lefts_Matched, initial_pot)
else (let final_state = search_path_loop_impl initial_state
      in (case augpath final_state of 
               None ⇒ (Dual_Unbounded, initial_pot)
              | Some p ⇒ (Next_Iteration p, new_potential final_state))))"

lemma search_path_loop_impl_same:
  assumes "search_path_loop_dom state"
  shows "search_path_loop_impl state = search_path_loop state"
  apply(induction rule: search_path_loop.pinduct[OF assms])
  apply(subst search_path_loop.psimps, simp)
  apply(subst search_path_loop_impl.simps)
  by (auto simp add: Let_def buddy_def split: if_split option.split prod.split)

lemmas [code] = 
  search_path_def 
  search_path_loop_impl.simps 
  new_potential_def
  w⇩π_code_def
  unmatched_lefts_def
  initial_state_def
  init_best_even_neighbour_def
  update_best_even_neighbours_def
  update_best_even_neighbour_def
  relax_neighbour_def
  scan_neighbours.simps
  forest_roots_def
end

subsection ‹Locale for Proofs›


locale primal_dual_path_search =

 primal_dual_path_search_spec 
      where G = "G::'v set set" 
      and   left = "left::'vset"
      and empty_forest="empty_forest::'vset ⇒ 'forest"
      and initial_pot = "initial_pot::'pot"
      and ben_empty="ben_empty::'ben"
      and extend_forest_even_unclassified = extend_forest_even_unclassified
      and evens = evens and odds = odds and get_path = get_path
      and abstract_forest = abstract_forest
      and forest_invar = forest_invar
      and roots = roots +

 alternating_forest_ordinary_extension_spec 
      where extend_forest_even_unclassified = extend_forest_even_unclassified
      and  evens = evens and odds = odds and get_path = get_path
      and abstract_forest = abstract_forest
      and forest_invar = forest_invar
      and roots = roots and empty_forest = empty_forest and forest_univ = K
      and vset_empty = vset_empty +

  key_value_queue "Vs G" heap_empty heap_extract_min heap_decrease_key heap_insert
      heap_invar heap_abstract +

  rnb: indexed_iterable_set rnb_invar rnb_abstract rnb_current rnb_has rnb_iterated
      rnb_remaining rnb_move rnb_reset "vset_to_set left"

    for G left  initial_pot ben_empty
    and evens::"'forest ⇒ 'vset"
    and odds::"'forest ⇒ 'vset"
    and get_path::"'forest ⇒ 'v ⇒ 'v list"
    and abstract_forest::"'forest ⇒ 'v set set"
    and forest_invar::"'v set set ⇒ 'forest ⇒ bool"
    and roots::"'forest ⇒ 'vset" 
    and extend_forest_even_unclassified::
        "'forest ⇒ 'v ⇒ 'v ⇒ 'v ⇒ 'forest"
    and empty_forest::"'vset ⇒ 'forest" +

assumes G: "bipartite G L R"
           "vset_invar left" "vset_invar right"
           "rnb_invar rnb_init"
           "⋀ v. v ∈ vset_to_set left ⟹ rnb_abstract rnb_init v = {u | u. {v, u} ∈ G}"
           "⋀ u v. {u, v} ∈ G ⟹ edge_costs u v = edge_costs v u"
           "⋀ u v. {u, v} ∈ G ⟹ π u + π v ≤ 𝗐 u v"
and matching: "⋀ u v. buddy u = Some v ⟹ buddy v = Some u"
              "graph_matching G {{u, v} | u v. buddy u = Some v}"
              "⋀ u v. {u, v} ∈ ℳ ⟹ π u + π v = 𝗐 u v"
and potential: "potential_invar initial_pot"
and empties: "nil ∉ K"
  "ben_invar ben_empty" "ben_get ben_empty = (λ _. nil)"
  "missed_invar missed_empty" "missed_get missed_empty = (λ _. 0)"
and vset_iterations:
  "⋀ V f init. vset_invar V ⟹
      ∃ vs. set vs = vset_to_set V ∧ distinct vs 
          ∧ vset_iterate_ben f init V = foldl f init vs"
  "⋀ V f init. vset_invar V ⟹
      ∃ vs. set vs = vset_to_set V ∧ distinct vs 
          ∧ vset_iterate_pot f init V = foldl f init vs"
  "⋀ V P. vset_invar V ⟹ vset_invar (vset_filter P V)"
  "⋀ V P. vset_invar V ⟹ vset_to_set (vset_filter P V) = vset_to_set V ∩ Collect P"
and vset_is_empty: "⋀ X. vset_invar X ⟹ vset_is_empty X ⟷ vset_to_set X = {}"
and edge_costs_code: 
  "⋀ u v. ⟦{u, v} ∈ G; u ∈ vset_to_set left; v ∈ vset_to_set right⟧ ⟹
            edge_costs_code u v = edge_costs u v"
begin

lemmas vset = 
  vset.fixed_univ_set_empty(1)
  vset.fixed_univ_set_empty(2)
  vset.fixed_univ_set_insert(1)
  vset.fixed_univ_set_insert(2)
  vset.fixed_univ_set_isin

lemma in_K_not_nil: "k ∈ K ⟹ k ≠ nil"
  using empties(1) by auto

lemma L_in_K: "L ⊆ K" and R_in_K: "R ⊆ K" and Vs_G_in_K: "Vs G ⊆ K"
  using vset.fixed_univ_set_universe[OF G(2)] vset.fixed_univ_set_universe[OF G(3)]
        bipartite_vs_subset[OF G(1)] by auto

lemma in_K: "x ∈ L ⟹ x ∈ K" "x ∈ R ⟹ x ∈ K" "x ∈ Vs G ⟹ x ∈ K"
  and not_nil: "x ∈ L ⟹ x ≠ nil" "x ∈ R ⟹ x ≠ nil" "x ∈ Vs G ⟹ x ≠ nil"
  using L_in_K R_in_K Vs_G_in_K in_K_not_nil by blast+

lemma ben_lookup_empty: "ben_lookup ben_empty = Map.empty"
  by (auto simp add: ben_lookup_def empties)

lemma ben_lookup_upd:
  "⟦ben_invar ben; k ∈ K; v ≠ nil⟧ ⟹
   ben_lookup (ben_upd ben k v) = (ben_lookup ben)(k ↦ v)"
  by (auto simp add: ben_lookup_def ben_map.fixed_univ_map_upd)

lemma ben_lookup_get: "ben_lookup ben r = Some l ⟹ ben_get ben r = l"
  by (auto simp add: ben_lookup_def split: if_splits)

lemmas missed = 
  empties(4)
  empties(5)
  missed_map.fixed_univ_map_upd_invar
  missed_map.fixed_univ_map_upd

lemmas best_even_neighbour = 
  empties(2)
  ben_map.fixed_univ_map_upd_invar
  ben_lookup_upd
  ben_lookup_empty

subsection ‹Misc about the Graph›

lemma w⇩π_symmetric: "{u, v} ∈ G ⟹ w⇩π u v = w⇩π v u"
  by(auto simp add: w⇩π_def intro: G(6))

lemma w⇩π_non_neg: "{u, v} ∈ G ⟹ w⇩π u v ≥ 0"
  using G(7) w⇩π_def by fastforce

lemma finite_L: "finite L" and finite_R: "finite R"
proof-
  show "finite L"
    by(rule exE[OF vset_iterations(2)[OF G(2)]])
      (auto dest: sym[of "set _" L])
  show "finite R"
    by(rule exE[OF vset_iterations(2)[OF G(3)]])
      (auto dest: sym[of "set _" R])
qed

lemma ℳ_is_matching: "matching ℳ"
proof(rule matchingI, rule ccontr, goal_cases)
  case (1 e1 e2)
  obtain u v where uv: "buddy u = Some v" "e1 ={u, v}"
    using 1(1) by(force simp add: ℳ_def doubleton_eq_iff)
  obtain u' v' where u'v': "buddy u' = Some v'" "e2 ={u', v'}"
    using 1(2) by(force simp add: ℳ_def doubleton_eq_iff)
  have more_buddies: "buddy v = Some u" "buddy v' =  Some u'"
    using matching(1) uv(1) u'v'(1) by blast+
  then show ?case 
    using uv u'v' more_buddies 1(3,4)
    by auto
qed

lemma Vs_M_in_K: "Vs ℳ ⊆ K"
proof-
  have "ℳ ⊆ G"
    using matching(2) by(force simp add: ℳ_def)
  thus ?thesis
    using Vs_subset Vs_G_in_K by blast
qed

lemma one_buddy_no_buddy_false: 
"⟦Some v = buddy u;  None = buddy v⟧ ⟹ False"
  using  matching(1)[of u v] by simp

lemma llist:
  obtains llist where "set llist = vset_to_set left" "distinct llist"
  using vset_iterations[OF G(2)] by force

lemma rlist:
  obtains rlist where "set rlist = vset_to_set right" "distinct rlist"
  using vset_iterations[OF G(3)] by force

lemma unmatched_lefts_are:
  "vset_to_set unmatched_lefts = vset_to_set left - Collect (λ v. buddy v ≠ None)"
  by(auto simp add: unmatched_lefts_def buddy_def vset_iterations(4)[OF G(2)])

lemma unmatched_lefts:
 "vset_to_set (unmatched_lefts) = L - Vs ℳ"
 "vset_invar unmatched_lefts"
proof-
  obtain llist where llist: "set llist = vset_to_set left" "distinct llist"
    using llist by auto
  obtain rlist where rlist: "set rlist = vset_to_set right" "distinct rlist"
    using rlist by auto
  show  "vset_to_set (unmatched_lefts) = L - Vs ℳ"
  proof(rule, all ‹rule›, goal_cases)
    case (1 x)
    then show ?case 
      by(cases "buddy x")
        (auto elim!: vs_member_elim 
         intro: one_buddy_no_buddy_false 
         simp add: unmatched_lefts_are ℳ_def)
  next
    case (2 x)
    then show ?case 
    using  vs_member_intro[of "x" "{x, the (buddy x)}" ℳ]
    by(cases "buddy x")
      (fastforce intro: one_buddy_no_buddy_false 
      simp add:  ℳ_def doubleton_eq_iff unmatched_lefts_are)+
qed
  show "vset_invar unmatched_lefts"
    by(auto simp add: unmatched_lefts_def intro!: vset_iterations(3) G(2))
qed  

lemma unmatched_lefts_in_L: "vset_to_set unmatched_lefts ⊆ L"
  using unmatched_lefts by simp

lemma M_verts_by_buddy:
  "x ∈ Vs ℳ ⟹ buddy x ≠ None"
  "buddy x ≠ None ⟹ x ∈ Vs ℳ"
proof(goal_cases)
  case 1
  then show ?case  
  by(cases "buddy x")
    (auto elim!: vs_member_elim 
      intro: one_buddy_no_buddy_false 
      simp add: ℳ_def)
next
  case 2
  then obtain y where "buddy x = Some y"
    by auto
  hence "{x, y} ∈ ℳ"
    by(auto simp add: ℳ_def intro: exI[of _ x])
  then show ?case 
    by blast 
qed

lemma finite_G: "finite G"
  using  finite_parts_bipartite_graph_invar[OF finite_L finite_R G(1)]
  by(auto intro!: finite_UnionD simp add: Vs_def)

lemma w⇩π_code_is:
  "⟦{l, r} ∈ G; l ∈ L⟧ ⟹ w⇩π_code l r = w⇩π l r"
  using bipartite_edgeD(1)[OF _ G(1)]
  by(auto simp add: w⇩π_code_def w⇩π_def edge_costs_code)

lemma finite_rneighbs: "l ∈ L ⟹ finite (rneighbs l)"
  by(rule rev_finite_subset[OF finite_R])
    (auto simp add: G(5) dest: bipartite_edgeD(1)[OF _ G(1)])

lemma rneighbs_in_G: "⟦l ∈ L; r ∈ rneighbs l⟧ ⟹ {l, r} ∈ G"
  by(simp add: G(5))

lemma foldl_cong_invar:
  "⟦P a; ⋀ a x. ⟦P a; x ∈ set xs⟧ ⟹ f a x = g a x ∧ P (f a x)⟧ 
    ⟹ foldl f a xs = foldl g a xs"
proof(induction xs arbitrary: a)
  case (Cons x xs)
  have fg: "f a x = g a x" "P (f a x)"
    using Cons(3)[of a x] Cons(2) by auto
  have "foldl f (f a x) xs = foldl g (f a x) xs"
    by(intro Cons(1)[OF fg(2)]) (meson Cons(3) list.set_intros(2))
  thus ?case
    by(simp add: fg(1))
qed simp


subsection ‹Scanning a Neighbourhood›

lemma scan_neighbours_is_foldl:
  assumes "rnb_invar C" "l ∈ L" "finite (rnb_remaining C l)"
  shows "∃ rs. distinct rs ∧ set rs = rnb_remaining C l ∧
            snd (scan_neighbours off l C bq) = foldl (relax_neighbour off l) bq rs ∧
            rnb_invar (fst (scan_neighbours off l C bq)) ∧
            rnb_abstract (fst (scan_neighbours off l C bq)) = rnb_abstract C"
  using assms
proof(induction "card (rnb_remaining C l)" arbitrary: C bq)
  case 0
  hence empty: "rnb_remaining C l = {}" 
    by simp
  hence not_has: "¬ rnb_has C l"
    using rnb.idx_has[OF 0(2,3)] by simp
  show ?case 
    using empty 0(2)
    by(auto intro!: exI[of _ "[]"] 
          simp add: scan_neighbours.simps[of off l C bq] not_has)
next
  case (Suc n)
  hence non_empty: "rnb_remaining C l ≠ {}"
    by auto
  hence has: "rnb_has C l"
    using rnb.idx_has[OF Suc(3,4)] by simp
  define x where "x = rnb_current C l"
  define C' where "C' = rnb_move C l"
  have x_in: "x ∈ rnb_remaining C l"
    using rnb.idx_current[OF Suc(3,4) non_empty] by(simp add: x_def)
  have C'_props: "rnb_invar C'" "rnb_remaining C' l = rnb_remaining C l - {x}"
                 "rnb_abstract C' = rnb_abstract C"
    using rnb.idx_move_invar[OF Suc(3,4)] rnb.idx_move_remaining[OF Suc(3,4) non_empty]
          rnb.idx_move_abstract[OF Suc(3,4) non_empty]
    by(auto simp add: C'_def x_def)
  have card_C': "n = card (rnb_remaining C' l)"
    using Suc(2,5) x_in by(simp add: C'_props(2))
  obtain rs where rs: "distinct rs" "set rs = rnb_remaining C' l"
     "snd (scan_neighbours off l C' (relax_neighbour off l bq x)) =
       foldl (relax_neighbour off l) (relax_neighbour off l bq x) rs"
     "rnb_invar (fst (scan_neighbours off l C' (relax_neighbour off l bq x)))"
     "rnb_abstract (fst (scan_neighbours off l C' (relax_neighbour off l bq x))) = 
      rnb_abstract C'"
    using Suc(1)[of C' "relax_neighbour off l bq x", OF card_C' C'_props(1) Suc(4)] Suc(5) 
    by(auto simp add: C'_props(2))
  have scan_is: "scan_neighbours off l C bq = 
                 scan_neighbours off l C' (relax_neighbour off l bq x)"
    by(simp add: scan_neighbours.simps[of off l C bq] has C'_def x_def)
  have rs': "distinct (x#rs)" "set (x#rs) = rnb_remaining C l"
    using rs(1,2) x_in by(auto simp add: C'_props(2))
  show ?case
    using rs' rs(3,4,5) 
    by(intro exI[of _ "x#rs"]) (simp add: scan_is C'_props(3))
qed

lemma update_best_even_neighbour_is_foldl:
  assumes "rnb_invar C" "l ∈ L" "rnb_abstract C = rnb_abstract rnb_init"
          "(C', ben', queue') = update_best_even_neighbour off C ben queue l"
  shows "∃ rs. distinct rs ∧ set rs = rneighbs l ∧ 
                (ben', queue') = foldl (relax_neighbour off l) (ben, queue) rs"
        "rnb_invar C'" "rnb_abstract C' = rnb_abstract rnb_init"
proof-
  define C0 where "C0 = rnb_reset C l"
  have C0_props: "rnb_invar C0" "rnb_remaining C0 l = rneighbs l" 
                 "rnb_abstract C0 = rnb_abstract rnb_init"
    using rnb.idx_reset_invar[OF assms(1,2)] rnb.idx_reset_remaining[OF assms(1,2)]
          rnb.idx_reset_abstract[OF assms(1,2)] assms(3)
    by(auto simp add: C0_def)
  note scan = scan_neighbours_is_foldl[OF C0_props(1) assms(2), 
                   simplified C0_props(2), OF finite_rneighbs[OF assms(2)], of off "(ben, queue)"]
  have upd_is: "update_best_even_neighbour off C ben queue l = 
                scan_neighbours off l C0 (ben, queue)"
    by(simp add: update_best_even_neighbour_def C0_def)
  show "∃ rs. distinct rs ∧ set rs = rneighbs l ∧ 
                (ben', queue') = foldl (relax_neighbour off l) (ben, queue) rs"
       "rnb_invar C'" "rnb_abstract C' = rnb_abstract rnb_init"
    using scan assms(4) C0_props(3)
    by(auto simp add: upd_is split_pairs)
qed

subsection ‹Setting Up Invariants›

definition "invar_basic state= 
  (forest_invar ℳ (forest state) ∧
    ben_invar (best_even_neighbour state) ∧
    heap_invar (heap state) ∧
    missed_invar (missed state) ∧
    ℱ state ⊆ G ∧
    dom (ben_lookup (best_even_neighbour state)) ⊆ Vs G ∧
    {v. missed_get (missed state) v ≠ 0} ⊆ Vs G ∧
     fst ` heap_abstract (heap state) ⊆ Vs G ∧
     aevens state ⊆ L ∧ aodds state ⊆ R ∧
    {l | l r. ben_lookup (best_even_neighbour state) r = Some l} ⊆ aevens state ∧
    aodds state ⊆ dom (ben_lookup (best_even_neighbour state)) ∧
    rnb_invar (neighb_coll state) ∧
    rnb_abstract (neighb_coll state) = rnb_abstract rnb_init ∧
    (∀ r l. ben_lookup (best_even_neighbour state) r = Some l ⟶ {l, r} ∈ G) ∧
    vset_to_set (roots (forest state)) = L - Vs ℳ)"

lemma invar_basicE:
  "invar_basic state ⟹
  (⟦forest_invar ℳ (forest state);
    ben_invar (best_even_neighbour state);
    heap_invar (heap state);
    missed_invar (missed state);ℱ state ⊆ G;
    dom (ben_lookup (best_even_neighbour state)) ⊆ Vs G;
    {v. missed_get (missed state) v ≠ 0} ⊆ Vs G;
    fst ` heap_abstract (heap state) ⊆ Vs G;
    aevens state ⊆ L; aodds state ⊆ R;
    {l | l r. ben_lookup (best_even_neighbour state) r = Some l} ⊆ aevens state;
    aodds state ⊆ dom (ben_lookup (best_even_neighbour state));
    rnb_invar (neighb_coll state);
    rnb_abstract (neighb_coll state) = rnb_abstract rnb_init;
    ⋀ r l. ben_lookup (best_even_neighbour state) r = Some l ⟹ {l, r} ∈ G;
    vset_to_set (roots (forest state)) = L - Vs ℳ⟧ ⟹ P)
   ⟹ P"
and invar_basicI:
  "⟦forest_invar ℳ (forest state);
    ben_invar (best_even_neighbour state);
    heap_invar (heap state);
    missed_invar (missed state);ℱ state ⊆ G;
    dom (ben_lookup (best_even_neighbour state)) ⊆ Vs G;
    {v. missed_get (missed state) v ≠ 0} ⊆ Vs G;
    fst ` heap_abstract (heap state) ⊆ Vs G;
    aevens state ⊆ L; aodds state ⊆ R;
    {l | l r. ben_lookup (best_even_neighbour state) r = Some l} ⊆ aevens state;
    aodds state ⊆ dom (ben_lookup (best_even_neighbour state));
    rnb_invar (neighb_coll state);
    rnb_abstract (neighb_coll state) = rnb_abstract rnb_init;
    ⋀ r l. ben_lookup (best_even_neighbour state) r = Some l ⟹ {l, r} ∈ G;
    vset_to_set (roots (forest state)) = L - Vs ℳ⟧ 
   ⟹ invar_basic state"
and invar_basicD:
  "invar_basic state ⟹ forest_invar ℳ (forest state)"
  "invar_basic state ⟹ ben_invar (best_even_neighbour state)"
  "invar_basic state ⟹ heap_invar (heap state)"
  "invar_basic state ⟹ missed_invar (missed state)"
  "invar_basic state ⟹ ℱ state ⊆ G"
  "invar_basic state ⟹ dom (ben_lookup (best_even_neighbour state)) ⊆ Vs G"
  "invar_basic state ⟹ {v. missed_get (missed state) v ≠ 0} ⊆ Vs G"
  "invar_basic state ⟹ fst ` heap_abstract (heap state) ⊆ Vs G"
  "invar_basic state ⟹ aevens state ⊆ L"
  "invar_basic state ⟹ aodds state ⊆ R"
  "invar_basic state ⟹ 
    {l | l r. ben_lookup (best_even_neighbour state) r = Some l} ⊆ aevens state"
  "invar_basic state ⟹ aodds state ⊆ dom (ben_lookup (best_even_neighbour state))"
  "invar_basic state ⟹ rnb_invar (neighb_coll state)"
  "invar_basic state ⟹ rnb_abstract (neighb_coll state) = rnb_abstract rnb_init"
  "⟦invar_basic state; ben_lookup (best_even_neighbour state) r = Some l⟧ ⟹ {l, r} ∈ G"
  "invar_basic state ⟹ vset_to_set (roots (forest state)) = L - Vs ℳ"
  by(auto simp add: invar_basic_def)

definition "invar_feasible_potential state =
            (∀ u v. {u, v} ∈ G ⟶
               edge_costs u v ≥ π⇧* state u + π⇧* state v)"

lemma invar_feasible_potentialE:
  "⟦invar_feasible_potential state; 
    (⋀ u v. {u, v} ∈ G ⟹ edge_costs u v ≥ π⇧* state u + π⇧* state v) ⟹ P⟧
    ⟹ P"
and invar_feasible_potentialI:
  "(⋀ u v. {u, v} ∈ G ⟹ edge_costs u v ≥ π⇧* state u + π⇧* state v) 
    ⟹ invar_feasible_potential state"
and invar_feasible_potentialD:
  "⟦invar_feasible_potential state;  {u, v} ∈ G⟧
    ⟹ edge_costs u v ≥ π⇧* state u + π⇧* state v"
  by (auto simp add: invar_feasible_potential_def)

definition "invar_forest_tight state = 
            (∀ u v.  {u, v} ∈ ℱ state ⟶ edge_costs u v = π⇧* state u + π⇧* state v)"

lemma invar_forest_tightE:
  "invar_forest_tight state ⟹
   ((⋀ u v. {u, v} ∈ ℱ state ⟹edge_costs u v = π⇧* state u + π⇧* state v) ⟹ P)
   ⟹ P"
and invar_forest_tightI:
  "(⋀ u v. {u, v} ∈ ℱ state ⟹ edge_costs u v = π⇧* state u + π⇧* state v)
   ⟹ invar_forest_tight state"
and invar_forest_tightD:
  "⟦invar_forest_tight state; {u, v} ∈ ℱ state⟧ ⟹ edge_costs u v = π⇧* state u + π⇧* state v"
  by(auto simp add: invar_forest_tight_def)

definition "invar_matching_tight state = 
            (∀ u v. {u, v} ∈ ℳ ⟶
               edge_costs u v = π⇧* state u + π⇧* state v)"

lemma invar_matching_tightE:
  "invar_matching_tight state ⟹
  ((⋀ u v. {u, v} ∈ ℳ ⟹ edge_costs u v = π⇧* state u + π⇧* state v) ⟹ P)
  ⟹ P"
and invar_matching_tightI:
  "(⋀ u v. {u, v} ∈ ℳ ⟹ edge_costs u v = π⇧* state u + π⇧* state v)
   ⟹ invar_matching_tight state"
and invar_matching_tightD:
  "⟦invar_matching_tight state; {u, v} ∈ ℳ⟧ ⟹ edge_costs u v = π⇧* state u + π⇧* state v"
  by(auto simp add: invar_matching_tight_def)

definition "invar_best_even_neighbour_heap state =
  (heap_abstract (heap state) = 
   {(r, k) | r k. r ∈ Vs G - aevens state - aodds state ∧
                  (∃ l. k = w⇩π l r + missed_at state l ∧
                       ben_lookup (best_even_neighbour state) r = Some l)})"

lemma invar_best_even_neighbour_heapE:
  "invar_best_even_neighbour_heap state ⟹
  (heap_abstract (heap state) = 
     {(r, k) | r k. r ∈ Vs G - aevens state - aodds state ∧
                    (∃ l. k = w⇩π l r + missed_at state l ∧
                         ben_lookup (best_even_neighbour state) r = Some l)}
    ⟹ P)
   ⟹P"
and invar_best_even_neighbour_heapI:
  "heap_abstract (heap state) = 
     {(r, k) | r k. r ∈ Vs G - aevens state - aodds state ∧
                   (∃ l. k = w⇩π l r + missed_at state l ∧
                         ben_lookup (best_even_neighbour state) r = Some l)}
   ⟹ invar_best_even_neighbour_heap state"
and invar_best_even_neighbour_heapD:
  "invar_best_even_neighbour_heap state ⟹
   heap_abstract (heap state) = 
     {(r, k) | r k. r ∈ Vs G - aevens state - aodds state ∧
                    (∃ l. k = w⇩π l r + missed_at state l ∧
                         ben_lookup (best_even_neighbour state) r = Some l)}"
  by(auto simp add: invar_best_even_neighbour_heap_def)

lemma invar_best_even_neighbour_heap_get:
  "⟦invar_best_even_neighbour_heap state; (r, k) ∈ heap_abstract (heap state)⟧ ⟹
   ben_get (best_even_neighbour state) r = the (ben_lookup (best_even_neighbour state) r)"
proof-
  assume "invar_best_even_neighbour_heap state" "(r, k) ∈ heap_abstract (heap state)"
  then obtain l where l: "ben_lookup (best_even_neighbour state) r = Some l"
    by(auto dest!: invar_best_even_neighbour_heapD)
  thus ?thesis
    by(simp add: ben_lookup_get[OF l])
qed

definition "invar_best_even_neighbour_map state = 
 (∀ r ∈ Vs G - aevens state - aodds state.
     ((∄ l. l ∈ aevens state ∧ {l, r} ∈ G) 
          ⟶ ben_lookup (best_even_neighbour state) r = None)
  ∧ ((∃ l. l ∈ aevens state ∧ {l, r} ∈ G)
         ⟶ (∃ l. ben_lookup (best_even_neighbour state) r = Some l ∧
                   {r, l} ∈ G  ∧  l ∈ aevens state ∧
                   w⇩π l r + missed_at state l = 
                   Min {w⇩π l r + missed_at state l | l. l ∈ aevens state ∧ {l, r} ∈ G})))"

lemma invar_best_even_neighbour_mapE:
  "invar_best_even_neighbour_map state ⟹
  (⟦(⋀ r. ⟦ r ∈ Vs G; r ∉  aevens state; r ∉ aodds state; ∄ l. l ∈ aevens state ∧ {l, r} ∈ G ⟧ 
      ⟹ ben_lookup (best_even_neighbour state) r = None);
  (⋀ r. ⟦ r ∈ Vs G; r ∉  aevens state; r ∉ aodds state; ∃ l. l ∈ aevens state ∧ {l, r} ∈ G ⟧ 
      ⟹ (∃ l. ben_lookup (best_even_neighbour state) r = Some l ∧ {r, l} ∈ G  ∧ l ∈ aevens state 
                ∧ w⇩π l r + missed_at state l = 
                  Min {w⇩π l r + missed_at state l | l. l ∈ aevens state ∧ {l, r} ∈ G}))⟧
    ⟹ P)
   ⟹ P"
and invar_best_even_neighbour_mapI:
  "⟦(⋀ r. ⟦ r ∈ Vs G; r ∉  aevens state; r ∉ aodds state; ∄ l. l ∈ aevens state ∧ {l, r} ∈ G ⟧ 
       ⟹ ben_lookup (best_even_neighbour state) r = None);
   (⋀ r. ⟦ r ∈ Vs G; r ∉  aevens state; r ∉ aodds state; ∃ l. l ∈ aevens state ∧ {l, r} ∈ G ⟧ 
       ⟹ (∃ l. ben_lookup (best_even_neighbour state) r = Some l ∧ {r, l} ∈ G  ∧ l ∈ aevens state
               ∧ w⇩π l r + missed_at state l = 
                 Min {w⇩π l r + missed_at state l | l. l ∈ aevens state ∧ {l, r} ∈ G}))⟧
  ⟹ invar_best_even_neighbour_map state"
and invar_best_even_neighbour_mapD:
  "⟦invar_best_even_neighbour_map state ; r ∈ Vs G; 
    r ∉  aevens state; r ∉ aodds state; ∄ l. l ∈ aevens state ∧ {l, r} ∈ G ⟧ 
    ⟹ ben_lookup (best_even_neighbour state) r = None"
  "⟦invar_best_even_neighbour_map state; r ∈ Vs G; 
    r ∉  aevens state; r ∉ aodds state;∃ l. l ∈ aevens state ∧ {l, r} ∈ G ⟧ 
    ⟹ (∃ l. ben_lookup (best_even_neighbour state) r = Some l ∧ {r, l} ∈ G  ∧  l ∈ aevens state ∧
              w⇩π l r + missed_at state l = 
              Min {w⇩π l r + missed_at state l | l. l ∈ aevens state ∧ {l, r} ∈ G})"
  by(auto simp add: invar_best_even_neighbour_map_def)

definition "invar_out_of_heap state =
   (∀ r l. ben_lookup (best_even_neighbour state) r = Some l
             ∧ (∄ k. (r, k) ∈ heap_abstract (heap state)) ⟶
            (∀ kr ∈ heap_abstract (heap state). snd kr  
               ≥ w⇩π l r + missed_at state l))"

lemma invar_out_of_heapD:
  "⟦invar_out_of_heap state; ben_lookup (best_even_neighbour state) r = Some l;
    ∄ k. (r, k) ∈ heap_abstract (heap state); kr ∈ heap_abstract (heap state)⟧ 
   ⟹ snd kr  ≥ w⇩π l r + missed_at state l"
and invar_out_of_heapI:
  "(⋀ r l kr. ⟦ben_lookup (best_even_neighbour state) r = Some l; 
               ∄ k. (r, k) ∈ heap_abstract (heap state); kr ∈ heap_abstract (heap state)⟧ 
           ⟹  snd kr  ≥ w⇩π l r + missed_at state l)
   ⟹ invar_out_of_heap state"
  by(auto simp add: invar_out_of_heap_def)

subsection ‹Manipulation of Heap and Best Even Neighbours›

lemmas heap =  
 queue_empty(1)
 queue_extract_min(1)
 queue_insert(1)
 queue_decrease_key(1)
 queue_extract_min(2,3)
 key_for_element_unique
 queue_extract_min(4)
 queue_decrease_key(2)
 queue_insert(2)
 queue_empty(2)

lemma update_best_even_neighbour_correct:
  assumes "ben_invar ben" "heap_invar queue" "l ∈ L"
          "⋀ r k. (r, k) ∈ heap_abstract queue ⟶
          (∃ l. ben_lookup ben r = Some l ∧ k = w⇩π l r + off l)"
          "⋀ r l'. ben_lookup ben r = Some l' ∧ (∄ k. (r, k) ∈ heap_abstract queue) ⟶
             off l ≥ w⇩π l' r + off l'"
          "(C', ben', queue') = update_best_even_neighbour off C ben queue l"
          "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "⋀ r l'. ben_lookup ben r = Some l' ⟶ l' ∈ L ∧ {l', r} ∈ G"
 shows "ben_invar ben'" (is ?thesis1) "heap_invar queue'" (is ?thesis2)
       "⋀ r k.  (r, k) ∈ heap_abstract queue' ⟹ 
        ∃ l. ben_lookup ben' r = Some l ∧ k = w⇩π l r + off l"
        "⋀ r l'. ben_lookup ben' r = Some l' ∧ (∄ k. (r, k) ∈ heap_abstract queue') ⟹
             off l ≥ w⇩π l' r + off l'"
      "ben_lookup ben' = (λ r. if r ∉ rneighbs l then ben_lookup ben r
                               else if ben_lookup ben r = None 
                                    then Some l
                               else if w⇩π l r + off l < 
                                      w⇩π (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))
                                    then Some l
                                else ben_lookup ben r)" (is ?thesis3)
      "heap_abstract queue' = 
       heap_abstract queue
       - {(r, k) | r k. r ∈ rneighbs l}
       ∪ {(r, min (w⇩π l r + off l) 
                  (w⇩π (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))))
          | r. r ∈ rneighbs l ∧ r ∈ fst ` (heap_abstract queue)}
       ∪ { (r, w⇩π l r + off l) 
          | r . r ∈ rneighbs l ∧ ben_lookup ben r = None}" (is ?thesis4)
      "rnb_invar C'" "rnb_abstract C' = rnb_abstract rnb_init"
      "⋀ r l'. ben_lookup ben' r = Some l' ⟹ l' ∈ L ∧ {l', r} ∈ G"
proof-
  define f where "f = (λ (ben, queue) r.
     case ben_lookup ben r of
     None ⇒ (ben_upd ben r l, heap_insert queue r (w⇩π l r + off l))
     | Some l' ⇒
         if w⇩π l r + off l < w⇩π l' r + off l'
         then (ben_upd ben r l, heap_decrease_key queue r (w⇩π l r + off l))
         else (ben, queue))"
  obtain rnlist where rnlist:"set rnlist = rneighbs l" "distinct rnlist"
                      "(ben', queue') = foldl (relax_neighbour off l) (ben, queue) rnlist"
    using update_best_even_neighbour_is_foldl(1)[OF assms(7,3,8,6)] by force
  have code_is_proof: "foldl (relax_neighbour off l) (ben, queue) rnlist = foldl f (ben, queue) rnlist"
  proof(rule foldl_cong_invar[where P = "λ bq. ben_invar (fst bq) ∧ 
          (∀ r l'. ben_lookup (fst bq) r = Some l' ⟶ l' ∈ L ∧ {l', r} ∈ G)"], goal_cases)
    case 1
    then show ?case 
      using assms(1,9) by simp
  next
    case (2 bq x)
    obtain b q where bq: "bq = (b, q)" by(cases bq) auto
    have x_props: "{l, x} ∈ G" 
      using 2(2) rnlist(1) rneighbs_in_G[OF assms(3)] by auto
    have ben_props: "ben_invar b" "⋀ r l'. ben_lookup b r = Some l' ⟹ l' ∈ L ∧ {l', r} ∈ G"
      using 2(1) by(auto simp add: bq)
    have x_K: "x ∈ K" "l ≠ nil"
      using in_K(3)[OF edges_are_Vs_2[OF x_props]] not_nil(1)[OF assms(3)] by auto
    show ?case 
      using ben_props x_props assms(3) x_K
      by(auto simp add: bq relax_neighbour_view f_def w⇩π_code_is
                        best_even_neighbour(2,3) split: option.split)
  qed
  define rs where "rs = rev rnlist"
  have rs_props: "distinct rs" "set rs = rneighbs l"
    using rnlist
    by (auto simp add: rs_def)
  have news_in_G:"{{l, r} | r. r ∈ set rs} ⊆ G" 
    unfolding rs_props G(5)[OF assms(3)] by blast
  have induction:"?thesis1 ∧ ?thesis2 ∧
        (∀ r k.  (r, k) ∈ heap_abstract queue' ⟶ 
               (∃ l. ben_lookup ben' r = Some l ∧ k = w⇩π l r + off l)) ∧
        (∀ r l'. ben_lookup ben' r = Some l' ∧ (∄ k. (r, k) ∈ heap_abstract queue') ⟶
             off l ≥ w⇩π l' r + off l')
           ∧ ?thesis3 ∧ ?thesis4"
    using assms(1,2,4,5) rnlist(3)[simplified code_is_proof] rs_props(1)  news_in_G
    unfolding rs_def[symmetric] rs_props(2)[symmetric] f_def[symmetric]
              foldl_conv_foldr rs_def[symmetric] 
  proof(induction rs arbitrary: queue ben queue' ben')
    case Nil
    thus ?case
      by simp
  next
    case (Cons r rs)
    define ben_before where "ben_before = (fst (foldr (λx y. f y x) rs (ben, queue)))"
    define queue_before where "queue_before = (snd (foldr (λx y. f y x) rs (ben, queue)))"
    have state_before_is: "(ben_before, queue_before) = foldr (λx y. f y x) rs (ben, queue)"
      by(simp add: ben_before_def queue_before_def)
    have ben'_is: "ben' = (fst (f (ben_before, queue_before) r))"
                  "queue' = (snd (f (ben_before, queue_before) r))"
      using Cons.prems(5) 
      by (simp add: split_pairs ben_before_def queue_before_def)+
    have distinct_rs: "distinct rs" using Cons(7) by auto
  have news_in_G:"{{l, r} | r. r ∈ set rs} ⊆ G"
    using Cons.prems(7) by auto
  have pos_new_e:" w⇩π l r ≥ 0" 
          using Cons.prems(7) w⇩π_non_neg[of l r] by auto
  have r_in_VsG: "r ∈ Vs G"
    using Cons.prems(7) edges_are_Vs_2[of l r G] by auto
  have r_K[simp]: "r ∈ K" "l ≠ nil"
    using in_K(3)[OF r_in_VsG] not_nil(1)[OF assms(3)] by auto
    note IH_applied_all = Cons(1)[OF Cons(2,3,4,5) state_before_is 
             distinct_rs news_in_G]
    note IH_applied = conj6D(1)[OF IH_applied_all]
                      conj6D(2)[OF IH_applied_all]
                      mp[OF spec[OF spec[OF conj6D(3)[OF IH_applied_all]]]]
                      mp[OF spec[OF spec[OF conj6D(4)[OF IH_applied_all]]]]
                      conj6D(5)[OF IH_applied_all]
                       conj6D(6)[OF IH_applied_all]
    show ?case 
      unfolding ben'_is
    proof(rule conj6I, goal_cases)
      case 1
      then show ?case
        using IH_applied
        by(auto split: option.split 
               intro!: best_even_neighbour(2) 
             simp add: f_def)
    next
      case 2
      have helper: "ben_lookup ben r = Some x2 ⟹
          w⇩π l r + off l < w⇩π x2 r + off x2 ⟹
          (r, w⇩π x2 r + off x2) ∈ heap_abstract queue_before" for x2
      proof(rule ccontr, goal_cases)
        case 1
        hence "(r, k) ∈ heap_abstract queue_before ⟹ False" for k
          using Cons.prems(6) IH_applied(3)[of r k] IH_applied(5) by simp
        hence "∄ k. (r, k) ∈ heap_abstract queue_before" by auto
        hence "off l ≥ w⇩π x2 r + off x2"
          using "1"(1) Cons.prems(6) IH_applied_all by auto
        thus ?case
          using "1"(2) pos_new_e by simp
      qed
      from 2 show ?case 
        using IH_applied(1,2) IH_applied(3) Cons.prems(3)[of r] IH_applied(4)[of r] r_in_VsG
        by(auto split: option.split 
               intro!: heap(3,4) helper 
                 dest: IH_applied(3)
             simp add: f_def IH_applied(5))
    next
      case 3
      then show ?case
      proof(cases "ben_lookup ben_before r")
        case None
        hence not_in_heap_before:"∄k. (r, k) ∈ heap_abstract queue_before" 
          using IH_applied(3) by force
        show ?thesis 
        using IH_applied(1,2,3) not_in_heap_before
        by(auto simp add: f_def best_even_neighbour(3) None 
                          heap(10)[OF IH_applied(2) r_in_VsG not_in_heap_before])
      next
        case (Some l')
        hence in_heap_before: "w⇩π l r + off l < w⇩π l' r + off l' ⟹ 
            (r, w⇩π l' r + off l') ∈ heap_abstract queue_before"
          using IH_applied(4)[of r l'] IH_applied(3)[of r] pos_new_e by force
        show ?thesis 
        using IH_applied(1,2,3) heap(9)[OF IH_applied(2) r_in_VsG in_heap_before]
              heap(7)[OF IH_applied(2) in_heap_before]
        by(auto simp add: f_def best_even_neighbour(3) Some)
    qed
    next
      case 4
      then show ?case 
      proof(cases "ben_lookup ben_before r")
        case None
        hence not_in_heap_before:"∄k. (r, k) ∈ heap_abstract queue_before" 
          using IH_applied(3) by force
        show ?thesis 
        using IH_applied(1,2)
        by(auto simp add: f_def best_even_neighbour(3) None 
                          heap(10)[OF IH_applied(2) r_in_VsG not_in_heap_before] 
                  intro!: IH_applied(4))
      next
        case (Some l')
        hence in_heap_before: "w⇩π l r + off l < w⇩π l' r + off l' 
              ⟹  (r, w⇩π l' r + off l') ∈ heap_abstract queue_before"
         using IH_applied(4)[of r l'] IH_applied(3)[of r] pos_new_e by force
        show ?thesis 
        using IH_applied(1,2,3)
        by(auto simp add: f_def best_even_neighbour(3) Some
                          heap(9)[OF IH_applied(2) r_in_VsG in_heap_before]
                  intro!: IH_applied(4))
     qed
    next
      case 5
      show ?case
      proof(cases "ben_lookup ben_before r")
        case None
        hence not_in_heap_before:"∄k. (r, k) ∈ heap_abstract queue_before" 
          using IH_applied(3) by force
        show ?thesis 
        using IH_applied(1,2)
        by(auto simp add: f_def best_even_neighbour(3) None IH_applied(5))
      next
        case (Some l')
        hence in_heap_before: "w⇩π l r + off l < w⇩π l' r + off l' 
             ⟹ (r, w⇩π l' r + off l') ∈ heap_abstract queue_before"
          using IH_applied(4)[of r l'] IH_applied(3)[of r] pos_new_e by force
        show ?thesis 
        using IH_applied(1,2,3)
        by(auto simp add: f_def best_even_neighbour(3) Some IH_applied(5)
                          heap(9)[OF IH_applied(2) r_in_VsG in_heap_before])
    qed
  next
    case 6
     have ben_before_r_is:"ben_lookup ben_before r = ben_lookup ben r"
          using Cons.prems(6) IH_applied(5) by auto
    have Collect_Cons: "{f x | x. x ∈ set (y#ys)}
              = insert ( f y) {f x | x. x ∈ set ys}"
          for f y ys by auto
      show ?case
      proof(cases "ben_lookup ben_before r")
        case None
        hence not_in_heap_before:"∄k. (r, k) ∈ heap_abstract queue_before" 
          using IH_applied(3) by force
        show ?thesis 
          unfolding Collect_Cons
          using None ben_before_r_is Cons.prems(3)[of r]
          by (auto simp add: f_def  None  IH_applied(6) 
                             heap(10)[OF IH_applied(2) r_in_VsG not_in_heap_before] )
      next
        case (Some l')
        hence in_heap_before: 
        "w⇩π l r + off l < w⇩π l' r + off l' ⟹ (r, w⇩π l' r + off l') ∈ heap_abstract queue_before"
          using IH_applied(4)[of r l'] IH_applied(3)[of r] pos_new_e by force
        have if_not_P2:"ben_lookup ben r ≠ None"
          using Some ben_before_r_is by auto
        have ben_of_r_is_l':"(the (ben_lookup ben r)) = l'" 
          using Some ben_before_r_is by auto
        have helper1: " (r, k) ∈ heap_abstract queue ⟹ k = w⇩π l' r + off l'" for k
            using Some ben_before_r_is Cons.prems(3)[of r] Cons.prems(2,4)
            by(auto intro: heap(7))
        show ?thesis
          unfolding Collect_Cons f_def split Some option.case(2)
        proof(cases "w⇩π l r + off l < w⇩π l' r + off l'", goal_cases)
          case 1
          have helpers2: "(r, w⇩π l r + off l) ∈ heap_abstract queue" False
            if "w⇩π l r + off l < w⇩π l' r + off l'" "r ∉ fst ` heap_abstract queue"
               "ben_lookup ben r = Some l'"
            using that Cons.prems(4) image_iff pos_new_e helper1 by fastforce+
          have helpers3: "k = w⇩π (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))"
            if "l' = the (ben_lookup ben r)" "(r, k) ∈ heap_abstract queue" for k
            using that  Cons.prems(4) image_iff pos_new_e helper1 by fastforce
          have helpers4: " k = w⇩π l' r + off l'"
            if"(r, k) ∈ heap_abstract queue" for k
          using that  Cons.prems(4) image_iff pos_new_e helper1 by fastforce
        from 1 show ?case 
            unfolding if_P[OF 1] snd_conv if_not_P[OF if_not_P2] ben_of_r_is_l'
                      heap(9)[OF IH_applied(2) r_in_VsG in_heap_before[OF 1] 1]   
                      IH_applied(6)
            using  ben_of_r_is_l' helpers2 helpers3 helpers4 by auto
        next
          case 2
          thus ?case
            using Cons.prems(3,4,7) helper1 if_not_P2 Some ben_before_r_is
            unfolding if_not_P[OF 2] snd_conv if_not_P[OF if_not_P2] ben_of_r_is_l'
                      IH_applied(6)
            by (auto simp add: rev_image_eqI)
        qed
      qed
    qed
  qed
  show ?thesis1 ?thesis2
    using conj6D(1,2)[OF induction]
    by simp+
  show ?thesis3 
    using conj6D(5)[OF induction] by simp
  show ?thesis4
    using conj6D(6)[OF induction] by simp
  show"⋀ r k. (r, k) ∈ heap_abstract queue'
         ⟹ ∃l. ben_lookup ben' r = Some l ∧ k = w⇩π l r + off l"
    using conj6D(3)[OF induction] by auto
  show "⋀ r l'. ben_lookup ben' r = Some l' ∧ (∄k. (r, k) ∈ heap_abstract queue') ⟹
        w⇩π l' r + off l' ≤ off l"
    using conj6D(4)[OF induction] by auto
  show "rnb_invar C'" "rnb_abstract C' = rnb_abstract rnb_init"
    using update_best_even_neighbour_is_foldl(2,3)[OF assms(7,3,8,6)] by auto
  show "⋀ r l'. ben_lookup ben' r = Some l' ⟹ l' ∈ L ∧ {l', r} ∈ G"
  proof(goal_cases)
    case (1 r l')
    show ?case
      using 1 assms(3) assms(9)[of r] rneighbs_in_G[OF assms(3), of r]
      unfolding conj6D(5)[OF induction]
      by(auto split: if_split_asm)
  qed
qed

lemma update_best_even_neighbours_correct:
  assumes "ben_invar ben" "heap_invar queue" "vset_to_set ls ⊆ L"
          "⋀ r k. (r, k) ∈ heap_abstract queue ⟶
          (∃ l. ben_lookup ben r = Some l ∧ k = w⇩π l r + off l)"
          "⋀ r l' l. ben_lookup ben r = Some l' ∧ (∄ k. (r, k) ∈ heap_abstract queue)  ⟶
             off l ≥ w⇩π l' r + off l'"
          "(C', ben', queue') = update_best_even_neighbours off C ben queue ls"
          "vset_invar ls"
          "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "⋀ r l'. ben_lookup ben r = Some l' ⟶ l' ∈ L ∧ {l', r} ∈ G"
 defines "conn_min ≡ (λ r.
     Min ((if ben_lookup ben r ≠ None
          then {w⇩π (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))}
          else {}) ∪ 
          {w⇩π l r + off l | l. l ∈ vset_to_set ls ∧ r ∈ rneighbs l}))"
 shows "ben_invar ben'" (is ?thesis1) "heap_invar queue'" (is ?thesis2)
       "⋀ r k. (r, k) ∈ heap_abstract queue' ⟹
         (∃ l. ben_lookup ben' r = Some l ∧ k = w⇩π l r + off l)"
       "⋀ r l' l. ben_lookup ben' r = Some l' ∧ (∄ k. (r, k) ∈ heap_abstract queue') ⟹
             off l ≥ w⇩π l' r + off l'"
       "⋀ r. r ∉ ⋃ {rneighbs l| l. l ∈ vset_to_set ls} 
                 ⟹ ben_lookup ben' r = ben_lookup ben r"
       "⋀ r. r ∈ ⋃ {rneighbs l| l. l ∈ vset_to_set ls} 
                 ⟹ ∃ l. ((l ∈ vset_to_set ls ∧ r ∈ rneighbs l)
                            ∨ Some l = ben_lookup ben r) 
                          ∧ w⇩π l r + off l = conn_min r ∧ ben_lookup ben' r = Some l"
      "heap_abstract queue' = 
       heap_abstract queue
           - {(r, k) | r k l. r ∈ rneighbs l ∧l ∈ vset_to_set ls}
           ∪ {(r, w⇩π ll r + off ll) | r l ll. 
               r ∈ rneighbs l ∧ 
               l ∈ vset_to_set ls ∧ Some ll = ben_lookup ben' r ∧
               (r ∈ fst ` (heap_abstract queue) ∨ ben_lookup ben r = None)}"
               (is ?thesis4)
      "rnb_invar C'" "rnb_abstract C' = rnb_abstract rnb_init"
      "⋀ r l'. ben_lookup ben' r = Some l' ⟹ l' ∈ L ∧ {l', r} ∈ G"
proof-
  obtain lslist where lslist: "vset_to_set ls = set lslist" "distinct lslist"
    "vset_iterate_ben 
         (λ cbq r. update_best_even_neighbour off (fst cbq) (fst (snd cbq)) (snd (snd cbq)) r) 
         (C, ben, queue) ls =
    foldl (λ cbq r. update_best_even_neighbour off (fst cbq) (fst (snd cbq)) (snd (snd cbq)) r) 
         (C, ben, queue) lslist"
    using vset_iterations(1)[OF assms(7), of _ "(C, ben, queue)"] by force
  define ls' where "ls' = rev lslist"
  have set_ls_is:"vset_to_set ls = set ls'"
    by(auto simp add: ls'_def lslist(1))
  have induct_result: "(?thesis1 ∧ ?thesis2 ∧
       (∀ r k. (r, k) ∈ heap_abstract queue' ⟶ 
          (∃ l. ben_lookup ben' r = Some l ∧ k = w⇩π l r + off l)) ∧
       (∀ l r l'.  ben_lookup ben' r = Some l' ∧ (∄ k. (r, k) ∈ heap_abstract queue')⟶
             off l ≥ w⇩π l' r + off l') ∧
       (∀ r.  r ∉ ⋃ {rneighbs l| l. l ∈ vset_to_set ls} ⟶ 
         ben_lookup ben' r = ben_lookup ben r) ∧
       (∀ r ∈ ⋃ {rneighbs l| l. l ∈ vset_to_set ls}.  
         ∃l. ((l ∈ vset_to_set ls ∧ r ∈ rneighbs l)
                  ∨ Some l = ben_lookup ben r) ∧ 
             w⇩π l r + off l = conn_min r ∧ ben_lookup ben' r = Some l) ∧
       ?thesis4) ∧
       (rnb_invar C' ∧ rnb_abstract C' = rnb_abstract rnb_init ∧
        (∀ r l'. ben_lookup ben' r = Some l' ⟶ l' ∈ L ∧ {l', r} ∈ G))"
    using assms(1-6) meta_eq_to_obj_eq[OF assms(11)] assms(8,9,10)
    unfolding update_best_even_neighbours_def foldl_conv_foldr
              ls'_def[symmetric] set_ls_is lslist(3)
  proof(induction ls' arbitrary: C' ben' queue' queue ben conn_min)
    case (Cons l ls)
    have ls_in_L: "set ls ⊆ L"
      using Cons(4) by auto
    define result3 where "result3 = 
      foldr (λx y. update_best_even_neighbour off (fst y) (fst (snd y)) (snd (snd y)) x)
            ls (C, ben, queue)"
    define result where "result = snd result3"
    define ben_before where "ben_before = 
     fst result"
    define queue_before where "queue_before = 
     snd result"
    have result_is: "(fst result3, fst result, snd result) = result3"
      by(auto simp add: result_def)
    define conn_min_before where "conn_min_before =
       (λr. Min ((if ben_lookup ben r ≠ None
            then {w⇩π (the (ben_lookup ben r)) r + off (the (ben_lookup ben r))}
            else {}) ∪
           {w⇩π l r + off l | l. (l ∈ set ls ∧ r ∈ rneighbs l)}))"

    note IH_all =
       Cons(1)[OF Cons(2,3) ls_in_L Cons(5,6), simplified result3_def[symmetric],OF
         result_is conn_min_before_def Cons.prems(8,9,10)]
    note IH_applied_all = conjunct1[OF IH_all]
    have IH_graph: "rnb_invar (fst result3)" "rnb_abstract (fst result3) = rnb_abstract rnb_init"
         "⋀ r l'. ben_lookup (fst result) r = Some l' ⟶ l' ∈ L ∧ {l', r} ∈ G"
      using conjunct2[OF IH_all] by auto
    note IH_applied = conj6D(1)[OF IH_applied_all]
                      conj6D(2)[OF IH_applied_all]
                      spec[OF spec[OF conj6D(3)[OF IH_applied_all]]]
                      spec[OF spec[OF spec[OF conj6D(4)[OF IH_applied_all]]]]
                      conj6D(5)[OF IH_applied_all]
                      conjunct1[OF conj6D(6)[OF IH_applied_all]]
                      conjunct2[OF conj6D(6)[OF IH_applied_all]]
    thm Cons(7)
    thm Cons(7)[simplified foldr_Cons o_apply]
    have l_in_L: "l ∈ L" 
      using Cons(4) by simp
    have queue'_heap': "(C', ben', queue') = 
          update_best_even_neighbour off (fst result3) (fst result) (snd result) l"
      by(auto simp add: result3_def result_def Cons(7))
    note single_update = update_best_even_neighbour_correct[OF
            IH_applied(1,2) l_in_L IH_applied(3,4) queue'_heap' IH_graph]
    show ?case 
    proof(rule conjI[OF conj6I], goal_cases)
      case 1
      then show ?case 
        using single_update(1) by simp
    next
      case 2
      then show ?case
        using single_update(2) by simp
    next
      case 3
      then show ?case 
        using single_update(3) by simp
    next
      case 4
      show ?case 
      proof(rule, rule, rule, rule, goal_cases)
        case (1 l1 r1 l'1)
        show ?case 
        proof (cases "l1 = l")
          case True
          then show ?thesis 
           using single_update(4)[of r1 l'1] 1 by simp
        next
          case False
          have helper1: "y = l'1"
            if "r1 ∈ rneighbs l"
               "ben_lookup (fst result) r1 = Some y"
               "(if w⇩π l r1 + off l < w⇩π y r1 + off y then Some l
                 else ben_lookup (fst result) r1) = Some l'1" 
               "r1 ∉ fst ` heap_abstract (snd result)" for y
             apply(cases "w⇩π l r1 + off l < w⇩π y r1 + off y")
             using G(5)[OF l_in_L] IH_applied(4)[of r1 y l] that
                  w⇩π_non_neg[of l r1] 
             by force+
           have helper2: False 
             if "r1 ∈ rneighbs l'1"
                "ben_lookup (fst result) r1 = None"
                "l = l'1" "∀k. (r1, k) ∉ heap_abstract queue'"
             using single_update(6) that by blast
          from False have "ben_lookup (fst result) r1 = Some l'1" 
            using 1 unfolding single_update(5)
            by(cases "r1 ∉ rneighbs l",
               all ‹cases ‹ben_lookup (fst result) r1 = None››)
              (auto simp add: single_update(6) intro: helper1 helper2)
          moreover have "(∄k. (r1, k) ∈ heap_abstract (snd result))"
           using 1 unfolding single_update(5)
           by(cases "r1 ∉ rneighbs l",
              all ‹cases ‹ben_lookup (fst result) r1 = None››)
             (auto simp add: single_update(6) rev_image_eqI)
          ultimately show ?thesis 
            using IH_applied(4)[of r1 l'1 l1] by simp
        qed
      qed
    next
      case 5
      then show ?case 
        using IH_applied(5) single_update(5) by fastforce
    next
      case 6
      show ?case 
      proof(rule, rule ballI, goal_cases)
        case (1 r)
        note one = this
        show ?case 
          unfolding single_update(5) 
        proof(cases "r ∉ rneighbs l", goal_cases)
          case 1
          hence old_conn_min: "conn_min r =  conn_min_before r"
            by(auto intro: arg_cong[of _ _ Min] 
                 simp add: Cons.prems(7) conn_min_before_def )
          obtain l where l: 
           "((l ∈ set ls ∧ r ∈ rneighbs l) ∨ Some l = ben_lookup ben r)"
           "w⇩π l r + off l = conn_min_before r ∧ ben_lookup (fst result) r = Some l"
            using 1 one IH_applied(6) by auto
          show ?case
            using l 1
            by(auto intro!: exI[of _ l] simp add:  old_conn_min)
        next
          case 2
          note two = this
          show ?case
            unfolding if_not_P[OF 2]
          proof(cases "ben_lookup (fst result) r", goal_cases)
            case 1
            hence r_not_previously:
                "r ∉ ⋃ {rneighbs l| l. l ∈ set ls}"
              using IH_applied_all
              by fastforce
            hence init_None:"¬ (ben_lookup ben r ≠ None)" 
              using IH_applied(5)
              using "1" by presburger 
            show ?case
              unfolding Cons.prems(7)  if_P[OF 1] if_not_P[OF init_None]
            proof(rule exI[of _ l], rule forw_subst[of _ "{w⇩π l r + off l}"], goal_cases)
            qed (insert r_not_previously two, auto)
          next
            case (2 ll)
            note Two = this
            have "∃l. ((l ∈ set ls ∧ r ∈ rneighbs l) ∨ Some l = ben_lookup ben r) ∧
              w⇩π l r + off l = conn_min_before r ∧ ben_lookup (fst result) r = Some l"
            proof(cases "r ∈ ⋃ {rneighbs l| l. l ∈ set ls}", goal_cases)
              case 1
              thus ?case
                using IH_applied(6) by auto
            next
              case 2
              show ?case
              proof(rule exI[of _ ll], goal_cases)
                case 1
                show ?case
                unfolding conn_min_before_def
              proof(rule forw_subst[of _ "{w⇩π ll r + off ll}"], goal_cases)
              qed (insert two IH_applied(5) 2 Two, auto intro!:  exI[of _ "the (ben_lookup ben r)"])
            qed
          qed
          hence ll_props: 
              "((ll ∈ set ls ∧ r ∈ rneighbs ll) ∨ Some ll = ben_lookup ben r)"
              "w⇩π ll r + off ll = conn_min_before r" 
              "ben_lookup (fst result) r = Some ll"
            using 2 by auto
          have conn_min_is: "conn_min r = min (w⇩π l r + off l) (conn_min_before r)"
            using ll_props
            unfolding Cons.prems(7) conn_min_before_def
            apply(subst linorder_class.Min_insert[symmetric])
              defer defer
              apply(rule arg_cong[of _ _ Min])
            using IH_applied(5) two by auto
          show ?case
            using 2 two ll_props(1)
            by (auto simp add: "2" ll_props(1,2) conn_min_is)+
        qed
      qed 
      next
        case 2
        have queue'_is:"heap_abstract queue' =
             heap_abstract (snd result) 
               - {(r, k) | r k. r ∈ rneighbs l} ∪
               {(r, w⇩π ll r + off ll) | r ll. r ∈ rneighbs l ∧
                     Some ll = ben_lookup ben' r ∧
               (r ∈ fst ` heap_abstract (snd result) 
                   ∨ ben_lookup (fst result) r = None)}" 
        proof(rule set_eqI, rule, goal_cases)
          case (1 queue_entry)
          then show ?case 
          proof(cases  queue_entry, goal_cases)
            case (1 r' k)
            have helper1: "(r', w⇩π l r' + off l) ∈ heap_abstract (snd result)"
              if "queue_entry = (r', w⇩π l r' + off l)"  
                 " ∀ll. Some ll =
              (if ben_lookup (fst result) r' = None then Some l
               else if w⇩π l r' + off l
                       < w⇩π (the (ben_lookup (fst result) r')) r' +
                         off (the (ben_lookup (fst result) r'))
                    then Some l else ben_lookup (fst result) r') ⟶
              w⇩π l r' + off l = w⇩π ll r' + off ll ⟶
              r' ∉ fst ` heap_abstract (snd result) ∧
              (∃y. ben_lookup (fst result) r' = Some y)"
             "r' ∈ rneighbs l"
             "(r', b) ∈ heap_abstract (snd result)" for b
              using  "1"(1)  single_update(3,5) that
              by force
            have helper2: False
              if "∀ll. Some ll =
              (if ben_lookup (fst result) r' = None then Some l
               else if w⇩π l r' + off l
                       < w⇩π (the (ben_lookup (fst result) r')) r' +
                         off (the (ben_lookup (fst result) r'))
                    then Some l else ben_lookup (fst result) r') ⟶
              w⇩π l r' + off l = w⇩π ll r' + off ll ⟶
              r' ∉ fst ` heap_abstract (snd result) ∧
              (∃y. ben_lookup (fst result) r' = Some y)"
             "(r', b) ∈ heap_abstract (snd result)"
             " w⇩π l r' + off l
              ≤ w⇩π (the (ben_lookup (fst result) r')) r' +
            off (the (ben_lookup (fst result) r'))" for b
              apply(cases "ben_lookup (fst result) r' = None")
               apply (all ‹cases "w⇩π l r' + off l < w⇩π (the (ben_lookup (fst result) r')) r'
                                            + off (the (ben_lookup (fst result) r'))"›)
              using  that
              by force+
            have helper3: False
              if "∀ll. Some ll =
              (if ben_lookup (fst result) r' = None then Some l
               else if w⇩π l r' + off l
                       < w⇩π (the (ben_lookup (fst result) r')) r' +
                         off (the (ben_lookup (fst result) r'))
                    then Some l else ben_lookup (fst result) r') ⟶
              w⇩π (the (ben_lookup (fst result) r')) r' +
              off (the (ben_lookup (fst result) r')) =
              w⇩π ll r' + off ll ⟶
              r' ∉ fst ` heap_abstract (snd result) ∧
              (∃y. ben_lookup (fst result) r' = Some y)"
         "(r', b) ∈ heap_abstract (snd result)"
         "w⇩π (the (ben_lookup (fst result) r')) r' +
         off (the (ben_lookup (fst result) r'))
         ≤ w⇩π l r' + off l" for b
            using  that IH_applied(3)
              by (force simp add: if_split)+
            from 1 show ?thesis  
               using IH_applied(3)
             unfolding single_update(6) 
             by(force intro!: helper1 
                       intro: helper2 helper3 
                    simp add: single_update(5)
                      intro!: P_of_minI[of  _ _ "λ x. (r', x) ∈ heap_abstract (snd result)"]
                       elim!: P_of_minE[of "λ x. k = x"])
         qed
       qed (auto simp add: single_update(5,6) rev_image_eqI if_split)       
       show ?case 
         unfolding  queue'_is  IH_applied(7)
         unfolding Un_Diff  Un_assoc
       proof(rule arg_cong2[where f = union], goal_cases)
         case 2
         have helper: "r ∈ rneighbs l"
           if "⋀ la lla. ⟦r ∈ rneighbs la;
                              w⇩π ll r + off ll = w⇩π lla r + off lla⟧⟹
                   la ≠ l ∧ la ∉ set ls ∨ Some lla ≠ ben_lookup ben' r"
             "r ∈ rneighbs la" "la ∈ set ls"
             " Some ll = ben_lookup (fst result) r" for r ll la
             using that
             by(cases "r ∉ rneighbs l") 
               (auto simp add: single_update(5))
           show ?case
           proof(rule, all ‹rule›, goal_cases)
             case (1 rk)
             show ?case 
             proof(rule UnE[OF 1], goal_cases)
               case 1
               then show ?case 
                 by (force simp add:  single_update(5))
             next
               case 2
               then obtain r ll where rll:"rk = (r, w⇩π ll r + off ll)"
                                      "r ∈ rneighbs l"
                                      "Some ll = ben_lookup ben' r"
                 "r ∈ fst `
                (heap_abstract queue -
                {(r, k) | r k l. r ∈ rneighbs l ∧ l ∈ set ls} ∪
                { (r, w⇩π ll r + off ll) | r ll l. 
                      r ∈ rneighbs l ∧
                      l ∈ set ls ∧
                      Some ll = ben_lookup (fst result) r ∧
                      (r ∈ fst ` heap_abstract queue ∨ ben_lookup ben r = None)})
                ∨  ben_lookup (fst result) r = None"
                 by blast
               have helper: "⟦ben_lookup (fst result) r = Some y;
                   ben_lookup ben r = Some ya⟧ ⟹ ∃x∈heap_abstract queue. r = fst x" 
                 "⟦ben_lookup (fst result) r = None; ben_lookup ben r = Some y⟧ ⟹ ∃x∈heap_abstract queue. r = fst x"
                 for y ya
                 using IH_applied rll(4) 
                 by fastforce+
               show ?case 
                 unfolding if_split image_iff  single_update(5)
                 apply(rule CollectI)
                 apply(rule exI[of _ r])
                 apply(rule exI[of _ l])
                 apply(rule exI[of _ ll])
                 by(auto simp add: rll  single_update(5) intro: helper)
             qed
           next
             case (2 rk)
             then obtain r la ll where rk: "rk = (r, w⇩π ll r + off ll)"
             "r ∈ rneighbs la"
             "la ∈ set (l # ls)"
             "Some ll = ben_lookup ben' r"
             "(r ∈ fst ` heap_abstract queue ∨ ben_lookup ben r = None)"
               by auto
             show ?case 
             proof(cases "la = l")
               case True
               have helper: 
            "⟦ben_lookup ben r = None; ben_lookup (fst result) r = Some y⟧ ⟹
             ∃b. (r, b) ∈ heap_abstract queue ∧
             (∀l. r ∈ rneighbs l ⟶ l ∉ set ls) ∨
             b = w⇩π y r + off y ∧ (∃l. r ∈ rneighbs l ∧ l ∈ set ls)" for y
                 using IH_applied(5) by force
               from True show ?thesis 
                 using rk 
                 unfolding single_update(5)
                 by (auto intro: helper simp add: image_iff Diff_iff Bex_def)+
             next
               case False
               then show ?thesis 
               using rk 
               unfolding single_update(5) if_split
               apply(cases "r ∉ rneighbs l")
                apply(all ‹cases "ben_lookup (fst result) r = None"›)
               by(auto simp add: image_iff Bex_def)+
             qed
           qed
         qed auto
       qed
     next
       case 7
       show ?case
         using single_update(7,8,9) by auto
     qed
   qed auto
   thus ?thesis1 ?thesis2 ?thesis4       
        "⋀ r. r ∉ ⋃ {rneighbs l| l. l ∈ vset_to_set ls} 
                 ⟹ ben_lookup ben' r = ben_lookup ben r"
        "⋀ r. r ∈ ⋃ {rneighbs l| l. l ∈ vset_to_set ls} 
                 ⟹ ∃ l. ((l ∈ vset_to_set ls ∧ r ∈ rneighbs l)
                             ∨ Some l = ben_lookup ben r) 
                          ∧ w⇩π l r + off l = conn_min r ∧ ben_lookup ben' r = Some l"
        "⋀ r k. (r, k) ∈ heap_abstract queue' ⟹
         (∃ l. ben_lookup ben' r = Some l ∧ k = w⇩π l r + off l)"
       "⋀ r l' l. ben_lookup ben' r = Some l' ∧ (∄ k. (r, k) ∈ heap_abstract queue') ⟹
             off l ≥ w⇩π l' r + off l'"
    by auto
  show "rnb_invar C'" "rnb_abstract C' = rnb_abstract rnb_init"
       "⋀ r l'. ben_lookup ben' r = Some l' ⟹ l' ∈ L ∧ {l', r} ∈ G"
    using induct_result by auto
qed

subsection ‹Invariant Preservation›

lemma invar_pres_one_step:
  assumes "search_path_loop_cont_cond state"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
  shows "invar_basic (search_path_loop_cont_upd state)"
    "invar_feasible_potential (search_path_loop_cont_upd state)"
    "invar_forest_tight (search_path_loop_cont_upd state)"
    "invar_matching_tight (search_path_loop_cont_upd state)"
    "invar_best_even_neighbour_heap (search_path_loop_cont_upd state)"
    "invar_best_even_neighbour_map (search_path_loop_cont_upd state)"
    "invar_out_of_heap (search_path_loop_cont_upd state)"
    "card (aevens (search_path_loop_cont_upd state) ∪
                 aodds (search_path_loop_cont_upd state)) = 
        card (aevens state ∪ aodds state)+2"
proof-
  define F where "F = forest state"
  define ben where "ben = best_even_neighbour state"
  define missed_ε where  "missed_ε = missed_at state"
  obtain queue heap_min where queue_heap_min_def:
    " (queue, heap_min) = heap_extract_min (heap state)"
    by(cases "heap_extract_min (heap state)") auto
  obtain r where r_def: "heap_min = Some r"
    using queue_heap_min_def assms(1)
    by(auto elim: search_path_loop_cont_condE)
  define l where "l = the (ben_lookup ben r)"
  define acc' where "acc' = w⇩π l r + missed_ε l"
  obtain l' where l'_def: "buddy r = Some l'"
    using queue_heap_min_def assms(1)
    by(auto elim: search_path_loop_cont_condE simp add: r_def)
  define missed' where "missed' = missed_upd (missed_upd (missed state) r acc') l' acc'"
  obtain C' ben' queue' where ben'_queue'_def:
    "(C', ben', queue') = update_best_even_neighbour 
                                           (missed_get missed')
                                           (neighb_coll state) ben queue l'"
    by(metis prod_cases3)
  define F' where "F'= extend_forest_even_unclassified F l r l'"
  define state' where "state' = state ⦇ forest:= F', 
                            best_even_neighbour:=ben', neighb_coll:=C',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' ⦈"
  obtain k where k: "(r, k) ∈ heap_abstract (heap state)"
    "⋀ x' k'. (x', k') ∈ heap_abstract (heap state) ⟹ k ≤ k'"
    using r_def  pair_eq_fst_snd_eq[OF queue_heap_min_def]
      heap(5)[of "heap state" r] assms(2)
    by(auto elim!: invar_basicE)
  have r_unclassified: "r ∈ Vs G - aevens state - aodds state"
    using assms(6) k
    by (auto elim: invar_best_even_neighbour_heapE)
  have r_l_props: "{r, l} ∈ G" "l ∈ aevens state"
    "w⇩π l r + missed_at state l =
         Min {w⇩π l r + missed_at state l| l. l ∈ aevens state ∧ {l, r} ∈ G}"
    using assms(6,7) r_unclassified r_def  k(1) 
    by(fastforce elim!: invar_best_even_neighbour_mapE 
        dest: invar_best_even_neighbour_heapD 
        simp add: l_def ben_def)+
  have l_code: "w⇩π_code l r = w⇩π l r"
    using r_l_props(1,2) invar_basicD(9)[OF assms(2)]
    by(auto intro!: w⇩π_code_is simp add: insert_commute)
  have l_get: "ben_get (best_even_neighbour state) r = l"
    using invar_best_even_neighbour_heap_get[OF assms(6) k(1)] by(simp add: l_def ben_def)
  have upd_state_is_state':"search_path_loop_cont_upd state =  state'"
    using ben'_queue'_def r_def l'_def queue_heap_min_def l_code[unfolded l_def ben_def] l_get
    by(auto simp add: search_path_loop_cont_upd_def state'_def Let_def
        F'_def  missed'_def acc'_def l_def ben_def missed_ε_def F_def
        split: option.split prod.split)
  have k_is: "k = w⇩π l r + missed_at state l"
    using assms(6) ben_def k(1) l_def
    by(fastforce dest: invar_best_even_neighbour_heapD)
  have r_l'_in_M:"{r, l'} ∈ ℳ"
    using ℳ_def l'_def by fastforce
  have l'_not_even:"l' ∈ vset_to_set (evens F) ⟹ False"
  proof(goal_cases)
    case 1
    hence "{r, l'} ∈ abstract_forest F"
      using assms(2) evens_and_odds(3)[of ℳ F]  roots(2)[of ℳ F] higher_forest_properties(2)[OF  _ r_l'_in_M, of F] 
      by(auto elim!: invar_basicE dest!: 
          simp add: F_def)
    hence "r ∈ aevens state ∪ aodds state"
      using  assms(2) 1
      by(auto elim!: invar_basicE 
          simp add: F_def higher_forest_properties(3)  insert_commute)
    thus False
      using r_unclassified by blast
  qed
  have l'_not_even_or_odd:
    "l' ∈ vset_to_set (evens F) ∪  vset_to_set (odds F) ⟹ False"
  proof(goal_cases)
    case 1
    hence "{r, l'} ∈ abstract_forest F"
      using assms(2) evens_and_odds(3)[of ℳ F]  roots(2)[of ℳ F] higher_forest_properties(2)[OF  _ r_l'_in_M, of F] 
      by(auto elim!: invar_basicE dest!: 
          simp add: F_def)
    hence "r ∈ aevens state ∪ aodds state"
      using   1 higher_forest_properties(3)[of ℳ F]
      by(force intro: invar_basicE[OF assms(2)] 
          simp add: F_def   insert_commute)
    thus False
      using r_unclassified by blast
  qed
  have r_not_even_or_odd:
    "r ∈ vset_to_set (evens F) ∪  vset_to_set (odds F) ⟹ False"
    using F_def r_unclassified by fastforce
  have l_r_not_in_M:"{l, r} ∈ ℳ ⟹ False" 
    using r_l_props(2) assms(2) higher_forest_properties(2,3)[of ℳ F l r] 
      r_not_even_or_odd evens_and_odds(3)[of ℳ F]
    by(auto elim!: invar_basicE simp add: F_def)
  have l_in_L:"l ∈ L"
    using  assms(2) r_l_props(2)
    by(auto elim!: invar_basicE)
  hence r_in_R: "r ∈ R"
    using G(1) bipartite_edgeD(3) l_in_L r_l_props(1) by fastforce
  moreover have r_l'_in_G:"{r, l'} ∈ G"
    using l'_def matching(2) by blast
  ultimately have l'_in_L: "l' ∈ L" 
    using   bipartite_edgeD(2)[OF _ G(1)]
    by(auto simp add: insert_commute)
  have r_l'_K[simp]: "r ∈ K" "l' ∈ K"
    using in_K(1)[OF l'_in_L] in_K(2)[OF r_in_R] by auto  have ben_l'_None:"ben_lookup ben l' = None"
    using  bipartite_edgeD(1)[OF _ G(1)] edges_are_Vs_2[OF r_l'_in_G] 
      l'_in_L l'_not_even_or_odd  r_l'_in_G assms(2)
    by (auto elim!: invar_basicE 
        intro!: invar_best_even_neighbour_mapD(1)[OF assms(7), of l']
        simp add: ben_def F_def)
  have l'_not_a_ben: "ben_lookup ben rr = Some l' ⟹ False" for rr 
    using F_def assms(2)  l'_not_even 
    by(force elim!: invar_basicE simp add:  ben_def) 
  have queue'_is: "heap_abstract (fst (heap_extract_min (heap state))) =
         heap_abstract (heap state) - {(r, w⇩π l r + missed_at state l)}"
    using assms(2) k(1) k_is
    by(intro heap(8))
      (auto elim!: invar_basicE 
        simp add: r_def[symmetric] pair_eq_fst_snd_eq[OF queue_heap_min_def])
  note basic_invars = invar_basicD[OF assms(2)]
  have ben_edges_before: "ben_lookup ben rr = Some ll ⟶ ll ∈ L ∧ {ll, rr} ∈ G" for rr ll
    using basic_invars(9,11) basic_invars(15)[of rr ll] 
    by(fastforce simp add: ben_def)
  have r_l_l'_distinct:"r ≠ l" "l ≠ l'" "r ≠ l'"
    using r_l_props(2) r_unclassified  bipartite_edgeD(2)[OF r_l'_in_G  G(1)] r_in_R 
          F_def l'_not_even by auto
  hence forest_extension_precond: "forest_extension_precond F ℳ l r l'"
    using l'_not_even_or_odd r_not_even_or_odd l_r_not_in_M 
    by(auto intro!: forest_extension_precondI  ℳ_is_matching
        simp add: F_def assms(2) invar_basicD(1) r_l_props(2)  r_l'_in_M)
  have missed'_is: "missed_get missed' = 
                    (λ x. if x = r ∨ x = l' then acc' else missed_at state x)"
    using invar_basicD(4)[OF assms(2)] in_K(1)[OF l'_in_L] in_K(2)[OF r_in_R]
    by(auto simp add: missed'_def acc'_def missed(3,4))
  have queue_props: "heap_invar queue" 
    "heap_abstract queue = heap_abstract (heap state) - {(r, acc')}"
    "⋀ r' k'. (r', k') ∈ heap_abstract (heap state) ⟹ acc' ≤ k'"
    using invar_basicD(3)[OF assms(2)] heap(2)[of "heap state"] k(2) k_is 
    by (auto simp add: pair_eq_fst_snd_eq[OF queue_heap_min_def] missed_ε_def  acc'_def   queue'_is )
  have update_best_even_neighbour_conditions:
    "ben_invar ben" "heap_invar queue" "l' ∈ L"
    "⋀r k. (r, k) ∈ heap_abstract queue ⟶  
            (∃l. ben_lookup ben r = Some l ∧
             k = w⇩π l r + missed_get missed' l)"
    "⋀r l'a. ben_lookup ben r = Some l'a ∧ (∄k. (r, k) ∈ heap_abstract queue) ⟶
                 w⇩π l'a r + missed_get missed' l'a
                ≤ missed_get missed' l'"
  proof(goal_cases)
    case 1
    then show ?case 
      using assms(2) ben_def invar_basicD(2) by blast
  next
    case 2
    then show ?case 
      using heap(2)[OF invar_basicD(3)[OF  assms(2)]] queue_heap_min_def[symmetric] 
      by simp
  next
    case 3
    then show ?case 
      using l'_in_L by simp
  next
    case (4 rr k)
    then show ?case 
      using l'_not_even r_not_even_or_odd 
            invar_best_even_neighbour_mapD[OF assms(7), of rr]
      by(fastforce intro: exI[of _ "the (ben_lookup (best_even_neighbour state) rr)"]
                simp add: ben_def pair_eq_fst_snd_eq[OF queue_heap_min_def] F_def
                          queue'_is missed'_is invar_best_even_neighbour_heapD[OF assms(6)])
  next
    case (5 rr ll)
    show ?case 
    proof(rule, goal_cases)
      case 1
      note One = this
      hence h1:"r ≠ ll"
        using assms(2)  r_not_even_or_odd 
        by(force elim!: invar_basicE simp add: ben_def F_def)
      have h2: "ll ≠ l'"
        using l'_not_a_ben 1 by blast
      have cases:"(∄k. (rr, k) ∈ heap_abstract (heap state)) ∨ rr = r"
        using 1 unfolding queue_props(2) by blast
      have ll_ben_of_rr_old:"ben_lookup (best_even_neighbour state) rr = Some ll" 
        using One ben_def by fastforce
      show ?case
        unfolding missed'_is
        apply(subst (2) if_P,  simp)
        apply(subst if_not_P)
        using h1 h2 apply simp
      proof(cases rule: disjE[OF cases], goal_cases)
        case 1
        note one = this
        have "kr∈heap_abstract (heap state) ⟹ w⇩π ll rr + missed_at state ll ≤ snd kr" for kr
          using invar_out_of_heapD[OF assms(8) ll_ben_of_rr_old 1] by simp
        moreover have "(r, w⇩π l r + missed_at state l) ∈ heap_abstract (heap state)"
          using k(1) k_is by blast
        ultimately show ?case 
          by(auto simp add: acc'_def missed_ε_def)
      next
        case 2
        hence "w⇩π ll rr + missed_at state ll = acc'"
          using One acc'_def l_def missed_ε_def by auto
        thus ?case by blast
      qed
    qed
  qed 
  note after_ben_update = update_best_even_neighbour_correct[OF
      update_best_even_neighbour_conditions ben'_queue'_def basic_invars(13,14) ben_edges_before]
  have F'_is: "abstract_forest F' = abstract_forest F ∪ {{l, r}, {r, l'}}"
    "vset_to_set (evens F') = insert l' (vset_to_set (evens F))"
    "vset_to_set (odds F') = insert r (vset_to_set (odds F))"
    "vset_invar (evens F')"  "vset_invar (odds F')"
    "forest_invar ℳ F'"
    using F'_def forest_extend(1,2,3,4)[OF forest_extension_precond] 
      evens_and_odds(1,2) by force+
  show invar_basic_step: "invar_basic (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_basicI, goal_cases )
    case 1
    then show ?case 
      by(auto intro!: forest_extend(1) 
          simp add: state'_def F'_def forest_extension_precond)
  next
    case 2
    then show ?case
      using after_ben_update(1)
      by(auto simp add: state'_def)
  next
    case 3
    then show ?case 
      by (simp add: after_ben_update(2) state'_def)
  next
    case 4
    then show ?case
      by (simp add: assms(2) invar_basicD(4) missed'_def missed(3) state'_def)
  next
    case 5
    then show ?case
      using assms(2)
      by(auto elim: invar_basicE 
          simp add: state'_def F'_is(1) edge_commute r_l_props(1) r_l'_in_G F_def)
  next
    case 6
    then show ?case 
    proof(rule, goal_cases)
      case (1 x)
      thus ?case
        using assms(2)
        apply(cases ‹ben_lookup (best_even_neighbour state) x = None›)
         apply(all ‹cases "x ∉ rneighbs l'"›)
        by(auto elim!: invar_basicE 
            simp add: state'_def after_ben_update(5) ben_def G(5) 
            edges_are_Vs_2 l'_in_L)
    qed
  next
    case 7
    have "{v. missed_get missed' v ≠ 0} ⊆ Vs G"
      using invar_basicD(7)[OF assms(2)] r_unclassified edges_are_Vs_2[OF r_l'_in_G]
      by(auto simp add: missed'_is)
    thus ?case 
      by(simp add: state'_def)
  next
    case 8
    then show ?case 
    proof(rule, goal_cases)
      case (1 x)
      then obtain k where "(x, k) ∈ heap_abstract queue ∨ x ∈ rneighbs l'" 
        by(fastforce simp add: state'_def  after_ben_update(6))
      thus ?case 
        using assms(2) G(5) l'_in_L
        by(auto elim!: invar_basicE simp add: queue_props(2))
    qed
  next
    case 9
    show ?case
      using assms(2) l'_in_L
      by(auto elim!: invar_basicE simp add: state'_def F'_is F_def)
  next
    case 10
    show ?case
      using assms(2) r_in_R
      by(auto elim!: invar_basicE simp add: state'_def F'_is F_def)
  next
    case 11
    show ?case
      using assms(2)
      by(auto elim!: invar_basicE 
          simp add: F_def ben_def F'_is state'_def after_ben_update(5))+
  next
    case 12 
    show ?case 
      using r_l'_in_G basic_invars(12)
      by(auto simp add: state'_def F'_is F_def ben_def after_ben_update(5) G(5)[OF  l'_in_L] insert_commute)
  next
    case 13
    show ?case
      using after_ben_update(7) by(simp add: state'_def)
  next
    case 14
    show ?case
      using after_ben_update(8) by(simp add: state'_def)
  next
    case (15 rr ll)
    show ?case
      using after_ben_update(9)[of rr ll] 15 by(auto simp add: state'_def)
  next
    case 16
    show ?case
      using basic_invars(16) forest_extend(5)[OF forest_extension_precond]
      by (simp add: state'_def F'_def F_def)
  qed
  have F_invar:"forest_invar ℳ (forest state)" "vset_invar (evens (forest state))"
    "vset_invar (odds (forest state))"
    using assms(2) by(auto elim!: invar_basicE intro: evens_and_odds)
  hence F_even_odd_disjoint:"vset_to_set (evens F) ∩ vset_to_set (odds F) = {}"
    using F_def evens_and_odds(4) by blast
  have vset_is_old_F_sames:
      "vset_isin (odds (forest state)) x ⟷ x ∈ vset_to_set (odds F)"
       "vset_isin (evens (forest state)) x ⟷ x ∈ vset_to_set (evens F)" for x
    using F_def F_invar(2,3) vset.fixed_univ_set_isin by auto
  show "invar_feasible_potential (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
    text ‹A part of the proof for this invariant is discussed in the paper.
          The vertices $u$, $v$, $w$ in the paper are $l$, $r$ and $l'$ in the
          formalisation, respectively.›
  proof(rule invar_feasible_potentialI, goal_cases)
    case (1 u v)
    text ‹Wlog. assume $u'$ and $v'$ on the left and the right hand side, respectively.›
    then obtain u' v' where u'v': "{u', v'} = {u, v}" "u' ∈ L" "v' ∈ R"  "{u', v'} ∈ G"
      using G(1) by(force elim!: bipartite_edgeE)
    text ‹This is the case analysis whether $u'$ and $v'$ are even or odd after this iteration
          of the algorithm, respectively.
          We then have 4, 2, 2 and 1 subcases.›
    have u'v'_cases: P 
      if "⟦u' ∈ insert l' (aevens state); v' ∈ insert r (aodds state)⟧ ⟹ P"
        "⟦u' ∉ insert l' (aevens state); v' ∈ insert r (aodds state)⟧ ⟹ P"
        "⟦u' ∈ insert l' (aevens state); v' ∉ insert r (aodds state)⟧ ⟹ P"
        "⟦u' ∉ insert l' (aevens state); v' ∉ insert r (aodds state)⟧ ⟹ P" for P
      using that by blast
    have "π⇧* state' u' + π⇧* state' v' ≤ 𝗐 u' v'"
    proof(rule u'v'_cases, goal_cases)
      text ‹This is the case for which the proof is fully discussed in the paper.›
      case 1
      hence u'v'_in:
        "vset_isin (evens (forest state')) u'" "¬ vset_isin (evens (forest state')) v'"
        "vset_isin (odds (forest state')) v'"
        using r_unclassified l'_not_even_or_odd F_even_odd_disjoint
        by(auto simp add: state'_def F'_is(2-5) vset.fixed_univ_set_isin F_def r_l_l'_distinct(3))
      hence **: "π⇧* state' u' + π⇧* state' v' =
               π u' - missed_at state' u' + π v' + missed_at state' v'"
        by(auto simp add: working_potential_def)
      text ‹Case (1a)›
      have case_1a: ?case if "u' ≠ l'" "v' ≠ r"
      proof-
        have "missed_at state' u'= missed_at state u'"
          "missed_at state' v'= missed_at state v'"
          using that "1"(1,2) r_unclassified l'_not_even_or_odd
          by(auto simp add: state'_def missed'_is F_def)
        hence "π⇧* state' u' + π⇧* state' v' = π⇧* state u' + π⇧* state v'"
          using F_even_odd_disjoint 1(1,2) that(1,2)
          by(auto simp add: working_potential_def u'v'_in vset_is_old_F_sames F_def)
        thus ?thesis
          by (simp add: assms(3) invar_feasible_potentialD u'v'(4))
      qed
      text ‹Case (1b)›
      have case_1b: ?case if "u' ≠ l'" "v' = r"
      proof-
        have "missed_at state' v' = missed_at state l + w⇩π l r"
          using that
          by(auto simp add: state'_def missed'_is acc'_def missed_ε_def)
        hence "π⇧* state' u' + π⇧* state' v' ≤ 
                π u' - missed_at state' u' + π v' + missed_at state u' + w⇩π u' r"
          using 1(1) that(1)  u'v'(4)[simplified that(2)] basic_invars(1) finite_forest(1)
          by(auto simp add: ** r_l_props(3)[simplified add.commute[of "w⇩π l r"]]
              intro!: Min.coboundedI exI[of _ u'])
        also have "... = π u' + π v' + w⇩π u' r"
          using that(1) that(2) u'v'_in(1,2)
          by(auto simp add: state'_def missed'_is)
        also have "... = 𝗐  u' v'"
          using that(2) by(auto simp add: w⇩π_def)
        finally show ?thesis 
          by simp
      qed
      text ‹Case (1c)›
      have case_1c: ?case if "u' = l'" "v' ≠ r"
      proof-
        have "π⇧* state' u' + π⇧* state' v' = 
               π l' - w⇩π l r - missed_at state l + π v' + missed_at state' v'"
          using that F_even_odd_disjoint 1(2)
          by(auto simp add: working_potential_def state'_def
              missed'_is acc'_def missed_ε_def F'_is(2-5) vset.fixed_univ_set_isin F_def)
        also have "... =  π l' - (𝗐 l r  - π⇧* state l - π⇧* state r) + π v'
                            + missed_at state' v' - acc state"
          using  r_not_even_or_odd F_even_odd_disjoint r_l_props(2)
          by (auto simp add:  working_potential_def vset_is_old_F_sames F_def w⇩π_def)
        also have "... ≤ π l'  + π v' + missed_at state' v' - acc state"
          using invar_feasible_potentialD[OF assms(3), of l r]  r_l_props(1)
          by(auto simp add: insert_commute)
        also have "... = π⇧* state u' + π⇧* state v'"
          using l'_not_even that(1) F_even_odd_disjoint l'_not_even_or_odd u'v'_in(1,2) 1(2)
          by(auto simp add: working_potential_def vset_is_old_F_sames 
              state'_def missed'_is acc'_def missed_ε_def that(2) F_def)
        also have "... ≤ 𝗐 u' v'"
          using u'v'(4) assms(3)
          by (auto elim!: invar_feasible_potentialE)
        finally show ?thesis 
          by simp
      qed
      text ‹Case (1d)›
      have case_1d: ?case if "u' = l'" "v' = r"
      proof-
        have "missed_at state' = missed_get missed'"
          by(auto simp add: state'_def)
        hence  "π⇧* state' u' + π⇧* state' v' = π u' + π v'"
          by(auto simp add: ** missed'_is that(1,2)[symmetric])
        also have "... ≤ 𝗐 u' v'"
          by (simp add: G(7) u'v'(4))
        finally show ?thesis 
          by simp
      qed
      then show ?case 
        using case_1a case_1b case_1c case_1d 
        by auto
      text ‹The next cases are only hinted in the paper.›
       next
         case 2
         hence u'_v'_isins:
           "¬vset_isin (evens (forest state')) u'" "¬ vset_isin (odds (forest state')) u'"
           "¬ vset_isin (evens (forest state')) v'" "vset_isin (odds (forest state')) v'"
           using r_unclassified l'_not_even_or_odd F_even_odd_disjoint u'v'(2)
                 bipartite_edgeD(3)[OF u'v'(4) G(1)] r_in_R  basic_invars(10) 
                 bipartite_eqI[OF G(1) u'v'(4), of u' v']
            by(auto simp add: state'_def F'_is(2-5) vset.fixed_univ_set_isin F_def r_l_l'_distinct(3))
         hence **: "π⇧* state' u' + π⇧* state' v' =
            π u'  + π v' + missed_at state' v' -  acc state'"
           by(simp add: working_potential_def)
         have case_2a: ?case
           if "v' = r" 
         proof-
           have "missed_at state' v' = acc state'" 
             by(auto simp add: state'_def missed'_is that)
           hence "π⇧* state' u' + π⇧* state' v' = π u' + π v'"
             by(simp add: **)
           also have "...≤ 𝗐 u' v'"
             using G(7) u'v'(4) by auto
           finally show ?thesis 
             by simp
         qed
         have case_2b: ?case
           if "v' ≠ r"
         proof-
           have "missed_at state' v' = missed_at state v'"
             using that  l'_not_even_or_odd 2(2)
             by(auto simp add: state'_def missed'_is F_def)
           moreover have "missed_at state' u' = missed_at state u'"
             using that bipartite_eqI[OF G(1) u'v'(4), of u' v']  u'v'(2,3) r_in_R 2(1)
             by(auto simp add: state'_def missed'_is)
           moreover have "acc state' = w⇩π l r + missed_at state l"
             by(auto simp add: state'_def acc'_def missed_ε_def)
           ultimately have "π⇧* state' u' + π⇧* state' v' =
                π u'  + π v' + missed_at state v' -  (w⇩π l r + missed_at state l)"
             by(simp add: **)
           moreover have "w⇩π l r + missed_at state l + w⇩π u' v' ≥ missed_at state v'"
           proof-
             have "π u' + π v' - acc state + missed_at state v' ≤ 𝗐 u' v'"
                 (*unfolding π* of old state*)
                 using "2"(1,2)  F_even_odd_disjoint   G(7)[OF u'v'(4)] basic_invars(10)
                        bipartite_eqI[OF G(1) u'v'(4), of u' v']   u'_v'_isins(2,4)
                        that invar_feasible_potentialD[OF assms(3) u'v'(4)] that
                 by(cases "u' ∈ aodds state", all ‹cases "v' ∈ aevens state"›)
                   (auto simp add: w⇩π_def working_potential_def  F_def 
                             vset.fixed_univ_set_isin[OF F_invar(2)] vset.fixed_univ_set_isin[OF F_invar(3)])
               moreover have "π l + π r + acc state - missed_at state l ≤ 𝗐 l r"
                 (*unfolding π* of old state*)
                 using "2"(1,2)  F_even_odd_disjoint G(6)[OF r_l_props(1)]  basic_invars(10)
                       r_l_props(2) r_not_even_or_odd that
                       invar_feasible_potentialD[OF assms(3) r_l_props(1)]
                 by(cases "r ∈ aodds state", all ‹cases "r ∈ aevens state"›)
                   (auto simp add: w⇩π_def working_potential_def  F_def
                        vset.fixed_univ_set_isin[OF F_invar(2)] vset.fixed_univ_set_isin[OF F_invar(3)])
               ultimately show ?thesis
                 by(auto simp add: w⇩π_def)
             qed
           ultimately show "π⇧* state' u' + π⇧* state' v' ≤ 𝗐 u' v'"
             by (auto simp add: algebra_simps  w⇩π_def)
         qed 
         then show ?case 
           using case_2a case_2b 
           by auto
       next
         case 3
         hence u'_v'_isins:
           "vset_isin (evens (forest state')) u'"
           "¬ vset_isin (evens (forest state')) v'" "¬vset_isin (odds (forest state')) v'"
           using F_even_odd_disjoint u'v'(2) bipartite_edgeD(3)[OF u'v'(4) G(1)] 
                 bipartite_eqI[OF G(1) u'v'(4), of u' v'] basic_invars(9) l'_in_L
            by(auto simp add: state'_def F'_is(2-5) vset.fixed_univ_set_isin F_def r_l_l'_distinct(3))
          hence **: "π⇧* state' u' + π⇧* state' v' =
            π u'  + π v' - missed_at state' u' +  acc state'"
            by(simp add: working_potential_def)
          have case_3a: ?case
            if "u' = l'"
          proof-
            have "missed_at state' u' = acc state'"
              by(auto simp add: that state'_def missed'_is)
            thus ?thesis
              by(simp add: ** G(7) u'v'(4))
          qed
          have case_3b: ?case
            if That: "u' ≠ l'"
          proof-
            have "missed_at state' u' + w⇩π u' v'≥ acc state'"
            proof-
              obtain lu where lu: "Some lu = ben_lookup (best_even_neighbour state) v'"
                "{v', lu} ∈ G" "lu ∈ aevens state"
                "w⇩π lu v' + missed_at state lu =
                      Min {w⇩π l v' + missed_at state l | l. l ∈ aevens state ∧ {l, v'} ∈ G}"
                using invar_best_even_neighbour_mapD(2)[OF assms(7), of v', OF _ _ _ exI[of _ u']] 
                  u'v'(4) "3"(1,2) That basic_invars(9) bipartite_edgeD(3)[OF u'v'(4) G(1)] 
                  edges_are_Vs_2 
                by fastforce
              hence  "w⇩π lu v' + missed_at state lu ≤ w⇩π u' v' + missed_at state u'"
                using F_invar(1) finite_forest(1) that u'v'(4) 3(1)
                by(auto intro!: linorder_class.Min.coboundedI exI[of _ u'] 
                    simp add: lu(4))
              moreover have "w⇩π lu v' + missed_at state lu ≥ w⇩π l r + missed_at state l"
                using lu(1) u'v'(2,4) basic_invars(9) 3(2)
                by(intro k(2)[simplified k_is, of v'])
                  (auto simp add: invar_best_even_neighbour_heapD[OF assms(6)]
                    dest: bipartite_edgeD(3)[OF _ G(1)])
              ultimately show ?thesis
                using  w⇩π_non_neg[OF u'v'(4)] finite_forest(1)[OF basic_invars(1)]
                by(auto simp add: state'_def missed'_is acc'_def missed_ε_def that)
            qed
            hence "π u' + π v' - missed_at state' u' + acc state' ≤ π u' + π v' + w⇩π u' v'"
              by auto
            also have "... = 𝗐 u' v'"
              by(auto simp add: w⇩π_def)
            finally show ?thesis
              by(simp add: **)
          qed
          show ?case 
            using case_3a case_3b 
            by auto
       next
         case 4
         hence "¬ vset_isin (evens (forest state')) u'" "¬ vset_isin (odds (forest state')) u'"
               "¬ vset_isin (evens (forest state')) v'" "¬ vset_isin (odds (forest state')) v'"
               "¬ vset_isin (evens (forest state)) u'" "¬ vset_isin (odds (forest state)) u'"
               "¬ vset_isin (evens (forest state)) v'" "¬ vset_isin (odds (forest state)) v'"
           using bipartite_edgeD(3)[OF r_l'_in_G G(1)] l'_in_L u'v'(2,3)
                 bipartite_eqI[OF G(1) 1, of u' v']  u'v'(1) basic_invars(10,9)
                 bipartite_edgeD(3)[OF u'v'(4) G(1)]
             by(auto simp add: state'_def F_def F'_is(2-5)  vset.fixed_univ_set_isin vset_is_old_F_sames)
           hence "π⇧* state' u' = π⇧* state u'" "π⇧* state' v' = π⇧* state v'"
             by(auto simp add: working_potential_def)
           then show ?case
             using assms(3) u'v'(4) 
             by (auto dest: invar_feasible_potentialD)
         qed
    thus ?case
      using G(6)[OF u'v'(4)] u'v'(1)
      by(auto simp add: doubleton_eq_iff)
  qed
  show "invar_forest_tight (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_forest_tightI, goal_cases)
    case (1 u v)
    hence "{u, v} ∈ abstract_forest F ∪ {{l, r}, {r, l'}}"
      by(auto simp add: state'_def F'_is(1))
    moreover have "{u, v} ∈ abstract_forest F ⟹ ?case"
    proof(goal_cases)
      case 1
      then obtain u' v' where u'v':"u' ∈ aevens state" "v' ∈ aodds state"
        "{u, v} = {u', v'}"
        using edges_are_Vs[of u v "abstract_forest F"]
          evens_and_odds(3)[OF  basic_invars(1)] edges_are_Vs[of v u "abstract_forest F"]
          higher_forest_properties(3)[OF  basic_invars(1), of u v] 
        unfolding F_def by blast
      have "𝗐 u' v' = π⇧* state' u' + π⇧* state' v'"
        using l'_not_even u'v'(1,2) r_unclassified l'_not_even_or_odd 1
          evens_and_odds(4)[OF basic_invars(1)] invar_forest_tightD[OF assms(4), of u' v']
        by(auto simp add: state'_def  working_potential_def vset(5)[OF F'_is(5)] 
            vset(5)[OF F'_is(4)] F'_is(2,3) missed'_is 
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F_def u'v'(3))
      thus ?case 
        using "1" F_def G(6)[of u v] basic_invars(5) 
          u'v'(3)
        by(auto simp add: doubleton_eq_iff)
    qed
    moreover have "𝗐 l r = π⇧* state' l + π⇧* state' r"
      using l'_not_even  r_unclassified  r_l_props(2)
        bipartite_edgeD(1)[OF r_l'_in_G G(1)] l'_in_L
      by(auto simp add: state'_def  working_potential_def  vset(5)[OF F'_is(4)]
          F'_is(2,3) missed'_is  F_def missed_ε_def acc'_def w⇩π_def)
    moreover have "𝗐 l' r = π⇧* state' l' + π⇧* state' r"
      using bipartite_edgeD(1)[OF r_l'_in_G G(1)] l'_in_L
      by(auto simp add: state'_def  working_potential_def missed'_is F_def missed_ε_def
          acc'_def w⇩π_def edge_commute matching(3) r_l'_in_M)
    ultimately show ?case 
      by (auto simp add: doubleton_eq_iff G(6) r_l_props(1) r_l'_in_G)
  qed
  show "invar_matching_tight (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_matching_tightI, goal_cases)
    case (1 u v)
    note uv_in_M = this
    show ?case
    proof(cases "{u, v} ∩ Vs (abstract_forest F) = {}")
      case True
      hence no_inter:"{u, v} ∩ (aevens state ∪ aodds state) = {}" 
        using edges_are_Vs_2 evens_and_odds(3)[OF F_invar(1)]
          higher_forest_properties(2)[OF F_invar(1), of u v] uv_in_M 
        by (auto simp add: F_def)
      have "π⇧* state' u = π⇧* state u" "π⇧* state' v = π⇧* state v"
        using F_def l'_not_even r_unclassified l'_not_even_or_odd no_inter
        by(auto simp add: state'_def  working_potential_def vset(5)[OF F'_is(5)] 
            vset(5)[OF F'_is(4)] F'_is(2,3) missed'_is 
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F_def )
      thus ?thesis 
        using assms(5) invar_matching_tightD uv_in_M 
        by auto
    next
      case False
      then obtain u' v' where u'v': "{u, v} = {u', v'}" "u' ∈ aevens state" "v' ∈ aodds state"
        apply(cases rule: disjE[OF higher_forest_properties(2)[OF
                basic_invars(1) uv_in_M]])
        using evens_and_odds(3)[OF basic_invars(1)] uv_in_M
          higher_forest_properties(3)[OF basic_invars(1)]
        by(unfold F_def) blast+
      have v'_not_even: "v' ∉ aevens state" 
        using basic_invars(1) evens_and_odds(4) u'v'(3)
        by fastforce
      show ?thesis 
        unfolding state'_def  working_potential_def
        using matching(3)[OF r_l'_in_M]  l'_not_even_or_odd u'v'(1,2,3)  v'_not_even r_not_even_or_odd  evens_and_odds(4)[OF basic_invars(1)]
          invar_matching_tightD[OF assms(5)  uv_in_M]
        by auto (force simp add:  working_potential_def vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)] F_def  missed'_is missed_ε_def
            vset(5)[OF F'_is(5)]  vset(5)[OF F'_is(4)] F'_is(2,3))+
    qed
  qed
  show invar_best_even_neighbour_heap_step: 
    "invar_best_even_neighbour_heap (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_best_even_neighbour_heapI, goal_cases)
    case 1
    show ?case 
    proof(rule, all ‹rule›, goal_cases)
      case (1 rk)
      obtain rr kk where rk: "rk = (rr, kk)" by(cases rk) auto
      note queue'_is_that = after_ben_update(6)[simplified queue_props(2)]
      note 1 = 1[simplified state'_def, simplified]
      show ?case
      proof(cases rule: UnE[OF 1[simplified queue'_is_that], simplified  rk])
        case 1
        show ?thesis 
        proof(cases rule: UnE[OF 1])
          case 1
          then obtain ll where ll: "rr ∈ Vs G - aevens state - aodds state"
            "kk = w⇩π ll rr + missed_at state ll"
            "ben_lookup (best_even_neighbour state) rr = Some ll" 
            using invar_best_even_neighbour_heapD[OF assms(6)]
            by auto
          have "rr ∈ Vs G - aevens state' - aodds state'" 
            using ll ben_l'_None 1
            by(auto simp add: ben_def state'_def F'_is(2,3) F_def missed_ε_def  acc'_def l_def)
          moreover have " kk = w⇩π ll rr + missed_at state' ll"
            using ll 1 update_best_even_neighbour_conditions(4)[of rr kk] 
            by(auto simp add: state'_def missed_ε_def  l_def
                missed'_is acc'_def queue_props(2) ben_def)
          moreover have "ben_lookup (best_even_neighbour state') rr = Some ll"
            using ll 1
            by(auto simp add: state'_def  missed_ε_def  l_def missed'_is ben_def
                after_ben_update(5))
          ultimately show ?thesis
            by(simp add: rk) 
        next
          case 2
          hence rk_props:
            "kk = min (w⇩π l' rr + missed_get missed' l')
                 (w⇩π (the (ben_lookup ben rr)) rr +
                 missed_get missed' (the (ben_lookup ben rr)))"
            "rr ∈ rneighbs l'"
            "rr ∈ fst ` (heap_abstract (heap state) - {(r, acc')})" by auto
          obtain k_old where k_old: "(rr, k_old) ∈ heap_abstract (heap state) - {(r, acc')}"
            using rk_props(3) by force
          have "rr ∈ Vs G - aevens state' - aodds state'"
            using  ben_l'_None k_old basic_invars(8) 
              update_best_even_neighbour_conditions(4)[of rr k_old]
            by(auto simp add: ben_def state'_def F'_is(2,3) image_subset_iff
                F_def missed_ε_def  acc'_def l_def queue_props(2) 
                invar_best_even_neighbour_heapD[OF assms(6)])
          moreover have "(∃l. kk = w⇩π l rr +  missed_at state' l ∧
                         ben_lookup (best_even_neighbour state') rr = Some l)"
            unfolding rk_props(1)
          proof(rule P_of_minI_strict1, goal_cases)
            case 1
            have "ben_lookup (best_even_neighbour state') rr = Some l'" 
              using rk_props(2) 1 by(auto simp add: state'_def after_ben_update(5))  
            then show ?case 
              by(auto simp add: state'_def)
          next
            case 2
            hence "ben_lookup (best_even_neighbour state') rr = 
                   ben_lookup (best_even_neighbour state) rr "
              using rk_props(2) update_best_even_neighbour_conditions(4)[of rr k_old] k_old 
              by(auto simp add: state'_def after_ben_update(5) queue_props(2) ben_def)
            then show ?case 
              using l'_not_a_ben rk_props(2)
              by (auto simp add: state'_def  after_ben_update(5) ben_def if_split[of "λ x. x = _  rr"])
          qed
          ultimately show ?thesis 
            by(simp add: rk)
        qed
      next
        case 2
        hence rr_kk_props: "kk = w⇩π l' rr + missed_get missed' l'"
          "rr ∈ rneighbs l'" "ben_lookup ben rr = None"
          by auto
        have "rr ∈ Vs G - aevens state' - aodds state'" 
          using   basic_invars(9) rr_kk_props  G(5)[OF l'_in_L]
            bipartite_edgeD(1)[of rr l', OF _ G(1)] l'_in_L basic_invars(12)
            rr_kk_props(2)  edge_commute[of l' rr] invar_best_even_neighbour_mapD[OF assms(7), of rr]
            r_l_props(1,2) r_unclassified edge_commute[of rr]
          by(auto simp add: ben_def state'_def F'_is(2,3) F_def  
              invar_best_even_neighbour_heapD[OF assms(6)] ) force
        moreover have "ben_lookup ben' rr = Some l'"
          by(auto simp add: after_ben_update(5) rr_kk_props(2,3))
        ultimately show ?thesis 
          by (auto intro!: exI[of _ l']simp add: rk rr_kk_props(1) state'_def)   
      qed
    next
      case (2 rk)
      then obtain rr kk ll where rr_kk_ll:
        "rk = (rr, kk)"
        "rr ∈ Vs G - aevens state - aodds state - {r, l'}"
        "kk = w⇩π ll rr + missed_get missed' ll"
        "ben_lookup ben' rr = Some ll" 
        by (auto simp add: state'_def F'_is(2,3) F_def)
      have "(rr, w⇩π ll rr + missed_get missed' ll) ∈ heap_abstract queue'"
      proof(rule if_E[of "λ x. x = Some ll", OF
            rr_kk_ll(4)[simplified after_ben_update(5)]], goal_cases)
        case 1
        then show ?case 
          using invar_basicD(11)[OF assms(2)] r_not_even_or_odd
            l'_not_a_ben[of rr] rr_kk_ll(2)
          by (auto simp add: after_ben_update(6) queue_props(2) missed'_is acc'_def missed_ε_def 
              ben_def F_def  invar_best_even_neighbour_heapD[OF assms(6)])
      next
        case 2
        note Two = this
        show ?case 
        proof(rule if_E[of "λ x. x = Some ll", OF 2(2)], goal_cases)
          case 1
          then show ?case 
            using Two(1)
            by (auto simp add: after_ben_update(6)) 
        next
          case 2
          note two = this
          show ?case 
          proof(rule if_E[of "λ x. x = Some ll", OF 2(2)], goal_cases)
            case 1
            then show ?case 
              using invar_basicD(11)[OF assms(2)] r_not_even_or_odd
                l'_not_a_ben[of rr] rr_kk_ll(1-4) two Two 1
              by (auto simp add: after_ben_update(6) queue_props(2) missed'_is
                  acc'_def missed_ε_def ben_def F_def 
                  invar_best_even_neighbour_heapD[OF assms(6)]
                  if_split[of "λ x. _ < _ + x"  "_ = r ∨ _ = ll"] ) force+
          next
            case 2
            then show ?case
              using invar_basicD(11)[OF assms(2)] r_not_even_or_odd
                l'_not_a_ben[of rr] rr_kk_ll(1-4) 
              by (auto simp add: after_ben_update(6) queue_props(2) missed'_is
                  acc'_def missed_ε_def ben_def F_def 
                  invar_best_even_neighbour_heapD[OF assms(6)]) force
          qed
        qed
      qed
      thus ?case
        by(auto simp add: state'_def rr_kk_ll(1,3))
    qed
  qed
  show invar_best_even_neighbour_map_step:
    "invar_best_even_neighbour_map (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_best_even_neighbour_mapI, goal_cases)
    case (1 rr)
    then show ?case 
      using invar_best_even_neighbour_mapD(1)[OF assms(7), of rr]
      by(auto simp add: state'_def F'_is(2,3) after_ben_update(5)
          G(5)[OF l'_in_L] missed'_is F_def ben_def)
  next
    case (2 rr)
    note two = this
    show ?case 
    proof(cases "{l', rr} ∈ G")
      case True
      hence rr_in_ngbhd_l':"¬ rr ∉ rneighbs l'"
        by (simp add: G(5) l'_in_L)
      note true = True
      show ?thesis 
      proof(cases "ben_lookup ben rr = None")
        case True
        have "w⇩π l' rr + missed_get missed' l' =
             Min {w⇩π l rr + missed_get missed' l | 
             l .(l = l' ∨ l ∈ vset_to_set (evens F)) ∧ {l, rr} ∈ G}"
        proof(rule linorder_class.Min_eqI[symmetric], goal_cases)
          case 1
          then show ?case 
            by(rule rev_finite_subset[of "{w⇩π l rr + missed_get missed' l | l rr. {l, rr} ∈ G}"])
                  (auto simp add: finite_G finite_double_image_of_pairs_in_set_of_sets)
        next
          case (2 y)
          have "∄l. l ∈ aevens state ∧ {l, rr} ∈ G"
            using invar_best_even_neighbour_mapD(2)[OF assms(7), of rr] True true
              basic_invars(12,9) bipartite_edgeD(1)[of l' rr, OF _ G(1)]
              edges_are_Vs_2[of l' rr G]  l'_in_L
            by(auto simp add: ben_def)
          thus ?case 
            using  r_unclassified 2 2
            by(auto simp add: missed'_is F_def)
        next
          case 3
          then show ?case 
            by (auto intro!: exI[of _ l'] simp add: true)
        qed   
        thus ?thesis 
          using True rr_in_ngbhd_l'
          by(auto intro!: exI[of _ l'] 
              simp add: state'_def  after_ben_update(5) edge_commute true F'_is(2))
      next
        case False
        note false = this
        note rr_in_G = two(1)
        moreover have "rr ∉ aevens state" "rr ∉ aodds state"  
          using two by (auto simp add: state'_def F'_is(2,3) F_def)
        moreover hence there_is_l:"∃l. l ∈ aevens state ∧ {l, rr} ∈ G" 
          using two(4)
          using invar_best_even_neighbour_mapD(1)[OF assms(7), of rr] True 
            false rr_in_G
          by(force simp add: ben_def)  
        ultimately obtain ll where ll: 
          "ben_lookup (best_even_neighbour state) rr = Some ll"
          "{rr, ll} ∈ G" "ll ∈ aevens state"
          "w⇩π ll rr + missed_at state ll =
                             Min {w⇩π l rr + missed_at state l | 
                            l . l ∈ aevens state ∧ {l, rr} ∈ G}"
          using invar_best_even_neighbour_mapD(2)[OF assms(7), of rr] by blast
        have Min_set_is: "{w⇩π l rr + missed_get missed' l
               | l. (l = l' ∨ l ∈ vset_to_set (evens F))∧ {l, rr} ∈ G}
                 = insert (w⇩π l' rr + missed_get missed' l')
                   {w⇩π l rr + missed_at state l | l . l ∈ aevens state ∧ {l, rr} ∈ G}"
          using r_unclassified true l'_not_even by(force simp add: missed'_is F_def)            
        show ?thesis
        proof(cases "w⇩π l' rr + missed_get missed' l'
            < w⇩π (the (ben_lookup ben rr)) rr +
              missed_get missed' (the (ben_lookup ben rr))")
          case True
          have "w⇩π l' rr + missed_get missed' l' =
             Min {w⇩π l rr + missed_get missed' l | 
             l .(l = l' ∨ l ∈ vset_to_set (evens F)) ∧ {l, rr} ∈ G}"
          proof(rule linorder_class.Min_eqI[symmetric], goal_cases)
            case 1
            then show ?case 
              by(rule rev_finite_subset[of "{w⇩π l rr + missed_get missed' l | l rr. {l, rr} ∈ G}"])
                    (auto simp add: finite_G finite_double_image_of_pairs_in_set_of_sets)
          next
            case (2 y)
            have new_min_is: "w⇩π l' rr + missed_get missed' l' = 
                  min (w⇩π ll rr + missed_at state ll) (w⇩π l' rr + missed_get missed' l')"
              using True ll(3,1) l'_not_a_ben[of rr] 
                r_not_even_or_odd
              by(cases "ll = r", all ‹cases "ll = l'"›)
                (auto simp add: ben_def  missed'_is F_def)
            have "y ≥ Min {w⇩π l rr + missed_get missed' l
               | l. (l = l' ∨ l ∈ vset_to_set (evens F))∧ {l, rr} ∈ G}" 
              apply(rule linorder_class.Min.coboundedI)
              apply(rule rev_finite_subset[of "{w⇩π l rr + missed_get missed' l | l rr. {l, rr} ∈ G}"])
              using 2
              by(auto intro: rev_finite_subset[of "{w⇩π l rr + missed_get missed' l | l rr. {l, rr} ∈ G}"] 
                  simp add: finite_G finite_double_image_of_pairs_in_set_of_sets)
            thus ?case 
              apply(subst new_min_is)
              unfolding ll(4) Min_set_is 
              apply(subst (asm) linorder_class.Min_insert)
              apply(rule rev_finite_subset[of "{w⇩π l rr + missed_at state l | l rr. {l, rr} ∈ G}"])
              by(auto simp add: finite_G finite_double_image_of_pairs_in_set_of_sets there_is_l)
          next
            case 3
            then show ?case 
              by (auto intro!: exI[of _ l'] simp add: true)
          qed   
          thus ?thesis
            using True false rr_in_ngbhd_l'
            by(auto intro!: exI[of _ l'] 
                simp add: state'_def  after_ben_update(5)  edge_commute true F'_is(2))  
        next
          case False
          have "w⇩π ll rr + missed_get missed' ll =
             Min { w⇩π l rr + missed_get missed' l
                  | l. (l = l' ∨ l ∈ vset_to_set (evens F)) ∧ {l, rr} ∈ G}"
            unfolding Min_set_is
            apply(subst linorder_class.Min_insert)
            apply(rule rev_finite_subset[of "{w⇩π l rr + missed_at state l | l rr. {l, rr} ∈ G}"])
            using False  r_not_even_or_odd ll(1,3)  l'_not_even
            by(auto simp add: finite_G finite_double_image_of_pairs_in_set_of_sets
                              there_is_l ll(4)[symmetric] missed'_is F_def ben_def)
          thus ?thesis 
            using False false  rr_in_ngbhd_l'
            by(auto intro!: exI[of _ ll] 
                simp add: state'_def after_ben_update(5) ll(1-3) ben_def F'_is(2) F_def)
        qed
      qed
    next
      case False
      note rr_in_G = two(1)
      moreover have "rr ∉ aevens state" "rr ∉ aodds state"  
        using two by (auto simp add: state'_def F'_is(2,3) F_def)
      moreover hence there_is_l:"∃l. l ∈ aevens state ∧ {l, rr} ∈ G" 
        using two(4) False  rr_in_G
        by(auto simp add: ben_def state'_def F'_is(2) F_def)  
      ultimately obtain ll where ll: 
        "ben_lookup (best_even_neighbour state) rr = Some ll"
        "{rr, ll} ∈ G" "ll ∈ aevens state"
        "w⇩π ll rr + missed_at state ll =
                             Min {w⇩π l rr + missed_at state l | 
                            l . l ∈ aevens state ∧ {l, rr} ∈ G}"
        using invar_best_even_neighbour_mapD(2)[OF assms(7), of rr] by blast
      have same_ben:"ben_lookup ben' rr = ben_lookup ben rr"
        by (simp add: False G(5) after_ben_update(5) l'_in_L)
      have same_ben_value: "w⇩π ll rr + missed_get missed' ll = 
                                   w⇩π ll rr + missed_at state ll"
        using ll(3) r_unclassified l'_not_even 
        by(auto simp add: missed'_is F_def)
      have Min_set_is: 
        "{w⇩π l rr + missed_get missed' l 
             | l. (l = l' ∨ l ∈ aevens state) ∧ {l, rr} ∈G} = 
            {w⇩π l rr + missed_at state l | l . l ∈ aevens state ∧ {l, rr} ∈ G}"
        using False r_unclassified  by(auto simp add: missed'_is)
      show ?thesis
        using ll
        by(auto intro: exI[of _ ll] 
             simp add: ben_def F_def F'_is same_ben_value same_ben  state'_def Min_set_is)
    qed
  qed

  have Some_l_is: "ben_lookup ben r = Some l" 
    using  ben_def edge_commute invar_best_even_neighbour_mapD[OF assms(7)] l_def
      r_l_props(1,2) r_unclassified by fastforce
  show "invar_out_of_heap (search_path_loop_cont_upd state)"
    unfolding upd_state_is_state'
  proof(rule invar_out_of_heapI, goal_cases)
    case (1 rr ll kr)
    note one = this[simplified state'_def, simplified]
    have new_potential_key_leq_missed_l':
      "w⇩π ll rr + missed_get missed' ll
                 ≤ missed_get missed' l'"
      using after_ben_update(4)[of rr ll] one(1,2) by auto     
    from one have rr_prop:"rr = r ∨ (∄k. (rr, k) ∈ heap_abstract (heap state))"
      by(auto simp add: queue_props(2) after_ben_update(6) 
          in_image_with_fst_eq)
    obtain kr1 kr2 lkr where kr_split: "kr = (kr1, kr2)"
      "kr1 ∈ Vs G - aevens state' - aodds state'"
      "kr2 = w⇩π lkr kr1 + missed_at state' lkr"
      "ben_lookup ben' kr1 = Some lkr"
      using invar_best_even_neighbour_heapD[OF invar_best_even_neighbour_heap_step]
        one(3)
      by(auto simp add: state'_def upd_state_is_state')
    have kr1_further_props:
      "{kr1, lkr} ∈ G" "lkr ∈ aevens state'"
      using invar_best_even_neighbour_mapD[OF invar_best_even_neighbour_map_step, of kr1]
        kr_split
      by(auto simp add: state'_def upd_state_is_state')
    have missed_at_lkr_new_is:"missed_at state' lkr = 
               (if lkr = l' then w⇩π l r + missed_at state l else  missed_at state lkr)"
      using invar_basicD(9)[OF invar_basic_step]
        bipartite_edgeD(1)[OF r_l'_in_G G(1)]
        kr1_further_props(2) l'_in_L 
      by(auto simp add: state'_def missed'_is  upd_state_is_state' acc'_def missed_ε_def)
    have missed_at_l'_is: "missed_at state' l' =  w⇩π l r + missed_at state l"
      by(auto simp add: state'_def missed'_is acc'_def missed_ε_def)
    note one' = 1(3)[simplified kr_split(1), simplified state'_def, simplified]
    note kr1_kr2_in = one'[simplified after_ben_update(6) queue_props(2)]
    have "missed_get missed' l' ≤ kr2"
    proof(rule UnE[OF kr1_kr2_in], goal_cases)
      case 1
      show ?case 
      proof(rule UnE[OF 1], goal_cases)
        case 1
        show ?case
          using missed_at_l'_is  kr1_further_props(1) w⇩π_non_neg[of lkr kr1] 
            "1" k(2) k_is kr_split(3) 
          by (auto simp add: missed_at_lkr_new_is  kr_split(3) state'_def insert_commute)
      next
        case 2
        hence kr_more_props: "kr1 ∈ rneighbs l'"
          "kr1 ∈ fst ` heap_abstract (heap state)" "kr1 ≠ r"
          "kr2 = min (w⇩π l' kr1 + missed_get missed' l')
                       (w⇩π (the (ben_lookup ben kr1)) kr1 +
                        missed_get missed' (the (ben_lookup ben kr1)))" 
          using  basic_invars(3) heap(7) k(1) k_is
          by(auto simp add: missed_ε_def acc'_def)
        show ?case
        proof(rule P_of_minE_strict2[of "λ x. kr2 = x", OF kr_more_props(4)], goal_cases)
          case 1
          then show ?case 
            using G(5) kr_more_props(1)
 l'_in_L w⇩π_non_neg by force
        next
          case 2
          hence "(kr1, kr2) ∈ heap_abstract (heap state)"
            using kr_more_props(2,3) queue_props(2) update_best_even_neighbour_conditions(4)
            by fastforce
          then show ?case 
            using k(1) k(2)[of kr1 kr2]
            by(simp add: acc'_def missed_ε_def  k_is missed'_is)
        qed
      qed
    next
      case 2
      hence kr_more_props: "kr1 ∈ rneighbs l'"
        "ben_lookup ben kr1 = None"
        "kr2 = w⇩π l' kr1 + missed_get missed' l'" 
        using  basic_invars(3) heap(7) k(1) k_is
        by(auto simp add: missed_ε_def acc'_def)
      then show ?case 
        using after_ben_update(5) kr1_further_props(1) kr_split(4) w⇩π_non_neg w⇩π_symmetric
        by force
    qed
    thus ?case
      using missed_at_l'_is new_potential_key_leq_missed_l'
      by(auto simp add: state'_def kr_split(1))
  qed
  have "2 + card (aevens state ∪ aodds state) =
          card ({r, l'} ∪ (vset_to_set (evens F) ∪ vset_to_set (odds F)))"
    using basic_invars(1) finite_forest(1,2)evens_and_odds(4)[OF F'_is(6)]
      l'_not_even_or_odd r_not_even_or_odd 
    by(subst (2) card_Un_disjoint)(auto simp add: F_def F'_is(2,3))
  thus "card (aevens (search_path_loop_cont_upd state) ∪ aodds (search_path_loop_cont_upd state)) =
    card (aevens state ∪ aodds state) + 2"
    by(auto simp add: upd_state_is_state' state'_def F'_is(2,3))
qed

subsection ‹Termination›

lemma search_path_loop_term_gen_induct:
  assumes  
    "remaining = card L + card R - card (aevens state ∪ aodds state)"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
  shows "search_path_loop_dom state"
  using assms
proof(induction remaining arbitrary: state rule: less_induct)
  case (less remaining)
  show ?case 
  proof(cases state rule: search_path_loop_cases)
    case 3
    have decrease: "(card (aevens state ∪ aodds state)) +2 ≤ card L + card R"
      unfolding invar_pres_one_step(8)[OF 3 less(3-9), symmetric]
      using  invar_basicD(9,10)[OF invar_pres_one_step(1)[OF 3 less(3-9)]] finite_L finite_R
      by (auto intro:  order.trans[OF card_Un_le] simp add: add_le_mono card_mono)
    show ?thesis 
      using decrease  
      by(intro search_path_loop_domintros(3)[OF 3])
        (auto intro: less(1)[of "card L + card R 
            - Suc (Suc (card (aevens state ∪ aodds state)))"] 
           simp add: invar_pres_one_step[OF 3 less(3-9)] less(2))
  qed (auto intro: search_path_loop_domintros(1,2))
qed

lemmas search_path_loop_term_gen = search_path_loop_term_gen_induct[OF refl]

subsection ‹Unbounded Dual›

lemma search_path_loop_fail_cond_dual_unbounded:
  assumes "search_path_loop_fail_cond state"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "¬ L ⊆ Vs ℳ"
  shows "∃ p. (∀ u v. {u, v} ∈ G ⟶ edge_costs u v ≥ p u +  p v)
               ∧ sum p (L ∪ R) ≥ bound"
proof-
  obtain queue heap_min where queue_heap_min_def:
    " (queue, heap_min) = heap_extract_min (heap state)"
    by(cases "heap_extract_min (heap state)") auto
  have empty_heap:  "heap_abstract (heap state) = {}" "heap_min = None"
    using queue_heap_min_def[symmetric] assms(1,2) invar_basicD(3)
    by(auto elim!: search_path_loop_fail_condE intro!: heap(6))
  have no_even_non_odd_edge: False
    if asms: "l ∈ aevens state" "{l, r} ∈ G" "r ∉ aodds state" for l r
  proof-
    have l_in_L: "l ∈ L" 
      using assms(2) invar_basicD(9) that(1) by blast
    hence r_not_even: "r ∉ aevens state" 
      using G(1)  bipartite_edgeD(1) invar_basicD[OF assms(2)] that(2) by fast
    have r_in_G: "r ∈ Vs G"
      by (auto intro: edges_are_Vs_2 that(2))
    obtain l' where "ben_lookup (best_even_neighbour state) r = Some l'"
      using invar_best_even_neighbour_mapD(2)[OF assms(5) r_in_G r_not_even asms(3)] asms(1,2) 
      by blast
    hence "(r, w⇩π l' r + missed_at state l') ∈ heap_abstract (heap state)"
      using invar_best_even_neighbour_heapD[OF assms(4)]  r_not_even r_in_G asms(3) by blast
    thus False 
      using empty_heap(1) by blast
  qed
  define ε where "ε = ¦ sum (π⇧* state) (L ∪ R) ¦ + ¦bound¦"
  define p where "p = (λ x. if x ∈ aevens state then π⇧* state x + ε
                             else if x ∈ aodds state then π⇧* state x - ε
                             else π⇧* state x)"
  have odds_in_G:"aodds state ⊆ Vs G" 
    using  bipartite_vertex(1)[OF _ G(1)] insert_absorb
      insert_subset invar_basicD(6,9,10,12)[OF assms(2)]
    by auto
  have evens_odds_disjoint: "aodds state ∩ aevens state = {}" 
    using assms(2) evens_and_odds(4) invar_basic_def by blast
  have pos_eps: "ε ≥ 0"
    by(auto simp add: ε_def)
  have p_feasible:"{u, v} ∈ G ⟹ p u + p v ≤ 𝗐 u v" for u v
    using evens_odds_disjoint  invar_feasible_potentialD[OF assms(3), of u v] pos_eps
      no_even_non_odd_edge[of v u]
    by(auto simp add: p_def insert_commute dest:  no_even_non_odd_edge)
  moreover have "bound ≤ sum p (L ∪ R)"
  proof-
    have sum1:"sum p  (L ∪ R) = sum p (aevens state) + sum p (L ∪ R - aevens state)"
      using finite_forest(1)[OF invar_basicD(1)[OF assms(2)]]  invar_basicD(9)[OF assms(2)]
      by(subst comm_monoid_add_class.sum.union_disjoint[of 
            A "B - A" for A B, simplified, symmetric])
        (auto intro!: arg_cong[of  _ _ "sum p"] simp add: finite_L finite_R)
    have sum2: "sum p (L ∪ R - aevens state) = 
               sum p (aodds state) + sum p (L ∪ R - aevens state - aodds state)"
      using finite_forest(2)[OF invar_basicD(1)[OF assms(2)]]  invar_basicD(10)[OF assms(2)]
        evens_odds_disjoint
      by(subst comm_monoid_add_class.sum.union_disjoint[of 
            A "B - A" for A B, simplified, symmetric])
        (auto intro!: arg_cong[of  _ _ "sum p"] simp add: finite_L finite_R)
    have sum3: "sum p (aevens state) = ε * card (aevens state) + sum (π⇧* state) (aevens state)"
      by(auto simp add:  p_def sum_cong[of _ _ "λ x. π⇧* state x + ε"] comm_monoid_add_class.sum.distrib)
    have sum4: "sum p (aodds state) = - ε * card (aodds state) + sum (π⇧* state) (aodds state)"
      using evens_odds_disjoint
      by(subst  sum_cong[of _ _ "λ x. π⇧* state x - ε"])
        (auto simp add: p_def sum_subtractf)
    have sum5: "sum p (L ∪ R - aevens state - aodds state) = 
               sum (π⇧* state) (L ∪ R - aevens state - aodds state)"
      by(subst p_def sum_cong[of _ _ "π⇧* state"]) simp+
    have "card (aevens state) = card (aodds state) +
          card (vset_to_set (roots (forest state)))"
      using higher_forest_properties(1)[OF invar_basicD(1)[OF assms(2)]] .
    moreover have "card (vset_to_set (roots (forest state))) > 0"
      using invar_basicD(16)[OF assms(2)] assms(6)
      by (simp add: card_gt_0_iff finite_L)
    ultimately have card_diff: "card (aevens state) > card (aodds state)"
      by simp
    have sum6:"sum (π⇧* state) (L ∪ R) = sum (π⇧* state) (aevens state) + sum (π⇧* state) (L ∪ R - aevens state)"
      using finite_forest(1)[OF invar_basicD(1)[OF assms(2)]]  invar_basicD(9)[OF assms(2)]
      by(subst comm_monoid_add_class.sum.union_disjoint[of 
            A "B - A" for A B, simplified, symmetric])
        (auto intro!: arg_cong[of  _ _ "sum (π⇧* state)"] simp add: finite_L finite_R)
    have sum7: "sum (π⇧* state) (L ∪ R - aevens state) = 
               sum (π⇧* state) (aodds state) + sum (π⇧* state) (L ∪ R - aevens state - aodds state)"
      using finite_forest(2)[OF invar_basicD(1)[OF assms(2)]]  invar_basicD(10)[OF assms(2)]
        evens_odds_disjoint
      by(subst comm_monoid_add_class.sum.union_disjoint[of 
            A "B - A" for A B, simplified, symmetric])
        (auto intro!: arg_cong[of  _ _ "sum (π⇧* state)"] simp add: finite_L finite_R)     
    have "ε ≠ 0 ⟹ 
             ε * (1 + real (card (aodds state))) ≤ ε * real (card (aevens state))"
      using card_diff pos_eps
      by(auto simp add: linordered_ring_strict_class.mult_le_cancel_left_pos)
    hence sum_p_bigger_than_sum_pi_state:
      "sum p (L ∪ R)≥ ε + sum (π⇧* state) (L ∪ R)"
      by(cases "ε = 0")
        (auto simp add: sum1 sum2 sum3 sum4 sum5 sum6 sum7 algebra_simps)
    thus ?thesis
      by(auto simp add: ε_def)
  qed
  ultimately show ?thesis 
    by auto
qed

lemma augpath_None_gen_unbounded_dual:
  assumes "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
    "augpath (search_path_loop state) = None"
    "¬ L ⊆ Vs ℳ"
  shows "∃ p.  (∀ u v. {u, v} ∈ G ⟶ edge_costs u v ≥ p u +  p v)
             ∧ sum p (L ∪ R) ≥ bound"
  using assms(1-8)
proof(induction state rule: search_path_loop_induct, goal_cases)
  case 1
  then show ?case
    by (simp add: assms(1,2,3,4,5,6,7) search_path_loop_term_gen)
next
  case (2 state)
  note IH = this
  show ?case 
  proof(cases state rule: search_path_loop_cases)
    case 1
    then show ?thesis 
      using search_path_loop_fail_cond_dual_unbounded IH(3-9) assms(9)
      by auto
  next
    case 2
   show ?thesis 
     using IH(10) 2
     by(auto simp add: search_path_loop_simps(2)[OF 2] search_path_loop_succ_upd_def Let_def
                elim!: search_path_loop_succ_condE 
                dest!: sym[of _ "heap_extract_min (heap state)"]) 
  next
    case 3
    show ?thesis 
      using IH(10) 
      by(auto intro!: IH(2) 3  invar_pres_one_step IH(1,3-9)
           simp add: search_path_loop_simps(3)[OF IH(1) 3])
  qed
qed

subsection ‹Tight Augmenting Path and Potential›

lemma search_path_loop_succ_cond_valid_result:
  assumes "search_path_loop_succ_cond state"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "state' = (search_path_loop_succ_upd state)"
  shows "invar_feasible_potential state'"
        "invar_matching_tight state'"
      "augpath state' ≠ None"
      "∀ e ∈ set (edges_of_path (the (augpath state'))).
          ∃ u v. e = {u, v} ∧ 𝗐 u v = π⇧* state' u + π⇧* state' v"
      "graph_augmenting_path G ℳ (the (augpath state'))"
      "forest_invar ℳ (forest state')"
       "invar_basic state'"
proof-
  define F where "F = forest state"
  define ben where "ben = best_even_neighbour state"
  define missed_ε where  "missed_ε = missed_at state"
  obtain queue heap_min where queue_heap_min_def:
    " (queue, heap_min) = heap_extract_min (heap state)"
    by(cases "heap_extract_min (heap state)") auto
  obtain r where r_def: "heap_min = Some r"
    using queue_heap_min_def assms(1)
    by(auto elim!: search_path_loop_succ_condE 
        dest: sym[of _ "heap_extract_min (heap state)"])
  define l where "l = the (ben_lookup ben r)"
  define acc' where "acc' = w⇩π l r + missed_ε l"
  define p where "p = r # get_path F l"

  obtain k where k: "(r, k) ∈ heap_abstract (heap state)"
    "⋀ x' k'. (x', k') ∈ heap_abstract (heap state) ⟹ k ≤ k'"
    using r_def  pair_eq_fst_snd_eq[OF queue_heap_min_def]
      heap(5)[of "heap state" r] assms(2)
    by(auto elim!: invar_basicE)
  have r_unclassified: "r ∈ Vs G - aevens state - aodds state"
    using assms(6) k
    by (auto elim: invar_best_even_neighbour_heapE)
  have r_l_props: "{r, l} ∈ G" "l ∈ aevens state"
    "w⇩π l r + missed_at state l =
         Min {w⇩π l r + missed_at state l| l. l ∈ aevens state ∧ {l, r} ∈ G}"
    using assms(6,7) r_unclassified r_def  k(1) 
    by(fastforce elim!: invar_best_even_neighbour_mapE 
        dest: invar_best_even_neighbour_heapD 
        simp add: l_def ben_def)+
  have l_code: "w⇩π_code l r = w⇩π l r"
    using r_l_props(1,2) invar_basicD(9)[OF assms(2)]
    by(auto intro!: w⇩π_code_is simp add: insert_commute)
  have state'_def: "state' = state ⦇ acc:= acc', augpath:= Some p ⦈"
    by(simp add: assms(8) search_path_loop_succ_upd_def queue_heap_min_def[symmetric] 
        Let_def acc'_def r_def F_def missed_ε_def l_def ben_def p_def 
        l_code[unfolded l_def ben_def] invar_best_even_neighbour_heap_get[OF assms(6) k(1)])
  have k_is: "k = w⇩π l r + missed_at state l"
    using assms(6) ben_def k(1) l_def
    by(fastforce dest: invar_best_even_neighbour_heapD)
  have r_not_even_or_odd:
    "r ∈ vset_to_set (evens F) ∪  vset_to_set (odds F) ⟹ False" 
    using F_def r_unclassified by blast
  have l_r_not_in_M:"{l, r} ∈ ℳ ⟹ False" 
    using r_l_props(2) assms(2) higher_forest_properties(2,3)[of ℳ F l r] 
      r_not_even_or_odd evens_and_odds(3)[of ℳ F]
    by(auto elim!: invar_basicE simp add: F_def)
  have l_in_L:"l ∈ L"
    using  assms(2) r_l_props(2)
    by(auto elim!: invar_basicE)
  hence r_in_R: "r ∈ R"
    using G(1) bipartite_edgeD(3) l_in_L r_l_props(1) by fastforce
  have queue'_is: "heap_abstract (fst (heap_extract_min (heap state))) =
         heap_abstract (heap state) - {(r, w⇩π l r + missed_at state l)}"
    using assms(2) k(1) k_is
    by(intro heap(8))
      (auto elim!: invar_basicE 
        simp add: r_def[symmetric] pair_eq_fst_snd_eq[OF queue_heap_min_def])
  note basic_invars = invar_basicD[OF assms(2)]
  have r_neither_even_nor_odd: "r ∈ aevens state = False" "r ∈ aodds state = False" 
    using r_unclassified by blast+
  have "buddy r = None"
    using assms(1) sym[OF queue_heap_min_def]
    by(auto elim!:  search_path_loop_succ_condE
        simp add: r_def)
  hence r_unmatched:"r ∉ Vs ℳ"
    using M_verts_by_buddy(1)[of r] by blast
  have feasibility_hard_case: 
    "w⇩π l r + missed_at state l ≤  w⇩π v u + missed_at state v"
    if asms:"u ∉ aodds state" "v ∉ aodds state"
      "u ∉ aevens state" "v ∈ aevens state" "{u, v} ∈ G" for u v
  proof-
    have u_in_G_unclassified: "u ∈ Vs G - aevens state - aodds state"
      using edges_are_Vs that(1,3,5) by auto
    then obtain v' where u_v'_props: 
      "ben_lookup (best_even_neighbour state) u = Some v'"
      "{u, v'} ∈ G" "v' ∈ aevens state"
      "w⇩π v' u + missed_at state v' =
         Min {w⇩π l u + missed_at state l| l. l ∈ aevens state ∧ {l, u} ∈ G}"
      using invar_best_even_neighbour_mapD(2)[OF assms(7), of u] asms(4,5)
      by(auto simp add: insert_commute[of u v])
    have u'v'_better: "w⇩π v' u + missed_at state v' ≤ w⇩π v u + missed_at state v"
      using asms(4,5)
      by(auto intro!: linorder_class.Min.coboundedI finite_subset[of 
            "{ _  l u | l. l ∈ _ ∧ {l, u} ∈ G}"  "{ _  l u | l u. {l, u} ∈ G}"]
          exI[of "λ l. _" v]
          simp add: u_v'_props(4) finite_G finite_double_image_of_pairs_in_set_of_sets
                    insert_commute)
    have "(u, w⇩π v' u + missed_at state v') ∈ heap_abstract (heap state)" 
      using invar_best_even_neighbour_heapD[OF assms(6)] u_in_G_unclassified
        u_v'_props(1) 
      by auto
    hence "w⇩π v' u + missed_at state v' ≥ w⇩π l r + missed_at state l"
      using k(2) k_is by auto
    thus ?thesis
      using u'v'_better by simp
  qed

  show "invar_feasible_potential state'"
    unfolding state'_def
  proof(rule invar_feasible_potentialI, goal_cases)
    case (1 u v)
    note evens_odds = evens_and_odds(1,2,4)[OF  basic_invars(1)]
    note fsbl_uv = invar_feasible_potentialD[OF assms(3) 1]
    note fsbl_lr = invar_feasible_potentialD[OF assms(3)  r_l_props(1)]
    note hard_cases = feasibility_hard_case[OF _ _ _ _ 1]
      feasibility_hard_case[OF _ _ _ _ edge_commute[OF 1]]
    show ?case 
      using evens_odds(3) basic_invars(10) bipartite_edgeD(4)[OF 1 G(1)]
        fsbl_uv G(6)[OF r_l_props(1)]
        fsbl_lr  r_l_props(2) r_not_even_or_odd bipartite_edgeD(3)[OF 1 G(1)] 
        basic_invars(9) G(6)[OF 1] hard_cases
      by(auto simp add: working_potential_def acc'_def missed_ε_def
          vset(5)[OF evens_odds(1)] vset(5)[OF evens_odds(2)] F_def 
          w⇩π_def r_neither_even_nor_odd) 
  qed

  show "augpath state' ≠ None"
    by(auto simp add: state'_def)
  have the_path_is:"the (augpath state') = p" 
    by(auto simp add: state'_def)
  have p_pref_props: "rev_alt_path ℳ (get_path F l)"
    "odd (length (get_path F l))"
    "last (get_path F l)
                    ∈ vset_to_set (roots F)"
    "walk_betw (abstract_forest F) l (get_path F l) (last (get_path F l)) ∨ get_path F l = [l]"
    "distinct (get_path F l)"
    using get_path[OF basic_invars(1) r_l_props(2)]
    by(auto simp add: p_def F_def)
  have get_path_split_off_first:"get_path F l = hd (get_path F l)# tl (get_path F l)"
    and get_path_non_empty: "get_path F l ≠ []"
    and get_path_length: "length (get_path F l) ≥ 1"
    using p_pref_props(2) by(all ‹cases "get_path F l"›) auto 
  have hd_get_path:"(hd (get_path F l)) = l" 
    using p_pref_props(4)
    by (auto intro: walk_between_nonempty_pathD(3))
  have edges_of_p_are:"edges_of_path p = {r, l}#edges_of_path (get_path F l)"
    using get_path_split_off_first  hd_get_path p_def 
    by(cases "get_path F l") simp+
  show "∀e∈set (edges_of_path (the (augpath state'))).
       ∃u v. e = {u, v} ∧ 𝗐 u v = π⇧* state' u + π⇧* state' v "
  proof(rule, goal_cases)
    case (1 e)
    hence one: "e ∈ set (edges_of_path (get_path F l)) ∨ e = {l, r}" 
      using edges_of_p_are by(auto simp add: state'_def p_def)
    show ?case 
    proof(cases rule: disjE[OF one], goal_cases)
      case 1
      hence e_in_F:"e ∈ abstract_forest F" 
        using p_pref_props(4) path_ball_edges by(auto simp add: walk_betw_def)
      moreover then obtain u v where e_is: "e = {u, v}"
        using "1" in_edges_of_path_split by blast
      ultimately have uv_in_G:"{u, v} ∈ G" 
        using  F_def invar_basicD[OF assms(2)] by blast
      note evens_odds = evens_and_odds(1,2,4)[OF  basic_invars(1)]
      have "π⇧* state' u + π⇧* state' v = 𝗐 u v"
        using invar_forest_tightD[OF assms(4), of u v] e_in_F evens_odds(3) 
          higher_forest_properties(3)[OF basic_invars(1), of v u]
          higher_forest_properties(3)[OF basic_invars(1), of u v]
        by(auto simp add: working_potential_def 
            vset(5)[OF evens_odds(1)] vset(5)[OF evens_odds(2)] F_def 
            insert_commute e_is state'_def) 
      thus ?case
        using e_is by fastforce
    next
      case 2
      note evens_odds = evens_and_odds(1,2,4)[OF  basic_invars(1)]
      have "𝗐 l r = π⇧* state' l + π⇧* state' r"
        using evens_odds(1,2,3) r_neither_even_nor_odd(1) r_l_props(2)
        by(auto simp add: state'_def acc'_def working_potential_def missed_ε_def vset(5)
            r_neither_even_nor_odd(2)  w⇩π_def)
      thus ?case 
        using 2 by blast
    qed
  qed
  have F_invar:"forest_invar ℳ (forest state)" "vset_invar (evens (forest state))"
    "vset_invar (odds (forest state))"
    using assms(2) by(auto elim!: invar_basicE intro: evens_and_odds)
  show "invar_matching_tight state'"
    unfolding state'_def
  proof(rule invar_matching_tightI, goal_cases)
    case (1 u v)
    note uv_in_M = this
    show ?case
    proof(cases "{u, v} ∩ Vs (abstract_forest F) = {}")
      case True
      hence no_inter:"{u, v} ∩ (aevens state ∪ aodds state) = {}" 
        using edges_are_Vs_2 evens_and_odds(3)[OF F_invar(1)]
          higher_forest_properties(2)[OF F_invar(1), of u v] uv_in_M 
        by (auto simp add: F_def)
      have "π⇧* state' u = π⇧* state u" "π⇧* state' v = π⇧* state v"
        using F_def r_unclassified  no_inter
        by(auto simp add: state'_def  working_potential_def 
            vset(5)[OF F_invar(2)] vset(5)[OF F_invar(3)] F_def )
      thus ?thesis 
        using  invar_matching_tightD[OF assms(5) uv_in_M ] no_inter
        by(auto simp add: working_potential_def acc'_def 
            vset(5)[OF F_invar(2)]  vset(5)[OF F_invar(3)])
    next
      case False
      then obtain u' v' where u'v': "{u, v} = {u', v'}" "u' ∈ aevens state" "v' ∈ aodds state"
        apply(cases rule: disjE[OF higher_forest_properties(2)[OF
                basic_invars(1) uv_in_M]])
        using evens_and_odds(3)[OF basic_invars(1)] uv_in_M
          higher_forest_properties(3)[OF basic_invars(1)]
        by(unfold F_def) blast+
      have v'_not_even: "v' ∉ aevens state" 
        using basic_invars(1) evens_and_odds(4) u'v'(3) by fastforce
      show ?thesis 
        unfolding state'_def  working_potential_def
        using  u'v'(1,2,3)  v'_not_even r_not_even_or_odd  evens_and_odds(4)[OF basic_invars(1)]
          invar_matching_tightD[OF assms(5)  uv_in_M]
        by auto (force simp add:  working_potential_def vset(5)[OF F_invar(2)] 
            vset(5)[OF F_invar(3)] F_def   missed_ε_def)+
    qed
  qed
    have path_in_F:"set (get_path F l) ⊆ Vs (abstract_forest F) ∪ (vset_to_set (roots F))"
      using  p_pref_props(3,4) by (auto dest: walk_in_Vs) 
  have "path G p"
    unfolding p_def
  proof(cases rule: disjE[OF p_pref_props(4)], goal_cases)
    case 1
    have path_in_F:"set (get_path F l) ⊆ Vs (abstract_forest F)"
      using 1  by (auto dest: walk_in_Vs)
    show ?case 
    apply(rule  path.path2[of r l G "tl (get_path F l)", 
          simplified get_path_split_off_first[simplified  hd_get_path, symmetric]])
    using r_l_props(1) 1 invar_basicD(5)[OF assms(2)]
    by(auto intro!:  path_subset[of "abstract_forest F" _ G]
        simp add: p_def walk_betw_def F_def)
  next
    case 2
    then show ?case 
      by (auto intro: edges_are_Vs_2 r_l_props(1))
  qed
  moreover have  "distinct p"
    using  path_in_F basic_invars(1) evens_and_odds(3) r_not_even_or_odd p_pref_props(5)
    by(auto simp add: p_def F_def)
  moreover have "matching_augmenting_path ℳ p"
  proof(rule matching_augmenting_pathI, goal_cases)
    case 1
    then show ?case 
      using get_path_length
      by(auto simp add: p_def)
  next
    case 2
    then show ?case 
      by(auto simp add: edges_of_p_are alt_list_step insert_commute p_pref_props(1)
          intro: l_r_not_in_M)
  next
    case 3
    then show ?case 
      using r_unmatched
      by(auto simp add: p_def)
  next
    case 4
    show ?case
      using get_path_non_empty p_pref_props(3) roots(3)[OF basic_invars(1)]
      by(auto simp add: p_def F_def)
  qed
  ultimately show "graph_augmenting_path G ℳ (the (augpath state'))"
    by(auto simp add: state'_def)
  show "forest_invar ℳ (forest state')"
    using assms(2)
    by(auto simp add: state'_def dest: invar_basicD)
  show   "invar_basic state'" 
    unfolding state'_def
    apply(rule  invar_basicI)
    using invar_basicD[OF assms(2)]
    by simp_all
qed

lemma augpath_Some_valid_result:
  assumes "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
    "augpath state' ≠ None"
    "state' = search_path_loop state"
  shows "invar_feasible_potential state'" (is ?th1)
    "invar_matching_tight state'" (is ?th2)
    "∀ e ∈ set (edges_of_path (the (augpath state'))).
          ∃ u v. e = {u, v} ∧ 𝗐 u v = π⇧* state' u + π⇧* state' v" (is ?th4)
    "graph_augmenting_path G ℳ (the (augpath state'))" (is ?th5)
     "forest_invar ℳ (forest state')" (is ?th6)
     "invar_basic state'" (is ?th7)
proof-
  have  "?th1 ∧ ?th2 ∧ ?th4 ∧ ?th5 ∧ ?th6 ∧ ?th7"
    using assms(1-8)
    unfolding assms(9) 
  proof(induction state rule: search_path_loop_induct, goal_cases)
    case 1
    then show ?case
      by (simp add: assms(1,2,3,4,5,6,7) search_path_loop_term_gen)
  next
    case (2 state)
    note IH = this
    show ?case 
    proof(cases state rule: search_path_loop_cases)
      case 1
      then show ?thesis 
        using IH(10) 2
        by(auto simp add: search_path_loop_simps(1)[OF 1] search_path_loop_fail_upd_def Let_def
            elim!: search_path_loop_fail_condE 
            dest!: sym[of _ "heap_extract_min (heap state)"]) 
    next
      case 2
      show ?thesis
        using search_path_loop_succ_cond_valid_result[OF 2 IH(3-8) refl]
        by(auto simp add: search_path_loop_simps(2)[OF 2])
    next
      case 3
      show ?thesis 
        using IH(10) 
        by(unfold search_path_loop_simps(3)[OF IH(1) 3], intro IH(2))
          (auto intro!: 3 invar_pres_one_step IH(1,3-9)
            simp add: search_path_loop_simps(3)[OF IH(1) 3])
    qed
  qed
  thus ?th1 ?th2 ?th4 ?th5 ?th6 ?th7
    by auto
qed

subsection ‹Properties of Initial State›

context
  assumes there_are_unmatched_lefts: "L -  Vs ℳ ≠ {}"
begin

lemma forest_roots:
"vset_invar forest_roots"
"vset_to_set forest_roots = L - Vs ℳ"
"vset_to_set forest_roots ≠ {}"
"finite (vset_to_set forest_roots)"
"vset_to_set forest_roots ∩ Vs ℳ = {}"
proof-
  show ths1and2:"vset_invar forest_roots" "vset_to_set forest_roots = L - Vs ℳ"
    using  unmatched_lefts
    unfolding forest_roots_def 
    by auto
  thus "vset_to_set forest_roots ≠ {}"
    using there_are_unmatched_lefts by auto
  show "finite (vset_to_set forest_roots)" 
    by (simp add: finite_L ths1and2(2))
  show "vset_to_set forest_roots ∩ Vs ℳ = {}" 
    by (simp add: inf.commute ths1and2(2))
qed

lemma triple_collapse: "(fst x, fst (snd x), snd (snd x)) = x"
  by simp

lemmas props_of_init_heap_and_ben = 
update_best_even_neighbours_correct[where off = "λ x. 0" and C = rnb_init, 
 OF best_even_neighbour(1) heap(1) unmatched_lefts_in_L _ _ _ unmatched_lefts(2) G(4), 
 simplified best_even_neighbour heap(11), simplified, folded init_best_even_neighbour_def]

lemma initial_forest_invar: "forest_invar ℳ (empty_forest forest_roots)"
  using forest_roots Vs_M_in_K
  by(auto intro!: empty_forest(5) simp add: ℳ_is_matching)

lemma initial_forest_odds: "vset_to_set (odds (empty_forest forest_roots)) = {}"
  by (rule empty_forest_odds[OF initial_forest_invar])

lemma invars_init:
"invar_basic initial_state"
"invar_feasible_potential initial_state"
"invar_forest_tight initial_state"
"invar_matching_tight initial_state"
"invar_best_even_neighbour_heap initial_state"
"invar_best_even_neighbour_map initial_state"
"invar_out_of_heap initial_state"
proof(goal_cases)
  case 1
    have helper:"dom (ben_lookup (best_even_neighbour initial_state)) =
        {r | r l. r ∈ rneighbs l ∧ l ∈ vset_to_set unmatched_lefts}"
    proof(rule set_eqI, goal_cases)
      case (1 x)
      then show ?case 
        using  props_of_init_heap_and_ben(5,6)[OF triple_collapse, of x] 
      by (auto simp add: initial_state_def)+
     qed
  show ?case 
  proof(rule  invar_basicI, goal_cases)
    case 1
    then show ?case 
    using forest_roots Vs_M_in_K
    by(auto intro!: empty_forest(5) 
          simp add: initial_state_def  ℳ_is_matching) 
  next
    case 2
    then show ?case  
    by(simp add: initial_state_def 
                 props_of_init_heap_and_ben(1,2)[OF triple_collapse])     
  next
    case 3
    then show ?case 
    by(simp add: initial_state_def 
                 props_of_init_heap_and_ben(1,2)[OF triple_collapse])
  next
    case 4
    then show ?case 
      by (simp add: initial_state_def missed(1))
  next
    case 5
    then show ?case 
      by (simp add: empty_forest(4) initial_state_def)
  next
    case 6
     show ?case 
       using G(5) unmatched_lefts_in_L
       by(auto simp add: helper)
  next
    case 7
     show ?case 
       by (simp add: domIff missed(2) initial_state_def subset_iff)
  next
    case 8
    have helper:"fst ` heap_abstract (heap initial_state) =
        {r | r l. r ∈ rneighbs l ∧ l ∈ vset_to_set unmatched_lefts}"
    proof(rule, all ‹rule›, goal_cases)
      case (1 x)
      then show ?case 
        by(auto simp add: initial_state_def unmatched_lefts(2)
            props_of_init_heap_and_ben(7)[OF triple_collapse])
    next
      case (2 x)
      then obtain l where l: "l ∈ vset_to_set unmatched_lefts" "x ∈ rneighbs l"
        by blast
       obtain l where l: "l ∈ vset_to_set unmatched_lefts" "x ∈ rneighbs l"
              "ben_lookup (fst (snd init_best_even_neighbour)) x = Some l"
         using props_of_init_heap_and_ben(6)[OF triple_collapse, of x] l
               unmatched_lefts(2)
                by blast
        then show ?case
            by(auto simp add: initial_state_def unmatched_lefts(2)
               props_of_init_heap_and_ben(7)[OF triple_collapse]
              intro!: image_eqI[of _ _ "(x, w⇩π l x)"])
        qed
     show ?case 
       using G(5) unmatched_lefts_in_L
       by(auto simp add: helper)
   next
     case 9
     show ?case
       by(auto simp add: initial_state_def empty_forest(1) forest_roots(2))
   next
     case 10
     show ?case
       by(simp add: initial_forest_odds initial_state_def)
   next
     case 11
     show ?case
     proof(rule, goal_cases)
       case (1 l)
       have "∃la r. l = la ∧ ben_lookup (best_even_neighbour initial_state) r = Some la" 
         using 1[simplified mem_Collect_eq] 
         by (simp add: initial_state_def)
       then obtain r where
                "ben_lookup (best_even_neighbour initial_state) r = Some l"
         by auto
       then show ?case 
         using props_of_init_heap_and_ben(5,6)[OF triple_collapse, of r]
               unmatched_lefts(1) forest_roots(2) empty_forest(1) unmatched_lefts(2)
         by(auto simp add: initial_state_def)
     qed
   next 
     case 12
     show ?case
       by (simp add: initial_forest_odds initial_state_def)
   next 
     case 13
     show ?case
       by (simp add: initial_state_def props_of_init_heap_and_ben(8)[OF triple_collapse])
   next 
     case 14
     show ?case
       by (simp add: initial_state_def props_of_init_heap_and_ben(9)[OF triple_collapse])
   next 
     case (15 r l)
     show ?case
       using 15 props_of_init_heap_and_ben(10)[OF triple_collapse, of r l]
       by (simp add: initial_state_def)
   next
     case 16
     show ?case
       by (simp add: initial_state_def empty_forest(3) forest_roots(2))
   qed
next
  case 2
  then show ?case 
    using G(7)
    by(auto intro!: invar_feasible_potentialI
          simp add:  initial_state_def working_potential_def missed(2) 
         abstract_real_map_def)
next
  case 3
  then show ?case 
    by(auto intro!: invar_forest_tightI
          simp add:  initial_state_def empty_forest(4))
next
  case 4
  then show ?case
    using matching(3)
    by(auto intro!: invar_matching_tightI
          simp add:  initial_state_def empty_forest(4)
                     working_potential_def empty_forest(1) initial_forest_odds missed(2)
                     abstract_real_map_def)
next
  case 5
  have help1: "(a, b) ∈ heap_abstract (snd (snd init_best_even_neighbour)) 
                  ⟹ a ∈ Vs G" for a b
    by (auto intro: edges_are_Vs_2 
          simp add: G(5)[OF set_mp[OF unmatched_lefts_in_L]] unmatched_lefts(2)
                    props_of_init_heap_and_ben(7)[OF triple_collapse])
  have help2: "⟦(a, b) ∈ heap_abstract (snd (snd init_best_even_neighbour));
                a ∈ vset_to_set forest_roots⟧ ⟹ False" for a b
    by(auto simp add: props_of_init_heap_and_ben(7)[OF triple_collapse]
                      forest_roots(2) unmatched_lefts G(5) 
                dest: bipartite_edgeD(1)[OF _ G(1)])
  have help3: "(a, b) ∈ heap_abstract (snd (snd init_best_even_neighbour)) ⟹
           ∃l. b = w⇩π l a ∧ ben_lookup (fst (snd init_best_even_neighbour)) a = Some l"
    for a b
    by(auto simp add: props_of_init_heap_and_ben(7)[OF triple_collapse]
                      forest_roots(2) unmatched_lefts)
  have help4:"(a, w⇩π l a) ∈ heap_abstract (snd (snd init_best_even_neighbour))" 
    if "a ∈ Vs G" "a ∉ vset_to_set forest_roots"
       "ben_lookup (fst (snd init_best_even_neighbour)) a = Some l" for a l
    using that
          props_of_init_heap_and_ben(5)[OF triple_collapse, of a]
    by(auto simp add: props_of_init_heap_and_ben(7)[OF triple_collapse]
                      forest_roots(2) unmatched_lefts)
  show ?case 
    by(auto intro!: help1 help2 help3 help4 invar_best_even_neighbour_heapI
         simp add: initial_state_def missed(2) abstract_real_map_def
                   empty_forest(1) initial_forest_odds vset(2))
next
  case 6
  have helper1: False if
        "r ∈ Vs G"" r ∉ vset_to_set forest_roots"
        "∀l. l ∈ vset_to_set forest_roots ⟶ {l, r} ∉ G"
        "r ∈ rneighbs l" "l ∈ vset_to_set unmatched_lefts" for r l
    using that by(simp add: G(5) forest_roots(2) unmatched_lefts(1))
  have helper2: "∃l. ben_lookup (fst (snd init_best_even_neighbour)) r = Some l ∧
               {r, l} ∈ G ∧ l ∈ vset_to_set forest_roots∧
               w⇩π l r =
               Min {(w⇩π l r) | l. l ∈ vset_to_set forest_roots ∧ {l, r} ∈ G}"
    if  "r ∈ Vs G" "r ∉ vset_to_set forest_roots"
        "l ∈ vset_to_set forest_roots" "{l, r} ∈ G" for l r
  proof-
    have first_step:
     "∃x. (∃l. x = rneighbs l ∧ l ∈ vset_to_set unmatched_lefts) ∧ r ∈ x"
      using that unmatched_lefts(1) forest_roots(2)
      by(auto intro!: exI[of _ "rneighbs l"] exI[of _ l]
             simp add:  G(5))
    then obtain l' where l': "l' ∈ vset_to_set unmatched_lefts"
        "r ∈ rneighbs l'"
        "w⇩π l' r =
        Min {w⇩π l r | l. l ∈ vset_to_set unmatched_lefts ∧ r ∈ rneighbs l}"
        "ben_lookup (fst (snd init_best_even_neighbour)) r = Some l'"
      using props_of_init_heap_and_ben(6)[OF triple_collapse, of r] 
            unmatched_lefts(2)
      by auto     
    then show ?thesis
      using G(5) forest_roots(2) unmatched_lefts(1)
      by (auto intro!: arg_cong[of _ _ Min] simp add: insert_commute)
   qed
   show ?case 
     by(force intro: invar_best_even_neighbour_mapI helper1 helper2
                     props_of_init_heap_and_ben(5)[OF triple_collapse]
         simp add: initial_state_def missed(2) abstract_real_map_def
                   empty_forest(1) initial_forest_odds vset(2) unmatched_lefts(2))
 next
   case 7
   show ?case
     using  props_of_init_heap_and_ben(5)[OF triple_collapse] unmatched_lefts(2)
     by(fastforce intro!: invar_out_of_heapI
                simp add: initial_state_def props_of_init_heap_and_ben(7)[OF triple_collapse])
 qed

lemma search_path_loop_of_init_dom:  "search_path_loop_dom initial_state" 
  by(auto intro: search_path_loop_term_gen simp add: invars_init)

lemma search_path_loop_of_init_same:
  "search_path_loop_impl initial_state = search_path_loop initial_state"
  using search_path_loop_impl_same search_path_loop_of_init_dom by blast
end

subsection ‹Correctness of Path Search›
 
lemma Lefts_Matched_all_lefts_matched:
  assumes "fst search_path = Lefts_Matched"
  shows   "L ⊆ Vs ℳ"
  using assms  unmatched_lefts(1) 
  by(auto simp add: search_path_def Let_def vset_is_empty[OF unmatched_lefts(2)]
             split: if_split_asm option.split_asm)

lemma Dual_Unbounded_dual_unbounded:
  assumes "fst search_path = Dual_Unbounded"
  shows   "∃ p.  (∀ u v. {u, v} ∈ G ⟶ edge_costs u v ≥ p u +  p v)
             ∧ sum p (L ∪ R) ≥ bound"
  apply(rule augpath_None_gen_unbounded_dual[of initial_state])
  using assms unmatched_lefts(1)
  by(auto simp add: search_path_def  search_path_loop_of_init_same
                    Let_def vset_is_empty[OF unmatched_lefts(2)]
             split: if_split_asm option.split_asm
             intro!: invars_init) 

lemma not_Next_Iteration_same_potential:
  assumes "∄p. fst search_path = Next_Iteration p"
  shows   "snd search_path = initial_pot"
  using assms
  by(auto simp add: search_path_def Let_def split: if_split option.split)

lemma new_potential_correct:
  assumes "forest_invar ℳ (forest state)"
  shows "potential_invar (new_potential state)"
        "potential_get (new_potential state) = 
         working_potential state"
proof-
  define fo where "fo = (λx y. potential_upd y x (π x - acc state + missed_at state x))"
  define fe where "fe = (λx y. potential_upd y x (π x + acc state - missed_at state x))"
  have fe_it_invar_pres: 
       "⟦potential_invar p; set evs ⊆ K⟧ ⟹ potential_invar (foldr fe evs p)" for p evs
    by(induction evs) (auto simp add: fe_def intro!: potential_map.fixed_univ_map_upd_invar)
  have fo_it_invar_pres: 
       "⟦potential_invar p; set ods ⊆ K⟧ ⟹ potential_invar (foldr fo ods p)" for p ods
    by(induction ods) (auto simp add: fo_def intro!: potential_map.fixed_univ_map_upd_invar)
 obtain evenlist where evenlist:
    "vset_to_set (evens (forest state)) = set evenlist" "distinct evenlist"
    "vset_iterate_pot (λ x y. fe y x) initial_pot (evens (forest state))
          = foldl (λ x y. fe y x) initial_pot evenlist"
    using vset_iterations(2)[OF evens_and_odds(1), OF assms] by blast     
  define evs where "evs = rev evenlist"
  have evs_props: "rev evenlist = evs" "distinct evs" "set evs ⊆ K"
    using evenlist(1,2) vset.fixed_univ_set_universe[OF evens_and_odds(1)[OF assms]]
    by (auto simp add: evs_def)
  define intermed_pot where "intermed_pot = foldr fe evs initial_pot"
 obtain oddlist where oddlist:
    "vset_to_set (odds (forest state)) = set oddlist" "distinct oddlist"
    "vset_iterate_pot (λ x y. fo y x) intermed_pot (odds (forest state))
          = foldl (λ x y. fo y x) intermed_pot oddlist"
    using vset_iterations(2)[OF evens_and_odds(2), OF assms] by blast     
  define ods where "ods = rev oddlist"
  have ods_props: "rev oddlist = ods" "distinct ods" "set ods ⊆ K"
    using oddlist(1,2) vset.fixed_univ_set_universe[OF evens_and_odds(2)[OF assms]]
    by (auto simp add: ods_def)
  have new_potential_def: "new_potential state = foldr fo ods (foldr fe evs initial_pot)"
    using oddlist(3) evenlist(3)
    by(auto simp add: new_potential_def foldr_conv_foldl intermed_pot_def
                      fe_def fo_def evs_def ods_def)
  show  "potential_invar (new_potential state)"
    by(auto intro!: fo_it_invar_pres fe_it_invar_pres potential evs_props(3) ods_props(3)
          simp add: new_potential_def)
 have fe_it_is: 
       "⟦potential_invar p; distinct evs; set evs ⊆ K⟧
          ⟹ potential_get (foldr fe evs p) = 
               (λ x. if x ∈ set evs then π x + acc state - missed_at state x
                      else potential_get p x)" for p evs
  proof(induction evs)
    case (Cons a evs)
    hence "potential_invar (foldr fe evs p)" 
      by(auto intro: fe_it_invar_pres)
    thus ?case 
      using Cons by(auto simp add: fe_def potential_map.fixed_univ_map_upd)
  qed simp
 have fo_it_is: 
       "⟦potential_invar p; distinct ods; set ods ⊆ K⟧
          ⟹ potential_get (foldr fo ods p) = 
               (λ x. if x ∈ set ods then π x - acc state + missed_at state x
                      else potential_get p x)" for p ods
  proof(induction ods)
    case (Cons a ods)
    hence "potential_invar (foldr fo ods p)" 
      by(auto intro: fo_it_invar_pres)
    thus ?case 
      using Cons by(auto simp add: fo_def potential_map.fixed_univ_map_upd)
  qed simp
  note fo_it_is_applied =
    fo_it_is[OF fe_it_invar_pres[OF potential evs_props(3)] ods_props(2,3)]
  note fe_it_is_applied =  fe_it_is[OF potential evs_props(2,3)]
  have "(λx. if x ∈ set ods then π x - acc state + missed_at state x
          else if x ∈ set evs then π x + acc state - missed_at state x else π x) =
    π⇧* state"
    using evens_and_odds(1,2,4)[OF assms]
    by(auto intro!: ext 
          simp add: disjoint_iff working_potential_def evs_def ods_def vset(5)
                   evenlist(1) oddlist(1))
  thus "potential_get (new_potential state) = π⇧* state"
    by((subst new_potential_def fo_it_is_applied fe_it_is_applied)+)
    auto
qed

lemma Next_Iteration_tight_path_and_new_feasible_potential:
  assumes "search_path = (Next_Iteration p, π')"
  shows "⋀ u v. {u, v} ∈ G ⟹
               𝗐 u v ≥ potential_get π' u +
                        potential_get π' v" 
    "⋀ u v. {u, v} ∈ ℳ ⟹
               𝗐 u v = potential_get π' u +
                       potential_get π' v" 
    "⋀ u v. {u, v} ∈ set (edges_of_path p) ⟹
               𝗐 u v = potential_get π' u +
                        potential_get π' v" 
    "graph_augmenting_path G ℳ p"
    "potential_invar π'"
proof-
  have from_assms: "L - Vs ℳ ≠ {}" 
    "augpath (search_path_loop initial_state) = Some p"
    "π' = new_potential (search_path_loop initial_state)"
    "augpath (search_path_loop initial_state) ≠ None"
    using assms unmatched_lefts(1)
    by(auto simp add: search_path_def  search_path_loop_of_init_same
        unmatched_lefts(2) vset_is_empty Let_def 
        split: if_split_asm option.split_asm
        intro: invars_init)
  note result_props = augpath_Some_valid_result[OF invars_init[OF from_assms(1)]
      from_assms(4) refl]
  note new_potential_props = new_potential_correct[OF result_props(5)]
  show "potential_get π' u +
           potential_get π' v
           ≤ 𝗐 u v"
    if asm: "{u, v} ∈ G" for u v
    using  invar_feasible_potentialD result_props(1) asm
    by (auto simp add: from_assms(3) new_potential_props(2))
  show "𝗐 u v =  potential_get π' u +
                        potential_get π' v"
    if asm: "{u, v} ∈ ℳ"for u v
    using  invar_matching_tightD result_props(2) asm
    by (auto simp add: from_assms(3) new_potential_props(2))
  show "graph_augmenting_path G ℳ p"
    using result_props(4)
    by (auto simp add: from_assms(2,3) new_potential_props(2) )
  hence "{u, v} ∈ set (edges_of_path p) ⟹ {u, v} ∈ G" for u v 
    using path_ball_edges by auto
  thus "𝗐 u v =  potential_get π' u +
                        potential_get π' v"
    if asm: "{u, v} ∈ set (edges_of_path p)" for u v
    using  bspec[OF result_props(3), of "{u, v}"] asm G(6)[of u v]
    by (auto simp add: from_assms(2,3) new_potential_props(2) doubleton_eq_iff)
  show     "potential_invar π'"
    by (simp add: from_assms(3) new_potential_props(1))

qed

lemmas search_path_correct = 
 Lefts_Matched_all_lefts_matched
 Dual_Unbounded_dual_unbounded
 Next_Iteration_tight_path_and_new_feasible_potential


end

subsection ‹Facts about Single Steps of the Path Search›

text ‹This is for refinement, not necessary for functional correctness.›

text ‹These functional facts about the single steps of the path search are the pure
      preconditions of the imperative operations in the imperative refinement: whenever the
      imperative program inserts into the queue, decreases a key, extends the forest or writes a
      path, the functional state satisfies the precondition of the corresponding operation.›

context primal_dual_path_search
begin

subsubsection ‹Scanning a Neighbourhood›

text ‹The invariant of a scan of the neighbourhood of @{term l} with offset @{term off}. These
      are the assumptions of @{thm update_best_even_neighbour_correct}.›

definition "scan_inv off l ben queue =
  (ben_invar ben ∧ heap_invar queue ∧ l ∈ L ∧
   (∀r k. (r, k) ∈ heap_abstract queue ⟶
          (∃l. ben_lookup ben r = Some l ∧ k = w⇩π l r + off l)) ∧
   (∀r l'. (ben_lookup ben r = Some l' ∧ (∄k. (r, k) ∈ heap_abstract queue)) ⟶
          w⇩π l' r + off l' ≤ off l) ∧
   (∀r l'. ben_lookup ben r = Some l' ⟶ l' ∈ L ∧ {l', r} ∈ G))"

lemma scan_invD:
  assumes "scan_inv off l ben queue"
  shows "ben_invar ben" "heap_invar queue" "l ∈ L"
    "⋀r k. (r, k) ∈ heap_abstract queue ⟹
            ∃l. ben_lookup ben r = Some l ∧ k = w⇩π l r + off l"
    "⋀r l'. ⟦ben_lookup ben r = Some l'; ∄k. (r, k) ∈ heap_abstract queue⟧ ⟹
            w⇩π l' r + off l' ≤ off l"
    "⋀r l'. ben_lookup ben r = Some l' ⟹ l' ∈ L"
    "⋀r l'. ben_lookup ben r = Some l' ⟹ {l', r} ∈ G"
  using assms by (auto simp: scan_inv_def)

text ‹All entries of the best even neighbours are still in the queue. This holds during the
      initial scans, where nothing has been extracted yet.›

definition "all_in_heap ben queue =
  (∀r l'. ben_lookup ben r = Some l' ⟶ (∃k. (r, k) ∈ heap_abstract queue))"

lemma relax_neighbour_None:
  assumes "scan_inv off l ben queue" "r ∈ rneighbs l" "ben_lookup ben r = None"
  shows "r ∈ Vs G" "∄k. (r, k) ∈ heap_abstract queue"
  using scan_invD[OF assms(1)] rneighbs_in_G[of l r] assms(2,3)
  by (fastforce intro: edges_are_Vs_2)+

lemma relax_neighbour_Some:
  assumes "scan_inv off l ben queue" "r ∈ rneighbs l" "ben_lookup ben r = Some l'"
          "w⇩π_code l r + off l < w⇩π_code l' r + off l'"
  shows "r ∈ Vs G" "(r, w⇩π_code l' r + off l') ∈ heap_abstract queue"
proof-
  note inv = scan_invD[OF assms(1)]
  have lr: "{l, r} ∈ G" using rneighbs_in_G[OF inv(3) assms(2)] .
  have l'r: "{l', r} ∈ G" "l' ∈ L" using inv(6,7)[OF assms(3)] by auto
  have codes: "w⇩π_code l r = w⇩π l r" "w⇩π_code l' r = w⇩π l' r"
    using w⇩π_code_is[OF lr inv(3)] w⇩π_code_is[OF l'r] by auto
  show "r ∈ Vs G" using lr by (auto intro: edges_are_Vs_2)
  have in_heap: "∃k. (r, k) ∈ heap_abstract queue"
  proof(rule ccontr)
    assume "∄k. (r, k) ∈ heap_abstract queue"
    hence "w⇩π l' r + off l' ≤ off l" using inv(5)[OF assms(3)] by blast
    moreover have "0 ≤ w⇩π l r" using w⇩π_non_neg[OF lr] .
    ultimately show False using assms(4) by (simp add: codes)
  qed
  then obtain k where k: "(r, k) ∈ heap_abstract queue" by blast
  then obtain l'' where "ben_lookup ben r = Some l''" "k = w⇩π l'' r + off l''"
    using inv(4) by blast
  thus "(r, w⇩π_code l' r + off l') ∈ heap_abstract queue"
    using k assms(3) codes(2) by auto
qed

lemma relax_neighbour_pres:
  assumes "scan_inv off l ben queue" "r ∈ rneighbs l"
  shows "scan_inv off l (fst (relax_neighbour off l (ben, queue) r))
                        (snd (relax_neighbour off l (ben, queue) r))"
        "all_in_heap ben queue ⟹
         all_in_heap (fst (relax_neighbour off l (ben, queue) r))
                     (snd (relax_neighbour off l (ben, queue) r))"
proof-
  note inv = scan_invD[OF assms(1)]
  have lr: "{l, r} ∈ G" using rneighbs_in_G[OF inv(3) assms(2)] .
  have code_l: "w⇩π_code l r = w⇩π l r" using w⇩π_code_is[OF lr inv(3)] .
  have rK: "r ∈ K" "l ≠ nil"
    using in_K(3)[OF edges_are_Vs_2[OF lr]] not_nil(1)[OF inv(3)] by auto
  have "scan_inv off l (fst (relax_neighbour off l (ben, queue) r))
                       (snd (relax_neighbour off l (ben, queue) r)) ∧
        (all_in_heap ben queue ⟶
         all_in_heap (fst (relax_neighbour off l (ben, queue) r))
                     (snd (relax_neighbour off l (ben, queue) r)))"
  proof(cases "ben_lookup ben r")
    case None
    note legal = relax_neighbour_None[OF assms None]
    have heap': "heap_abstract (heap_insert queue r (w⇩π_code l r + off l)) =
                 heap_abstract queue ∪ {(r, w⇩π_code l r + off l)}"
      using heap(10)[OF inv(2) legal(1,2)] .
    show ?thesis
      using inv legal None lr
      by (auto simp: relax_neighbour_view scan_inv_def all_in_heap_def heap'[unfolded code_l] rK
                     code_l best_even_neighbour heap(3) insert_commute)
  next
    case (Some l')
    note l'r = inv(6,7)[OF Some]
    have code_l': "w⇩π_code l' r = w⇩π l' r" using w⇩π_code_is[of l' r] l'r by auto
    show ?thesis
    proof(cases "w⇩π_code l r + off l < w⇩π_code l' r + off l'")
      case True
      note legal = relax_neighbour_Some[OF assms Some True]
      have heap': "heap_abstract (heap_decrease_key queue r (w⇩π_code l r + off l)) =
                   heap_abstract queue - {(r, w⇩π_code l' r + off l')} ∪
                   {(r, w⇩π_code l r + off l)}"
        using heap(9)[OF inv(2) legal(1,2) True] .
      have invar': "heap_invar (heap_decrease_key queue r (w⇩π_code l r + off l))"
        using heap(4)[OF inv(2) legal(1,2) True] .
      have uniq: "⋀k. (r, k) ∈ heap_abstract queue ⟹ k = w⇩π_code l' r + off l'"
        using heap(7)[OF inv(2) _ legal(2)] by blast
      define ben' where "ben' = ben_upd ben r l"
      define queue' where "queue' = heap_decrease_key queue r (w⇩π_code l r + off l)"
      have rel: "relax_neighbour off l (ben, queue) r = (ben', queue')"
        by (simp add: relax_neighbour_view Some True ben'_def queue'_def)
      have look': "ben_lookup ben' = (ben_lookup ben)(r ↦ l)"
        using best_even_neighbour(3)[OF inv(1) rK] by (simp add: ben'_def)
      have binv': "ben_invar ben'"
        using best_even_neighbour(2)[OF inv(1) rK(1)] by (simp add: ben'_def)
      have habs': "heap_abstract queue' =
                   heap_abstract queue - {(r, w⇩π l' r + off l')} ∪ {(r, w⇩π l r + off l)}"
        using heap' by (simp add: queue'_def code_l code_l')
      have r_in': "(r, w⇩π l r + off l) ∈ heap_abstract queue'"
        by (simp add: habs')
      have heap_r: "⋀k. (r, k) ∈ heap_abstract queue' ⟹ k = w⇩π l r + off l"
        using uniq by (auto simp: habs' code_l')
      have heap_other: "⋀r' k. ⟦(r', k) ∈ heap_abstract queue'; r' ≠ r⟧ ⟹
                                  (r', k) ∈ heap_abstract queue"
        by (simp add: habs')
      have heap_other': "⋀r' k. ⟦(r', k) ∈ heap_abstract queue; r' ≠ r⟧ ⟹
                                   (r', k) ∈ heap_abstract queue'"
        by (simp add: habs')
      have s: "scan_inv off l ben' queue'"
        unfolding scan_inv_def
      proof(intro conjI allI impI)
        show "ben_invar ben'" by (rule binv')
        show "heap_invar queue'" using invar' by (simp add: queue'_def)
        show "l ∈ L" by (rule inv(3))
      next
        fix r'' k assume "(r'', k) ∈ heap_abstract queue'"
        thus "∃l. ben_lookup ben' r'' = Some l ∧ k = w⇩π l r'' + off l"
          using heap_r heap_other inv(4) by (cases "r'' = r") (auto simp: look')
      next
        fix r'' l'' assume a: "ben_lookup ben' r'' = Some l'' ∧ (∄k. (r'', k) ∈ heap_abstract queue')"
        have rr: "r'' ≠ r" using a r_in' by blast
        have b: "ben_lookup ben r'' = Some l''" using a rr by (simp add: look')
        have c: "∄k. (r'', k) ∈ heap_abstract queue" using a rr heap_other' by blast
        show "w⇩π l'' r'' + off l'' ≤ off l" by (rule inv(5)[OF b c])
      next
        fix r'' l'' assume "ben_lookup ben' r'' = Some l''"
        thus "l'' ∈ L" using inv(3,6) by (cases "r'' = r") (auto simp: look')
      next
        fix r'' l'' assume "ben_lookup ben' r'' = Some l''"
        thus "{l'', r''} ∈ G" using inv(7) lr by (cases "r'' = r") (auto simp: look')
      qed
      have a: "all_in_heap ben queue ⟹ all_in_heap ben' queue'"
        unfolding all_in_heap_def look'
        by (metis fun_upd_apply r_in' heap_other')
      show ?thesis
        using s a by (simp add: rel)
    next
      case False
      show ?thesis
        using assms(1) False Some by (auto simp: relax_neighbour_view)
    qed
  qed
  thus "scan_inv off l (fst (relax_neighbour off l (ben, queue) r))
                       (snd (relax_neighbour off l (ben, queue) r))"
       "all_in_heap ben queue ⟹
         all_in_heap (fst (relax_neighbour off l (ben, queue) r))
                     (snd (relax_neighbour off l (ben, queue) r))"
    by auto
qed

lemma scan_inv_zero:
  "⟦ben_invar ben; heap_invar queue; l ∈ L;
    ∀r k. (r, k) ∈ heap_abstract queue ⟶ (∃l. ben_lookup ben r = Some l ∧ k = w⇩π l r);
    all_in_heap ben queue;
    ∀r l'. ben_lookup ben r = Some l' ⟶ l' ∈ L ∧ {l', r} ∈ G⟧ ⟹
   scan_inv (λx. 0) l ben queue"
  by (auto simp: scan_inv_def all_in_heap_def)

subsubsection ‹The Invariants of the Loop›

definition "search_invars state =
  (invar_basic state ∧ invar_feasible_potential state ∧ invar_forest_tight state ∧
   invar_matching_tight state ∧ invar_best_even_neighbour_heap state ∧
   invar_best_even_neighbour_map state ∧ invar_out_of_heap state)"

lemma search_invars_step:
  "⟦search_path_loop_cont_cond state; search_invars state⟧ ⟹
   search_invars (search_path_loop_cont_upd state)"
  using invar_pres_one_step[of state] by (auto simp: search_invars_def)

lemma search_invars_dom: "search_invars state ⟹ search_path_loop_dom state"
  by (auto simp: search_invars_def intro: search_path_loop_term_gen)

lemma search_invars_init: "L - Vs ℳ ≠ {} ⟹ search_invars initial_state"
  using invars_init by (auto simp: search_invars_def)

subsubsection ‹Facts about a Continuing Step›

lemma cont_step_facts:
  assumes "search_path_loop_cont_cond state"
    "invar_basic state"
    "invar_feasible_potential state"
    "invar_forest_tight state"
    "invar_matching_tight state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    "invar_out_of_heap state"
    and ext: "heap_extract_min (heap state) = (queue0, Some r0)"
    and bud: "buddy r0 = Some l0"
  defines "lx ≡ the (ben_lookup (best_even_neighbour state) r0)"
  defines "accx ≡ w⇩π_code lx r0 + missed_at state lx"
  defines "missedx ≡ missed_upd (missed_upd (missed state) r0 accx) l0 accx"
  shows "ben_lookup (best_even_neighbour state) r0 = Some lx"
        "lx ∈ L" "{lx, r0} ∈ G" "l0 ∈ L"
        "forest_extension_precond (forest state) ℳ lx r0 l0"
        "scan_inv (missed_get missedx) l0 (best_even_neighbour state) queue0"
proof-
  define F where "F = forest state"
  define ben where "ben = best_even_neighbour state"
  define missed_ε where  "missed_ε = missed_at state"
  obtain queue heap_min where queue_heap_min_def:
    " (queue, heap_min) = heap_extract_min (heap state)"
    by(cases "heap_extract_min (heap state)") auto
  obtain r where r_def: "heap_min = Some r"
    using queue_heap_min_def assms(1)
    by(auto elim: search_path_loop_cont_condE)
  define l where "l = the (ben_lookup ben r)"
  define acc' where "acc' = w⇩π l r + missed_ε l"
  obtain l' where l'_def: "buddy r = Some l'"
    using queue_heap_min_def assms(1)
    by(auto elim: search_path_loop_cont_condE simp add: r_def)
  define missed' where "missed' = missed_upd (missed_upd (missed state) r acc') l' acc'"
  obtain C' ben' queue' where ben'_queue'_def:
    "(C', ben', queue') = update_best_even_neighbour 
                                           (missed_get missed')
                                           (neighb_coll state) ben queue l'"
    by(metis prod_cases3)
  define F' where "F'= extend_forest_even_unclassified F l r l'"
  define state' where "state' = state ⦇ forest:= F', 
                            best_even_neighbour:=ben', neighb_coll:=C',
                            heap:=queue',
                            missed:=missed',
                            acc:= acc' ⦈"
  obtain k where k: "(r, k) ∈ heap_abstract (heap state)"
    "⋀ x' k'. (x', k') ∈ heap_abstract (heap state) ⟹ k ≤ k'"
    using r_def  pair_eq_fst_snd_eq[OF queue_heap_min_def]
      heap(5)[of "heap state" r] assms(2)
    by(auto elim!: invar_basicE)
  have r_unclassified: "r ∈ Vs G - aevens state - aodds state"
    using assms(6) k
    by (auto elim: invar_best_even_neighbour_heapE)
  have r_l_props: "{r, l} ∈ G" "l ∈ aevens state"
    "w⇩π l r + missed_at state l =
         Min {w⇩π l r + missed_at state l| l. l ∈ aevens state ∧ {l, r} ∈ G}"
    using assms(6,7) r_unclassified r_def  k(1) 
    by(fastforce elim!: invar_best_even_neighbour_mapE 
        dest: invar_best_even_neighbour_heapD 
        simp add: l_def ben_def)+
  have l_code: "w⇩π_code l r = w⇩π l r"
    using r_l_props(1,2) invar_basicD(9)[OF assms(2)]
    by(auto intro!: w⇩π_code_is simp add: insert_commute)
  have upd_state_is_state':"search_path_loop_cont_upd state =  state'"
    using ben'_queue'_def r_def l'_def queue_heap_min_def l_code[unfolded l_def ben_def]
          invar_best_even_neighbour_heap_get[OF assms(6) k(1)]
    by(auto simp add: search_path_loop_cont_upd_def state'_def Let_def
        F'_def  missed'_def acc'_def l_def ben_def missed_ε_def F_def
        split: option.split prod.split)
  have k_is: "k = w⇩π l r + missed_at state l"
    using assms(6) ben_def k(1) l_def
    by(fastforce dest: invar_best_even_neighbour_heapD)
  have r_l'_in_M:"{r, l'} ∈ ℳ"
    using ℳ_def l'_def by fastforce
  have l'_not_even:"l' ∈ vset_to_set (evens F) ⟹ False"
  proof(goal_cases)
    case 1
    hence "{r, l'} ∈ abstract_forest F"
      using assms(2) evens_and_odds(3)[of ℳ F]  roots(2)[of ℳ F] higher_forest_properties(2)[OF  _ r_l'_in_M, of F] 
      by(auto elim!: invar_basicE dest!: 
          simp add: F_def)
    hence "r ∈ aevens state ∪ aodds state"
      using  assms(2) 1
      by(auto elim!: invar_basicE 
          simp add: F_def higher_forest_properties(3)  insert_commute)
    thus False
      using r_unclassified by blast
  qed
  have l'_not_even_or_odd:
    "l' ∈ vset_to_set (evens F) ∪  vset_to_set (odds F) ⟹ False"
  proof(goal_cases)
    case 1
    hence "{r, l'} ∈ abstract_forest F"
      using assms(2) evens_and_odds(3)[of ℳ F]  roots(2)[of ℳ F] higher_forest_properties(2)[OF  _ r_l'_in_M, of F] 
      by(auto elim!: invar_basicE dest!: 
          simp add: F_def)
    hence "r ∈ aevens state ∪ aodds state"
      using   1 higher_forest_properties(3)[of ℳ F]
      by(force intro: invar_basicE[OF assms(2)] 
          simp add: F_def   insert_commute)
    thus False
      using r_unclassified by blast
  qed
  have r_not_even_or_odd:
    "r ∈ vset_to_set (evens F) ∪  vset_to_set (odds F) ⟹ False"
    using F_def r_unclassified by fastforce
  have l_r_not_in_M:"{l, r} ∈ ℳ ⟹ False" 
    using r_l_props(2) assms(2) higher_forest_properties(2,3)[of ℳ F l r] 
      r_not_even_or_odd evens_and_odds(3)[of ℳ F]
    by(auto elim!: invar_basicE simp add: F_def)
  have l_in_L:"l ∈ L"
    using  assms(2) r_l_props(2)
    by(auto elim!: invar_basicE)
  hence r_in_R: "r ∈ R"
    using G(1) bipartite_edgeD(3) l_in_L r_l_props(1) by fastforce
  moreover have r_l'_in_G:"{r, l'} ∈ G"
    using l'_def matching(2) by blast
  ultimately have l'_in_L: "l' ∈ L" 
    using   bipartite_edgeD(2)[OF _ G(1)]
    by(auto simp add: insert_commute)
  have ben_l'_None:"ben_lookup ben l' = None"
    using  bipartite_edgeD(1)[OF _ G(1)] edges_are_Vs_2[OF r_l'_in_G] 
      l'_in_L l'_not_even_or_odd  r_l'_in_G assms(2)
    by (auto elim!: invar_basicE 
        intro!: invar_best_even_neighbour_mapD(1)[OF assms(7), of l']
        simp add: ben_def F_def)
  have l'_not_a_ben: "ben_lookup ben rr = Some l' ⟹ False" for rr 
    using F_def assms(2)  l'_not_even 
    by(force elim!: invar_basicE simp add:  ben_def) 
  have queue'_is: "heap_abstract (fst (heap_extract_min (heap state))) =
         heap_abstract (heap state) - {(r, w⇩π l r + missed_at state l)}"
    using assms(2) k(1) k_is
    by(intro heap(8))
      (auto elim!: invar_basicE 
        simp add: r_def[symmetric] pair_eq_fst_snd_eq[OF queue_heap_min_def])
  note basic_invars = invar_basicD[OF assms(2)]
  have ben_edges_before: "ben_lookup ben rr = Some ll ⟶ ll ∈ L ∧ {ll, rr} ∈ G" for rr ll
    using basic_invars(9,11) basic_invars(15)[of rr ll] 
    by(fastforce simp add: ben_def)
  have r_l_l'_distinct:"r ≠ l" "l ≠ l'" "r ≠ l'"
    using r_l_props(2) r_unclassified  bipartite_edgeD(2)[OF r_l'_in_G  G(1)] r_in_R 
          F_def l'_not_even by auto
  hence forest_extension_precond: "forest_extension_precond F ℳ l r l'"
    using l'_not_even_or_odd r_not_even_or_odd l_r_not_in_M 
    by(auto intro!: forest_extension_precondI  ℳ_is_matching
        simp add: F_def assms(2) invar_basicD(1) r_l_props(2)  r_l'_in_M)
  have missed'_is: "missed_get missed' = 
                    (λ x. if x = r ∨ x = l' then acc' else missed_at state x)"
    using invar_basicD(4)[OF assms(2)] in_K(1)[OF l'_in_L] in_K(2)[OF r_in_R]
    by(auto simp add: missed'_def acc'_def missed(3,4))
  have queue_props: "heap_invar queue" 
    "heap_abstract queue = heap_abstract (heap state) - {(r, acc')}"
    "⋀ r' k'. (r', k') ∈ heap_abstract (heap state) ⟹ acc' ≤ k'"
    using invar_basicD(3)[OF assms(2)] heap(2)[of "heap state"] k(2) k_is 
    by (auto simp add: pair_eq_fst_snd_eq[OF queue_heap_min_def] missed_ε_def  acc'_def   queue'_is )
  have update_best_even_neighbour_conditions:
    "ben_invar ben" "heap_invar queue" "l' ∈ L"
    "⋀r k. (r, k) ∈ heap_abstract queue ⟶  
            (∃l. ben_lookup ben r = Some l ∧
             k = w⇩π l r + missed_get missed' l)"
    "⋀r l'a. ben_lookup ben r = Some l'a ∧ (∄k. (r, k) ∈ heap_abstract queue) ⟶
                 w⇩π l'a r + missed_get missed' l'a
                ≤ missed_get missed' l'"
  proof(goal_cases)
    case 1
    then show ?case 
      using assms(2) ben_def invar_basicD(2) by blast
  next
    case 2
    then show ?case 
      using heap(2)[OF invar_basicD(3)[OF  assms(2)]] queue_heap_min_def[symmetric] 
      by simp
  next
    case 3
    then show ?case 
      using l'_in_L by simp
  next
    case (4 rr k)
    then show ?case 
      using l'_not_even r_not_even_or_odd 
            invar_best_even_neighbour_mapD[OF assms(7), of rr]
      by(fastforce intro: exI[of _ "the (ben_lookup (best_even_neighbour state) rr)"]
                simp add: ben_def pair_eq_fst_snd_eq[OF queue_heap_min_def] F_def
                          queue'_is missed'_is invar_best_even_neighbour_heapD[OF assms(6)])
  next
    case (5 rr ll)
    show ?case 
    proof(rule, goal_cases)
      case 1
      note One = this
      hence h1:"r ≠ ll"
        using assms(2)  r_not_even_or_odd 
        by(force elim!: invar_basicE simp add: ben_def F_def)
      have h2: "ll ≠ l'"
        using l'_not_a_ben 1 by blast
      have cases:"(∄k. (rr, k) ∈ heap_abstract (heap state)) ∨ rr = r"
        using 1 unfolding queue_props(2) by blast
      have ll_ben_of_rr_old:"ben_lookup (best_even_neighbour state) rr = Some ll" 
        using One ben_def by fastforce
      show ?case
        unfolding missed'_is
        apply(subst (2) if_P,  simp)
        apply(subst if_not_P)
        using h1 h2 apply simp
      proof(cases rule: disjE[OF cases], goal_cases)
        case 1
        note one = this
        have "kr∈heap_abstract (heap state) ⟹ w⇩π ll rr + missed_at state ll ≤ snd kr" for kr
          using invar_out_of_heapD[OF assms(8) ll_ben_of_rr_old 1] by simp
        moreover have "(r, w⇩π l r + missed_at state l) ∈ heap_abstract (heap state)"
          using k(1) k_is by blast
        ultimately show ?case 
          by(auto simp add: acc'_def missed_ε_def)
      next
        case 2
        hence "w⇩π ll rr + missed_at state ll = acc'"
          using One acc'_def l_def missed_ε_def by auto
        thus ?case by blast
      qed
    qed
  qed 
  have eqs: "queue = queue0" "r = r0" "l' = l0"
    using queue_heap_min_def ext r_def l'_def bud by auto
  have lx_eq: "lx = l" by (simp add: lx_def l_def ben_def eqs)
  have accx_eq: "accx = acc'"
    using l_code by (simp add: accx_def acc'_def missed_ε_def lx_eq eqs)
  have missedx_eq: "missedx = missed'" by (simp add: missedx_def missed'_def accx_eq eqs)
  obtain l'' where l'': "ben_lookup ben r = Some l''"
    using invar_best_even_neighbour_heapD[OF assms(6)] k(1) by (auto simp: ben_def)
  show "ben_lookup (best_even_neighbour state) r0 = Some lx"
    using l'' by (simp add: lx_eq l_def ben_def eqs[symmetric])
  show "lx ∈ L" "{lx, r0} ∈ G" "l0 ∈ L"
    using l_in_L r_l_props(1) l'_in_L by (auto simp: lx_eq eqs[symmetric] insert_commute)
  show "forest_extension_precond (forest state) ℳ lx r0 l0"
    using forest_extension_precond by (simp add: F_def lx_eq eqs[symmetric])
  show "scan_inv (missed_get missedx) l0 (best_even_neighbour state) queue0"
    using update_best_even_neighbour_conditions ben_edges_before
    unfolding scan_inv_def missedx_eq eqs[symmetric] ben_def
    by blast
qed

subsubsection ‹Facts about the Extracted Vertex›

lemma extract_facts:
  assumes "invar_basic state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    and ext: "heap_extract_min (heap state) = (queue0, Some r0)"
  defines "lx ≡ the (ben_lookup (best_even_neighbour state) r0)"
  shows "ben_lookup (best_even_neighbour state) r0 = Some lx"
        "lx ∈ aevens state" "{lx, r0} ∈ G" "lx ∈ L"
        "r0 ∉ aevens state" "r0 ∉ aodds state" "r0 ∈ Vs G"
        "forest_invar ℳ (forest state)"
proof-
  obtain k where k: "(r0, k) ∈ heap_abstract (heap state)"
    using ext heap(5)[of "heap state" r0] assms(1)
    by (auto elim!: invar_basicE)
  have r_unclassified: "r0 ∈ Vs G - aevens state - aodds state"
    using assms(2) k by (auto elim: invar_best_even_neighbour_heapE)
  obtain l'' where l'': "ben_lookup (best_even_neighbour state) r0 = Some l''"
    using invar_best_even_neighbour_heapD[OF assms(2)] k by auto
  hence lx: "lx = l''" by (simp add: lx_def)
  have r_l_props: "{r0, lx} ∈ G" "lx ∈ aevens state"
    using assms(2,3) r_unclassified k(1) l''
    by (fastforce elim!: invar_best_even_neighbour_mapE
                   dest: invar_best_even_neighbour_heapD simp add: lx)+
  show "ben_lookup (best_even_neighbour state) r0 = Some lx" using l'' lx by simp
  show "lx ∈ aevens state" "{lx, r0} ∈ G"
    using r_l_props by (auto simp: insert_commute)
  show "lx ∈ L" using assms(1) r_l_props(2) by (auto elim!: invar_basicE)
  show "r0 ∉ aevens state" "r0 ∉ aodds state" "r0 ∈ Vs G" using r_unclassified by auto
  show "forest_invar ℳ (forest state)" using assms(1) by (auto elim!: invar_basicE)
qed

lemma succ_path_length:
  assumes "invar_basic state"
    "invar_best_even_neighbour_heap state"
    "invar_best_even_neighbour_map state"
    and ext: "heap_extract_min (heap state) = (queue0, Some r0)"
  defines "lx ≡ the (ben_lookup (best_even_neighbour state) r0)"
  shows "length (r0 # get_path (forest state) lx) ≤ card (L ∪ R)"
proof-
  note facts = extract_facts[OF assms(1-3) ext, folded lx_def]
  define p where "p = get_path (forest state) lx"
  have p_props: "distinct p" "walk_betw (ℱ state) lx p (last p) ∨ p = [lx]"
    using get_path[OF facts(8) facts(2) refl] by (auto simp: p_def)
  have p_sub: "set p ⊆ aevens state ∪ aodds state"
  proof-
    have "set p ⊆ Vs (ℱ state) ∪ {lx}"
      using p_props(2) by (auto dest: walk_in_Vs)
    moreover have "Vs (ℱ state) ⊆ aevens state ∪ aodds state"
      using evens_and_odds(3)[OF facts(8)] by auto
    ultimately show ?thesis using facts(2) by auto
  qed
  moreover have "aevens state ∪ aodds state ⊆ L ∪ R"
    using assms(1) by (auto elim!: invar_basicE)
  moreover have "r0 ∈ R"
    using bipartite_edgeD(3)[of r0 lx G L R] facts(3,4) G(1) by (simp add: insert_commute)
  ultimately have sub: "set (r0 # p) ⊆ L ∪ R" by auto
  have dist: "distinct (r0 # p)"
    using p_props(1) facts(5,6) p_sub by auto
  show ?thesis
    using card_mono[OF _ sub] finite_L finite_R distinct_card[OF dist]
    by (simp add: p_def)
qed

end

end