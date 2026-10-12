theory Primal_Dual_Path_Search_Imperative
  imports
    Hungarian_Method.Primal_Dual_Path_Search
    Data_Structures.Fixed_Univ_Map_Specs_Imp
    Data_Structures.Fixed_Univ_Key_Value_Queue_Specs_Imp
    Directed_Set_Graphs.Weighted_Neighbourhoods_Imperative_Spec
    Basic_Matching.Alternating_Forest_Imperative_Spec
    Data_Structures.Real_Embedding

begin


section \<open>Imperative Refinement of the Path Search\<close>

text \<open>The path search of @{locale primal_dual_path_search} is refined to Imperative HOL. The
      refinement follows the discipline of the Dijkstra refinement: a code locale fixes the
      imperative operations (only their types) and defines the imperative programs; a proof locale
      combines the functional locale with the imperative ADT locales, which supply the Hoare
      triples.

      \<^emph>\<open>The programs do not allocate.\<close> All data structures of the search -- the best even
      neighbours, the missed values, the forest, the queue and the collection of neighbourhoods --
      are passed in as handles, emptied in place at the beginning of each search, and reused. The
      maps are total maps on a fixed universe that are updated in place; a vertex without best
      even neighbour or without buddy is mapped to the sentinel @{term nil}. The path is written
      into an array @{term Ra} that belongs to the caller.

      Values (weights, potentials, keys) are executable values of type @{typ 'n}, read into the
      reals by an embedding. Weights are only read at the cursor of the collection of
      neighbourhoods. All other quantities that the functional algorithm computes from weights
      are keys that are already in the queue: the key of a right vertex is the reduced weight of
      the edge to its best even neighbour plus the missed value there, and the extracted key is the
      new accumulated value. The programs read these keys from the queue instead of recomputing
      them.\<close>

subsection \<open>The Programs\<close>

locale primal_dual_path_search_imp_code =
  fixes nil :: "'v::heap"
    and ben_get_imp :: "'bi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and ben_upd_imp :: "'bi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and ben_clear_imp :: "'bi \<Rightarrow> unit Heap"
    and missed_get_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'n::linordered_idom Heap"
    and missed_upd_imp :: "'mi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and missed_clear_imp :: "'mi \<Rightarrow> unit Heap"
    and pot_get_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and pot_upd_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and buddy_imp :: "'bdi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and left_it_init :: "'li \<Rightarrow> 'lit Heap"
    and left_it_has_next :: "'lit \<Rightarrow> bool Heap"
    and left_it_next :: "'lit \<Rightarrow> ('v \<times> 'lit) Heap"
    and forest_clear_imp :: "'fi \<Rightarrow> 'fi Heap"
    and forest_add_root_imp :: "'v \<Rightarrow> 'fi \<Rightarrow> 'fi Heap"
    and forest_extend_imp :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'fi \<Rightarrow> 'fi Heap"
    and forest_it_init :: "forest_part \<Rightarrow> 'fi \<Rightarrow> 'fit Heap"
    and forest_it_has_next :: "'fit \<Rightarrow> bool Heap"
    and forest_it_next :: "'fit \<Rightarrow> ('v \<times> 'fit) Heap"
    and get_path_imp :: "'fi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> nat Heap"
    and queue_clear_imp :: "'qi \<Rightarrow> unit Heap"
    and queue_extract_min_imp :: "'qi \<Rightarrow> ('v \<times> 'n) option Heap"
    and queue_key_of_imp :: "'qi \<Rightarrow> 'v \<Rightarrow> 'n option Heap"
    and queue_decrease_key_imp :: "'qi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and queue_insert_imp :: "'qi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and has_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and current_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and current_cost_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and move_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_all_imp :: "'ci \<Rightarrow> unit Heap"
begin

text \<open>Relaxing the edge from @{term l} to @{term r} of weight @{term c}, where @{term pl} and
      @{term ml} are the potential and the missed value of @{term l}. The key of the current best
      even neighbour of @{term r} is read from the queue. If @{term r} has a best even neighbour
      but is not in the queue any more, no improvement is possible.\<close>

definition "relax_new_imp Qi Bi l r key = do {
   ben_upd_imp Bi r l;
   queue_insert_imp Qi r key }"

definition "relax_old_imp Qi Bi l r key = do {
   ko \<leftarrow> queue_key_of_imp Qi r;
   (case ko of
      None \<Rightarrow> return ()
    | Some k' \<Rightarrow>
        (if key < k'
         then do { ben_upd_imp Bi r l; queue_decrease_key_imp Qi r key }
         else return ())) }"

definition "relax_imp Pti Qi Bi l pl ml r c = do {
   pr \<leftarrow> pot_get_imp Pti r;
   b \<leftarrow> ben_get_imp Bi r;
   (if b = nil then relax_new_imp Qi Bi l r (c - pl - pr + ml)
    else relax_old_imp Qi Bi l r (c - pl - pr + ml)) }"

partial_function (heap) scan_imp ::
  "'ci \<Rightarrow> 'pi \<Rightarrow> 'qi \<Rightarrow> 'bi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> unit Heap" where
  "scan_imp Ci Pti Qi Bi l pl ml = do {
     b \<leftarrow> has_imp Ci l;
     (if b then do { r \<leftarrow> current_imp Ci l;
                     c \<leftarrow> current_cost_imp Ci l;
                     move_imp Ci l;
                     relax_imp Pti Qi Bi l pl ml r c;
                     scan_imp Ci Pti Qi Bi l pl ml }
      else return ()) }"

definition "update_ben_imp Ci Pti Mi Qi Bi l = do {
   reset_imp Ci l;
   pl \<leftarrow> pot_get_imp Pti l;
   ml \<leftarrow> missed_get_imp Mi l;
   scan_imp Ci Pti Qi Bi l pl ml }"

text \<open>Emptying the data structures of the search in place.\<close>

definition "clear_imp Ci Qi Fi Bi Mi = do {
   ben_clear_imp Bi;
   missed_clear_imp Mi;
   Fi' \<leftarrow> forest_clear_imp Fi;
   queue_clear_imp Qi;
   reset_all_imp Ci;
   return Fi' }"

text \<open>The initial state: every unmatched left vertex becomes a root, and its neighbourhood is
      scanned. The filter for the unmatched left vertices is fused with the iteration over the left
      vertices. The flag records whether there is a root at all.\<close>

definition "init_step Ci Pti Mi Qi Bi Bdi l st = (case st of (Fi, found) \<Rightarrow> do {
   b \<leftarrow> buddy_imp Bdi l;
   (if b = nil
    then do { Fi' \<leftarrow> forest_add_root_imp l Fi;
              update_ben_imp Ci Pti Mi Qi Bi l;
              return (Fi', True) }
    else return (Fi, found)) })"

definition "init_imp Ci Pti Mi Qi Bi Bdi Li Fi = do {
   it \<leftarrow> left_it_init Li;
   iter_fold left_it_has_next left_it_next (init_step Ci Pti Mi Qi Bi Bdi) it (Fi, False) }"

text \<open>The main loop of the search. The key of the extracted vertex is the new accumulated value.
      On success, the path is written into @{term Ra}, starting at position 0, and its length is
      returned.\<close>

partial_function (heap) loop_imp ::
  "'ci \<Rightarrow> 'qi \<Rightarrow> 'pi \<Rightarrow> 'bdi \<Rightarrow> 'v array \<Rightarrow> 'bi \<Rightarrow> 'mi \<Rightarrow> 'fi \<Rightarrow>
   (imp_search_result \<times> 'n \<times> 'fi) Heap" where
  "loop_imp Ci Qi Pti Bdi Ra Bi Mi Fi = do {
     x \<leftarrow> queue_extract_min_imp Qi;
     (case x of
        None \<Rightarrow> return (Imp_Unbounded, 0, Fi)
      | Some rk \<Rightarrow> do {
          l \<leftarrow> ben_get_imp Bi (fst rk);
          l' \<leftarrow> buddy_imp Bdi (fst rk);
          (if l' = nil
           then do {
             _ \<leftarrow> Array.upd 0 (fst rk) Ra;
             k \<leftarrow> get_path_imp Fi Ra 1 l;
             return (Imp_Path k, snd rk, Fi) }
           else do {
             missed_upd_imp Mi (fst rk) (snd rk);
             missed_upd_imp Mi l' (snd rk);
             Fi' \<leftarrow> forest_extend_imp l (fst rk) l' Fi;
             update_ben_imp Ci Pti Mi Qi Bi l';
             loop_imp Ci Qi Pti Bdi Ra Bi Mi Fi' }) }) }"

text \<open>The new potential. The even vertices are updated first, then the odd ones. Each vertex is
      updated once, and it still has its old potential when it is processed.\<close>

definition "pot_step_even Pti Mi av v (u::unit) = do {
   pv \<leftarrow> pot_get_imp Pti v; mv \<leftarrow> missed_get_imp Mi v; pot_upd_imp Pti v (pv + av - mv) }"

definition "pot_step_odd Pti Mi av v (u::unit) = do {
   pv \<leftarrow> pot_get_imp Pti v; mv \<leftarrow> missed_get_imp Mi v; pot_upd_imp Pti v (pv - av + mv) }"

definition "new_pot_imp Fi Mi av Pti = do {
   it \<leftarrow> forest_it_init Evens Fi;
   iter_fold forest_it_has_next forest_it_next (pot_step_even Pti Mi av) it ();
   it' \<leftarrow> forest_it_init Odds Fi;
   iter_fold forest_it_has_next forest_it_next (pot_step_odd Pti Mi av) it' () }"

text \<open>The path search. It updates the potential in place and returns the result and the handle
      of the forest.\<close>

definition "search_imp Ci Qi Pti Bdi Li Ra Fi Bi Mi = do {
   Fi1 \<leftarrow> clear_imp Ci Qi Fi Bi Mi;
   (Fi2, found) \<leftarrow> init_imp Ci Pti Mi Qi Bi Bdi Li Fi1;
   (if \<not> found then return (Imp_Matched, Fi2)
    else do {
      (res, av, Fi3) \<leftarrow> loop_imp Ci Qi Pti Bdi Ra Bi Mi Fi2;
      (case res of
         Imp_Path k \<Rightarrow> do { new_pot_imp Fi3 Mi av Pti; return (res, Fi3) }
       | _ \<Rightarrow> return (res, Fi3)) }) }"

end

subsection \<open>The Proof Locale\<close>

text \<open>The imperative data structures of the search are related to the functional ones:

        \<^item> the best even neighbours by an imperative fixed-universe map with the functional
          values,
        \<^item> the missed values and the potential by imperative fixed-universe maps whose values are
          read into the reals by @{term h},
        \<^item> the queue, the collection of neighbourhoods and the forest by their imperative
          specifications, where the weights of the collection are @{term edge_costs_code},
        \<^item> the left vertices by an imperative fixed-universe set, iterated in the order
          @{term lst}, and
        \<^item> the buddy function by an imperative lookup.

      Clearing the maps is not part of their specification and fixed here. The iteration
      functions of the functional algorithm iterate in the same order.\<close>

locale primal_dual_path_search_imp =
  primal_dual_path_search where G = G +
  real_embedding h +
  queue: key_value_queue_imp
    where U = "Vs G" and queue_empty = heap_empty and queue_extract_min = heap_extract_min
      and queue_decrease_key = heap_decrease_key and queue_insert = heap_insert
      and queue_invar = heap_invar and queue_abstract = heap_abstract and queue_key = h
      and queue_assn = queue_assn and queue_empty_imp = queue_empty_imp
      and queue_clear_imp = queue_clear_imp and queue_extract_min_imp = queue_extract_min_imp
      and queue_key_of_imp = queue_key_of_imp and queue_decrease_key_imp = queue_decrease_key_imp
      and queue_insert_imp = queue_insert_imp +
  nb: weighted_neighbourhoods_imp_spec
    where idx_invar = rnb_invar and idx_abstract = rnb_abstract and idx_current = rnb_current
      and idx_has = rnb_has and idx_iterated = rnb_iterated and idx_remaining = rnb_remaining
      and idx_move = rnb_move and idx_reset = rnb_reset and K = "vset_to_set left"
      and cost = edge_costs_code and wval = h and nb_init = rnb_init and nb_assn = nb_assn
      and has_imp = has_imp and current_imp = current_imp and current_cost_imp = current_cost_imp
      and move_imp = move_imp and reset_imp = reset_imp and reset_all_imp = reset_all_imp +
  forest: alternating_forest_imp_spec
    where vset_invar = vset_invar and vset_to_set = vset_to_set and odds = odds
      and abstract_forest = abstract_forest and forest_invar = forest_invar and roots = roots
      and vset_empty = vset_empty
      and extend_forest_even_unclassified = extend_forest_even_unclassified
      and empty_forest = empty_forest and forest_univ = K and get_path = get_path
      and evens = evens and lst = lst
      and forest_assn = forest_assn and forest_empty_imp = forest_empty_imp
      and forest_clear_imp = forest_clear_imp and forest_add_root_imp = forest_add_root_imp
      and forest_extend_imp = forest_extend_imp and evens_memb_imp = evens_memb_imp
      and odds_memb_imp = odds_memb_imp and forest_is_it = forest_is_it
      and forest_it_init = forest_it_init and forest_it_has_next = forest_it_has_next
      and forest_it_next = forest_it_next and get_path_imp = get_path_imp +
  ben: fixed_univ_map_imp
    where K = K and fixed_univ_map_invar = ben_invar and fixed_univ_map_upd = ben_upd
      and fixed_univ_map_lookup = ben_get and fixed_univ_map_val = id
      and fixed_univ_map_assn = ben_assn and fixed_univ_map_upd_imp = ben_upd_imp
      and fixed_univ_map_lookup_imp = ben_get_imp +
  ben: fixed_univ_map_clear_imp K ben_invar ben_get id ben_assn ben_get_imp ben_empty
    ben_clear_imp +
  missed: fixed_univ_map_imp
    where K = K and fixed_univ_map_invar = missed_invar and fixed_univ_map_upd = missed_upd
      and fixed_univ_map_lookup = missed_get and fixed_univ_map_val = h
      and fixed_univ_map_assn = missed_assn and fixed_univ_map_upd_imp = missed_upd_imp
      and fixed_univ_map_lookup_imp = missed_get_imp +
  missed: fixed_univ_map_clear_imp K missed_invar missed_get h missed_assn missed_get_imp
    missed_empty missed_clear_imp +
  pot: fixed_univ_map_imp
    where K = K and fixed_univ_map_invar = potential_invar
      and fixed_univ_map_upd = potential_upd and fixed_univ_map_lookup = potential_get
      and fixed_univ_map_val = h and fixed_univ_map_assn = pot_assn
      and fixed_univ_map_upd_imp = pot_upd_imp and fixed_univ_map_lookup_imp = pot_get_imp +
  left: fixed_univ_set_iterate_imp
    where U = K and set_invar = vset_invar and set_abstract = vset_to_set
      and set_empty = vset_empty and set_insert = vset_insert and set_delete = vset_delete
      and set_isin = vset_isin and set_assn = vset_assn and set_empty_imp = vset_empty_imp
      and set_insert_imp = vset_insert_imp and set_delete_imp = vset_delete_imp
      and set_isin_imp = vset_isin_imp and lst = lst and is_it = left_is_it
      and it_init = left_it_init and it_has_next = left_it_has_next and it_next = left_it_next
  for G :: "'v::heap set set" and h :: "'n::{linordered_idom, heap} \<Rightarrow> real"
    and queue_assn queue_empty_imp queue_clear_imp queue_extract_min_imp queue_key_of_imp
        queue_decrease_key_imp queue_insert_imp
    and nb_assn has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp
    and lst forest_assn forest_empty_imp forest_clear_imp forest_add_root_imp
        forest_extend_imp evens_memb_imp odds_memb_imp forest_is_it forest_it_init
        forest_it_has_next forest_it_next get_path_imp
    and ben_assn :: "_ \<Rightarrow> 'bi \<Rightarrow> assn" and ben_upd_imp ben_get_imp
    and missed_assn :: "_ \<Rightarrow> 'mi \<Rightarrow> assn" and missed_upd_imp missed_get_imp
    and pot_assn pot_upd_imp pot_get_imp
    and vset_assn vset_empty_imp vset_insert_imp vset_delete_imp vset_isin_imp
    and left_is_it left_it_init left_it_has_next left_it_next
    and ben_clear_imp :: "'bi \<Rightarrow> unit Heap" and missed_clear_imp :: "'mi \<Rightarrow> unit Heap" +
  fixes buddy_assn :: "'bdi \<Rightarrow> assn"
    and buddy_imp :: "'bdi \<Rightarrow> 'v \<Rightarrow> 'v Heap"

  assumes buddy_rule[sep_heap_rules]:
      "v \<in> K \<Longrightarrow> <buddy_assn Bdi> buddy_imp Bdi v <\<lambda>r. buddy_assn Bdi * \<up>(r = buddy_get v)>"

    and vset_iterate_ben_lst:
      "\<And>V f init. vset_invar V \<Longrightarrow> vset_iterate_ben f init V = foldl f init (lst (vset_to_set V))"
    and vset_iterate_pot_lst:
      "\<And>V f init. vset_invar V \<Longrightarrow> vset_iterate_pot f init V = foldl f init (lst (vset_to_set V))"
begin

end

sublocale primal_dual_path_search_imp \<subseteq> code: primal_dual_path_search_imp_code
  nil ben_get_imp ben_upd_imp ben_clear_imp missed_get_imp missed_upd_imp missed_clear_imp
  pot_get_imp pot_upd_imp buddy_imp left_it_init left_it_has_next left_it_next forest_clear_imp
  forest_add_root_imp forest_extend_imp forest_it_init forest_it_has_next forest_it_next
  get_path_imp queue_clear_imp queue_extract_min_imp queue_key_of_imp queue_decrease_key_imp
  queue_insert_imp has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp .

context primal_dual_path_search_imp
begin

subsection \<open>Reading and Writing the Best Even Neighbours\<close>

lemma ben_get_rule[sep_heap_rules]:
  "\<lbrakk>ben_invar B; r \<in> K\<rbrakk> \<Longrightarrow>
   <ben_assn B Bi> ben_get_imp Bi r <\<lambda>x. ben_assn B Bi * \<up>(x = ben_get B r)>"
  using ben.fixed_univ_map_lookup_rule[of B r Bi] by simp

lemma ben_upd_rule[sep_heap_rules]:
  "\<lbrakk>ben_invar B; r \<in> K\<rbrakk> \<Longrightarrow>
   <ben_assn B Bi> ben_upd_imp Bi r l <\<lambda>_. ben_assn (ben_upd B r l) Bi>"
  using ben.fixed_univ_map_upd_rule[of B r Bi l] by simp

declare ben.fixed_univ_map_lookup_rule[sep_heap_rules del]
        ben.fixed_univ_map_upd_rule[sep_heap_rules del]

lemma ben_lookup_None: "ben_lookup B r = None \<longleftrightarrow> ben_get B r = nil"
  by (simp add: ben_lookup_def)

lemma ben_lookup_Some: "ben_lookup B r = Some l \<Longrightarrow> ben_get B r = l \<and> l \<noteq> nil"
  by (simp add: ben_lookup_def split: if_splits)

subsection \<open>Relaxing an Edge\<close>

text \<open>The queue key of a right vertex with a best even neighbour is the key that the functional
      algorithm recomputes. If the vertex is not in the queue any more, the functional algorithm
      does not change anything.\<close>

lemma relax_queue_key:
  assumes "scan_inv off l ben queue" "r \<in> rneighbs l" "ben_lookup ben r = Some l'"
  shows "(r, k) \<in> heap_abstract queue \<Longrightarrow> k = w\<^sub>\<pi>_code l' r + off l'"
        "\<nexists>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> \<not> w\<^sub>\<pi>_code l r + off l < w\<^sub>\<pi>_code l' r + off l'"
proof-
  note I = scan_invD[OF assms(1)]
  have code': "w\<^sub>\<pi>_code l' r = w\<^sub>\<pi> l' r"
    using w\<^sub>\<pi>_code_is[of l' r] I(6,7)[OF assms(3)] by simp
  show "(r, k) \<in> heap_abstract queue \<Longrightarrow> k = w\<^sub>\<pi>_code l' r + off l'"
    using I(4)[of r k] assms(3) code' by auto
  show "\<nexists>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> \<not> w\<^sub>\<pi>_code l r + off l < w\<^sub>\<pi>_code l' r + off l'"
    using relax_neighbour_Some(2)[OF assms] by blast
qed

lemma relax_new_rule:
  "\<lbrakk>heap_invar queue; ben_invar ben; r \<in> Vs G; \<nexists>k. (r, k) \<in> heap_abstract queue\<rbrakk> \<Longrightarrow>
   <queue_assn queue Qi * ben_assn ben Bi> code.relax_new_imp Qi Bi l r key
   <\<lambda>_. queue_assn (heap_insert queue r (h key)) Qi * ben_assn (ben_upd ben r l) Bi>"
  unfolding code.relax_new_imp_def
  by (sep_auto heap: queue.queue_insert_rule simp: in_K(3))

lemma relax_old_rule:
  assumes "heap_invar queue" "ben_invar ben" "r \<in> Vs G"
      and in_heap: "\<And>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> k = K'"
      and not_in_heap: "\<nexists>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> \<not> h key < K'"
  shows "<queue_assn queue Qi * ben_assn ben Bi> code.relax_old_imp Qi Bi l r key
         <\<lambda>_. if h key < K'
              then queue_assn (heap_decrease_key queue r (h key)) Qi *
                   ben_assn (ben_upd ben r l) Bi
              else queue_assn queue Qi * ben_assn ben Bi>"
proof-
  have some: "(r, h k') \<in> heap_abstract queue \<Longrightarrow> h k' = K'" for k'
    using in_heap by blast
  have rK: "r \<in> K" using in_K(3)[OF assms(3)] .
  show ?thesis
    unfolding code.relax_old_imp_def
    apply(sep_auto heap: queue.queue_key_of_rule simp: assms(1,3) split: option.splits)
    subgoal using not_in_heap by (sep_auto)
    subgoal for ha haa ra k'
      using some[of k']
      by (cases "key < k'")
         (sep_auto heap: queue.queue_decrease_key_rule[of queue r "h k'"] simp: assms(1,2,3) rK)+
    done
qed

lemma relax_imp_rule:
  assumes inv: "scan_inv off l ben queue" and rn: "r \<in> rneighbs l"
      and hc: "h c = edge_costs_code l r" and hpl: "h pl = \<pi> l" and hml: "h ml = off l"
  shows "<pot_assn initial_pot Pti * queue_assn queue Qi * ben_assn ben Bi>
         code.relax_imp Pti Qi Bi l pl ml r c
         <\<lambda>_. pot_assn initial_pot Pti *
              queue_assn (snd (relax_neighbour off l (ben, queue) r)) Qi *
              ben_assn (fst (relax_neighbour off l (ben, queue) r)) Bi>"
proof-
  note I = scan_invD[OF inv]
  have rG: "r \<in> Vs G" using rneighbs_in_G[OF I(3) rn] by (auto intro: edges_are_Vs_2)
  have rK: "r \<in> K" using in_K(3)[OF rG] .
  have key: "h pr = \<pi> r \<Longrightarrow> h (c - pl - pr + ml) = w\<^sub>\<pi>_code l r + off l" for pr
    using hc hpl hml by (simp add: w\<^sub>\<pi>_code_def h_add)
  show ?thesis
  proof(cases "ben_lookup ben r")
    case None
    note legal = relax_neighbour_None[OF inv rn None]
    have nil: "ben_get ben r = nil" using None by (simp add: ben_lookup_None)
    show ?thesis
      unfolding code.relax_imp_def
      by (sep_auto heap: relax_new_rule
                   simp: None nil relax_neighbour_view key I(1,2) rG rK legal(2) potential)
  next
    case (Some l')
    have get: "ben_get ben r = l'" "l' \<noteq> nil" "nil \<noteq> l'" using ben_lookup_Some[OF Some] by auto
    note qk = relax_queue_key[OF inv rn Some]
    have old: "h pr = \<pi> r \<Longrightarrow>
      <queue_assn queue Qi * ben_assn ben Bi> code.relax_old_imp Qi Bi l r (c - pl - pr + ml)
      <\<lambda>_. queue_assn (snd (relax_neighbour off l (ben, queue) r)) Qi *
           ben_assn (fst (relax_neighbour off l (ben, queue) r)) Bi>" for pr
      apply(rule ht_cons_post[OF relax_old_rule[OF I(2,1) rG, of "w\<^sub>\<pi>_code l' r + off l'"]])
      using qk
      by (auto simp: key relax_neighbour_view Some split: if_splits intro: ent_refl_true)
    show ?thesis
      unfolding code.relax_imp_def
      by (sep_auto heap: old simp: get I(1) rK potential)
  qed
qed

subsection \<open>Scanning a Neighbourhood\<close>

lemma scan_imp_rule:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
      and "scan_inv off l ben queue" "h pl = \<pi> l" "h ml = off l"
  shows "<nb_assn C Ci * pot_assn initial_pot Pti * queue_assn queue Qi * ben_assn ben Bi>
         code.scan_imp Ci Pti Qi Bi l pl ml
         <\<lambda>_. nb_assn (fst (scan_neighbours off l C (ben, queue))) Ci *
              pot_assn initial_pot Pti *
              queue_assn (snd (snd (scan_neighbours off l C (ben, queue)))) Qi *
              ben_assn (fst (snd (scan_neighbours off l C (ben, queue)))) Bi>"
  using assms
proof(induction "card (rnb_remaining C l)" arbitrary: C ben queue rule: less_induct)
  case less
  have sub: "rnb_remaining C l \<subseteq> rneighbs l"
    using rnb.idx_partition_union[OF less.prems(1,2)] less.prems(3) by auto
  have fin: "finite (rnb_remaining C l)"
    using finite_rneighbs[OF less.prems(2)] sub by (rule finite_subset[rotated])
  show ?case
  proof(cases "rnb_has C l")
    case True
    have ne: "rnb_remaining C l \<noteq> {}" using rnb.idx_has[OF less.prems(1,2)] True by simp
    have x_in: "rnb_current C l \<in> rnb_remaining C l"
      using rnb.idx_current[OF less.prems(1,2) ne] .
    have x_rn: "rnb_current C l \<in> rneighbs l" using x_in sub by auto
    have C': "rnb_invar (rnb_move C l)"
             "rnb_abstract (rnb_move C l) = rnb_abstract rnb_init"
             "rnb_remaining (rnb_move C l) l = rnb_remaining C l - {rnb_current C l}"
      using rnb.idx_move_invar[OF less.prems(1,2)] rnb.idx_move_remaining[OF less.prems(1,2) ne]
            rnb.idx_move_abstract[OF less.prems(1,2) ne] less.prems(3)
      by (auto simp: fun_eq_iff)
    have card_less: "card (rnb_remaining (rnb_move C l) l) < card (rnb_remaining C l)"
      using card_Diff1_less[OF fin x_in] by (simp add: C'(3))
    have scan_eq: "scan_neighbours off l C (ben, queue) =
                   scan_neighbours off l (rnb_move C l)
                      (relax_neighbour off l (ben, queue) (rnb_current C l))"
      by (simp add: scan_neighbours.simps[of off l C] True)
    have inv': "scan_inv off l (fst (relax_neighbour off l (ben, queue) (rnb_current C l)))
                               (snd (relax_neighbour off l (ben, queue) (rnb_current C l)))"
      using relax_neighbour_pres(1)[OF less.prems(4) x_rn] .
    note IH = less.hyps[OF card_less C'(1) less.prems(2) C'(2) inv' less.prems(5,6), simplified]
    note relax = relax_imp_rule[OF less.prems(4) x_rn _ less.prems(5,6)]
    show ?thesis
      apply(subst code.scan_imp.simps)
      apply(sep_auto heap: nb.idx_has_rule nb.idx_current_rule nb.current_cost_rule nb.idx_move_rule
                     simp: less.prems(1,2) True ne)
      apply(sep_auto heap: relax)
      by (sep_auto heap: IH simp: scan_eq True)
  next
    case False
    have scan_eq: "scan_neighbours off l C (ben, queue) = (C, ben, queue)"
      by (simp add: scan_neighbours.simps[of off l C] False)
    show ?thesis
      apply(subst code.scan_imp.simps)
      by (sep_auto heap: nb.idx_has_rule simp: less.prems(1,2) False scan_eq)
  qed
qed


lemma update_ben_imp_rule:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
      and "missed_invar M" "scan_inv (missed_get M) l ben queue"
  shows "<nb_assn C Ci * pot_assn initial_pot Pti * missed_assn M Mi *
          queue_assn queue Qi * ben_assn ben Bi>
         code.update_ben_imp Ci Pti Mi Qi Bi l
         <\<lambda>_. nb_assn (fst (update_best_even_neighbour (missed_get M) C ben queue l)) Ci *
              pot_assn initial_pot Pti * missed_assn M Mi *
              queue_assn (snd (snd (update_best_even_neighbour (missed_get M) C ben queue l))) Qi *
              ben_assn (fst (snd (update_best_even_neighbour (missed_get M) C ben queue l))) Bi>"
proof-
  have C0: "rnb_invar (rnb_reset C l)" "rnb_abstract (rnb_reset C l) = rnb_abstract rnb_init"
    using rnb.idx_reset_invar[OF assms(1,2)] rnb.idx_reset_abstract[OF assms(1,2)] assms(3)
    by (auto simp: fun_eq_iff)
  have lK: "l \<in> K" using in_K(1)[OF assms(2)] .
  note scan = scan_imp_rule[OF C0(1) assms(2) C0(2) assms(5)]
  show ?thesis
    unfolding code.update_ben_imp_def update_best_even_neighbour_def
    by (sep_auto heap: nb.idx_reset_rule scan simp: assms(1,2,4) lK potential)
qed

text \<open>Functional preservation facts for a whole scan.\<close>

lemma foldl_relax_pres:
  "\<lbrakk>scan_inv off l ben queue; set rs \<subseteq> rneighbs l\<rbrakk> \<Longrightarrow>
   scan_inv off l (fst (foldl (relax_neighbour off l) (ben, queue) rs))
                  (snd (foldl (relax_neighbour off l) (ben, queue) rs)) \<and>
   (all_in_heap ben queue \<longrightarrow>
    all_in_heap (fst (foldl (relax_neighbour off l) (ben, queue) rs))
                (snd (foldl (relax_neighbour off l) (ben, queue) rs)))"
proof(induction rs arbitrary: ben queue)
  case (Cons r rs)
  have r: "r \<in> rneighbs l" using Cons.prems(2) by simp
  obtain ben' queue' where bq': "relax_neighbour off l (ben, queue) r = (ben', queue')"
    by (cases "relax_neighbour off l (ben, queue) r") auto
  have inv': "scan_inv off l ben' queue'" "all_in_heap ben queue \<Longrightarrow> all_in_heap ben' queue'"
    using relax_neighbour_pres[OF Cons.prems(1) r] by (auto simp: bq')
  show ?case
    using Cons.IH[OF inv'(1)] Cons.prems(2) inv'(2) by (simp add: bq')
qed simp

lemma ubn_pres:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
      and "scan_inv off l ben queue"
  shows "rnb_invar (fst (update_best_even_neighbour off C ben queue l))"
        "rnb_abstract (fst (update_best_even_neighbour off C ben queue l)) = rnb_abstract rnb_init"
        "scan_inv off l (fst (snd (update_best_even_neighbour off C ben queue l)))
                        (snd (snd (update_best_even_neighbour off C ben queue l)))"
        "all_in_heap ben queue \<Longrightarrow>
         all_in_heap (fst (snd (update_best_even_neighbour off C ben queue l)))
                     (snd (snd (update_best_even_neighbour off C ben queue l)))"
proof-
  obtain C' ben' queue' where eq: "update_best_even_neighbour off C ben queue l = (C', ben', queue')"
    by (cases "update_best_even_neighbour off C ben queue l") auto
  note fl = update_best_even_neighbour_is_foldl[OF assms(1-3) eq[symmetric]]
  obtain rs where rs: "set rs = rneighbs l" "(ben', queue') = foldl (relax_neighbour off l) (ben, queue) rs"
    using fl(1) by blast
  note pres = foldl_relax_pres[OF assms(4), of rs]
  show "rnb_invar (fst (update_best_even_neighbour off C ben queue l))"
       "rnb_abstract (fst (update_best_even_neighbour off C ben queue l)) = rnb_abstract rnb_init"
    using fl(2,3) by (auto simp: eq)
  show "scan_inv off l (fst (snd (update_best_even_neighbour off C ben queue l)))
                        (snd (snd (update_best_even_neighbour off C ben queue l)))"
       "all_in_heap ben queue \<Longrightarrow>
         all_in_heap (fst (snd (update_best_even_neighbour off C ben queue l)))
                     (snd (snd (update_best_even_neighbour off C ben queue l)))"
  proof-
    have "set rs \<subseteq> rneighbs l" using rs(1) by simp
    hence "scan_inv off l ben' queue' \<and> (all_in_heap ben queue \<longrightarrow> all_in_heap ben' queue')"
      using pres unfolding rs(2)[symmetric] by simp
    thus "scan_inv off l (fst (snd (update_best_even_neighbour off C ben queue l)))
                        (snd (snd (update_best_even_neighbour off C ben queue l)))"
       "all_in_heap ben queue \<Longrightarrow>
         all_in_heap (fst (snd (update_best_even_neighbour off C ben queue l)))
                     (snd (snd (update_best_even_neighbour off C ben queue l)))"
      by (simp_all add: eq)
  qed
qed

subsection \<open>Clearing\<close>

text \<open>The data structures of the search, with arbitrary contents. Only the collection of
      neighbourhoods has to be one of the collection of the graph.\<close>

definition "scratch_assn Ci Qi Fi Bi Mi =
  (\<exists>\<^sub>AC H F B M. nb_assn C Ci * queue_assn H Qi * forest_assn F Fi * ben_assn B Bi *
                 missed_assn M Mi *
                 \<up>(rnb_invar C \<and> (\<forall>i\<in>L. rnb_abstract C i = rnb_abstract rnb_init i) \<and>
                   ben_invar B \<and> missed_invar M))"

lemma clear_imp_rule:
  "<scratch_assn Ci Qi Fi Bi Mi> code.clear_imp Ci Qi Fi Bi Mi
   <\<lambda>Fi'. nb_assn rnb_init Ci * queue_assn heap_empty Qi *
          forest_assn (empty_forest vset_empty) Fi' *
          ben_assn ben_empty Bi * missed_assn missed_empty Mi>"
  unfolding code.clear_imp_def scratch_assn_def
  by (sep_auto heap: forest.forest_clear_rule[OF vset(1,2)]
                     queue.queue_clear_rule nb.reset_all_rule)

subsection \<open>The Initial State: Functional Part\<close>

text \<open>The iteration over the left vertices with the fused test for the unmatched ones. The state
      of the fold consists of the roots so far, the collection, the best even neighbours and the
      queue, and the flag.\<close>

definition "init_g = (\<lambda>(S, cbq, fnd) v.
   if buddy_get v = nil
   then (insert v S,
         update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) v, True)
   else (S, cbq, fnd))"

lemma init_fold:
  "foldl init_g (S, cbq, fnd) xs =
   (S \<union> set (filter (\<lambda>v. buddy_get v = nil) xs),
    foldl (\<lambda>cbq l. update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) l)
          cbq (filter (\<lambda>v. buddy_get v = nil) xs),
    fnd \<or> filter (\<lambda>v. buddy_get v = nil) xs \<noteq> [])"
  by (induction xs arbitrary: S cbq fnd) (auto simp: init_g_def)

definition "init_ok cbq =
  (rnb_invar (fst cbq) \<and> rnb_abstract (fst cbq) = rnb_abstract rnb_init \<and>
   ben_invar (fst (snd cbq)) \<and>
   all_in_heap (fst (snd cbq)) (snd (snd cbq)) \<and>
   (\<forall>l\<in>L. scan_inv (\<lambda>x. 0) l (fst (snd cbq)) (snd (snd cbq))))"

lemma scan_inv_zero_other:
  "\<lbrakk>scan_inv (\<lambda>x. 0) l ben queue; all_in_heap ben queue; l' \<in> L\<rbrakk> \<Longrightarrow>
   scan_inv (\<lambda>x. 0) l' ben queue"
  by (auto simp: scan_inv_def all_in_heap_def)

lemma init_ok_step:
  assumes "init_ok cbq" "l \<in> L"
  shows "init_ok (update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) l)"
proof-
  have c: "rnb_invar (fst cbq)" "rnb_abstract (fst cbq) = rnb_abstract rnb_init"
          "all_in_heap (fst (snd cbq)) (snd (snd cbq))"
          "scan_inv (\<lambda>x. 0) l (fst (snd cbq)) (snd (snd cbq))"
    using assms by (auto simp: init_ok_def)
  note P = ubn_pres[OF c(1) assms(2) c(2) c(4)]
  note aih = P(4)[OF c(3)]
  show ?thesis
    unfolding init_ok_def
    using P(1,2) aih scan_inv_zero_other[OF P(3) aih] scan_invD(1)[OF P(3)] by blast
qed

lemma init_ok_init: "init_ok (rnb_init, ben_empty, heap_empty)"
  using G(4) best_even_neighbour(1,4) heap(1,11)
  by (auto simp: init_ok_def all_in_heap_def scan_inv_def)

definition "init_P v b = (v \<in> L \<and> init_ok (fst (snd b)))"

lemma init_fold_pre:
  "\<lbrakk>set xs \<subseteq> L; init_ok cbq\<rbrakk> \<Longrightarrow> fold_pre init_P init_g (S, cbq, fnd) xs"
proof(induction xs arbitrary: S cbq fnd)
  case (Cons x xs)
  have x: "x \<in> L" "set xs \<subseteq> L" using Cons.prems(1) by auto
  show ?case
  proof(cases "buddy_get x = nil")
    case True
    thus ?thesis
      using Cons.IH[OF x(2) init_ok_step[OF Cons.prems(2) x(1)]] Cons.prems(2) x(1)
      by (simp add: init_P_def init_g_def)
  next
    case False
    have eq: "init_g (S, cbq, fnd) x = (S, cbq, fnd)" by (simp add: init_g_def False)
    show ?thesis
      using Cons.IH[OF x(2) Cons.prems(2)] Cons.prems(2) x(1)
      by (simp add: init_P_def eq)
  qed
qed simp

lemma init_fold_result:
  defines "res \<equiv> foldl init_g ({}, (rnb_init, ben_empty, heap_empty), False) (lst L)"
  shows "fst res = vset_to_set forest_roots"
        "fst (snd res) = init_best_even_neighbour"
        "snd (snd res) \<longleftrightarrow> \<not> vset_is_empty unmatched_lefts"
proof-
  have U: "vset_to_set unmatched_lefts = L \<inter> Collect (\<lambda>v. buddy_get v = nil)"
    using vset_iterations(4)[OF G(2)] by (simp add: unmatched_lefts_def)
  have lstU: "lst (vset_to_set unmatched_lefts) = filter (\<lambda>v. buddy_get v = nil) (lst L)"
    using forest.lst_filter[OF finite_L] U by simp
  have "set (filter (\<lambda>v. buddy_get v = nil) (lst L)) = vset_to_set unmatched_lefts"
    using forest.lst_set[OF finite_L] U by auto
  thus "fst res = vset_to_set forest_roots"
    by (simp add: res_def init_fold forest_roots_def)
  show "fst (snd res) = init_best_even_neighbour"
    by (simp add: res_def init_fold init_best_even_neighbour_def update_best_even_neighbours_def
                  vset_iterate_ben_lst[OF unmatched_lefts(2)] lstU)
  have "filter (\<lambda>v. buddy_get v = nil) (lst L) \<noteq> [] \<longleftrightarrow> vset_to_set unmatched_lefts \<noteq> {}"
    using forest.lst_set[OF finite_L] U by (auto simp: filter_empty_conv)
  thus "snd (snd res) \<longleftrightarrow> \<not> vset_is_empty unmatched_lefts"
    by (simp add: res_def init_fold vset_is_empty[OF unmatched_lefts(2)])
qed

subsection \<open>The Initial State: Imperative Part\<close>

lemma add_root_insert:
  "\<lbrakk>vset_invar Rs; v \<in> K\<rbrakk> \<Longrightarrow>
   <forest_assn (empty_forest Rs) Fi> forest_add_root_imp v Fi
   <forest_assn (empty_forest (vset_insert v Rs))>"
  by (rule forest.forest_add_root_rule) (auto simp: vset(3,4))

definition "init_A Ci Pti Mi Qi Bi Bdi b c = (case b of (S, cbq, fnd) \<Rightarrow> case c of (Fi, fndi) \<Rightarrow>
   (\<exists>\<^sub>ARs. forest_assn (empty_forest Rs) Fi * \<up>(vset_invar Rs \<and> vset_to_set Rs = S)) *
   nb_assn (fst cbq) Ci * queue_assn (snd (snd cbq)) Qi * ben_assn (fst (snd cbq)) Bi *
   pot_assn initial_pot Pti * missed_assn missed_empty Mi * buddy_assn Bdi *
   \<up>(fndi = fnd))"

lemma init_step_rule:
  assumes "init_P v b"
  shows "<init_A Ci Pti Mi Qi Bi Bdi b c> code.init_step Ci Pti Mi Qi Bi Bdi v c
         <init_A Ci Pti Mi Qi Bi Bdi (init_g b v)>"
proof-
  obtain S C ben queue fnd where b: "b = (S, (C, ben, queue), fnd)" by (cases b) auto
  obtain Fi fndi where c: "c = (Fi, fndi)" by (cases c) auto
  have v: "v \<in> L" and ok: "init_ok (C, ben, queue)" using assms by (auto simp: init_P_def b)
  have vK: "v \<in> K" using in_K(1)[OF v] .
  have C: "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "scan_inv (missed_get missed_empty) v ben queue"
    using ok v by (auto simp: init_ok_def missed(2))
  note ubi = update_ben_imp_rule[OF C(1) v C(2) missed(1) C(3), unfolded missed(2)]
  show ?thesis
  proof(cases "buddy_get v = nil")
    case True
    have bud: "<buddy_assn Bdi> buddy_imp Bdi v <\<lambda>r. buddy_assn Bdi * \<up>(r = nil)>"
      using buddy_rule[OF vK] by (simp add: True)
    show ?thesis
      unfolding code.init_step_def init_A_def b c
      supply buddy_rule[sep_heap_rules del]
      by (sep_auto heap: bud add_root_insert ubi simp: True vK init_g_def vset(3,4))
  next
    case False
    have bud: "<buddy_assn Bdi> buddy_imp Bdi v <\<lambda>r. buddy_assn Bdi * \<up>(r \<noteq> nil)>"
      using buddy_rule[OF vK] False by (sep_auto simp: hoare_triple_def)
    have eq: "init_g b v = b" by (simp add: b init_g_def False)
    show ?thesis
      unfolding code.init_step_def eq unfolding init_A_def b c
      supply buddy_rule[sep_heap_rules del]
      by (sep_auto heap: bud)
  qed
qed

lemma forest_roots_cong:
  "\<lbrakk>vset_invar Rs; vset_to_set Rs = vset_to_set forest_roots\<rbrakk> \<Longrightarrow>
   forest_assn (empty_forest Rs) = forest_assn (empty_forest forest_roots)"
  using forest.forest_empty_cong[of Rs forest_roots] unmatched_lefts(2)
  by (simp add: forest_roots_def)

lemma init_imp_rule:
  "<vset_assn left Li * forest_assn (empty_forest vset_empty) Fi * nb_assn rnb_init Ci *
    queue_assn heap_empty Qi * ben_assn ben_empty Bi * pot_assn initial_pot Pti *
    missed_assn missed_empty Mi * buddy_assn Bdi>
   code.init_imp Ci Pti Mi Qi Bi Bdi Li Fi
   <\<lambda>(Fi', fnd). vset_assn left Li * forest_assn (empty_forest forest_roots) Fi' *
       nb_assn (fst init_best_even_neighbour) Ci *
       queue_assn (snd (snd init_best_even_neighbour)) Qi *
       ben_assn (fst (snd init_best_even_neighbour)) Bi * pot_assn initial_pot Pti *
       missed_assn missed_empty Mi * buddy_assn Bdi *
       \<up>(fnd \<longleftrightarrow> \<not> vset_is_empty unmatched_lefts)>"
proof-
  define b0 where "b0 = ({}::'v set, (rnb_init, ben_empty, heap_empty), False)"
  have pre: "fold_pre init_P init_g b0 (lst L)"
    unfolding b0_def
    by (rule init_fold_pre[OF _ init_ok_init]) (simp add: forest.lst_set[OF finite_L])
  note fold = iter_fold_rule_gen[where I = "left_is_it left Li" and Q = "vset_assn left Li"
                 and A = "init_A Ci Pti Mi Qi Bi Bdi",
                 OF left.it_has_next_rule left.it_next_rule left.quit_iteration init_step_rule pre]
  have main: "<vset_assn left Li * init_A Ci Pti Mi Qi Bi Bdi b0 (Fi, False)>
               code.init_imp Ci Pti Mi Qi Bi Bdi Li Fi
               <\<lambda>c'. vset_assn left Li * init_A Ci Pti Mi Qi Bi Bdi (foldl init_g b0 (lst L)) c'>"
    unfolding code.init_imp_def
    by (sep_auto heap: left.it_init_rule fold simp: G(2))
  have res: "foldl init_g b0 (lst L) =
             (vset_to_set forest_roots, init_best_even_neighbour, \<not> vset_is_empty unmatched_lefts)"
    using init_fold_result unfolding b0_def by (simp add: prod_eq_iff)
  show ?thesis
  proof(rule ht_cons[OF _ _ main], goal_cases)
    case 1
    show ?case
      by (sep_auto simp: init_A_def b0_def vset(1,2))
  next
    case (2 c)
    obtain Fi' fnd where c: "c = (Fi', fnd)" by (cases c) auto
    show ?case
      unfolding init_A_def res c prod.case
      apply(simp only: ex_assn_move_out star_aci)
      apply(rule ent_ex_preI)
      subgoal for Rs
        by (cases fnd; cases "vset_invar Rs \<and> vset_to_set Rs = vset_to_set forest_roots")
           (sep_auto simp: forest_roots_cong)+
      done
  qed
qed

subsection \<open>The Loop: Functional Part\<close>

lemma extract_key:
  assumes "search_invars state" "heap_extract_min (heap state) = (queue0, Some r)"
      and "(r, k) \<in> heap_abstract (heap state)"
  shows "k = w\<^sub>\<pi>_code (ben_get (best_even_neighbour state) r) r +
             missed_at state (ben_get (best_even_neighbour state) r)"
proof-
  have I: "invar_basic state" "invar_best_even_neighbour_heap state"
          "invar_best_even_neighbour_map state"
    using assms(1) by (auto simp: search_invars_def)
  note F = extract_facts[OF I assms(2)]
  obtain l where l: "ben_lookup (best_even_neighbour state) r = Some l" "k = w\<^sub>\<pi> l r + missed_at state l"
    using invar_best_even_neighbour_heapD[OF I(2)] assms(3) by blast
  have code: "w\<^sub>\<pi>_code l r = w\<^sub>\<pi> l r"
    using w\<^sub>\<pi>_code_is[of l r] F(3,4) l(1) F(1) by simp
  show ?thesis using l code ben_lookup_Some[OF l(1)] by simp
qed

lemma cont_upd_eq:
  assumes "heap_extract_min (heap state) = (queue0, Some r)" "buddy r = Some l'"
  defines "l \<equiv> ben_get (best_even_neighbour state) r"
  defines "acc' \<equiv> w\<^sub>\<pi>_code l r + missed_at state l"
  defines "missed' \<equiv> missed_upd (missed_upd (missed state) r acc') l' acc'"
  defines "U \<equiv> update_best_even_neighbour (missed_get missed')
                  (neighb_coll state) (best_even_neighbour state) queue0 l'"
  shows "search_path_loop_cont_upd state =
         state \<lparr> forest := extend_forest_even_unclassified (forest state) l r l',
                 best_even_neighbour := fst (snd U), neighb_coll := fst U,
                 heap := snd (snd U), missed := missed', acc := acc' \<rparr>"
  using assms(1,2)
  by (simp add: search_path_loop_cont_upd_def Let_def l_def acc'_def missed'_def U_def
         split: prod.split)

lemma search_invars_basic:
  "search_invars state \<Longrightarrow> invar_basic state"
  by (simp add: search_invars_def)

lemma invar_basic_upd:
  "invar_basic (state\<lparr>augpath := p\<rparr>) = invar_basic state"
  "invar_basic (state\<lparr>acc := a\<rparr>) = invar_basic state"
  by (simp_all add: invar_basic_def)

lemma succ_upd_shape:
  "\<exists>a p. search_path_loop_succ_upd state = state\<lparr>acc := a, augpath := p\<rparr>"
  by (auto simp: search_path_loop_succ_upd_def Let_def split: prod.split)

lemma loop_final_basic:
  assumes "search_invars state"
  shows "invar_basic (search_path_loop state)"
proof-
  have "search_invars state \<longrightarrow> invar_basic (search_path_loop state)"
  proof(induction rule: search_path_loop_induct[OF search_invars_dom[OF assms]])
    case (1 state)
    show ?case
    proof(rule, cases state rule: search_path_loop_cases)
      assume "search_invars state" "search_path_loop_fail_cond state"
      thus "invar_basic (search_path_loop state)"
        by (simp add: search_path_loop_simps(1) search_path_loop_fail_upd_def
                      search_invars_basic invar_basic_upd)
    next
      assume "search_invars state" "search_path_loop_succ_cond state"
      thus "invar_basic (search_path_loop state)"
        using succ_upd_shape[of state]
        by (auto simp: search_path_loop_simps(2) search_invars_basic invar_basic_upd)
    next
      assume a: "search_invars state" "search_path_loop_cont_cond state"
      thus "invar_basic (search_path_loop state)"
        using 1(2)[OF a(2)] search_invars_step[OF a(2,1)]
        by (simp add: search_path_loop_simps(3)[OF 1(1) a(2)])
    qed
  qed
  thus ?thesis using assms by simp
qed

subsection \<open>The Loop: Imperative Part\<close>

definition "loop_assn st Ci Qi Fi Bi Mi =
  nb_assn (neighb_coll st) Ci * queue_assn (heap st) Qi * forest_assn (forest st) Fi *
  ben_assn (best_even_neighbour st) Bi * missed_assn (missed st) Mi"

text \<open>After the loop, the queue is not needed any more; its contents are arbitrary.\<close>

definition "loop_post st Ci Qi Fi Bi Mi =
  nb_assn (neighb_coll st) Ci * (\<exists>\<^sub>AH. queue_assn H Qi) * forest_assn (forest st) Fi *
  ben_assn (best_even_neighbour st) Bi * missed_assn (missed st) Mi"

definition "res_rel res av st xs =
  (case augpath st of
     None \<Rightarrow> res = Imp_Unbounded
   | Some p \<Rightarrow> (\<exists>k. res = Imp_Path k \<and> k \<le> length xs \<and> take k xs = p) \<and> h av = acc st)"

lemma take_path_array:
  "\<lbrakk>0 < length xs; k' = 1 + length p\<rbrakk> \<Longrightarrow>
   take k' (take 1 (xs[0 := r]) @ p @ drop k' (xs[0 := r])) = r # p"
  by (cases xs) auto

lemma length_path_array:
  "\<lbrakk>k' = 1 + length p; k' \<le> length xs\<rbrakk> \<Longrightarrow>
   length (take 1 (xs[0 := r]) @ p @ drop k' (xs[0 := r])) = length xs"
  by (cases xs) auto

lemma loop_imp_rule:
  assumes "search_invars state" "card (L \<union> R) \<le> length xs"
  shows "<loop_assn state Ci Qi Fi Bi Mi * pot_assn initial_pot Pti * buddy_assn Bdi *
          Ra \<mapsto>\<^sub>a xs>
         code.loop_imp Ci Qi Pti Bdi Ra Bi Mi Fi
         <\<lambda>(res, av, Fi'). \<exists>\<^sub>Axs'.
            loop_post (search_path_loop state) Ci Qi Fi' Bi Mi *
            pot_assn initial_pot Pti * buddy_assn Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs \<and> res_rel res av (search_path_loop state) xs')>"
proof-
  have "search_invars state \<longrightarrow> (\<forall>Fi xs. card (L \<union> R) \<le> length xs \<longrightarrow>
         <loop_assn state Ci Qi Fi Bi Mi * pot_assn initial_pot Pti * buddy_assn Bdi *
          Ra \<mapsto>\<^sub>a xs>
         code.loop_imp Ci Qi Pti Bdi Ra Bi Mi Fi
         <\<lambda>(res, av, Fi'). \<exists>\<^sub>Axs'.
            loop_post (search_path_loop state) Ci Qi Fi' Bi Mi *
            pot_assn initial_pot Pti * buddy_assn Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs \<and> res_rel res av (search_path_loop state) xs')>)"
  proof(induction rule: search_path_loop_induct[OF search_invars_dom[OF assms(1)]])
    case (1 state)
    show ?case
    proof(intro impI allI)
      fix Fi and xs :: "'v list"
      assume inv: "search_invars state" and len: "card (L \<union> R) \<le> length xs"
      have I: "invar_basic state" "invar_best_even_neighbour_heap state"
              "invar_best_even_neighbour_map state"
        using inv by (auto simp: search_invars_def)
      have hinv: "heap_invar (heap state)" using I(1) by (auto elim: invar_basicE)
      have binv: "ben_invar (best_even_neighbour state)" "missed_invar (missed state)"
        using I(1) by (auto elim: invar_basicE)
      obtain queue0 hm where ext: "heap_extract_min (heap state) = (queue0, hm)"
        by (cases "heap_extract_min (heap state)") auto
      show "<loop_assn state Ci Qi Fi Bi Mi * pot_assn initial_pot Pti * buddy_assn Bdi *
             Ra \<mapsto>\<^sub>a xs>
            code.loop_imp Ci Qi Pti Bdi Ra Bi Mi Fi
            <\<lambda>(res, av, Fi'). \<exists>\<^sub>Axs'.
               loop_post (search_path_loop state) Ci Qi Fi' Bi Mi *
               pot_assn initial_pot Pti * buddy_assn Bdi * Ra \<mapsto>\<^sub>a xs' *
               \<up>(length xs' = length xs \<and> res_rel res av (search_path_loop state) xs')>"
      proof(cases hm)
        case None
        have fail: "search_path_loop_fail_cond state"
          by (simp add: search_path_loop_fail_cond_def ext None)
        have sp: "search_path_loop state = state\<lparr>augpath := None\<rparr>"
          by (simp add: search_path_loop_simps(1)[OF fail] search_path_loop_fail_upd_def)
        show ?thesis
          apply(subst code.loop_imp.simps)
          by (sep_auto heap: queue.queue_extract_min_rule
                       simp: hinv ext None sp loop_assn_def loop_post_def res_rel_def)
      next
        case (Some r)
        note ext' = ext[unfolded Some]
        note F0 = extract_facts[OF I ext']
        define l where "l = ben_get (best_even_neighbour state) r"
        have bl: "ben_lookup (best_even_neighbour state) r = Some l"
          using F0(1) ben_lookup_Some[OF F0(1)] by (simp add: l_def)
        have lthe: "the (ben_lookup (best_even_neighbour state) r) = l" using bl by simp
        note F = F0[unfolded lthe]
        have rK: "r \<in> K" using in_K(3)[OF F(7)] .
        have key: "\<And>k. (r, k) \<in> heap_abstract (heap state) \<Longrightarrow>
                         k = w\<^sub>\<pi>_code l r + missed_at state l"
          using extract_key[OF inv ext'] by (simp add: l_def)
        have ext_rule: "<queue_assn (heap state) Qi> queue_extract_min_imp Qi
                        <\<lambda>x. \<exists>\<^sub>Ak. queue_assn queue0 Qi *
                             \<up>(x = Some (r, k) \<and> h k = w\<^sub>\<pi>_code l r + missed_at state l)>"
          apply(rule ht_cons_post[OF queue.queue_extract_min_rule[OF hinv]])
          subgoal for x
            using key by (cases x) (sep_auto simp: ext')+
          done
        have ben_r: "<ben_assn (best_even_neighbour state) Bi> ben_get_imp Bi r
                     <\<lambda>x. ben_assn (best_even_neighbour state) Bi * \<up>(x = l)>"
          using ben_get_rule[OF binv(1) rK] by (simp add: l_def)
        show ?thesis
        proof(cases "buddy r")
          case None
          have bud0: "buddy_get r = nil" using None by (simp add: buddy_def split: if_splits)
          have bud_r: "<buddy_assn Bdi> buddy_imp Bdi r <\<lambda>x. buddy_assn Bdi * \<up>(x = nil)>"
            using buddy_rule[OF rK] by (simp add: bud0)
          have succ: "search_path_loop_succ_cond state"
            by (simp add: search_path_loop_succ_cond_def ext' None)
          have sp: "search_path_loop state =
                    state\<lparr>acc := w\<^sub>\<pi>_code l r + missed_at state l,
                          augpath := Some (r # get_path (forest state) l)\<rparr>"
            by (simp add: search_path_loop_simps(2)[OF succ] search_path_loop_succ_upd_def
                          ext' l_def Let_def)
          have plen: "Suc (length (get_path (forest state) l)) \<le> length xs"
            using succ_path_length[OF I ext', unfolded lthe] len by simp
          hence xsne: "xs \<noteq> []" by auto
          note gp = forest.get_path_rule[OF F(8) F(2), of "Suc 0"]
          show ?thesis
            supply buddy_rule[sep_heap_rules del] ben_get_rule[sep_heap_rules del]
                   forest.get_path_rule[sep_heap_rules del]
            apply(subst code.loop_imp.simps)
            apply(sep_auto heap: ext_rule ben_r bud_r gp simp: loop_assn_def xsne plen)
            subgoal for k a b
              apply(erule entailsD[rotated])
              apply(rule ent_ex_postI[where x = "[r] @ get_path (forest state) l @
                            drop (Suc (length (get_path (forest state) l))) xs"])
              using xsne plen
              by (sep_auto simp: sp loop_post_def res_rel_def neq_Nil_conv)
            subgoal premises p for a b k ha ra haa raa
              using p(5)[unfolded p(3)] by (rule notE) (rule refl)
            done
        next
          case (Some l')
          have bud0: "buddy_get r = l'" "l' \<noteq> nil" "nil \<noteq> l'"
            using Some by (auto simp: buddy_def split: if_splits)
          have bud_r: "<buddy_assn Bdi> buddy_imp Bdi r <\<lambda>x. buddy_assn Bdi * \<up>(x = l')>"
            using buddy_rule[OF rK] by (simp add: bud0)
          have cont: "search_path_loop_cont_cond state"
            by (simp add: search_path_loop_cont_cond_def ext' Some)
          have J: "invar_feasible_potential state" "invar_forest_tight state"
                  "invar_matching_tight state" "invar_out_of_heap state"
            using inv by (auto simp: search_invars_def)
          define acc' where "acc' = w\<^sub>\<pi>_code l r + missed_at state l"
          define missed' where "missed' = missed_upd (missed_upd (missed state) r acc') l' acc'"
          define U where "U = update_best_even_neighbour (missed_get missed')
                                (neighb_coll state) (best_even_neighbour state) queue0 l'"
          note CF = cont_step_facts[OF cont I(1) J(1,2,3) I(2,3) J(4) ext' Some,
                                    unfolded lthe, folded acc'_def, folded missed'_def]
          have cu: "search_path_loop_cont_upd state =
                    state \<lparr> forest := extend_forest_even_unclassified (forest state) l r l',
                            best_even_neighbour := fst (snd U), neighb_coll := fst U,
                            heap := snd (snd U), missed := missed', acc := acc' \<rparr>"
            using cont_upd_eq[OF ext' Some] by (simp add: U_def missed'_def acc'_def l_def)
          have sp: "search_path_loop state = search_path_loop (search_path_loop_cont_upd state)"
            using search_path_loop_simps(3)[OF 1(1) cont] .
          have inv': "search_invars (search_path_loop_cont_upd state)"
            using search_invars_step[OF cont inv] .
          note IH = 1(2)[OF cont, rule_format, OF inv' len, unfolded loop_assn_def cu, simplified]
          have nbI: "rnb_invar (neighb_coll state)"
                    "rnb_abstract (neighb_coll state) = rnb_abstract rnb_init"
            using I(1) by (auto elim!: invar_basicE)
          have l'K: "l' \<in> K" using in_K(1)[OF CF(4)] .
          have minv: "missed_invar (missed_upd (missed state) r acc')" "missed_invar missed'"
            using missed(3) binv(2) rK l'K by (auto simp: missed'_def)
          have mupd1: "h k = acc' \<Longrightarrow>
            <missed_assn (missed state) Mi> missed_upd_imp Mi r k
            <\<lambda>_. missed_assn (missed_upd (missed state) r acc') Mi>" for k
            using missed.fixed_univ_map_upd_rule[OF binv(2) rK, of Mi k] by simp
          have mupd2: "h k = acc' \<Longrightarrow>
            <missed_assn (missed_upd (missed state) r acc') Mi> missed_upd_imp Mi l' k
            <\<lambda>_. missed_assn missed' Mi>" for k
            using missed.fixed_univ_map_upd_rule[OF minv(1) l'K, of Mi k] by (simp add: missed'_def)
          note ubi = update_ben_imp_rule[OF nbI(1) CF(4) nbI(2) minv(2) CF(6), folded U_def]
          note fe = forest.forest_extend_rule[OF CF(5)]
          show ?thesis
            supply buddy_rule[sep_heap_rules del] ben_get_rule[sep_heap_rules del]
                   missed.fixed_univ_map_upd_rule[sep_heap_rules del]
                   forest.forest_extend_rule[sep_heap_rules del]
            apply(subst code.loop_imp.simps)
            apply(sep_auto heap: ext_rule[folded acc'_def] ben_r bud_r mupd1 mupd2 fe ubi IH
                           simp: loop_assn_def bud0 sp cu)
            done
        qed
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

subsection \<open>The New Potential\<close>

definition "pot_pre v p =
  (potential_invar p \<and> v \<in> K \<and> potential_get p v = potential_get initial_pot v)"

lemma foldl_pot_upd:
  "\<lbrakk>potential_invar p; set xs \<subseteq> K\<rbrakk> \<Longrightarrow>
   potential_invar (foldl (\<lambda>p v. potential_upd p v (f v)) p xs) \<and>
   (\<forall>w. w \<notin> set xs \<longrightarrow>
        potential_get (foldl (\<lambda>p v. potential_upd p v (f v)) p xs) w = potential_get p w)"
  by (induction xs arbitrary: p)
     (auto simp: potential_map.fixed_univ_map_upd_invar potential_map.fixed_univ_map_upd)

lemma fold_pre_pot:
  "\<lbrakk>distinct xs; set xs \<subseteq> K; potential_invar p;
    \<forall>v\<in>set xs. potential_get p v = potential_get initial_pot v\<rbrakk> \<Longrightarrow>
   fold_pre pot_pre (\<lambda>p v. potential_upd p v (f v)) p xs"
  by (induction xs arbitrary: p)
     (auto simp: pot_pre_def potential_map.fixed_univ_map_upd_invar potential_map.fixed_univ_map_upd)

lemma pot_step_even_rule:
  assumes "pot_pre v p" "h av = a" "missed_invar M"
  shows "<pot_assn p Pti * missed_assn M Mi> code.pot_step_even Pti Mi av v u
         <\<lambda>_. pot_assn (potential_upd p v (\<pi> v + a - missed_get M v)) Pti * missed_assn M Mi>"
proof-
  have p: "potential_invar p" "v \<in> K" "potential_get p v = \<pi> v"
    using assms(1) by (auto simp: pot_pre_def)
  have mget: "<missed_assn M Mi> missed_get_imp Mi v
              <\<lambda>x. missed_assn M Mi * \<up>(h x = missed_get M v)>"
    using missed.fixed_univ_map_lookup_rule[OF assms(3) p(2)] .
  show ?thesis
    unfolding code.pot_step_even_def
    using assms(2) p by (sep_auto heap: mget simp: h_add)
qed

lemma pot_step_odd_rule:
  assumes "pot_pre v p" "h av = a" "missed_invar M"
  shows "<pot_assn p Pti * missed_assn M Mi> code.pot_step_odd Pti Mi av v u
         <\<lambda>_. pot_assn (potential_upd p v (\<pi> v - a + missed_get M v)) Pti * missed_assn M Mi>"
proof-
  have p: "potential_invar p" "v \<in> K" "potential_get p v = \<pi> v"
    using assms(1) by (auto simp: pot_pre_def)
  have mget: "<missed_assn M Mi> missed_get_imp Mi v
              <\<lambda>x. missed_assn M Mi * \<up>(h x = missed_get M v)>"
    using missed.fixed_univ_map_lookup_rule[OF assms(3) p(2)] .
  show ?thesis
    unfolding code.pot_step_odd_def
    using assms(2) p by (sep_auto heap: mget simp: h_add)
qed

lemma new_pot_imp_rule:
  assumes "forest_invar \<M> (forest st)" "h av = acc st" "missed_invar (missed st)"
  shows "<forest_assn (forest st) Fi * missed_assn (missed st) Mi * pot_assn initial_pot Pti>
         code.new_pot_imp Fi Mi av Pti
         <\<lambda>_. forest_assn (forest st) Fi * missed_assn (missed st) Mi *
              pot_assn (new_potential st) Pti>"
proof-
  define ge where "ge = (\<lambda>p v. potential_upd p v (\<pi> v + acc st - missed_at st v))"
  define go where "go = (\<lambda>p v. potential_upd p v (\<pi> v - acc st + missed_at st v))"
  have fin: "finite (aevens st)" "finite (aodds st)"
    using finite_forest(1,2)[OF assms(1)] by auto
  have vinv: "vset_invar (evens (forest st))" "vset_invar (odds (forest st))"
    using evens_and_odds(1,2)[OF assms(1)] by auto
  have sub: "aevens st \<subseteq> K" "aodds st \<subseteq> K"
    using vset.fixed_univ_set_universe[OF vinv(1)] vset.fixed_univ_set_universe[OF vinv(2)] .
  have disj: "aevens st \<inter> aodds st = {}" using evens_and_odds(4)[OF assms(1)] .
  have NP: "new_potential st = foldl go (foldl ge initial_pot (lst (aevens st))) (lst (aodds st))"
    by (simp add: new_potential_def vset_iterate_pot_lst[OF vinv(1)]
                  vset_iterate_pot_lst[OF vinv(2)] ge_def go_def)
  have pre1: "fold_pre pot_pre ge initial_pot (lst (aevens st))"
    unfolding ge_def
    by (rule fold_pre_pot)
       (auto simp: forest.lst_distinct[OF fin(1)] forest.lst_set[OF fin(1)] sub(1) potential)
  have P1: "potential_invar (foldl ge initial_pot (lst (aevens st)))"
           "\<And>w. w \<notin> aevens st \<Longrightarrow> potential_get (foldl ge initial_pot (lst (aevens st))) w = \<pi> w"
    using foldl_pot_upd[where p = initial_pot and xs = "lst (aevens st)"
                          and f = "\<lambda>v. \<pi> v + acc st - missed_at st v", OF potential]
          forest.lst_set[OF fin(1)] sub(1)
    by (auto simp: ge_def)
  have P1': "\<forall>w\<in>set (lst (aodds st)). potential_get (foldl ge initial_pot (lst (aevens st))) w = \<pi> w"
    using P1(2) disj forest.lst_set[OF fin(2)] by blast
  have pre2: "fold_pre pot_pre go (foldl ge initial_pot (lst (aevens st))) (lst (aodds st))"
    unfolding go_def
    by (rule fold_pre_pot)
       (auto simp: forest.lst_distinct[OF fin(2)] forest.lst_set[OF fin(2)] sub(2) P1(1) P1')
  have step1: "\<And>v p u. pot_pre v p \<Longrightarrow>
    <pot_assn p Pti * missed_assn (missed st) Mi> code.pot_step_even Pti Mi av v u
    <\<lambda>_. pot_assn (ge p v) Pti * missed_assn (missed st) Mi>"
    unfolding ge_def using pot_step_even_rule[OF _ assms(2,3)] .
  have step2: "\<And>v p u. pot_pre v p \<Longrightarrow>
    <pot_assn p Pti * missed_assn (missed st) Mi> code.pot_step_odd Pti Mi av v u
    <\<lambda>_. pot_assn (go p v) Pti * missed_assn (missed st) Mi>"
    unfolding go_def using pot_step_odd_rule[OF _ assms(2,3)] .
  note fold1 = iter_fold_rule_gen[where I = "forest_is_it (forest st) Fi Evens"
      and Q = "forest_assn (forest st) Fi"
      and A = "\<lambda>p (u::unit). pot_assn p Pti * missed_assn (missed st) Mi",
      OF forest.forest_it_has_next_rule forest.forest_it_next_rule forest.forest_quit_iteration
         step1 pre1]
  note fold2 = iter_fold_rule_gen[where I = "forest_is_it (forest st) Fi Odds"
      and Q = "forest_assn (forest st) Fi"
      and A = "\<lambda>p (u::unit). pot_assn p Pti * missed_assn (missed st) Mi",
      OF forest.forest_it_has_next_rule forest.forest_it_next_rule forest.forest_quit_iteration
         step2 pre2]
  show ?thesis
    unfolding code.new_pot_imp_def
    by (sep_auto heap: forest.forest_it_init_rule fold1 fold2 simp: NP)
qed

subsection \<open>The Path Search\<close>

lemma init_ok_foldl:
  "\<lbrakk>set xs \<subseteq> L; init_ok cbq\<rbrakk> \<Longrightarrow>
   init_ok (foldl (\<lambda>cbq l. update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq))
                              (snd (snd cbq)) l) cbq xs)"
proof(induction xs arbitrary: cbq)
  case (Cons x xs)
  have "init_ok (update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) x)"
    using init_ok_step[OF Cons.prems(2), of x] Cons.prems(1) by simp
  from Cons.IH[OF _ this] Cons.prems(1) show ?case by simp
qed simp

lemma init_ok_initial: "init_ok init_best_even_neighbour"
proof-
  have "init_best_even_neighbour =
        foldl (\<lambda>cbq l. update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq))
                          (snd (snd cbq)) l)
              (rnb_init, ben_empty, heap_empty) (filter (\<lambda>v. buddy_get v = nil) (lst L))"
    using init_fold_result(2) by (simp add: init_fold)
  thus ?thesis
    using init_ok_foldl[OF _ init_ok_init, of "filter (\<lambda>v. buddy_get v = nil) (lst L)"]
          forest.lst_set[OF finite_L]
    by auto
qed

lemma scratch_assnI:
  "\<lbrakk>rnb_invar C; rnb_abstract C = rnb_abstract rnb_init; ben_invar B; missed_invar M\<rbrakk> \<Longrightarrow>
   nb_assn C Ci * queue_assn H Qi * forest_assn F Fi * ben_assn B Bi * missed_assn M Mi
   \<Longrightarrow>\<^sub>A scratch_assn Ci Qi Fi Bi Mi"
  unfolding scratch_assn_def by (sep_auto simp: fun_eq_iff)

text \<open>The result of the imperative search, relative to the functional one.\<close>

definition "search_post Pti res xs' =
  (case search_path of (r, \<pi>') \<Rightarrow> \<up>(imp_result_rel xs' res r) * pot_assn \<pi>' Pti)"

theorem search_imp_rule:
  assumes len: "card (L \<union> R) \<le> length xs"
  shows "<scratch_assn Ci Qi Fi Bi Mi * vset_assn left Li * buddy_assn Bdi *
          pot_assn initial_pot Pti * Ra \<mapsto>\<^sub>a xs>
         code.search_imp Ci Qi Pti Bdi Li Ra Fi Bi Mi
         <\<lambda>(res, Fi'). \<exists>\<^sub>Axs'.
            scratch_assn Ci Qi Fi' Bi Mi * vset_assn left Li * buddy_assn Bdi *
            Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) * search_post Pti res xs'>"
proof-
  have ok: "rnb_invar (fst init_best_even_neighbour)"
           "rnb_abstract (fst init_best_even_neighbour) = rnb_abstract rnb_init"
           "ben_invar (fst (snd init_best_even_neighbour))"
    using init_ok_initial by (auto simp: init_ok_def)
  show ?thesis
  proof(cases "vset_is_empty unmatched_lefts")
    case True
    have sp: "search_path = (Lefts_Matched, initial_pot)" by (simp add: search_path_def True)
    show ?thesis
      unfolding code.search_imp_def
      apply(sep_auto heap: clear_imp_rule init_imp_rule simp: True)
      using ok True by (sep_auto simp: scratch_assn_def search_post_def sp fun_eq_iff missed(1))
  next
    case False
    have ne: "L - Vs \<M> \<noteq> {}"
      using False vset_is_empty[OF unmatched_lefts(2)] unmatched_lefts(1) by simp
    have inv0: "search_invars initial_state" using search_invars_init[OF ne] .
    have dom: "search_path_loop_dom initial_state" using search_invars_dom[OF inv0] .
    define fin where "fin = search_path_loop initial_state"
    have basic: "invar_basic fin" using loop_final_basic[OF inv0] by (simp add: fin_def)
    have fb: "rnb_invar (neighb_coll fin)" "rnb_abstract (neighb_coll fin) = rnb_abstract rnb_init"
             "forest_invar \<M> (forest fin)" "ben_invar (best_even_neighbour fin)"
             "missed_invar (missed fin)"
      using basic by (auto elim!: invar_basicE)
    have spe: "search_path = (case augpath fin of None \<Rightarrow> (Dual_Unbounded, initial_pot)
                              | Some p \<Rightarrow> (Next_Iteration p, new_potential fin))"
      unfolding fin_def
      by (simp add: search_path_def False search_path_loop_impl_same[OF dom] Let_def)
    have fields: "neighb_coll initial_state = fst init_best_even_neighbour"
                 "heap initial_state = snd (snd init_best_even_neighbour)"
                 "forest initial_state = empty_forest forest_roots"
                 "best_even_neighbour initial_state = fst (snd init_best_even_neighbour)"
                 "missed initial_state = missed_empty"
      by (simp_all add: initial_state_def)
    note lp = loop_imp_rule[OF inv0 len, unfolded loop_assn_def fields, folded fin_def]
    show ?thesis
    proof(cases "augpath fin")
      case None
      show ?thesis
        unfolding code.search_imp_def
        apply(sep_auto heap: clear_imp_rule init_imp_rule lp simp: False)
        apply(all \<open>clarsimp simp: None res_rel_def False\<close>)
        using fb(1,2,4,5)
        by (sep_auto simp: loop_post_def scratch_assn_def search_post_def spe None fun_eq_iff)
    next
      case (Some p)
      note np = new_pot_imp_rule[OF fb(3) _ fb(5)]
      show ?thesis
        unfolding code.search_imp_def
        apply(sep_auto heap: clear_imp_rule init_imp_rule lp simp: False)
        apply(all \<open>clarsimp simp: Some res_rel_def False\<close>)
        using fb(1,2,4,5)
        by (sep_auto heap: np simp: loop_post_def scratch_assn_def search_post_def spe Some
                                    fun_eq_iff)
    qed
  qed
qed

end
end

