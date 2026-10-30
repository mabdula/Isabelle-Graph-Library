theory Primal_Dual_Path_Search_Imperative
  imports
    Hungarian_Method.Primal_Dual_Path_Search
    Data_Structures.Fixed_Univ_Map_Specs_Imp
    Data_Structures.Fixed_Univ_Key_Value_Queue_Specs_Imp
    Directed_Set_Graphs.Weighted_Neighbourhoods_Imperative_Spec
    Basic_Matching.Alternating_Forest_Imperative_Spec
    Data_Structures.Real_Embedding

begin

provenance ai



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

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) scan_imp ::
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

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) loop_imp ::
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
      and set_assn = vset_assn and lst = lst and is_it = left_is_it
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
    and vset_assn
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

lemma \<^marker>\<open>provenance ai_human\<close> ben_get_rule[sep_heap_rules]:
  "\<lbrakk>ben_invar B; r \<in> K\<rbrakk> \<Longrightarrow>
   <ben_assn B Bi> ben_get_imp Bi r <\<lambda>x. ben_assn B Bi * \<up>(x = ben_get B r)>"
  using ben.fixed_univ_map_lookup_rule[of B r Bi]
  by simp

lemma \<^marker>\<open>provenance ai_human\<close> ben_upd_rule[sep_heap_rules]:
  "\<lbrakk>ben_invar B; r \<in> K\<rbrakk> \<Longrightarrow>
   <ben_assn B Bi> ben_upd_imp Bi r l <\<lambda>_. ben_assn (ben_upd B r l) Bi>"
  using ben.fixed_univ_map_upd_rule[of B r Bi l]
  by simp

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
  using assms scan_invD(4,6,7) w\<^sub>\<pi>_code_is[of l' r] relax_neighbour_Some(2)[OF assms]
  by fastforce+

lemma \<^marker>\<open>provenance ai_human\<close> relax_new_rule:
  "\<lbrakk>heap_invar queue; ben_invar ben; r \<in> Vs G; \<nexists>k. (r, k) \<in> heap_abstract queue\<rbrakk> \<Longrightarrow>
   <queue_assn queue Qi * ben_assn ben Bi> code.relax_new_imp Qi Bi l r key
   <\<lambda>_. queue_assn (heap_insert queue r (h key)) Qi * ben_assn (ben_upd ben r l) Bi>"
  unfolding code.relax_new_imp_def
  by (sep_auto heap: queue.queue_insert_rule simp: in_K(3))

lemma \<^marker>\<open>provenance ai_human\<close> relax_old_rule:
  assumes "heap_invar queue" "ben_invar ben" "r \<in> Vs G"
      and "\<And>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> k = K'"
      and "\<nexists>k. (r, k) \<in> heap_abstract queue \<Longrightarrow> \<not> h key < K'"
  shows "<queue_assn queue Qi * ben_assn ben Bi> code.relax_old_imp Qi Bi l r key
         <\<lambda>_. if h key < K'
              then queue_assn (heap_decrease_key queue r (h key)) Qi *
                   ben_assn (ben_upd ben r l) Bi
              else queue_assn queue Qi * ben_assn ben Bi>"
  unfolding code.relax_old_imp_def
  using assms(4,5)
  by (sep_auto heap: queue.queue_key_of_rule queue.queue_decrease_key_rule
               simp: assms(1-3) in_K(3) split: option.splits)

lemma relax_key:
  "\<lbrakk>h c = edge_costs_code l r; h pl = \<pi> l; h ml = off l; h pr = \<pi> r\<rbrakk> \<Longrightarrow>
     h (c - pl - pr + ml) = w\<^sub>\<pi>_code l r + off l"
  by (simp add: w\<^sub>\<pi>_code_def h_add)

lemma rneighb_in_K:
  assumes "scan_inv off l ben queue" "r \<in> rneighbs l"
  shows "r \<in> Vs G" "r \<in> K"
  using assms scan_invD(3)[of off l ben queue] rneighbs_in_G[of l r] in_K(3)
  by (auto intro: edges_are_Vs_2)

lemma \<^marker>\<open>provenance ai_human\<close> relax_old_imp_rule:
  assumes "scan_inv off l ben queue" "r \<in> rneighbs l" "ben_lookup ben r = Some l'"
          "h key = w\<^sub>\<pi>_code l r + off l"
  shows "<queue_assn queue Qi * ben_assn ben Bi> code.relax_old_imp Qi Bi l r key
         <\<lambda>_. queue_assn (snd (relax_neighbour off l (ben, queue) r)) Qi *
              ben_assn (fst (relax_neighbour off l (ben, queue) r)) Bi>"
  apply(rule ht_cons_post[OF relax_old_rule[where K' = "w\<^sub>\<pi>_code l' r + off l'"]])
  using scan_invD(1,2)[OF assms(1)] rneighb_in_K(1)[OF assms(1,2)] relax_queue_key[OF assms(1-3)] assms(3,4)
  by (auto simp: relax_neighbour_view split: if_splits intro: ent_refl_true)

lemma \<^marker>\<open>provenance ai_human\<close> relax_imp_rule:
  assumes "scan_inv off l ben queue" "r \<in> rneighbs l" "h c = edge_costs_code l r" "h pl = \<pi> l"
          "h ml = off l"
  shows "<pot_assn initial_pot Pti * queue_assn queue Qi * ben_assn ben Bi>
         code.relax_imp Pti Qi Bi l pl ml r c
         <\<lambda>_. pot_assn initial_pot Pti *
              queue_assn (snd (relax_neighbour off l (ben, queue) r)) Qi *
              ben_assn (fst (relax_neighbour off l (ben, queue) r)) Bi>"
proof(cases "ben_lookup ben r")
  case None
  show ?thesis
    unfolding code.relax_imp_def
    using relax_neighbour_None[OF assms(1,2) None] relax_key[of c l r pl ml off, OF assms(3-5)]
    by (sep_auto heap: relax_new_rule
                 simp: None None[unfolded ben_lookup_None] relax_neighbour_view scan_invD(1,2)[OF assms(1)]
                       rneighb_in_K[OF assms(1,2)] potential)
next
  case (Some l')
  show ?thesis
    unfolding code.relax_imp_def
    using ben_lookup_Some[OF Some] relax_key[of c l r pl ml off, OF assms(3-5)]
    by (sep_auto heap: relax_old_imp_rule[OF assms(1,2) Some]
                 simp: scan_invD(1)[OF assms(1)] rneighb_in_K(2)[OF assms(1,2)] potential)
qed

subsection \<open>Scanning a Neighbourhood\<close>

lemma scan_remaining_props:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
  shows "rnb_remaining C l \<subseteq> rneighbs l" "finite (rnb_remaining C l)"
  using assms rnb.idx_partition_union[of C l] finite_subset[OF _ finite_rneighbs[OF assms(2)]]
  by auto

lemma scan_move_props:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init" "rnb_has C l"
  shows "rnb_remaining C l \<noteq> {}" "rnb_current C l \<in> rneighbs l" "rnb_invar (rnb_move C l)"
        "rnb_abstract (rnb_move C l) = rnb_abstract rnb_init"
        "card (rnb_remaining (rnb_move C l) l) < card (rnb_remaining C l)"
  using assms rnb.idx_has[of C l] rnb.idx_current[of C l] scan_remaining_props[of C l] rnb.idx_move_invar[of C l]
        rnb.idx_move_remaining[of C l] rnb.idx_move_abstract[of C l]
        card_Diff1_less[of "rnb_remaining C l" "rnb_current C l"]
  by (auto simp: fun_eq_iff)

lemma \<^marker>\<open>provenance ai_human\<close> scan_imp_rule:
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
  show ?case
  proof(cases "rnb_has C l")
    case True
    note M = scan_move_props[OF less.prems(1-3) True]
    note IH = less.hyps[OF M(5,3) less.prems(2) M(4) relax_neighbour_pres(1)[OF less.prems(4) M(2)]
                           less.prems(5,6), simplified]
    show ?thesis
      apply(subst code.scan_imp.simps)
      apply(sep_auto heap: nb.idx_has_rule nb.idx_current_rule nb.current_cost_rule nb.idx_move_rule
                     simp: less.prems(1,2) True M(1))
      apply(sep_auto heap: relax_imp_rule[OF less.prems(4) M(2) _ less.prems(5,6)])
      by (sep_auto heap: IH simp: scan_neighbours.simps[of off l C] True)
  next
    case False
    show ?thesis
      by (subst code.scan_imp.simps)
         (sep_auto heap: nb.idx_has_rule simp: less.prems(1,2) False scan_neighbours.simps[of off l C])
  qed
qed

lemma scan_reset_props:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
  shows "rnb_invar (rnb_reset C l)" "rnb_abstract (rnb_reset C l) = rnb_abstract rnb_init"
  using assms rnb.idx_reset_invar rnb.idx_reset_abstract
  by (auto simp: fun_eq_iff)

lemma \<^marker>\<open>provenance ai_human\<close> update_ben_imp_rule:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
      and "missed_invar M" "scan_inv (missed_get M) l ben queue"
  shows "<nb_assn C Ci * pot_assn initial_pot Pti * missed_assn M Mi *
          queue_assn queue Qi * ben_assn ben Bi>
         code.update_ben_imp Ci Pti Mi Qi Bi l
         <\<lambda>_. nb_assn (fst (update_best_even_neighbour (missed_get M) C ben queue l)) Ci *
              pot_assn initial_pot Pti * missed_assn M Mi *
              queue_assn (snd (snd (update_best_even_neighbour (missed_get M) C ben queue l))) Qi *
              ben_assn (fst (snd (update_best_even_neighbour (missed_get M) C ben queue l))) Bi>"
  unfolding code.update_ben_imp_def update_best_even_neighbour_def
  by (sep_auto heap: nb.idx_reset_rule
                     scan_imp_rule[OF scan_reset_props(1)[OF assms(1-3)] assms(2)
                                        scan_reset_props(2)[OF assms(1-3)] assms(5)]
               simp: assms(1,2,4) in_K(1) potential)

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
  thus ?case
    using Cons.IH[of "fst (relax_neighbour off l (ben, queue) r)" "snd (relax_neighbour off l (ben, queue) r)"]
          relax_neighbour_pres[OF Cons.prems(1), of r]
    by simp
qed simp

lemma ubn_pres:
  assumes "rnb_invar C" "l \<in> L" "rnb_abstract C = rnb_abstract rnb_init"
          "scan_inv off l ben queue" "update_best_even_neighbour off C ben queue l = (C', ben', queue')"
  shows "rnb_invar C'" "rnb_abstract C' = rnb_abstract rnb_init" "scan_inv off l ben' queue'"
        "all_in_heap ben queue \<Longrightarrow> all_in_heap ben' queue'"
proof-
  obtain rs where "set rs = rneighbs l" "(ben', queue') = foldl (relax_neighbour off l) (ben, queue) rs"
    using update_best_even_neighbour_is_foldl(1)[OF assms(1-3) assms(5)[symmetric]]
    by blast
  thus "scan_inv off l ben' queue'" "all_in_heap ben queue \<Longrightarrow> all_in_heap ben' queue'"
    using foldl_relax_pres[OF assms(4), of rs]
    by (simp_all add: prod_eq_iff)
  show "rnb_invar C'" "rnb_abstract C' = rnb_abstract rnb_init"
    using update_best_even_neighbour_is_foldl(2,3)[OF assms(1-3) assms(5)[symmetric]]
    by simp_all
qed

subsection \<open>Clearing\<close>

text \<open>The data structures of the search, with arbitrary contents. Only the collection of
      neighbourhoods has to be one of the collection of the graph.\<close>

definition "scratch_assn Ci Qi Fi Bi Mi =
  (\<exists>\<^sub>AC H F B M. nb_assn C Ci * queue_assn H Qi * forest_assn F Fi * ben_assn B Bi *
                 missed_assn M Mi *
                 \<up>(rnb_invar C \<and> (\<forall>i\<in>L. rnb_abstract C i = rnb_abstract rnb_init i) \<and>
                   ben_invar B \<and> missed_invar M))"

lemma \<^marker>\<open>provenance ai_human\<close> clear_imp_rule:
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

lemma init_ok_props:
  assumes "init_ok cbq" "l \<in> L"
  shows "rnb_invar (fst cbq)" "rnb_abstract (fst cbq) = rnb_abstract rnb_init"
        "all_in_heap (fst (snd cbq)) (snd (snd cbq))" "scan_inv (\<lambda>x. 0) l (fst (snd cbq)) (snd (snd cbq))"
  using assms
  by (simp_all add: init_ok_def)

lemma init_ok_step:
  assumes "init_ok cbq" "l \<in> L"
  shows "init_ok (update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) l)"
proof(cases "update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq)) (snd (snd cbq)) l" rule: prod_cases3)
  case (fields C' ben' queue')
  note I = init_ok_props[OF assms]
  note P = ubn_pres[OF I(1) assms(2) I(2,4) fields]
  show ?thesis
    using I P scan_inv_zero_other[OF P(3)] scan_invD(1)[OF P(3)]
    by (simp add: fields init_ok_def)
qed

lemma init_ok_init: "init_ok (rnb_init, ben_empty, heap_empty)"
  using G(4) best_even_neighbour(1,4) heap(1,11)
  by (auto simp: init_ok_def all_in_heap_def scan_inv_def)

definition "init_P v b = (v \<in> L \<and> init_ok (fst (snd b)))"

lemma init_fold_pre:
  "\<lbrakk>set xs \<subseteq> L; init_ok cbq\<rbrakk> \<Longrightarrow> fold_pre init_P init_g (S, cbq, fnd) xs"
proof(induction xs arbitrary: S cbq fnd)
  case (Cons x xs)
  thus ?case
    using init_ok_step[OF Cons.prems(2), of x]
    by (cases "buddy_get x = nil") (simp_all add: init_P_def init_g_def)
qed simp

lemma unmatched_lefts_set: "vset_to_set unmatched_lefts = L \<inter> Collect (\<lambda>v. buddy_get v = nil)"
  using G(2) vset_iterations(4)
  by (simp add: unmatched_lefts_def)

lemma unmatched_lefts_lst:
  "lst (vset_to_set unmatched_lefts) = filter (\<lambda>v. buddy_get v = nil) (lst L)"
  "set (filter (\<lambda>v. buddy_get v = nil) (lst L)) = vset_to_set unmatched_lefts"
  using finite_L forest.lst_filter forest.lst_set unmatched_lefts_set
  by auto

lemma init_fold_result:
  "foldl init_g ({}, (rnb_init, ben_empty, heap_empty), False) (lst L) =
   (vset_to_set forest_roots, init_best_even_neighbour, \<not> vset_is_empty unmatched_lefts)"
  using unmatched_lefts_lst(2)
  by (auto simp: init_fold forest_roots_def init_best_even_neighbour_def update_best_even_neighbours_def
                 unmatched_lefts(2) vset_iterate_ben_lst unmatched_lefts_lst(1) vset_is_empty filter_empty_conv)

subsection \<open>The Initial State: Imperative Part\<close>

lemma \<^marker>\<open>provenance ai_human\<close> add_root_insert:
  "\<lbrakk>vset_invar Rs; v \<in> K\<rbrakk> \<Longrightarrow>
   <forest_assn (empty_forest Rs) Fi> forest_add_root_imp v Fi
   <forest_assn (empty_forest (vset_insert v Rs))>"
  by (rule forest.forest_add_root_rule) (auto simp: vset(3,4))

definition "init_A Ci Pti Mi Qi Bi Bdi b c = (case b of (S, cbq, fnd) \<Rightarrow> case c of (Fi, fndi) \<Rightarrow>
   (\<exists>\<^sub>ARs. forest_assn (empty_forest Rs) Fi * \<up>(vset_invar Rs \<and> vset_to_set Rs = S)) *
   nb_assn (fst cbq) Ci * queue_assn (snd (snd cbq)) Qi * ben_assn (fst (snd cbq)) Bi *
   pot_assn initial_pot Pti * missed_assn missed_empty Mi * buddy_assn Bdi *
   \<up>(fndi = fnd))"

lemma init_P_props:
  assumes "init_P v (S, (C, ben, queue), fnd)"
  shows "v \<in> L" "v \<in> K" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
        "scan_inv (missed_get missed_empty) v ben queue"
  using assms in_K(1)
  by (auto simp: init_P_def init_ok_def missed(2))

lemma \<^marker>\<open>provenance ai_human\<close> init_step_rule:
  assumes "init_P v b"
  shows "<init_A Ci Pti Mi Qi Bi Bdi b c> code.init_step Ci Pti Mi Qi Bi Bdi v c
         <init_A Ci Pti Mi Qi Bi Bdi (init_g b v)>"
proof(cases b rule: prod_cases3)
  case (fields S cbq fnd)
  then obtain C ben queue where "b = (S, (C, ben, queue), fnd)"
    by (cases cbq) auto
  note P = init_P_props[OF assms[unfolded this]]
  show ?thesis
  proof(cases "buddy_get v = nil")
    case True
    show ?thesis
      unfolding code.init_step_def init_A_def \<open>b = (S, (C, ben, queue), fnd)\<close>
      by (sep_auto heap: add_root_insert update_ben_imp_rule[OF P(3,1,4) missed(1) P(5), unfolded missed(2)]
                   simp: True P(2) init_g_def vset(3,4) split: prod.splits)
  next
    case False
    show ?thesis
      unfolding code.init_step_def init_A_def \<open>b = (S, (C, ben, queue), fnd)\<close>
      by (sep_auto simp: False init_g_def eq_commute[of nil] P(2) split: prod.splits)
  qed
qed

lemma forest_roots_cong:
  "\<lbrakk>vset_invar Rs; vset_to_set Rs = vset_to_set forest_roots\<rbrakk> \<Longrightarrow>
   forest_assn (empty_forest Rs) = forest_assn (empty_forest forest_roots)"
  using forest.forest_empty_cong[of Rs forest_roots] unmatched_lefts(2)
  by (simp add: forest_roots_def)

lemma \<^marker>\<open>provenance ai_human\<close> init_imp_rule:
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
  note fold = iter_fold_rule_gen[where I = "\<lambda>xs it. vset_assn left Li * left_is_it L Li xs it"
                 and Q = "vset_assn left Li" and A = "init_A Ci Pti Mi Qi Bi Bdi",
                 OF left.it_has_next_rule left.it_next_rule left.quit_iteration init_step_rule
                    init_fold_pre[OF equalityD1[OF forest.lst_set[OF finite_L]] init_ok_init,
                                    where S = "{}" and fnd = False],
                 unfolded init_fold_result]
  have "<vset_assn left Li * init_A Ci Pti Mi Qi Bi Bdi ({}, (rnb_init, ben_empty, heap_empty), False) (Fi, False)>
        code.init_imp Ci Pti Mi Qi Bi Bdi Li Fi
        <\<lambda>c'. vset_assn left Li * init_A Ci Pti Mi Qi Bi Bdi
                (vset_to_set forest_roots, init_best_even_neighbour, \<not> vset_is_empty unmatched_lefts) c'>"
    unfolding code.init_imp_def
    by (sep_auto heap: left.it_init_rule fold simp: G(2))
  thus ?thesis
  proof(rule ht_cons[rotated 2], goal_cases)
    case 1
    show ?case
      by (sep_auto simp: init_A_def vset(1,2))
  next
    case (2 c)
    show ?case
      unfolding init_A_def
      apply(cases c)
      apply(simp only: prod.case ex_assn_move_out star_aci)
      apply(rule ent_ex_preI)
      subgoal for Fi' fnd Rs
        by (cases fnd) (sep_auto simp: forest_roots_cong)+
      done
  qed
qed

subsection \<open>The Loop: Functional Part\<close>

lemma search_invarsD:
  assumes "search_invars state"
  shows "invar_basic state" "invar_best_even_neighbour_heap state" "invar_best_even_neighbour_map state"
        "invar_feasible_potential state" "invar_forest_tight state" "invar_matching_tight state"
        "invar_out_of_heap state"
  using assms
  by (simp_all add: search_invars_def)

lemma invar_basic_props:
  assumes "invar_basic state"
  shows "heap_invar (heap state)" "ben_invar (best_even_neighbour state)" "missed_invar (missed state)"
        "rnb_invar (neighb_coll state)" "rnb_abstract (neighb_coll state) = rnb_abstract rnb_init"
        "forest_invar \<M> (forest state)"
  using assms
  by (auto elim!: invar_basicE)

lemma extract_key:
  assumes "search_invars state" "heap_extract_min (heap state) = (queue0, Some r)"
      and "(r, k) \<in> heap_abstract (heap state)"
  shows "k = w\<^sub>\<pi>_code (ben_get (best_even_neighbour state) r) r +
             missed_at state (ben_get (best_even_neighbour state) r)"
proof-
  note I = search_invarsD[OF assms(1)]
  obtain l where "ben_lookup (best_even_neighbour state) r = Some l" "k = w\<^sub>\<pi> l r + missed_at state l"
    using invar_best_even_neighbour_heapD[OF I(2)] assms(3)
    by blast
  thus ?thesis
    using extract_facts(1,3,4)[OF I(1-3) assms(2)] w\<^sub>\<pi>_code_is[of l r] ben_lookup_Some
    by auto
qed

lemma \<^marker>\<open>provenance ai_human\<close> extract_min_key_rule:
  assumes "search_invars state" "heap_extract_min (heap state) = (queue0, Some r)"
  shows "<queue_assn (heap state) Qi> queue_extract_min_imp Qi
         <\<lambda>x. \<exists>\<^sub>Ak. queue_assn queue0 Qi *
              \<up>(x = Some (r, k) \<and> h k = w\<^sub>\<pi>_code (ben_get (best_even_neighbour state) r) r +
                                       missed_at state (ben_get (best_even_neighbour state) r))>"
  apply(rule ht_cons_post[OF queue.queue_extract_min_rule])
  subgoal
    using assms(1)
    by (simp add: search_invars_def invar_basic_props(1))
  subgoal for x
    using extract_key[OF assms]
    by (cases x) (sep_auto simp: assms(2))+
  done

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

lemma loop_fail:
  "heap_extract_min (heap state) = (queue0, None) \<Longrightarrow> search_path_loop state = state\<lparr>augpath := None\<rparr>"
  by (simp add: search_path_loop_simps(1) search_path_loop_fail_cond_def search_path_loop_fail_upd_def)

lemma loop_succ:
  "\<lbrakk>heap_extract_min (heap state) = (queue0, Some r); buddy r = None\<rbrakk> \<Longrightarrow>
   search_path_loop state =
   state\<lparr>acc := w\<^sub>\<pi>_code (ben_get (best_even_neighbour state) r) r +
                missed_at state (ben_get (best_even_neighbour state) r),
         augpath := Some (r # get_path (forest state) (ben_get (best_even_neighbour state) r))\<rparr>"
  by (simp add: search_path_loop_simps(2) search_path_loop_succ_cond_def search_path_loop_succ_upd_def
                Let_def ben_lookup_def)

lemma buddy_get_props:
  "buddy r = None \<Longrightarrow> buddy_get r = nil"
  "buddy r = Some l' \<Longrightarrow> buddy_get r = l' \<and> l' \<noteq> nil"
  by (auto simp: buddy_def split: if_splits)

lemma ben_lookup_the: "ben_lookup B r = Some l \<Longrightarrow> the (ben_lookup B r) = ben_get B r"
  by (simp add: ben_lookup_def split: if_splits)

lemma loop_final_basic:
  assumes "search_invars state"
  shows "invar_basic (search_path_loop state)"
  using assms
proof(induction rule: search_path_loop_induct[OF search_invars_dom[OF assms]])
  case (1 state)
  note dom = 1(1) and IH = 1(2) and inv = 1(3)
  show ?case
  proof(cases state rule: search_path_loop_cases)
    case 1
    thus ?thesis
      using inv
      by (simp add: search_path_loop_simps(1) search_path_loop_fail_upd_def search_invars_basic invar_basic_upd)
  next
    case 2
    thus ?thesis
      using inv succ_upd_shape[of state]
      by (auto simp: search_path_loop_simps(2) search_invars_basic invar_basic_upd)
  next
    case 3
    thus ?thesis
      using 3 inv search_invars_step[of state] IH
      by (simp add: search_path_loop_simps(3)[OF dom 3])
  qed
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

lemma \<^marker>\<open>provenance ai_human\<close> loop_imp_rule:
  assumes "search_invars state" "card (L \<union> R) \<le> length xs"
  shows "<loop_assn state Ci Qi Fi Bi Mi * pot_assn initial_pot Pti * buddy_assn Bdi *
          Ra \<mapsto>\<^sub>a xs>
         code.loop_imp Ci Qi Pti Bdi Ra Bi Mi Fi
         <\<lambda>(res, av, Fi'). \<exists>\<^sub>Axs'.
            loop_post (search_path_loop state) Ci Qi Fi' Bi Mi *
            pot_assn initial_pot Pti * buddy_assn Bdi * Ra \<mapsto>\<^sub>a xs' *
            \<up>(length xs' = length xs \<and> res_rel res av (search_path_loop state) xs')>"
  using assms
proof(induction arbitrary: Fi xs rule: search_path_loop_induct[OF search_invars_dom[OF assms(1)]])
  case (1 state)
  note I = search_invarsD[OF 1(3)]
  note B = invar_basic_props[OF I(1)]
  obtain queue0 hm where "heap_extract_min (heap state) = (queue0, hm)"
    by (cases "heap_extract_min (heap state)") auto
  note ext = this
  show ?case
  proof(cases hm)
    case None
    show ?thesis
      by (subst code.loop_imp.simps)
         (sep_auto heap: queue.queue_extract_min_rule
                   simp: B(1) ext None loop_fail loop_assn_def loop_post_def res_rel_def)
  next
    case (Some r)
    note ext' = ext[unfolded Some]
    note lthe = ben_lookup_the[OF extract_facts(1)[OF I(1-3) ext']]
    note F = extract_facts[OF I(1-3) ext', unfolded lthe]
    note ex = extract_min_key_rule[OF 1(3) ext']
    show ?thesis
    proof(cases "buddy r")
      case None
      note sp = loop_succ[OF ext' None]
       and plen = order.trans[OF succ_path_length[OF I(1-3) ext', unfolded lthe] 1(4)]
      show ?thesis
        supply buddy_rule[sep_heap_rules del] ben_get_rule[sep_heap_rules del]
               forest.get_path_rule[sep_heap_rules del]
        apply(subst code.loop_imp.simps)
        apply(sep_auto heap: ex ben_get_rule[OF B(2) in_K(3)[OF F(7)]]
                             buddy_rule[OF in_K(3)[OF F(7)], unfolded buddy_get_props(1)[OF None]]
                             forest.get_path_rule[OF F(8) F(2), of "Suc 0"]
                       simp: loop_assn_def plen[simplified])
        subgoal for k a b
          apply(erule entailsD[rotated])
          apply(rule ent_ex_postI[where x = "[r] @ get_path (forest state) (ben_get (best_even_neighbour state) r) @
                        drop (Suc (length (get_path (forest state) (ben_get (best_even_neighbour state) r)))) xs"])
          using plen
          by (sep_auto simp: sp loop_post_def res_rel_def neq_Nil_conv)
        subgoal premises p for a b k ha ra haa raa
          using p(5)[unfolded p(3)]
          by (rule notE) (rule refl)
        done
    next
      case (Some l')
      have "search_path_loop_cont_cond state"
        by (simp add: search_path_loop_cont_cond_def ext' Some)
      note CF = cont_step_facts[OF this I(1,4,5,6,2,3,7) ext' Some, unfolded lthe]
       and IH = 1(2)[OF this search_invars_step[OF this 1(3)],
                     unfolded cont_upd_eq[OF ext' Some] loop_assn_def, simplified]
       and sp = search_path_loop_simps(3)[OF 1(1) this]
      show ?thesis
        supply buddy_rule[sep_heap_rules del] ben_get_rule[sep_heap_rules del]
               missed.fixed_univ_map_upd_rule[sep_heap_rules del] forest.forest_extend_rule[sep_heap_rules del]
        by (subst code.loop_imp.simps)
           (sep_auto heap: ex ben_get_rule[OF B(2) in_K(3)[OF F(7)]] buddy_rule[OF in_K(3)[OF F(7)]]
                           missed.fixed_univ_map_upd_rule[OF B(3) in_K(3)[OF F(7)]]
                           missed.fixed_univ_map_upd_rule[OF missed(3)[OF B(3) in_K(3)[OF F(7)]] in_K(1)[OF CF(4)]]
                           forest.forest_extend_rule[OF CF(5)] update_ben_imp_rule[OF B(4) CF(4) B(5) _ CF(6)] IH
                     simp: loop_assn_def buddy_get_props(2)[OF Some] eq_commute[of nil] sp
                           cont_upd_eq[OF ext' Some] missed(3) B(3) CF(4) F(7) in_K(1,3) 1(4))
    qed
  qed
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

lemma \<^marker>\<open>provenance ai_human\<close> pot_step_even_rule:
  assumes "pot_pre v p" "h av = a" "missed_invar M"
  shows "<pot_assn p Pti * missed_assn M Mi> code.pot_step_even Pti Mi av v u
         <\<lambda>_. pot_assn (potential_upd p v (\<pi> v + a - missed_get M v)) Pti * missed_assn M Mi>"
  unfolding code.pot_step_even_def
  using assms
  by (sep_auto simp: pot_pre_def h_add)

lemma \<^marker>\<open>provenance ai_human\<close> pot_step_odd_rule:
  assumes "pot_pre v p" "h av = a" "missed_invar M"
  shows "<pot_assn p Pti * missed_assn M Mi> code.pot_step_odd Pti Mi av v u
         <\<lambda>_. pot_assn (potential_upd p v (\<pi> v - a + missed_get M v)) Pti * missed_assn M Mi>"
  unfolding code.pot_step_odd_def
  using assms
  by (sep_auto simp: pot_pre_def h_add)

lemma forest_parts_props:
  assumes "forest_invar \<M> (forest st)"
  shows "finite (aevens st)" "finite (aodds st)" "vset_invar (evens (forest st))"
        "vset_invar (odds (forest st))" "aevens st \<subseteq> K" "aodds st \<subseteq> K" "aevens st \<inter> aodds st = {}"
  using assms finite_forest(1,2) evens_and_odds(1,2,4) vset.fixed_univ_set_universe
  by auto

lemma new_potential_foldl:
  assumes "forest_invar \<M> (forest st)"
  shows "new_potential st =
         foldl (\<lambda>p v. potential_upd p v (\<pi> v - acc st + missed_at st v))
               (foldl (\<lambda>p v. potential_upd p v (\<pi> v + acc st - missed_at st v)) initial_pot (lst (aevens st)))
               (lst (aodds st))"
  using forest_parts_props(3,4)[OF assms]
  by (simp add: new_potential_def vset_iterate_pot_lst)

lemma new_pot_pre:
  assumes "forest_invar \<M> (forest st)"
  shows "fold_pre pot_pre (\<lambda>p v. potential_upd p v (\<pi> v + acc st - missed_at st v)) initial_pot
                  (lst (aevens st))"
        "fold_pre pot_pre (\<lambda>p v. potential_upd p v (\<pi> v - acc st + missed_at st v))
           (foldl (\<lambda>p v. potential_upd p v (\<pi> v + acc st - missed_at st v)) initial_pot (lst (aevens st)))
           (lst (aodds st))"
  using assms forest_parts_props[of st] forest.lst_distinct forest.lst_set
        foldl_pot_upd[OF potential, of "lst (aevens st)" "\<lambda>v. \<pi> v + acc st - missed_at st v"]
  by (auto intro!: fold_pre_pot simp: potential)

lemma \<^marker>\<open>provenance ai_human\<close> new_pot_imp_rule:
  assumes "forest_invar \<M> (forest st)" "h av = acc st" "missed_invar (missed st)"
  shows "<forest_assn (forest st) Fi * missed_assn (missed st) Mi * pot_assn initial_pot Pti>
         code.new_pot_imp Fi Mi av Pti
         <\<lambda>_. forest_assn (forest st) Fi * missed_assn (missed st) Mi *
              pot_assn (new_potential st) Pti>"
proof-
  note fold1 = iter_fold_rule_gen[where I = "\<lambda>xs it. forest_assn (forest st) Fi *
                                               forest_is_it Evens (aevens st) Fi xs it"
      and Q = "forest_assn (forest st) Fi"
      and A = "\<lambda>p (u::unit). pot_assn p Pti * missed_assn (missed st) Mi",
      OF forest.ev.it_has_next_rule forest.ev.it_next_rule forest.ev.quit_iteration
         pot_step_even_rule[OF _ assms(2,3)] new_pot_pre(1)[OF assms(1)]]
  note fold2 = iter_fold_rule_gen[where I = "\<lambda>xs it. forest_assn (forest st) Fi *
                                               forest_is_it Odds (aodds st) Fi xs it"
      and Q = "forest_assn (forest st) Fi"
      and A = "\<lambda>p (u::unit). pot_assn p Pti * missed_assn (missed st) Mi",
      OF forest.od.it_has_next_rule forest.od.it_next_rule forest.od.quit_iteration
         pot_step_odd_rule[OF _ assms(2,3)] new_pot_pre(2)[OF assms(1)]]
  show ?thesis
    unfolding code.new_pot_imp_def
    by (sep_auto heap: forest.ev.it_init_rule[OF forest_parts_props(3)[OF assms(1)]]
                       forest.od.it_init_rule[OF forest_parts_props(4)[OF assms(1)]] fold1 fold2
                 simp: new_potential_foldl[OF assms(1)])
qed

subsection \<open>The Path Search\<close>

lemma init_ok_foldl:
  "\<lbrakk>set xs \<subseteq> L; init_ok cbq\<rbrakk> \<Longrightarrow>
   init_ok (foldl (\<lambda>cbq l. update_best_even_neighbour (\<lambda>x. 0) (fst cbq) (fst (snd cbq))
                              (snd (snd cbq)) l) cbq xs)"
  by (induction xs arbitrary: cbq) (simp_all add: init_ok_step)

lemma init_ok_initial: "init_ok init_best_even_neighbour"
  using init_fold_result init_ok_foldl[OF _ init_ok_init, of "filter (\<lambda>v. buddy_get v = nil) (lst L)"]
        forest.lst_set[OF finite_L]
  by (auto simp: init_fold)

lemma scratch_assnI:
  "\<lbrakk>rnb_invar C; rnb_abstract C = rnb_abstract rnb_init; ben_invar B; missed_invar M\<rbrakk> \<Longrightarrow>
   nb_assn C Ci * queue_assn H Qi * forest_assn F Fi * ben_assn B Bi * missed_assn M Mi
   \<Longrightarrow>\<^sub>A scratch_assn Ci Qi Fi Bi Mi"
  unfolding scratch_assn_def
  by (sep_auto simp: fun_eq_iff)

text \<open>The result of the imperative search, relative to the functional one.\<close>

definition "search_post Pti res xs' =
  (case search_path of (r, \<pi>') \<Rightarrow> \<up>(imp_result_rel xs' res r) * pot_assn \<pi>' Pti)"

lemma init_ben_props:
  "rnb_invar (fst init_best_even_neighbour)"
  "rnb_abstract (fst init_best_even_neighbour) = rnb_abstract rnb_init"
  "ben_invar (fst (snd init_best_even_neighbour))"
  using init_ok_initial
  by (simp_all add: init_ok_def)

lemma search_initial_invars: "\<not> vset_is_empty unmatched_lefts \<Longrightarrow> search_invars initial_state"
  using unmatched_lefts vset_is_empty search_invars_init
  by simp

lemma search_path_final:
  "\<not> vset_is_empty unmatched_lefts \<Longrightarrow>
   search_path = (case augpath (search_path_loop initial_state) of
                    None \<Rightarrow> (Dual_Unbounded, initial_pot)
                  | Some p \<Rightarrow> (Next_Iteration p, new_potential (search_path_loop initial_state)))"
  using search_invars_dom[OF search_initial_invars]
  by (simp add: search_path_def search_path_loop_impl_same Let_def)

lemma initial_state_fields:
  "neighb_coll initial_state = fst init_best_even_neighbour"
  "heap initial_state = snd (snd init_best_even_neighbour)"
  "forest initial_state = empty_forest forest_roots"
  "best_even_neighbour initial_state = fst (snd init_best_even_neighbour)"
  "missed initial_state = missed_empty"
  by (simp_all add: initial_state_def)

lemma \<^marker>\<open>provenance ai_human\<close> search_imp_rule:
  assumes "card (L \<union> R) \<le> length xs"
  shows "<scratch_assn Ci Qi Fi Bi Mi * vset_assn left Li * buddy_assn Bdi *
          pot_assn initial_pot Pti * Ra \<mapsto>\<^sub>a xs>
         code.search_imp Ci Qi Pti Bdi Li Ra Fi Bi Mi
         <\<lambda>(res, Fi'). \<exists>\<^sub>Axs'.
            scratch_assn Ci Qi Fi' Bi Mi * vset_assn left Li * buddy_assn Bdi *
            Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) * search_post Pti res xs'>"
proof(cases "vset_is_empty unmatched_lefts")
  case True
  show ?thesis
    unfolding code.search_imp_def
    apply(sep_auto heap: clear_imp_rule init_imp_rule simp: True)
    using init_ben_props True
    by (sep_auto simp: scratch_assn_def search_post_def search_path_def fun_eq_iff missed(1))
next
  case False
  note inv = search_initial_invars[OF False]
  note fb = invar_basic_props[OF loop_final_basic[OF inv]]
  note lp = loop_imp_rule[OF inv assms, unfolded loop_assn_def initial_state_fields]
  show ?thesis
  proof(cases "augpath (search_path_loop initial_state)")
    case None
    show ?thesis
      unfolding code.search_imp_def
      apply(sep_auto heap: clear_imp_rule init_imp_rule lp simp: False)
      apply(all \<open>clarsimp simp: None res_rel_def False\<close>)
      using fb(2-5)
      by (sep_auto simp: loop_post_def scratch_assn_def search_post_def search_path_final False None
                         fun_eq_iff)
  next
    case (Some p)
    show ?thesis
      unfolding code.search_imp_def
      apply(sep_auto heap: clear_imp_rule init_imp_rule lp simp: False)
      apply(all \<open>clarsimp simp: Some res_rel_def False\<close>)
      using fb(2-5)
      by (sep_auto heap: new_pot_imp_rule[OF fb(6) _ fb(3)]
                   simp: loop_post_def scratch_assn_def search_post_def search_path_final False Some
                         fun_eq_iff)
  qed
qed

end
end

