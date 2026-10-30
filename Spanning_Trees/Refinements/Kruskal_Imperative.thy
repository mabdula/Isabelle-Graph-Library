theory Kruskal_Imperative
  imports Spanning_Trees.Kruskal
          Separation_Logic_Imperative_HOL_Partial.Sep_Main
          "HOL-Library.Rewrite"
begin

provenance ai_human

no_notation Ref.update (\<open>_ := _\<close> 62)

section \<open>Imperative Kruskal's Algorithm\<close>

subsection \<open>Setup\<close>

text \<open>The imperative state.

  The list of remaining edges of the functional state is refined by an array together with a
  pointer into that array: the part of the array starting at the pointer is the list of
  remaining edges. Advancing in the list is thus implemented by incrementing the pointer.

  The result of the functional state is a pair of the list of chosen edges and a union-find
  structure. The list of chosen edges is kept as a (pure) list, since new edges are only
  prepended to it. The union-find structure (of type \<open>'u\<close>) is refined by an imperative
  union-find structure (of type \<open>'ui\<close>), connected via the assertion \<open>uf_assn\<close>.\<close>

record ('e, 'ui) kruskal_state_imp =
  edge_array :: "'e array" edge_ptr :: nat result_list :: "'e list" uf_impl :: 'ui

text \<open>We assume imperative implementations of the union-find operations, together with Hoare
  triples relating them to their functional counterparts. They are only required to work on
  union-find structures satisfying the invariant and on elements of the universe.

  The endpoints of the edges are given by imperative data (of type \<open>'epi\<close>), which refines the
  functional function \<open>endpoints\<close> via the assertion \<open>endpoints_assn\<close>. The endpoints of an edge
  are obtained with \<open>endpoints_impl\<close>, which is only required to work on the edges in \<open>order\<close>.
  For example, if edges are natural numbers, the endpoints can be stored in an array of pairs,
  indexed by the edges.

  As in \<open>BestInGreedy_Imperative\<close>, we additionally assume an imperative cost function
  \<open>c_impl\<close> (of type \<open>'ci\<close>), which refines the functional cost function \<open>c\<close> via the assertion
  \<open>cost_assn\<close>, and an imperative sorting function \<open>sort_desc_impl\<close>, which sorts an array of
  edges in \<open>order\<close> in-place and only reads the cost function. For example, \<open>c_impl\<close> can be an
  array of costs on the heap, indexed by the edges.\<close>

locale Kruskal_Imperative = Kruskal
  where lookup = "lookup :: 'adjmap \<Rightarrow> ('v::{linorder, heap}) \<Rightarrow> 'vset option"
    and uf_invar = "uf_invar :: 'u \<Rightarrow> 'i \<Rightarrow> bool"
    and order = "order :: ('e::{linorder, heap}) list"
  for lookup uf_invar order +
  fixes uf_assn :: "'u \<Rightarrow> 'ui \<Rightarrow> assn"
    and uf_init_impl :: "'i \<Rightarrow> 'ui Heap"
    and uf_merge_impl :: "'ui \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'ui Heap"
    and uf_in_same_set_impl :: "'ui \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and endpoints_assn :: "('e \<Rightarrow> 'v \<times> 'v) \<Rightarrow> 'epi \<Rightarrow> assn"
    and endpoints_impl :: "'epi \<Rightarrow> 'e \<Rightarrow> ('v \<times> 'v) Heap"
    and cost_assn :: "('e \<Rightarrow> rat) \<Rightarrow> 'ci \<Rightarrow> assn"
    and sort_desc_impl :: "'ci \<Rightarrow> 'e array \<Rightarrow> 'e array Heap"
  assumes uf_init_impl_rule[sep_heap_rules]:
    "<emp> uf_init_impl s <uf_assn (uf_init s)>"
  and uf_merge_impl_rule[sep_heap_rules]:
    "\<lbrakk>uf_invar u s; x \<in> uf_set s; y \<in> uf_set s\<rbrakk> \<Longrightarrow>
      <uf_assn u ui> uf_merge_impl ui x y <uf_assn (merge u x y)>"
  and uf_in_same_set_impl_rule[sep_heap_rules]:
    "\<lbrakk>uf_invar u s; x \<in> uf_set s; y \<in> uf_set s\<rbrakk> \<Longrightarrow>
      <uf_assn u ui> uf_in_same_set_impl ui x y <\<lambda>r. uf_assn u ui * \<up>(r = in_same_set u x y)>"
  and endpoints_impl_rule[sep_heap_rules]:
    "e \<in> set order \<Longrightarrow>
      <endpoints_assn endpoints ep_impl> endpoints_impl ep_impl e
      <\<lambda>r. endpoints_assn endpoints ep_impl * \<up>(r = endpoints e)>"
  and sort_desc_impl_rule[sep_heap_rules]:
    "set es \<subseteq> set order \<Longrightarrow>
      <cost_assn c c_impl * edges_array \<mapsto>\<^sub>a es> sort_desc_impl c_impl edges_array
      <\<lambda>r. cost_assn c c_impl * edges_array \<mapsto>\<^sub>a sort_desc c es * \<up>(r = edges_array)>"
begin

subsection \<open>State\<close>

text \<open>The array holds some list \<open>ys\<close>, whose suffix starting at the pointer is the list of
  remaining edges. The prefix of \<open>ys\<close> (the edges already processed) is irrelevant.
  The invariant of the union-find structure is preserved by merging any two vertices of the
  universe, so it suffices to know that all remaining edges are edges of the graph.
  The imperative endpoints data is not part of the state; it is passed to the main loop
  separately, since it is only read.\<close>

definition "kruskal_state_assn state si \<equiv>
    (\<exists>\<^sub>Ays. edge_array si \<mapsto>\<^sub>a ys
       * \<up>(edge_ptr si \<le> length ys \<and> drop (edge_ptr si) ys = carrier_list state))
  * uf_assn (snd (result state)) (uf_impl si)
  * \<up>(result_list si = fst (result state) \<and> uf_invar (snd (result state)) s
      \<and> set (carrier_list state) \<subseteq> set order)"

text \<open>The initial state is created from an array holding the list of edges and an imperative
  cost function. The array is sorted in-place, and then becomes the edge array.\<close>

definition "kruskal_initial_state_impl c_impl edges_array = do {
  edge_array \<leftarrow> sort_desc_impl c_impl edges_array;
  uf \<leftarrow> uf_init_impl s;
  Heap_Monad.return \<lparr> edge_array = edge_array, edge_ptr = 0, result_list = [], uf_impl = uf \<rparr>
}"

subsection \<open>Main Algorithm\<close>

partial_function (heap) kruskal_imperative ::
  "'epi \<Rightarrow> ('e, 'ui) kruskal_state_imp \<Rightarrow> ('e, 'ui) kruskal_state_imp Heap" where
  "kruskal_imperative ep_impl state = do {
     len \<leftarrow> Array.len (edge_array state);
     (if edge_ptr state < len then do {
        e \<leftarrow> Array.nth (edge_array state) (edge_ptr state);
        uv \<leftarrow> endpoints_impl ep_impl e;
        b \<leftarrow> uf_in_same_set_impl (uf_impl state) (fst uv) (snd uv);
        (if \<not> b then do {
           uf \<leftarrow> uf_merge_impl (uf_impl state) (fst uv) (snd uv);
           kruskal_imperative ep_impl (state
             \<lparr>edge_ptr := edge_ptr state + 1, result_list := e # result_list state,
              uf_impl := uf\<rparr>)
         }
         else
           kruskal_imperative ep_impl (state \<lparr>edge_ptr := edge_ptr state + 1\<rparr>))
      }
      else Heap_Monad.return state)
  }"

text \<open>The complete algorithm returns the list of chosen edges.\<close>

definition "kruskal_imperative' c_impl ep_impl edges_array = do {
  state \<leftarrow> kruskal_initial_state_impl c_impl edges_array;
  state' \<leftarrow> kruskal_imperative ep_impl state;
  Heap_Monad.return (result_list state')
}"

lemmas [code] = kruskal_imperative.simps kruskal_initial_state_impl_def kruskal_imperative'_def

subsection \<open>Refinement of the Functional Algorithm\<close>

lemma order_endpoints_in_universe[simp]:
  "e \<in> set order \<Longrightarrow> fst (endpoints e) \<in> uf_set s"
  "e \<in> set order \<Longrightarrow> snd (endpoints e) \<in> uf_set s"
  using order_edge_props(3,4)[of e "fst (endpoints e)" "snd (endpoints e)"] by auto

lemma set_sort_desc_order: "set (sort_desc c order) = set order"
  using sort_desc_axioms by (simp add: sort_desc_axioms_def)

lemma kruskal_initial_state_rule[sep_heap_rules]:
  "<cost_assn c c_impl * edges_array \<mapsto>\<^sub>a order>
     kruskal_initial_state_impl c_impl edges_array
   <\<lambda>si. cost_assn c c_impl * kruskal_state_assn (kruskal_greedy.initial_state' c order) si>"
  unfolding kruskal_initial_state_impl_def kruskal_greedy.initial_state'_def kruskal_state_assn_def
  by (sep_auto simp: uf.uf_init_invar set_sort_desc_order kruskal_wrapper_empty_def)

text \<open>Reading the head of the remaining edges from the array.\<close>

lemma drop_eq_Cons_conv:
  "drop p ys = x # xs \<longleftrightarrow> p < length ys \<and> ys ! p = x \<and> drop (Suc p) ys = xs"
  by (metis Cons_nth_drop_Suc drop_all leI list.distinct(1) list.inject)

lemma kruskal_imperative_rule[sep_heap_rules]:
  "<endpoints_assn endpoints ep_impl * kruskal_state_assn state statei>
     kruskal_imperative ep_impl statei
   <\<lambda>ri. endpoints_assn endpoints ep_impl *
     kruskal_state_assn (kruskal_greedy.BestInGreedy_exec state) ri>"
proof (induction arbitrary: state statei rule: kruskal_imperative.fixp_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 f)

  note IH = "3.IH"[of "\<lparr>carrier_list = cl, result = (R, uf)\<rparr>"
                     "\<lparr>edge_array = ea, edge_ptr = p, result_list = rl, uf_impl = ui\<rparr>"
                     for cl R uf ea p rl ui]
  note IH[sep_heap_rules] = IH[unfolded kruskal_state_assn_def, simplified, rule_format]

  let "<?P> ?body <\<lambda>r. ?post (kruskal_greedy.BestInGreedy_exec state) r>" = ?case
  define P where "P = ?P"
  define body where "body = ?body"
  define post where "post = ?post"

  note IMP_DEFS = P_def body_def post_def kruskal_state_assn_def

  show "<P> body <\<lambda>r. post (kruskal_greedy.BestInGreedy_exec state) r>"
    apply (cases state; cases statei; simp)
    subgoal for carrier_list result edge_array edge_ptr result_list uf_impl
      apply (cases result; simp)
      subgoal for R uf
        (* The functional algorithm controls the case split. *)
        apply (rewrite in "<_> _ <\<hole>>" kruskal_greedy.BestInGreedy_exec.simps)
        apply (clarsimp split!: list.split if_split
            simp: Let_def kruskal_oracle_def kruskal_wrapper_insert_def)

        subgoal (* no edges left *)
          unfolding IMP_DEFS by sep_auto

        subgoal (* the edge connects two different components *)
          unfolding IMP_DEFS by (sep_auto simp: drop_eq_Cons_conv uf.merge_invar)

        subgoal (* the edge would close a cycle *)
          unfolding IMP_DEFS by (sep_auto simp: drop_eq_Cons_conv uf.merge_invar)
        done
      done
    done
qed

text \<open>The imperative algorithm returns the list of edges computed by the functional algorithm.\<close>

lemma kruskal_imperative'_rule[sep_heap_rules]:
  "<cost_assn c c_impl * endpoints_assn endpoints ep_impl * edges_array \<mapsto>\<^sub>a order>
     kruskal_imperative' c_impl ep_impl edges_array
   <\<lambda>r. cost_assn c c_impl * endpoints_assn endpoints ep_impl * \<up>(r = kruskal_result c) * true>"
  unfolding kruskal_imperative'_def kruskal_def
  by (sep_auto simp: kruskal_state_assn_def)

subsection \<open>Correctness\<close>

theorem kruskal_imperative'_correct:
  assumes "\<And>e. e \<in> set order \<Longrightarrow> c e \<ge> 0"
  shows
    "<cost_assn c c_impl * endpoints_assn endpoints ep_impl * edges_array \<mapsto>\<^sub>a order>
       kruskal_imperative' c_impl ep_impl edges_array
     <\<lambda>r. cost_assn c c_impl * endpoints_assn endpoints ep_impl * \<up>(
         set r \<subseteq> set order
       \<and> graph_abs.is_spanning_forest E (set_of_edge ` set r)
       \<and> (\<forall>X. X \<subseteq> set order \<and> graph_abs.has_no_cycle E (set_of_edge ` X) \<longrightarrow>
            sum c X \<le> sum c (set r))) * true>"
  by (rule ht_cons_post_prec[OF kruskal_imperative'_rule])
    (sep_auto simp: kruskal_subset[OF assms] kruskal_spanning_forest[OF assms]
      kruskal_max_weight[OF assms])

end

end
